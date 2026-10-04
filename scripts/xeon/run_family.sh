#!/bin/bash
# One family, two stages, resumable. This is the pipeline of the paper:
#   stage 1  the algebraic (series) solver alone on every instance of the family
#            (DecompositionCanonicalFormsTest.parityCampaign, SOLVER=seriesfull, no fallback, paper caps, 300 s);
#   stage 2  the decomposition-guided stabiliser chain on every instance that stage 1 did not solve exactly
#            (PieceProfileTest.stabiliserChain, one JVM per instance, PI start, retried from plain 1-WL
#            (SC_COLOUR=wl1) when the PI colouring runs out of memory; 1-WL start on r2/s2/t2, see COLOUR).
# No Traces in stages 1 and 2 (our times are purely ours). The oracle / baseline is a SEPARATE job:
#   ./run_traces.sh <family>   (uncoloured Traces, one process per instance); summarize.py joins the two.
#
# Usage (from the directory the files were copied into, see README.md):
#   GRAPHS=/path/to/graphs ./run_family.sh <family>          (dialysis-paper3.jar next to this script)
# Stop it any time (Ctrl-C); running it again continues where it stopped:
#   stage 1 skips instances that already have a row in results/<family>/series.csv,
#   stage 2 skips instances listed in results/<family>/chain_done.txt.
#
# Settings (environment, defaults in brackets):
#   GRAPHS        folder holding the family folders                                  [required]
#   OUT           output folder                                                      [./results]
#   SERIES_HEAP   -Xmx of the stage-1 JVM (one JVM for the whole family)              [6g]
#   SERIES_DEADLINE  stage-1 solver budget per instance, seconds (colouring time not counted). The paper's
#                 setting is 300; had-sw from 352 vertices needs ~10-20 min (base length 3: ~n^3 image
#                 tuples, polynomial but large), e.g. SERIES_DEADLINE=2400 for had-sw            [300]
#   CHAIN_HEAP    -Xmx of each stage-2 JVM                                            [3g]
#   CHAIN_JOBS    stage-2 instances in parallel (8 GB machine: keep 2)                [2]
#   CHAIN_TIMEOUT wall-clock limit per stage-2 instance, seconds                      [3600]
#   CHAIN_COMPLEMENT  1 = before the chain, replace every dense pair of 1-WL classes by its complement, when that removes
#                 at least half of the edges (exact: the group does not change; every final generator is re-verified
#                 on the original graph). Solves tnn (non-disjoint unions) far faster; no effect on other families. [0]
#   CHAIN_AFFINE  1 = an affine plane is solved through its projective completion (points at infinity and the line at
#                 infinity added and marked; exact, generators re-verified on the original graph). Needed for rigid
#                 affine planes (Aff25); on ag it is exact but slower, 0 keeps the plain chain.            [1]
#   CHAIN_THREADS threads per stage-2 JVM for the plane invariants (projective/affine planes only; results and
#                 queries are identical to 1 thread, only faster). For pp: CHAIN_JOBS=1 CHAIN_THREADS=12   [1]
#   CHAIN_PRUNE   1 = automorphism pruning in the chain's witness search (projective planes: pp)      [0]
#   CHAIN_MAXDEPTH  most decomposition roots the chain individualises                 [32]
#   CHAIN_WORK1 / CHAIN_WORK2  deterministic work budget of the chain's first / second pass per depth
#                 (solver work units; the defaults equal ~10 s / ~60 s on the laptop)   [built into the jar]
#   JAVA          java binary (>= 17)                                                [java]
#   COLOUR        starting colouring of both stages: pi (our PI colouring) or wl1 (plain canonical 1-WL).
#                 On cfi-rigid-r2/s2/t2 1-WL gives the same partition as PI at a fraction of the cost; with wl1,
#                 stage 2 also runs from 1-WL directly.
#                 auto: stage 1 probes from 1-WL and computes PI only if the solver stops because no short base
#                 breaks a class (or on time); stage 2 then starts from PI exactly for the instances that escalated.
#                 The decision is recorded in series.csv, column stop_detail ("auto: ...").
#                                                         [wl1 for cfi-rigid-r2, -s2, -t2; pi otherwise]
#   TMP_DIR       folder for the PI colouring's temp files (needs GBs on big instances) [system temp]
#   JAR           the executable jar                                                 [./dialysis-paper3.jar]
set -u
FAM=${1:?give a family name, e.g. ./run_family.sh cfi-rigid-r2}
HERE=$(cd "$(dirname "$0")" && pwd)
: "${GRAPHS:?set GRAPHS=/path/to/graphs (the folder that contains cfi-rigid-r2/, pp/, johnson/, ...)}"
GRAPHS=$(cd "$GRAPHS" 2>/dev/null && pwd) || { echo "GRAPHS folder not found"; exit 2; }   # absolute: the script changes directory
[ -d "$GRAPHS/$FAM" ] || { echo "no such family folder: $GRAPHS/$FAM"; exit 2; }
OUT=${OUT:-$HERE/results}; mkdir -p "$OUT"; OUT=$(cd "$OUT" && pwd); SERIES_HEAP=${SERIES_HEAP:-6g}; CHAIN_HEAP=${CHAIN_HEAP:-3g}
SERIES_DEADLINE=${SERIES_DEADLINE:-300}; CHAIN_JOBS=${CHAIN_JOBS:-2}; CHAIN_TIMEOUT=${CHAIN_TIMEOUT:-3600}; JAVA=${JAVA:-java}
CHAIN_MAXDEPTH=${CHAIN_MAXDEPTH:-32}; CHAIN_WORK1=${CHAIN_WORK1:-}; CHAIN_WORK2=${CHAIN_WORK2:-}; CHAIN_THREADS=${CHAIN_THREADS:-1}; CHAIN_COMPLEMENT=${CHAIN_COMPLEMENT:-0}; CHAIN_AFFINE=${CHAIN_AFFINE:-1}; CHAIN_PRUNE=${CHAIN_PRUNE:-0}
R=$OUT/$FAM; mkdir -p "$R/chain"
case "$FAM" in cfi-rigid-r2|cfi-rigid-s2|cfi-rigid-t2) COLOUR=${COLOUR:-wl1} ;; *) COLOUR=${COLOUR:-pi} ;; esac
case "$COLOUR" in pi|wl1|auto) ;; *) echo "COLOUR must be pi, wl1 or auto"; exit 2 ;; esac
echo "$COLOUR" > "$R/colour.txt"   # recorded for the paper's table (which colouring each family started from)
echo "$(date +%T) [$FAM] starting colouring: $COLOUR"
# TMP_DIR: where the PI colouring writes its temp files (up to a few GB per large instance; the default
# /tmp may be too small or RAM-backed). Created if missing and made absolute (the script changes directory).
TMPBASE=${TMP_DIR:-${TMPDIR:-/tmp}}
mkdir -p "$TMPBASE" && TMPBASE=$(cd "$TMPBASE" && pwd) || { echo "cannot create TMP_DIR=$TMPBASE"; exit 2; }
# Every JVM gets its own temp folder inside RUNTMP, deleted as soon as that JVM exits: a JVM that is killed or times
# out never deletes its PI files itself (several GB each; 2026-10-01 they filled a 468 GB laptop disk). RUNTMP itself
# is removed when this script exits, also on Ctrl-C.
RUNTMP=$(mktemp -d "$TMPBASE/p3run.XXXXXX") || { echo "cannot create a temp folder in $TMPBASE"; exit 2; }
trap 'rm -rf "$RUNTMP"' EXIT
trap 'exit 130' INT TERM
JAVA_HOME_GUESS=$(dirname "$(dirname "$(readlink -f "$(command -v "$JAVA")")")")
JSIG=$JAVA_HOME_GUESS/lib/server/libjsig.so; [ -f "$JSIG" ] || JSIG=""
JAR=${JAR:-$HERE/dialysis-paper3.jar}; [ -f "$JAR" ] || { echo "missing $JAR (build it: ./gradlew paperJar, then JAR=build/libs/dialysis-paper3.jar)"; exit 2; }

# ---------------------------------------------------------------- stage 1: algebraic solver alone
# Small instances share one JVM (fast); every LARGE instance gets a fresh JVM, as in stage 2: in one long-running JVM
# the PI colouring's memory-mapped temp files and native memory pile up, and the large instances then fail with an
# ExecutionException (seen on cfi-rigid-z2 n >= 4,048). Rows that ended in ERROR_ are dropped and retried.
echo "$(date +%T) [$FAM] stage 1: algebraic solver alone"
python3 - "$GRAPHS/$FAM" "$R/series.csv" "$R/stage1_small.txt" "$R/stage1_large.txt" "${LARGE_EFF:-3000}" <<'EOF'
import csv, os, sys
d, csvp, small_p, large_p, lim = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4], int(sys.argv[5])
done = set()
if os.path.exists(csvp):                       # keep finished rows, drop ERROR_ rows so they are retried
    rows = list(csv.reader(open(csvp)))
    keep = [rows[0]] + [r for r in rows[1:] if not r[22].startswith('ERROR_')]
    if len(keep) != len(rows):
        with open(csvp, 'w', newline='') as f: csv.writer(f).writerows(keep)
    done = {r[1] for r in keep[1:]}
def eff(path):                                 # number of vertices (the PI colouring's memory is O(n^2))
    for line in open(path):
        t = line.split()
        if t and t[0] == 'p': return int(t[2])
    return 0
small, large = [], []
for f in sorted(os.listdir(d)):
    p = os.path.join(d, f)
    if not os.path.isfile(p) or f.startswith('.') or f in done: continue
    (large if os.path.getsize(p) > 20000 and eff(p) > lim else small).append(f)
open(small_p, 'w').write('\n'.join(small) + ('\n' if small else ''))
open(large_p, 'w').write('\n'.join(large) + ('\n' if large else ''))
print(f"  stage 1 to do: {len(small)} small (one JVM), {len(large)} large (one JVM each)")
EOF
s1() {   # $1 = instances file; one JVM
  ( cd "$R" && ln -sfn "$GRAPHS" graphs && jt=$(mktemp -d "$RUNTMP/jvm.XXXXXX") &&
    LD_PRELOAD=$JSIG FAMILY=$FAM DIR=$FAM SOLVER=seriesfull SERIES_COLOUR=$COLOUR IR_FALLBACK=0 OUT="$R/series.csv" NO_TRACES=1 INSTANCES_FILE="$1" \
    CAP=1000000 DEADLINE_S=$SERIES_DEADLINE MAX_CAND=20000 MAX_BASE=12 MAX_NODES=200000 MAX_PAIR=3000000 \
    timeout "${2:-864000}" "$JAVA" -Xmx$SERIES_HEAP -XX:+UseG1GC -Ddialysis.tmpDir=$jt -jar "$JAR" series >> "$R/series.log" 2>&1
    rm -rf "$jt" )
}
[ -s "$R/stage1_small.txt" ] && s1 "$R/stage1_small.txt"
while read -r name; do
  [ -n "$name" ] || continue
  echo "$name" > "$R/stage1_one.txt"; s1 "$R/stage1_one.txt" $(( SERIES_DEADLINE * 2 + 1200 ))
  echo "$(date +%T) [$FAM] stage 1 $name: $(grep -F ",$name," "$R/series.csv" | tail -1 | python3 -c 'import csv,sys; r=next(csv.reader(sys.stdin),None); print(r[22], r[23]+"s" if r else "") if r else print("no row (killed or crashed)")')"
  grep -qF ",$name," "$R/series.csv" || { echo "    last lines of series.log:"; tail -8 "$R/series.log" | sed 's/^/      /'; }
done < "$R/stage1_large.txt"
echo "$(date +%T) [$FAM] stage 1 done: $(( $(wc -l < "$R/series.csv" 2>/dev/null || echo 1) - 1 )) rows"

# ---------------------------------------------------------------- stage 2: chain on what stage 1 did not solve
# instances = every file of the family whose stage-1 status is not EXACT (including files stage 1 never reached)
python3 - "$GRAPHS/$FAM" "$R/series.csv" > "$R/chain_todo.txt" <<'EOF'
import csv, os, sys
d, csvp = sys.argv[1], sys.argv[2]
exact = set()
if os.path.exists(csvp):
    for r in csv.DictReader(open(csvp)):
        if r['status'] == 'EXACT': exact.add(r['instance'])
files = []
for f in os.listdir(d):
    p = os.path.join(d, f)
    if os.path.isfile(p) and not f.startswith('.') and f not in exact:
        files.append((os.path.getsize(p), f))
for _, f in sorted(files): print(f)
EOF
touch "$R/chain_done.txt"
TODO=$(grep -vxF -f <(cut -d' ' -f1 "$R/chain_done.txt") "$R/chain_todo.txt" || true)
echo "$(date +%T) [$FAM] stage 2: chain on $(echo "$TODO" | grep -c . ) instances ($(wc -l < "$R/chain_todo.txt") not exact after stage 1)"

chain_one() {
  name=$1
  run() {   # $1 = colour mode (pi|wl1)
    mode=$1; extra=""; [ "$mode" = wl1 ] && extra="SC_COLOUR=wl1"
    [ -n "$CHAIN_WORK1" ] && extra="$extra SC_WORK1=$CHAIN_WORK1"; [ -n "$CHAIN_WORK2" ] && extra="$extra SC_WORK2=$CHAIN_WORK2"
    rm -f "$R/chain/$name.$mode.txt"
    jt=$(mktemp -d "$RUNTMP/jvm.XXXXXX")
    env LD_PRELOAD=$JSIG SC_NO_TRACES=1 SC_COMPLEMENT=$CHAIN_COMPLEMENT SC_AFFINE=$CHAIN_AFFINE SC_PRUNE=$CHAIN_PRUNE SC_THREADS=$CHAIN_THREADS SC_MAXDEPTH=$CHAIN_MAXDEPTH SC_FILES="$GRAPHS/$FAM/$name" OUT="$R/chain/$name.$mode.txt" $extra \
      timeout "$CHAIN_TIMEOUT" "$JAVA" -Xmx$CHAIN_HEAP -XX:+UseG1GC -Ddialysis.tmpDir=$jt -jar "$JAR" chain > "$R/chain/$name.$mode.log" 2>&1
    rc=$?; rm -rf "$jt"; echo $rc
  }
  status=""; want=$COLOUR
  if [ "$COLOUR" = auto ]; then   # PI only where stage 1 escalated to it
    want=$(python3 -c "import csv,sys; r=[x for x in csv.DictReader(open('$R/series.csv')) if x['instance']=='$name']; print('pi' if r and 'escalated to PI' in r[-1]['stop_detail'] else 'wl1')" 2>/dev/null || echo wl1)
  fi
  if [ "$want" = pi ]; then rc=$(run pi); fi
  if [ "$want" = pi ] && grep -q 'Aut| =' "$R/chain/$name.pi.txt" 2>/dev/null; then status=pi
  elif [ "$want" = pi ] && grep -q 'no exact depth' "$R/chain/$name.pi.txt" 2>/dev/null; then status=pi-noexact
  elif [ "$want" = pi ] && [ "$rc" = 124 ]; then status=pi-timeout
  else   # COLOUR=wl1, or PI ran out of memory / crashed: run from plain 1-WL (sound: any invariant colouring works)
    rc=$(run wl1)
    if grep -q 'Aut| =' "$R/chain/$name.wl1.txt" 2>/dev/null; then status=wl1
    elif grep -q 'no exact depth' "$R/chain/$name.wl1.txt" 2>/dev/null; then status=wl1-noexact
    elif [ "$rc" = 124 ]; then status=wl1-timeout
    else status=wl1-fail-rc$rc; fi
  fi
  [ -n "$status" ] || status=unknown
  echo "$name $status" >> "$R/chain_done.txt"
  echo "$(date +%T) [$FAM] $name: $status $(grep -h 'Aut| =' "$R/chain/$name".*.txt 2>/dev/null | tail -1 | sed 's/  */ /g')"
}
export -f chain_one; export COLOUR RUNTMP R FAM GRAPHS CHAIN_HEAP CHAIN_TIMEOUT CHAIN_THREADS CHAIN_COMPLEMENT CHAIN_AFFINE CHAIN_PRUNE CHAIN_MAXDEPTH CHAIN_WORK1 CHAIN_WORK2 JAVA JSIG JAR
[ -n "$TODO" ] && echo "$TODO" | xargs -P "$CHAIN_JOBS" -I{} bash -c 'chain_one "$1"' _ {}
echo "$(date +%T) [$FAM] stage 2 done"

python3 "$HERE/summarize.py" "$OUT" "$GRAPHS" "$FAM"