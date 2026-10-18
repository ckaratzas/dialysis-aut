#!/bin/bash
# Stress test for the decomposition-guided stabiliser chain (CLOSURE_BOUND_SPEC.md, "find something we cannot break"):
# Latin square graphs of RANDOM class-2 p-groups (few automorphisms), the hard case for group isomorphism.
# Diagnostic instances only -- not a benchmark family, not for the paper.
#
#   1. generate the instances (plain python3)                             -> $INST
#   2. the chain on every instance, in every mode of $MODES, one JVM each -> $OUT/chain_<name>.<mode>.{txt,log}
#      base  = SC_NODE_INV=1 SC_FP_AFTER=8 SC_PRUNE=1 (node-invariant pruning, delayed fingerprint, automorphism pruning)
#      reset = base + SC_RESET=adaptive SC_RESET_SKIP=1 (restart with the known generators after the first deep refutation)
#      look  = base + SC_STABPRUNE=1 SC_LOOKAHEAD=1 SC_LOOK_FRAC=0.1 (2026-10-17: stabiliser-orbit pruning + lookahead)
#   3. uncoloured Traces on every instance, separately (oracle)           -> $OUT/traces.csv
#   4. summary                                                            -> $OUT/summary.txt
#
# Usage (from the folder holding this script, gen_class2_stress.py and the jar):
#   ./run_stress.sh                      # the default set: 3 x order 243, 3 x order 256, 2 x order 128, 2 controls
#   SPECS="3,3,2,1 2,5,3,1" ./run_stress.sh
# Run it inside tmux/screen. Resumable: a (instance, mode) with a finished .txt is skipped; delete it to redo.
#
# Settings (environment, defaults in brackets):
#   SPECS          generator specs p,d,e,seed (ctl:p,d,e,0 = symmetric control) or 'default'          [default]
#   INST           instance folder                                                                     [./stress_instances]
#   OUT            results folder                                                                      [./stress_results]
#   MODES          chain modes                                                                         ["base reset"]
#   JOBS           chain JVMs in parallel                                                              [2]
#   HEAP           -Xmx per chain JVM (65,536 vertices, 25M edges)                                     [24g]
#   TIMEOUT_S      wall clock per chain run                                                            [14400]
#   TRACES_TIMEOUT wall clock per Traces run (0 = skip Traces)                                         [14400]
#   TRACES_HEAP    -Xmx of the Traces JVM (Traces itself is native and not bounded by it)              [8g]
#   TMP_DIR        temp folder (each JVM gets its own subfolder, removed on exit)                      [system temp]
#   JAR            the executable jar                                                                  [./dialysis-paper3-fpfast.jar]
#   JAVA           java binary (>= 17)                                                                 [java]
#   FASTNODE       1 = incremental numeric node colourings in the tuple search (same results, faster)  [1]
#   XMS            initial heap of every JVM (keep small: a large default initial heap failed to commit) [2g]
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
SPECS=${SPECS:-default}; INST=${INST:-$HERE/stress_instances}; OUT=${OUT:-$HERE/stress_results}
MODES=${MODES:-base reset}; JOBS=${JOBS:-2}; HEAP=${HEAP:-24g}; TIMEOUT_S=${TIMEOUT_S:-14400}
TRACES_TIMEOUT=${TRACES_TIMEOUT:-14400}; TRACES_HEAP=${TRACES_HEAP:-8g}
JAR=${JAR:-$HERE/dialysis-paper3-fpfast.jar}; JAVA=${JAVA:-java}; FASTNODE=${FASTNODE:-1}; XMS=${XMS:-2g}
[ -f "$JAR" ] || { echo "jar not found: $JAR"; exit 2; }
mkdir -p "$INST" "$OUT"
TMPBASE=${TMP_DIR:-${TMPDIR:-/tmp}}; mkdir -p "$TMPBASE" && TMPBASE=$(cd "$TMPBASE" && pwd) || { echo "cannot create TMP_DIR"; exit 2; }
RUNTMP=$(mktemp -d "$TMPBASE/stress.XXXXXX") || exit 2
trap 'rm -rf "$RUNTMP"' EXIT; trap 'exit 130' INT TERM
JAVA_HOME_GUESS=$(dirname "$(dirname "$(readlink -f "$(command -v "$JAVA")")")")
JSIG=$JAVA_HOME_GUESS/lib/server/libjsig.so; [ -f "$JSIG" ] || JSIG=""

echo "$(date +%T) generating instances ($SPECS) -> $INST"
python3 "$HERE/gen_class2_stress.py" "$INST" $SPECS | tee -a "$OUT/generate.log" || { echo "generation failed"; exit 1; }
# the instances to run: those named by SPECS (all generated instances only for SPECS=default)
if [ "$SPECS" = default ]; then
  NAMES=$(ls "$INST" | grep '^c2stress-')
else
  NAMES=$(for sp in $SPECS; do kind=rnd; case $sp in ctl:*) kind=ctl; sp=${sp#ctl:};; esac
            IFS=, read p d e s <<< "$sp"; echo "c2stress-$kind-p$p-d$d-e$e-s$s"; done)
fi
LIST=$(for f in $NAMES; do [ -f "$INST/$f" ] || { echo "missing instance $f" >&2; continue; }
         echo "$(head -1 "$INST/$f" | awk '{print $3}') $f"; done | sort -n | awk '{print $2}')
echo "$(date +%T) instances to run: $(echo $LIST)"

run_one() {   # $1 instance name, $2 mode
  local name=$1 mode=$2 txt="$OUT/chain_$1.$2.txt"
  if [ -s "$txt" ] && grep -q '|Aut| =\|no exact depth' "$txt"; then echo "$(date +%T) skip $name $mode (done)"; return; fi
  rm -f "$txt"; local jt; jt=$(mktemp -d "$RUNTMP/jvm.XXXXXX")
  local extra=""; [ "$mode" = reset ] && extra="SC_RESET=adaptive SC_RESET_SKIP=1"
  # look (2026-10-17, 2-CLASS_SPEC option (c)): stabiliser-orbit pruning + canonical-cell lookahead (ski-rental 0.1)
  [ "$mode" = look ] && extra="SC_STABPRUNE=1 SC_LOOKAHEAD=1 SC_LOOK_FRAC=0.1"
  echo "$(date +%T) START $name $mode"
  local t0=$(date +%s)
  env LD_PRELOAD=$JSIG SC_COLOUR=wl1 SC_MAXDEPTH=30 SC_NODE_INV=1 SC_FP_AFTER=8 SC_PRUNE=1 SC_TRACE=1 SC_PROGRESS=1 SC_NO_TRACES=1 \
      SC_FASTNODE=$FASTNODE $extra SC_FILES="$INST/$name" OUT="$txt" \
    timeout "$TIMEOUT_S" "$JAVA" -Xms$XMS -Xmx$HEAP -XX:+UseG1GC -Ddialysis.tmpDir=$jt -jar "$JAR" chain > "$OUT/chain_$name.$mode.log" 2>&1
  local rc=$?; rm -rf "$jt"
  [ $rc -eq 124 ] && echo "   TIMEOUT after ${TIMEOUT_S}s" >> "$txt"
  echo "$(date +%T) END $name $mode rc=$rc $(( $(date +%s) - t0 ))s $(grep -h '|Aut| =' "$txt" 2>/dev/null | tail -1)"
}
export -f run_one; export OUT INST RUNTMP JSIG JAVA HEAP TIMEOUT_S JAR FASTNODE XMS

for mode in $MODES; do for name in $LIST; do echo "$name $mode"; done; done |
  xargs -P "$JOBS" -L 1 bash -c 'run_one "$0" "$1"' | tee -a "$OUT/chain_campaign.log"

if [ "$TRACES_TIMEOUT" != 0 ]; then
  for name in $LIST; do
    grep -q ",$name," "$OUT/traces.csv" 2>/dev/null && continue
    jt=$(mktemp -d "$RUNTMP/jvm.XXXXXX"); echo "$(date +%T) Traces $name"
    env LD_PRELOAD=$JSIG TR_FILE="$INST/$name" TR_COLOUR=none OUT="$OUT/traces.csv" \
      timeout "$TRACES_TIMEOUT" "$JAVA" -Xms$XMS -Xmx$TRACES_HEAP -Ddialysis.tmpDir=$jt -jar "$JAR" oracle >> "$OUT/traces.log" 2>&1
    rc=$?; rm -rf "$jt"
    [ $rc -ne 0 ] && echo "stress,$name,,,none,,,,,$((TRACES_TIMEOUT * 1000)),$([ $rc -eq 124 ] && echo TIMEOUT || echo FAIL_$rc)" >> "$OUT/traces.csv"
  done
fi

{ echo "instance | mode | ours |Aut| | ours time | Traces |Aut| | Traces ms | agree"
  for name in $LIST; do
    tr=$(grep ",$name," "$OUT/traces.csv" 2>/dev/null | tail -1)
    ta=$(echo "$tr" | cut -d, -f8); tm=$(echo "$tr" | cut -d, -f10); tst=$(echo "$tr" | cut -d, -f11)
    for mode in $MODES; do
      line=$(grep -h '|Aut| =' "$OUT/chain_$name.$mode.txt" 2>/dev/null | tail -1)
      oa=$(echo "$line" | sed -nE 's/.*\|Aut\| = ([0-9.e+]+).*/\1/p'); ot=$(echo "$line" | sed -nE 's/.*ours ([0-9.]+)s.*/\1/p')
      [ -z "$oa" ] && oa=$(grep -hoE 'TIMEOUT.*|no exact depth.*' "$OUT/chain_$name.$mode.txt" 2>/dev/null | head -1)
      ag=$(python3 -c "import sys; a,b=sys.argv[1],sys.argv[2]
try: print('yes' if abs(float(a)-float(b)) <= 1e-5*max(1,float(b)) else 'NO')
except Exception: print('-')" "$oa" "$ta")
      echo "$name | $mode | ${oa:--} | ${ot:--} | ${ta:-${tst:--}} | ${tm:--} | $ag"
    done
  done
  echo; echo "per-level search statistics (refutations / witnesses):"
  for f in "$OUT"/chain_*.txt; do echo "== $(basename "$f")"; grep -hE 'RESET|EXACT|orbit of|search r' "$f"; done
} > "$OUT/summary.txt"
echo "$(date +%T) done -> $OUT/summary.txt"
