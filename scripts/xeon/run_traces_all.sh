#!/bin/bash
# Traces (uncoloured, the oracle/baseline) on EVERY family in $GRAPHS, in one command:
#   GRAPHS=/path/to/graphs ./run_traces_all.sh
#
# - Every family folder in $GRAPHS is run (except EXCLUDE, default: tests polycirculant-orbital cfi-k5), smallest n first,
#   one process at a time (via run_traces.sh), so the result has a Traces group ORDER for every instance it finishes.
# - Skipped: the 305 instances where Traces, in the Paper-1 campaign on this same Xeon, failed (timeout/memory/crash)
#   or needed more than 60 s (samples/traces_v1_skip.txt, from _results.v1/*/gt-*.csv); their Paper-1 outcome and
#   time are merged into the tables afterwards. The other 1,328 Paper-1 instances are re-run (they take seconds in
#   total) because Paper 1 recorded orbit counts but not group orders.
# - Frontier rule: after K consecutive instances without a Traces result (TIMEOUT/MEMOUT/crash) the rest of that family
#   (all larger) is skipped and listed in <OUT>/<family>/traces_skipped.txt. K = 1 on cfi-rigid-* and sat_cfi_dim,
#   where Paper 1 already found where Traces starts failing, else K = 2.
# - Resumable: stop it any time and run the same command again (finished instances are skipped by run_traces.sh).
#
# Settings: TRACES_TIMEOUT [3600, as in Paper 1], FAMILIES (space-separated, to run a subset), EXCLUDE, K_DEFAULT [2],
#           plus everything run_traces.sh takes (OUT, JAVA, JAR, TRACES_HEAP, TMP_DIR).
# Worst case at 3600 s: about 6 h (cfi-rigid, 1 timeout each) + 1 h (sat_cfi_dim) + 2 h each for tnn and chh; the
# ~11,000 quick instances cost ~0.3 s of process start-up each (laptop test: Q3..Q13 and chh up to n=660 in 4 s).
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
: "${GRAPHS:?set GRAPHS=/path/to/graphs}"
GRAPHS=$(cd "$GRAPHS" && pwd) || exit 2
export GRAPHS OUT=${OUT:-$HERE/results} TRACES_TIMEOUT=${TRACES_TIMEOUT:-3600} NO_SUMMARY=1
mkdir -p "$OUT"; OUT=$(cd "$OUT" && pwd)
V1=$HERE/samples/traces_v1_skip.txt; [ -f "$V1" ] || { echo "missing $V1"; exit 2; }
EXCLUDE=${EXCLUDE:-"tests polycirculant-orbital cfi-k5"}
ALL=$(for d in "$GRAPHS"/*/; do f=$(basename "$d"); case " $EXCLUDE " in *" $f "*) ;; *) echo "$f" ;; esac; done)
FAMILIES=${FAMILIES:-$ALL}

for FAM in $FAMILIES; do
  [ -d "$GRAPHS/$FAM" ] || { echo "$(date +%T) [$FAM] no folder, skipped"; continue; }
  case "$FAM" in cfi-rigid-*|sat_cfi_dim) K=1 ;; *) K=${K_DEFAULT:-2} ;; esac
  C=$OUT/$FAM/traces.csv; mkdir -p "$OUT/$FAM"; SK=$OUT/$FAM/traces_skipped.txt
  # instances sorted by n (from the 'p' line), minus the Paper-1 failures and slow runs
  LIST=$(for f in "$GRAPHS/$FAM"/*; do b=$(basename "$f")
           grep -qxF "$FAM,$b" "$V1" && continue
           echo "$(grep -m1 '^p ' "$f" | awk '{print $3}') $b"; done | sort -n -k1,1 -k2,2 | awk '{print $2}')
  echo "$(date +%T) [$FAM] $(echo "$LIST" | grep -c .) instance(s) to run, frontier rule K=$K, timeout ${TRACES_TIMEOUT}s"
  fails=0; : > "$SK"; stop=0
  for name in $LIST; do
    if [ $stop = 1 ]; then echo "$name" >> "$SK"; continue; fi
    "$HERE/run_traces.sh" "$FAM" "$name" | grep -v ' Traces colour=' 
    out=$(awk -F, -v n="$name" '$2==n{o=$11} END{print o}' "$C" 2>/dev/null)
    if [ "$out" = OK ]; then fails=0; else fails=$((fails+1)); fi
    if [ $fails -ge $K ]; then stop=1; echo "$(date +%T) [$FAM] frontier: $K consecutive failure(s) at $name, larger instances skipped"; fi
  done
  [ -s "$SK" ] && echo "$(date +%T) [$FAM] skipped above the frontier: $(grep -c . "$SK") (list in $SK)"
  python3 "$HERE/summarize.py" "$OUT" "$GRAPHS" "$FAM" > /dev/null
done
echo "$(date +%T) all done"
