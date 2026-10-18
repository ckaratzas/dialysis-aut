#!/bin/bash
# G2 attack + Conjecture 11.1 scaling on the Xeon (2026-10-17, ATTACK_G2_SPEC.md, CONJECTURE_11.1_SPEC.md).
# For every instance in $INST (DIMACS files), each in its own JVM with its own timeout:
#   traces  Traces, uncoloured (ORACLE ONLY)                                          -> traces.csv
#   tcg     series solver, T_C as generators + Luks (SERIES_TCGROUP), pruned with the
#           leaf group (SERIES_TCPRUNE): status COND_EXACT = conditional on Conj. 11.1 -> tcg_<name>.log
#   tcgu    the same WITHOUT the leaf-group pruning: unconditional EXACT when it ends; stops after the first class
#           whose leaves are discrete on V (generator shortcut, SERIES_GENAUT)          -> tcgu_<name>.log
#   tcgl    the normal run: series with a quarter of TIMEOUT_S, then Luks on a STOP (SERIES_LUKS), all unconditional.
#           Since 2026-10-18: leaf-group pruning with admissibility on V (SERIES_TCPRUNE + SERIES_ADMIT_V, unconditional by
#           Theorem T), and the Luks fallback starts from the uniform colouring (SERIES_LUKS_PLAIN)
#                                                                                       -> tcgl_<name>.log
#   tcgl0   ablation of tcgl (2026-10-18): the same run WITHOUT the leaf-group pruning (no SERIES_TCPRUNE / ADMIT_V), to
#           measure what Theorem T (Conjecture 11.1 for admissibility on V) buys    -> tcgl0_<name>.log
#   luks    the (D) route: invariant cut -> pieces -> Luks (LUKSAUT lines, GIANTS)     -> luks_<name>.log
#           (pieces solved in the unconditional T_C-as-generators mode: no 20,000-candidate list cap)
# Then summary.txt: one line per instance, |Aut| per method, times, agreement with Traces.
#
# Usage (defaults in brackets):
#   INST=./g2_instances OUT=./g2_results JAR=./dialysis-paper3.jar ./run_g2_attack.sh
#   METHODS   which methods                         ["traces tcg tcgu luks"]
#   JOBS      JVMs in parallel                      [4]
#   HEAP      -Xmx per JVM                          [16g]
#   TIMEOUT_S wall clock per run                    [7200]
#   MAX_BASE  base length limit of the series stage [24]  (rc12-type classes need > 12)
#   PI_MAX_N  tcg/tcgu colour with PI up to this many vertices, plain 1-WL above [8000]
#             (PI's decomposition store grows quadratically and is written to TMP_DIR: on A5-K33, 22,680 vertices, it
#             filled /tmp -- "No space left on device", 2026-10-17)
#   TMP_DIR   scratch folder for the JVMs                                         [$TMPDIR or /tmp]
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
INST=${INST:-$HERE/g2_instances}; OUT=${OUT:-$HERE/g2_results}; JAR=${JAR:-$HERE/dialysis-paper3.jar}; JAVA=${JAVA:-java}
METHODS=${METHODS:-traces tcg tcgu luks}; JOBS=${JOBS:-4}; HEAP=${HEAP:-16g}; TIMEOUT_S=${TIMEOUT_S:-7200}; MAX_BASE=${MAX_BASE:-24}; PI_MAX_N=${PI_MAX_N:-8000}
INST=$(cd "$INST" && pwd); mkdir -p "$OUT"; OUT=$(cd "$OUT" && pwd); JAR=$(cd "$(dirname "$JAR")" && pwd)/$(basename "$JAR")
JAVA_HOME_GUESS=$(dirname "$(dirname "$(readlink -f "$(command -v "$JAVA")")")")
JSIG=$JAVA_HOME_GUESS/lib/server/libjsig.so; [ -f "$JSIG" ] || JSIG=""
TMPBASE=${TMP_DIR:-${TMPDIR:-/tmp}}; RUNTMP=$(mktemp -d "$TMPBASE/g2.XXXXXX") || exit 2
trap 'rm -rf "$RUNTMP"' EXIT
run_one() {   # $1 instance path, $2 method
  local f=$1 m=$2 name; name=$(basename "$1"); local log="$OUT/${m}_$name.log"
  if [ -s "$log" ] && grep -q '^DONE' "$log"; then echo "$(date +%T) skip $name $m"; return; fi
  local jt; jt=$(mktemp -d "$RUNTMP/jvm.XXXXXX"); local t0; t0=$(date +%s)
  local nv; nv=$(grep -m1 '^p' "$f" | awk '{print $3}'); local usepi=1; [ "${nv:-0}" -gt "$PI_MAX_N" ] && usepi=0
  echo "$(date +%T) START $name $m (n=$nv, colouring $([ $usepi = 1 ] && echo PI || echo 1-WL))"
  case $m in
    traces) env LD_PRELOAD=$JSIG TR_FILE="$f" TR_COLOUR=none OUT="$OUT/traces.csv" \
              timeout -k 60 "$TIMEOUT_S" "$JAVA" -Xmx$HEAP -Ddialysis.tmpDir=$jt -jar "$JAR" oracle > "$log" 2>&1 ;;
    tcg)    env LD_PRELOAD=$JSIG SERIES_TCPRUNE=1 SERIES_TCGROUP=1 SERIES_AUTPRUNE=1 ONE_PATH="$f" ONE_DEADLINE_S=$TIMEOUT_S \
              IR_FALLBACK=0 ONE_MAX_BASE=$MAX_BASE ONE_MAX_CAND=2000000 ONE_USE_PI=$usepi \
              timeout -k 60 "$TIMEOUT_S" "$JAVA" -Xmx$HEAP -Ddialysis.tmpDir=$jt -jar "$JAR" run dialysis.experimental.DecompositionCanonicalFormsTest seriesOne > "$log" 2>&1 ;;
    tcgu)   env LD_PRELOAD=$JSIG SERIES_TCGROUP=1 SERIES_AUTPRUNE=1 SERIES_GENAUT=1 ONE_PATH="$f" ONE_DEADLINE_S=$TIMEOUT_S \
              IR_FALLBACK=0 ONE_MAX_BASE=$MAX_BASE ONE_MAX_CAND=2000000 ONE_USE_PI=$usepi \
              timeout -k 60 "$TIMEOUT_S" "$JAVA" -Xmx$HEAP -Ddialysis.tmpDir=$jt -jar "$JAR" run dialysis.experimental.DecompositionCanonicalFormsTest seriesOne > "$log" 2>&1 ;;
    tcgl)   env LD_PRELOAD=$JSIG SERIES_TCPRUNE=1 SERIES_ADMIT_V=1 SERIES_LUKS_PLAIN=1 SERIES_TCGROUP=1 SERIES_AUTPRUNE=1 SERIES_GENAUT=1 SERIES_LUKS=1 LUKS_PIECE_S=$TIMEOUT_S LUKS_GLUE_MAX_TESTS=2000 ONE_PATH="$f" \
              ONE_DEADLINE_S=$((TIMEOUT_S / 4)) IR_FALLBACK=0 ONE_MAX_BASE=$MAX_BASE ONE_MAX_CAND=2000000 ONE_USE_PI=$usepi \
              timeout -k 60 "$TIMEOUT_S" "$JAVA" -Xmx$HEAP -Ddialysis.tmpDir=$jt -jar "$JAR" run dialysis.experimental.DecompositionCanonicalFormsTest seriesOne > "$log" 2>&1 ;;
    tcgl0)  env LD_PRELOAD=$JSIG SERIES_LUKS_PLAIN=1 SERIES_TCGROUP=1 SERIES_AUTPRUNE=1 SERIES_GENAUT=1 SERIES_LUKS=1 LUKS_PIECE_S=$TIMEOUT_S LUKS_GLUE_MAX_TESTS=2000 ONE_PATH="$f" \
              ONE_DEADLINE_S=$((TIMEOUT_S / 4)) IR_FALLBACK=0 ONE_MAX_BASE=$MAX_BASE ONE_MAX_CAND=2000000 ONE_USE_PI=$usepi \
              timeout -k 60 "$TIMEOUT_S" "$JAVA" -Xmx$HEAP -Ddialysis.tmpDir=$jt -jar "$JAR" run dialysis.experimental.DecompositionCanonicalFormsTest seriesOne > "$log" 2>&1 ;;
    luks)   echo "$f" > "$jt/list"; env LD_PRELOAD=$JSIG INSTANCES_FILE="$jt/list" LUKS_PIECE_S=$TIMEOUT_S \
              SERIES_AUTPRUNE=1 SERIES_TCGROUP=1 SERIES_GENAUT=1 \
              timeout -k 60 "$TIMEOUT_S" "$JAVA" -Xmx$HEAP -Ddialysis.tmpDir=$jt -jar "$JAR" run dialysis.experimental.DecompositionCanonicalFormsTest luksFullAut > "$log" 2>&1 ;;
  esac
  local rc=$?; rm -rf "$jt"
  echo "DONE rc=$rc seconds=$(( $(date +%s) - t0 ))" >> "$log"
  echo "$(date +%T) END $name $m rc=$rc $(( $(date +%s) - t0 ))s"
}
export -f run_one; export OUT RUNTMP JSIG JAVA HEAP TIMEOUT_S JAR MAX_BASE PI_MAX_N
for f in "$INST"/*; do for m in $METHODS; do echo "$f $m"; done; done | xargs -P "$JOBS" -L 1 bash -c 'run_one "$0" "$1"' | tee -a "$OUT/campaign.log"
# summary
{ echo "instance | Traces |Aut| (ms) | tcg (cond.) | tcgu (uncond.) | tcgl (series, then Luks) | luks (D) route | giants"
  for f in "$INST"/*; do n=$(basename "$f")
    tr=$(grep ",$n," "$OUT/traces.csv" 2>/dev/null | tail -1 | awk -F, '{print $8" ("$10")"}')
    tg=$(grep -h '^ONE' "$OUT/tcg_$n.log" 2>/dev/null | sed -E 's/.*-> ([A-Z_]+) \|Aut\|=([^ ]*).*\(([0-9.]+)s\)$/\1 \2 \3s/' | tail -1)
    tu=$(grep -h '^ONE' "$OUT/tcgu_$n.log" 2>/dev/null | sed -E 's/.*-> ([A-Z_]+) \|Aut\|=([^ ]*).*\(([0-9.]+)s\)$/\1 \2 \3s/' | tail -1)
    tl=$(grep -h '^ONE' "$OUT/tcgl_$n.log" 2>/dev/null | sed -E 's/.*-> ([A-Z_]+) \|Aut\|=([^ ]*).*\(([0-9.]+)s\)$/\1 \2 \3s/' | tail -1)
    lk=$(grep -h "^LUKSAUT $n |Aut(G)| =\|^LUKSAUT $n FAILED" "$OUT/luks_$n.log" 2>/dev/null | tail -1 | sed -E 's/^LUKSAUT [^ ]+ //' | cut -c1-60)
    gi=$(grep -ho 'giants=[0-9]* maxGiantDeg=[0-9]*\|GIANTS[^|]*' "$OUT/tcg_$n.log" "$OUT/tcgl_$n.log" "$OUT/luks_$n.log" 2>/dev/null | sort -u | tr '\n' ' ' | cut -c1-80)
    echo "$n | ${tr:-?} | ${tg:-?} | ${tu:-?} | ${tl:-?} | ${lk:-?} | $gi"
  done; } > "$OUT/summary.txt"
cat "$OUT/summary.txt"
