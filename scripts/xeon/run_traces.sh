#!/bin/bash
# The oracle / baseline, kept SEPARATE from our method: Traces on instances of one family, one fresh process per
# instance (never two at once), with a time limit per process. Resumable: instances already in the CSV are skipped.
#
#   GRAPHS=/path/to/graphs ./run_traces.sh <family>                     every instance of the family
#   GRAPHS=/path/to/graphs ./run_traces.sh <family> file1 file2 ...     only these files (names inside graphs/<family>)
#   SAMPLE=list.txt GRAPHS=/path/to/graphs ./run_traces.sh <family>     only the files listed in list.txt (one per line)
#
# Settings (environment, defaults in brackets):
#   COLOUR          none = plain uncoloured Traces, the independent oracle and baseline;
#                   pi   = Traces given exactly our starting colouring (PI), to show what the architecture adds
#                          beyond the colouring. Written to traces.csv / traces_pi.csv respectively.      [none]
#   TRACES_TIMEOUT  seconds per instance (the colouring time counts towards it in pi mode)                  [3600]
#   TRACES_HEAP     -Xmx of the JVM (PI on large non-bipartite graphs needs memory; Traces itself is native) [3g]
#   JAVA, JAR, OUT  as in run_family.sh
# Run it on its own, not alongside run_family.sh: Traces' native memory is not bounded by -Xmx.
set -u
FAM=${1:?give a family name}; shift
HERE=$(cd "$(dirname "$0")" && pwd)
: "${GRAPHS:?set GRAPHS=/path/to/graphs}"
GRAPHS=$(cd "$GRAPHS" 2>/dev/null && pwd) || { echo "GRAPHS folder not found"; exit 2; }   # absolute: the script changes directory
[ -d "$GRAPHS/$FAM" ] || { echo "no such family folder: $GRAPHS/$FAM"; exit 2; }
OUT=${OUT:-$HERE/results}; mkdir -p "$OUT"; OUT=$(cd "$OUT" && pwd); JAVA=${JAVA:-java}; JAR=${JAR:-$HERE/dialysis-paper3.jar}
COLOUR=${COLOUR:-none}; TRACES_TIMEOUT=${TRACES_TIMEOUT:-3600}; TRACES_HEAP=${TRACES_HEAP:-3g}
case "$COLOUR" in none) CSV=traces.csv ;; pi) CSV=traces_pi.csv ;; *) echo "COLOUR must be none or pi"; exit 2 ;; esac
R=$OUT/$FAM; mkdir -p "$R"; C=$R/$CSV
# TMP_DIR: where the PI colouring writes its temp files (up to a few GB per large non-bipartite instance; the default
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

if [ $# -gt 0 ]; then LIST=$(printf '%s\n' "$@")
elif [ -n "${SAMPLE:-}" ]; then LIST=$(grep -v '^\s*$' "$SAMPLE")
else LIST=$(ls -1 "$GRAPHS/$FAM"); fi
echo "$(date +%T) [$FAM] Traces colour=$COLOUR timeout=${TRACES_TIMEOUT}s on $(echo "$LIST" | grep -c .) instance(s) -> $C"

for name in $LIST; do
  [ -f "$GRAPHS/$FAM/$name" ] || { echo "  missing: $name"; continue; }
  if [ -f "$C" ] && cut -d, -f2 "$C" | grep -qxF "$name"; then continue; fi
  jt=$(mktemp -d "$RUNTMP/jvm.XXXXXX")
  env LD_PRELOAD=$JSIG TR_FILE="$GRAPHS/$FAM/$name" TR_COLOUR=$COLOUR OUT="$C" \
    timeout "$TRACES_TIMEOUT" "$JAVA" -Xmx$TRACES_HEAP -Ddialysis.tmpDir=$jt -jar "$JAR" oracle >> "$R/traces_$COLOUR.log" 2>&1
  rc=$?; rm -rf "$jt"
  if ! { [ -f "$C" ] && cut -d, -f2 "$C" | grep -qxF "$name"; }; then
    hdr="family,instance,n,m,colour,colour_classes,colour_ms,traces_order,traces_orbits,traces_ms,outcome"
    [ -f "$C" ] || echo "$hdr" > "$C"
    nm=$(grep -m1 '^p ' "$GRAPHS/$FAM/$name" | awk '{print $3","$4}')
    outcome=$([ $rc = 124 ] && echo TIMEOUT || echo "FAIL_rc$rc")
    echo "$FAM,$name,$nm,$COLOUR,,,,,$((TRACES_TIMEOUT * 1000)),$outcome" >> "$C"
  fi
  echo "$(date +%T) [$FAM] $name: $(tail -1 "$C" | cut -d, -f8,10,11)"
done
[ -n "${NO_SUMMARY:-}" ] || python3 "$HERE/summarize.py" "$OUT" "$GRAPHS" "$FAM" > /dev/null
