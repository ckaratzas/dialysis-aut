#!/bin/bash
# Same-machine comparison: each plane with and without SC_PRUNE, both variants started together (same contention).
# Run from the repository root. The run was stopped after pp-27-10 (pruning off: > 5,400 s, stopped).
J=build/libs/dialysis-paper3.jar; O=${OUT_DIR:-pruning-out}; mkdir -p "$O"
JSIG=$(dirname "$(dirname "$(readlink -f "$(command -v java)")")")/lib/server/libjsig.so
one() { # $1 plane, $2 prune(0/1)
  systemd-run --user --scope -q -p MemoryMax=1800M env LD_PRELOAD=$JSIG \
    SC_PRUNE=$2 SC_NO_TRACES=1 SC_COMPLEMENT=0 SC_AFFINE=1 SC_THREADS=8 SC_MAXDEPTH=32 SC_COLOUR=wl1 SC_FILES=graphs/pp/$1 \
    OUT=$O/$1.p$2.txt timeout 10800 java -Xmx1100m -XX:+UseG1GC -jar $J chain > $O/$1.p$2.log 2>&1
}
for pl in pp-27-10 pp-25-106 pp-25-104 pp-25-124 pp-25-108; do
  one $pl 0 & one $pl 1 & wait
  echo "$pl off: $(grep -h 'queries in total\||Aut|' $O/$pl.p0.txt | tr -s ' ' | tr '\n' ' ')"
  echo "$pl on : $(grep -h 'queries in total\||Aut|' $O/$pl.p1.txt | tr -s ' ' | tr '\n' ' ')"
done
echo DONE
