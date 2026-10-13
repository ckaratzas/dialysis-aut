#!/bin/bash
# scripts/safe_java_test.sh UNIT HEAP_MB CLASS METHOD LOG   (extra env passes through to the test)
# One plain JVM running build/libs/dialysis-paper3.jar (`scripts/run_gradle.sh paperJar` first) as `run CLASS METHOD`, -Xmx HEAP,
# cgroup cap HEAP+450M (metaspace, JNI natives, dreadnaut child), no swap, low CPU weight + nice.
# Watchdog: kill when NON-FILE memory (anon + shmem from memory.stat) exceeds heap + 300M -> exit 90 (job too big for
# this budget); kill when system MemAvailable < FLOOR_MB (default 2000) -> exit 91 (retry later). Refuses (exit 3) unless
# MemAvailable >= cap + FLOOR.
# File cache is NOT counted (2026-09-30, Christos): PI's DecompositionStore is an O(n^2) memory-mapped temp file (1.5 GB
# for had-68) -- clean, reclaimable page cache that memory.current counts, so the old watchdog killed jobs whose JVM used
# half the cap. The scope's MemoryMax is cap + FILE_MB (default 2048) so the kernel reclaims that cache inside the scope
# instead of the watchdog killing on it; anon stays bounded by the watchdog, the system by FLOOR.
U=$1; HEAP=$2; CLASS=$3; METHOD=$4; LOG=$5
FLOOR=${FLOOR_MB:-2000}
FILE_MB=${FILE_MB:-2048}
R=/home/christos/IdeaProjects/dialysis-aut
cd $R || exit 1
SCOPE_CAP=$((HEAP + 450))
avail=$(awk '/MemAvailable/{print int($2/1024)}' /proc/meminfo)
if [ "$avail" -lt $((SCOPE_CAP + FLOOR)) ]; then echo "REFUSED: MemAvailable ${avail}M < cap ${SCOPE_CAP}M + floor" >> "$LOG"; exit 3; fi
JAR=$R/build/libs/dialysis-paper3.jar
JAVA=${JAVA:-/usr/lib/jvm/java-17-openjdk-amd64/bin/java}
CG=/sys/fs/cgroup/user.slice/user-1000.slice/user@1000.service/app.slice/$U.scope
WD_LIMIT=$(( (SCOPE_CAP - 150) * 1024 * 1024 ))   # heap + 300M of anon+shmem: above the JVM heap limit, so the JVM throws its own OOM first
FLAG=$(mktemp)
(
  sleep 2; peak=0
  while [ -d "$CG" ]; do
    cur=$(awk '/^anon |^shmem /{s+=$2} END{print s+0}' $CG/memory.stat 2>/dev/null || echo 0); [ "$cur" -gt "$peak" ] && peak=$cur
    tot=$(cat $CG/memory.current 2>/dev/null || echo 0)
    sys=$(awk '/MemAvailable/{print int($2/1024)}' /proc/meminfo)
    if [ "$cur" -gt "$WD_LIMIT" ]; then echo 90 > $FLAG; echo "WATCHDOG_CAP: $U anon+shmem $((cur/1048576))M of cap ${SCOPE_CAP}M (total incl. file cache $((tot/1048576))M)" >> "$LOG"; systemctl --user kill -s KILL $U.scope; break; fi
    if [ "$sys" -lt "$FLOOR" ]; then echo 91 > $FLAG; echo "WATCHDOG_SYS: system avail ${sys}M < ${FLOOR}M, $U at $((cur/1048576))M" >> "$LOG"; systemctl --user kill -s KILL $U.scope; break; fi
    echo "$(date +%T) $((cur/1048576)) $sys $((tot/1048576))" >> "$LOG.mem"; sleep 2
  done
  echo "PEAK_ANON_MB $((peak/1048576))" >> "$LOG"
) &
systemd-run --user --scope -q --unit=$U -p MemoryMax=$((SCOPE_CAP + FILE_MB))M -p MemorySwapMax=0 -p CPUWeight=20 \
  env LD_PRELOAD=$(dirname $(dirname $JAVA))/lib/server/libjsig.so \
  nice -n 10 $JAVA -Xmx${HEAP}m -XX:MaxMetaspaceSize=192m -jar $JAR run $CLASS $METHOD >> "$LOG" 2>&1
rc=$?
wait
[ -s $FLAG ] && rc=$(cat $FLAG); rm -f $FLAG
echo "EXIT $rc" >> "$LOG"
exit $rc
