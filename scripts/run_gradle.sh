#!/usr/bin/env bash
# Memory-contained wrapper for any ./gradlew invocation (compile, paperJar, ...).
# ...). Reuses the exact same systemd-run/cgroup containment scripts/run_benchmark.sh and
# scripts/run_java.sh already validated. See feedback-gradle-compile-uncontained-hang in memory:
# a bare `./gradlew --no-daemon compileTestKotlin` has zero memory bound and hung the whole laptop
# session (not a clean OOM-kill -- a full freeze requiring a hard restart) on 2026-09-10. This
# wrapper is what closes that gap for gradle itself, distinct from run_java.sh which only covers
# running the already-built fat jar.
#
# Usage:
#   scripts/run_gradle.sh compileTestKotlin
#   scripts/run_gradle.sh --no-daemon test --tests "dialysis.groupdiscovery.*"
#   scripts/run_gradle.sh shadowJar
#
# RUN_GRADLE_MEMORY_CAP_MB overrides the default cap (4096); RUN_GRADLE_JVM_HEAP_MB overrides the
# -Xmx fraction (default 85% of the cap, forwarded via JAVA_OPTS which gradlew's launcher script
# respects natively); RUN_GRADLE_NO_MEMCAP=1 disables containment entirely (only on a real
# benchmark machine, not this laptop).
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
WORKDIR="$PWD"

MEMORY_CAP_MB="${RUN_GRADLE_MEMORY_CAP_MB:-4096}"
JVM_HEAP_MB="${RUN_GRADLE_JVM_HEAP_MB:-$((MEMORY_CAP_MB * 85 / 100))}"
MEMCAP_WRAPPER=()
GRADLE_JAVA_OPTS="${JAVA_OPTS:-}"

if [ "${RUN_GRADLE_NO_MEMCAP:-0}" != "1" ]; then
    GRADLE_JAVA_OPTS="-Xmx${JVM_HEAP_MB}m ${GRADLE_JAVA_OPTS}"

    # See run_java.sh for why these are defaulted rather than assumed inherited.
    : "${XDG_RUNTIME_DIR:=/run/user/$(id -u)}"
    : "${DBUS_SESSION_BUS_ADDRESS:=unix:path=${XDG_RUNTIME_DIR}/bus}"
    export XDG_RUNTIME_DIR DBUS_SESSION_BUS_ADDRESS

    SYSTEMD_RUN_OK=0
    if command -v systemd-run >/dev/null 2>&1; then
        if probe_err="$(systemd-run --scope --user --quiet true 2>&1 >/dev/null)"; then
            SYSTEMD_RUN_OK=1
        else
            echo "systemd-run --user unavailable (${probe_err:-no output}) -- trying a delegated cgroup v2 directly." >&2
        fi
    fi

    if [ "$SYSTEMD_RUN_OK" = 1 ]; then
        MEMCAP_WRAPPER=(systemd-run --scope --user --quiet \
            "--unit=dialysis-gradle-$$-$(date +%s)" \
            -p "MemoryMax=${MEMORY_CAP_MB}M" -p "MemorySwapMax=0" \
            "--working-directory=${WORKDIR}" --)
    else
        CGROUP_BASE=""
        if [ -f /sys/fs/cgroup/cgroup.controllers ]; then
            cg_rel="$(awk -F: '$1=="0"{print $3}' /proc/self/cgroup 2>/dev/null)"
            cg_path="/sys/fs/cgroup${cg_rel}"
            while [ -n "$cg_rel" ] && [ "$cg_path" != "/sys/fs/cgroup" ] && [ "$cg_path" != "/" ]; do
                if [ -d "$cg_path" ]; then
                    cg_probe="$cg_path/.dialysis-cgroup-probe-$$"
                    if mkdir "$cg_probe" 2>/dev/null; then
                        if (exec 2>/dev/null; echo max > "$cg_probe/memory.max"); then
                            rmdir "$cg_probe" 2>/dev/null
                            CGROUP_BASE="$cg_path"
                            break
                        fi
                        rmdir "$cg_probe" 2>/dev/null
                    fi
                fi
                cg_path="$(dirname "$cg_path")"
            done
        fi
        CG="${CGROUP_BASE:+$CGROUP_BASE/dialysis-gradle-$$}"
        if [ -n "$CGROUP_BASE" ] && \
           mkdir "$CG" 2>/dev/null && \
           echo "${MEMORY_CAP_MB}M" > "$CG/memory.max" 2>/dev/null && \
           echo 0 > "$CG/memory.swap.max" 2>/dev/null && \
           echo $$ > "$CG/cgroup.procs" 2>/dev/null; then
            echo "No D-Bus session -- contained via delegated cgroup v2 at $CG instead (cap ${MEMORY_CAP_MB}M)." >&2
        elif command -v sudo >/dev/null 2>&1 && { sudo -n true 2>/dev/null || sudo -v; }; then
            [ -n "$CG" ] && rmdir "$CG" 2>/dev/null
            MEMCAP_WRAPPER=(sudo systemd-run --scope --quiet \
                "--unit=dialysis-gradle-$$-$(date +%s)" \
                -p "MemoryMax=${MEMORY_CAP_MB}M" -p "MemorySwapMax=0" \
                "--working-directory=${WORKDIR}" \
                --uid="$(id -u)" --gid="$(id -g)" --)
            echo "No delegated cgroup -- contained via 'sudo systemd-run' (system mode) instead (cap ${MEMORY_CAP_MB}M)." >&2
        else
            [ -n "$CG" ] && rmdir "$CG" 2>/dev/null || true
            echo "Neither systemd-run --user, any writable delegated cgroup ancestor of $(awk -F: '$1=="0"{print $3}' /proc/self/cgroup 2>/dev/null || echo '(unknown)'), nor sudo is available" >&2
            echo "-- refusing to run without memory containment." >&2
            echo "Set RUN_GRADLE_NO_MEMCAP=1 to run uncontained anyway (only on a real benchmark machine)." >&2
            exit 1
        fi
    fi
fi

echo "Running: ${MEMCAP_WRAPPER[*]:-} JAVA_OPTS='${GRADLE_JAVA_OPTS}' ./gradlew --no-daemon $*"
exec "${MEMCAP_WRAPPER[@]}" env JAVA_OPTS="${GRADLE_JAVA_OPTS}" ./gradlew --no-daemon "$@"
