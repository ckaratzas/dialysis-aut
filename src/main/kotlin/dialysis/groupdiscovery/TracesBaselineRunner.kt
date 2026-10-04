package dialysis.groupdiscovery

import dialysis.campaign.CampaignEnv
import dialysis.cl.TracesJni
import dialysis.graph.Graph
import dialysis.util.GraphIO
import java.io.File
import java.io.FileWriter

/**
 * PAPER2_FINAL_SPEC.md Task 2/3/6 -- pure Traces automorphism-group timing baseline (generators +
 * order, NOT canonical form), one instance per OS PROCESS, not just per thread.
 *
 * Why per-process: `libtracesjni.so` keeps a shared static workspace across calls in the same JVM;
 * an orphaned timed-out call can corrupt a LATER call in the same process (already measured once --
 * see [GroupDiscoveryCampaignRunner]'s own retrospective on cross-check ordering, where Traces
 * orphaning itself on a hard instance silently starved every call queued behind it). A fresh `java`
 * process per instance sidesteps that entirely, at the cost of one JVM startup per instance -- worth
 * it here since Task 2 explicitly requires "ensure each call is in its own process".
 *
 * Two modes on the same entry point:
 *   orchestrator (`--family=...` / `--instances=...`, no `--instance=`): resolves the instance list
 *     via [CampaignEnv.resolveInstances], then re-execs itself as a FRESH `java` subprocess per
 *     not-yet-done instance, waiting for each to exit before starting the next -- never two Traces
 *     calls at once, matching Task 2's "run it serially, never alongside Part B workers".
 *   worker (`--instance=<single path>`): the actual measurement -- loads one graph, runs Traces
 *     under [CampaignEnv.withNautyDeadline], appends exactly one row, exits.
 *
 * `--minVertices`/`--maxVertices` (matching [dialysis.benchmark.BenchmarkRunner]'s own convention)
 * let a campaign go incrementally by size across several invocations of the same resumable `--out`
 * file, if preferred over one full-family-list run in one go -- checked via a cheap peek at the
 * DIMACS `p edge <n> <m>` header line (no full graph load) so filtering doesn't cost a parse per
 * candidate instance.
 *
 * Usage (orchestrator -- this is the one you actually run):
 * ```
 * java -cp graph-dialysis-1.0-all.jar dialysis.groupdiscovery.TracesBaselineRunnerKt \
 *   --family=cfi-rigid-d3,cfi-rigid-z3,cfi-rigid-r2,cfi-rigid-t2,cfi-rigid-s2,cfi-rigid-z2,had,latin,grid,sts \
 *   --timeoutMs=3600000 --out=results/traces-baseline.csv
 *   [--minVertices=0] [--maxVertices=999999999]
 * ```
 * Resumable: re-running with the same `--out` skips every instance already present as a row.
 */
private fun peekVertexCount(path: String): Int {
    File(path).bufferedReader().useLines { lines ->
        for (line in lines) {
            if (line.startsWith("p ")) return line.trim().split(Regex("\\s+"))[2].toInt()
        }
    }
    error("$path: no DIMACS 'p edge <n> <m>' header line found")
}
private fun parseFlags(args: Array<String>): Map<String, String> =
    args.associate { arg ->
        val body = arg.removePrefix("--")
        val eq = body.indexOf('=')
        if (eq < 0) body to "true" else body.substring(0, eq) to body.substring(eq + 1)
    }

// family FIRST, then instance -- CampaignEnv.alreadyDone(keyColumns=1) skips column 0 and keys off
// column 1 onward, matching every other runner in this codebase (family,instance,... order).
private val header = listOf(
    "family", "instance", "n", "m", "machine", "code_revision",
    "traces_order", "traces_num_orbits", "traces_ms", "outcome", "peak_rss_mb",
).joinToString(",")

private class OrchestratorMarker

fun main(args: Array<String>) {
    val flags = parseFlags(args)
    val out = File(flags["out"] ?: "results/traces-baseline.csv")
    val timeoutMs = (flags["timeoutMs"] ?: "3600000").toLong()
    val minVertices = (flags["minVertices"] ?: "0").toInt()
    val maxVertices = (flags["maxVertices"] ?: Int.MAX_VALUE.toString()).toInt()

    val singleInstance = flags["instance"]
    if (singleInstance != null) {
        runWorker(singleInstance, timeoutMs, out)
        return
    }

    out.parentFile?.mkdirs()
    val done = CampaignEnv.alreadyDone(out, keyColumns = 1)
    if (done.isNotEmpty()) println("Resuming: ${done.size} instance(s) already in ${out.path}.")
    if (!out.exists()) out.writeText(header + "\n")

    val instances = CampaignEnv.resolveInstances(flags["family"], flags["instances"])
    val jar = File(OrchestratorMarker::class.java.protectionDomain.codeSource.location.toURI()).absolutePath
    val javaBin = File(System.getProperty("java.home"), "bin/java").absolutePath
    println("Orchestrator: ${instances.size} instance(s) total, ${done.size} already done, jar=$jar")

    for (path in instances) {
        if (path in done) { println("SKIP (already done): $path"); continue }
        val n = peekVertexCount(path)
        if (n < minVertices || n > maxVertices) { println("SKIP (n=$n outside [$minVertices, $maxVertices]): $path"); continue }
        println("STARTING $path")
        System.out.flush()
        val exit = ProcessBuilder(
            javaBin, "--enable-native-access=ALL-UNNAMED", "-cp", jar,
            "dialysis.groupdiscovery.TracesBaselineRunnerKt",
            "--instance=$path", "--out=${out.path}", "--timeoutMs=$timeoutMs",
        ).inheritIO().start().waitFor()
        if (exit != 0) println("  WARNING: worker exited $exit for $path (no row written if it crashed before finishing)")
    }
    println("Results written to ${out.path}")
}

private fun runWorker(path: String, timeoutMs: Long, out: File) {
    val g: Graph = GraphIO.loadDimacs(File(path).toPath())
    val cells = listOf(IntArray(g.n) { it })
    val t0 = System.currentTimeMillis()
    val outcome = CampaignEnv.withNautyDeadline(timeoutMs) { TracesJni().stats(g, cells) }
    val ms = System.currentTimeMillis() - t0
    val row = when (outcome) {
        is CampaignEnv.DeadlineResult.Completed -> listOf(
            CampaignEnv.familyOf(path), path, g.n, g.m, CampaignEnv.hostname, CampaignEnv.codeRevision,
            outcome.value.autOrder, outcome.value.numOrbits, ms, "OK", "%.1f".format(CampaignEnv.peakRssMb()),
        )
        is CampaignEnv.DeadlineResult.TimedOut -> listOf(
            CampaignEnv.familyOf(path), path, g.n, g.m, CampaignEnv.hostname, CampaignEnv.codeRevision,
            "", "", ms, "TIMEOUT", "%.1f".format(CampaignEnv.peakRssMb()),
        )
    }
    FileWriter(out, true).use { it.write(row.joinToString(",") { v -> CampaignEnv.csv(v) } + "\n") }
    println("  -> ${row.joinToString(",")}")
}
