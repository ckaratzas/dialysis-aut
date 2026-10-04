package dialysis.campaign

import java.io.File
import java.lang.management.ManagementFactory
import java.util.concurrent.Callable
import java.util.concurrent.Executors
import java.util.concurrent.TimeUnit
import java.util.concurrent.TimeoutException

/**
 * Small shared pieces every standalone campaign CLI under `dialysis.groupdiscovery`/`dialysis.regimeiii`
 * needs -- `machine`/`code_revision` environment columns (PAPER2_CAMPAIGN_SPEC.md's own standing rule:
 * "record solver versions, CPU, RAM, OS, caps and seeds in a machine-readable environment block"), a
 * hard wall-clock deadline wrapper (same rationale as `dialysis.benchmark.BenchmarkRunner`'s own
 * `solveExecutor`/`maxInstanceSolveMs` pattern: a single pathological instance must not stall an
 * unattended multi-hour Xeon run), and permutation-order arithmetic every one of these campaigns reports
 * ("generators returned: count, and their orders" per GROUP_DISCOVERY_SPEC.md 1.3).
 */
object CampaignEnv {
    /** Short hostname -- PAPER2_CAMPAIGN_SPEC.md Part 0's whole point is that mixing this up between
     *  runs silently invalidates a comparison, so every row records it directly rather than relying on
     *  operator memory. `DIALYSIS_MACHINE_NAME` (env var) takes priority when set -- some cloud/VM
     *  hosts report a UUID as their OWN OS-level hostname (confirmed directly: a real run produced
     *  `machine=887e3150-6403-49ab-9384-03410c11bd71`, not a bug in this code, just not a name a human
     *  wants comparing rows by), and there's no way to get a friendlier name from the OS alone in that
     *  case. Falls back to `InetAddress.getLocalHost()`, then the `HOSTNAME` env var, then a fixed
     *  placeholder, since `InetAddress.getLocalHost()` can throw on a machine with no configured
     *  hostname resolution (seen on minimal benchmark VMs). */
    val hostname: String by lazy {
        System.getenv("DIALYSIS_MACHINE_NAME")
            ?: runCatching { java.net.InetAddress.getLocalHost().hostName }.getOrNull()
            ?: System.getenv("HOSTNAME")
            ?: "unknown-host"
    }

    /** Short git commit hash of the checkout this jar was built from -- read once at startup, not
     *  re-invoked per row. "unknown" (not a thrown error) when `.git` isn't present, e.g. a bundle
     *  produced by `scripts/package_*.sh` and copied to a machine with no repo checkout at all -- the
     *  packaging scripts stamp the revision into a sibling file instead (see their own comments), and
     *  campaigns run from a plain jar should still produce rows rather than fail outright. */
    val codeRevision: String by lazy {
        runCatching {
            val revFile = File("CODE_REVISION.txt")
            if (revFile.isFile) return@runCatching revFile.readText().trim()
            val proc = ProcessBuilder("git", "rev-parse", "--short", "HEAD").redirectErrorStream(true).start()
            val out = proc.inputStream.bufferedReader().readText().trim()
            if (proc.waitFor() == 0 && out.isNotBlank()) out else "unknown"
        }.getOrDefault("unknown")
    }

    /** Whole-process resident set size in MB -- identical logic to
     *  `dialysis.benchmark.BenchmarkRunner`'s own `peakRssMb` (kept as a separate copy, not shared,
     *  since that one is `private` to its own file). */
    fun peakRssMb(): Double {
        val status = File("/proc/self/status")
        if (status.exists()) {
            val line = status.readLines().firstOrNull { it.startsWith("VmHWM:") }
            if (line != null) {
                val kb = line.trim().split(Regex("\\s+"))[1].toLongOrNull()
                if (kb != null) return kb / 1024.0
            }
        }
        val heap = ManagementFactory.getMemoryMXBean().heapMemoryUsage
        return heap.used / (1024.0 * 1024.0)
    }

    /** Daemon threads so a still-running (deadline-abandoned) native SAT/Traces call never blocks JVM
     *  exit -- same rationale as BenchmarkRunner's own `solveExecutor`. Shared across every campaign CLI
     *  in this process rather than one pool per file, since they never run concurrently with each other
     *  (one `main` per JVM invocation). */
    private val executor = Executors.newCachedThreadPool { r -> Thread(r, "campaign-solve").apply { isDaemon = true } }

    /** [dialysis.cl.TracesJni]'s own doc: "Not thread-safe: Traces' own scratch workspace is static
     *  and shared across calls -- serialize calls from the JVM side." That covers every native call
     *  into `libtracesjni.so` -- not just `Traces()` itself, but also
     *  [dialysis.cl.TracesJni.groupOrderFromGenerators] (nauty's vendored `schreier.c`, which shares
     *  the same kind of static scratch, per that function's own doc), so this executor is named for
     *  the LIBRARY, not the algorithm. A timed-out call submitted to the general [executor] above
     *  leaves its native thread running (`Future.cancel(true)` is best-effort only, per
     *  [withDeadline]'s own doc) -- if a SUBSEQUENT call into this library is then submitted to that
     *  same cached pool, it can run CONCURRENTLY with the orphaned one, corrupting shared native
     *  state. Confirmed directly: a real SIGSEGV inside `traces_refine` while processing back-to-back
     *  Traces calls for consecutive instances/methods through the general executor (2026-09-04). A
     *  single-thread executor makes that impossible by construction -- a second call submitted here
     *  simply queues behind an orphaned first one (a stall, recoverable by restarting the process)
     *  instead of running alongside it (a crash, and potentially silent corruption of whatever
     *  "answer" the racing pair produces). */
    private val nautyExecutor = Executors.newSingleThreadExecutor { r -> Thread(r, "campaign-nauty").apply { isDaemon = true } }

    sealed class DeadlineResult<out T> {
        data class Completed<T>(val value: T) : DeadlineResult<T>()
        object TimedOut : DeadlineResult<Nothing>()
    }

    private fun <T> withDeadlineOn(exec: java.util.concurrent.ExecutorService, maxMs: Long, block: () -> T): DeadlineResult<T> {
        val future = exec.submit(Callable(block))
        return try {
            DeadlineResult.Completed(future.get(maxMs + 5_000L, TimeUnit.MILLISECONDS))
        } catch (e: TimeoutException) {
            future.cancel(true)
            DeadlineResult.TimedOut
        }
    }

    /** Runs [block] with a hard wall-clock cap. `Future.cancel(true)` is best-effort ONLY -- it cannot
     *  stop a thread blocked inside a native JNI call (CaDiCaL solve, Traces search) -- so a timeout
     *  here means "this row is reported as INSTANCE_TIMEOUT and the campaign moves on", exactly
     *  BenchmarkRunner's own documented caveat, not a guarantee the abandoned computation actually
     *  stops. Grace margin matches BenchmarkRunner's own `+5_000L`. Never call this with any
     *  [dialysis.cl.TracesJni] call inside [block] -- use [withNautyDeadline] instead, which
     *  serializes every call into that native library onto its own dedicated thread (see that
     *  function's own doc for why). */
    fun <T> withDeadline(maxMs: Long, block: () -> T): DeadlineResult<T> = withDeadlineOn(executor, maxMs, block)

    /** Same contract as [withDeadline], but for a [dialysis.cl.TracesJni] call specifically (any of
     *  them -- `Traces()` search, or [dialysis.cl.TracesJni.groupOrderFromGenerators]'s `schreier.c`
     *  bookkeeping) -- serialized onto a dedicated single-thread executor so a timed-out (orphaned)
     *  call can never run concurrently with a later one. See [nautyExecutor]'s own doc for the crash
     *  this prevents. */
    fun <T> withNautyDeadline(maxMs: Long, block: () -> T): DeadlineResult<T> = withDeadlineOn(nautyExecutor, maxMs, block)

    /** Order of a permutation: LCM of its cycle lengths. Used for "generators returned ... and their
     *  orders" (GROUP_DISCOVERY_SPEC.md 1.3's per-row schema). */
    fun permutationOrder(alpha: IntArray): Long {
        val seen = BooleanArray(alpha.size)
        var order = 1L
        for (start in alpha.indices) {
            if (seen[start]) continue
            var len = 0L
            var v = start
            while (!seen[v]) {
                seen[v] = true
                v = alpha[v]
                len++
            }
            order = lcm(order, len)
        }
        return order
    }

    private fun gcd(a: Long, b: Long): Long = if (b == 0L) a else gcd(b, a % b)
    private fun lcm(a: Long, b: Long): Long = if (a == 0L || b == 0L) 0L else a / gcd(a, b) * b

    /** CSV-safe rendering of an arbitrary value: commas/newlines replaced, matching
     *  BenchmarkRunner's own `errorRow` convention (this repo's CSVs are unquoted, so a literal comma
     *  or newline in a value would silently corrupt column alignment downstream). */
    fun csv(value: Any?): String = value?.toString()?.replace(',', ';')?.replace('\n', ' ') ?: ""

    /** Already-completed `(instance, method)` (or any two-part) keys from an existing CSV's first two
     *  columns after `family` -- i.e. columns 1 and 2 (0-indexed), matching every runner below's own
     *  header layout (`family, instance, method, ...` or `family, instance, ...`). [keyColumns] is how
     *  many of the leading (post-family) columns form the resume key -- 1 for an instance-only runner,
     *  2 for one keyed on (instance, method). */
    fun alreadyDone(out: File, keyColumns: Int): Set<String> {
        if (!out.exists()) return emptySet()
        return out.readLines().drop(1).mapNotNull { line ->
            val cols = line.split(',')
            if (cols.size <= keyColumns) null else cols.subList(1, 1 + keyColumns).joinToString("|").takeIf { it.isNotBlank() }
        }.toSet()
    }

    /** Lists every file directly under `graphs/<family>`, sorted -- identical convention to
     *  BenchmarkRunner's own `listInstances`. */
    fun listInstances(family: String): List<String> =
        File("graphs/$family").listFiles()?.filter { it.isFile }?.map { it.path }?.sorted() ?: emptyList()

    /** Resolves a CLI's `--family=a,b` and `--instances=path1,path2` flags (either or both) into one
     *  sorted, de-duplicated list of graph file paths -- the common instance-selection convention
     *  every runner below shares. */
    fun resolveInstances(familyFlag: String?, instancesFlag: String?): List<String> {
        val fromFamilies = familyFlag?.split(',')?.map { it.trim() }?.filter { it.isNotEmpty() }
            ?.flatMap { listInstances(it) } ?: emptyList()
        val explicit = instancesFlag?.split(',')?.map { it.trim() }?.filter { it.isNotEmpty() } ?: emptyList()
        require(fromFamilies.isNotEmpty() || explicit.isNotEmpty()) {
            "at least one of --family=<dir under graphs/> or --instances=<comma-separated paths> is required"
        }
        return (fromFamilies + explicit).distinct().sorted()
    }

    fun familyOf(path: String): String = File(path).parentFile?.name ?: "unknown"
}
