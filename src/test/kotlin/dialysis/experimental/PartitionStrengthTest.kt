package dialysis.experimental

import dialysis.content.Content
import dialysis.content.serialize
import dialysis.graph.Graph
import dialysis.util.GraphIO
import org.junit.jupiter.api.Test
import java.io.File

/**
 * Strength vs cost of the vertex partitions (2026-10-01, colleague's review, point 6): plain 1-WL, 2-WL (vertex colours
 * = colours of the diagonal pairs), the PI colouring, and the orbit partition from our algebraic solver.
 *
 *  - singles (PS_SINGLES, comma list of paths): class counts of 1-WL / 2-WL / PI, orbit count, whether PI refines the
 *    2-WL partition and vice versa, and the time of each.
 *  - pairs (PS_PAIRS, comma list "pathG+pathH"): everything is computed on the disjoint union U = G + H. A partition
 *    DISTINGUISHES G from H when its colour histogram on the G side differs from the H side (all three are
 *    Aut(U)-invariant, so a difference proves G and H non-isomorphic). Our solver decides isomorphism exactly:
 *    G = H iff orbits(U) == orbits(G) (= orbits(H)); G != H iff orbits(U) == orbits(G) + orbits(H) (connected G, H).
 *
 * 2-WL is run only up to PS_2WL_MAX vertices (default 1200): n^2 longs per array, O(n^3) per round.
 * Env: OUT (csv), PS_DEADLINE_S (solver budget, default 300). Never 3-WL.
 */
class PartitionStrengthTest {
    private val dc = DecompositionCanonicalFormsTest()
    private val max2wl = System.getenv("PS_2WL_MAX")?.toIntOrNull() ?: 1200
    private val deadlineMs = (System.getenv("PS_DEADLINE_S")?.toLongOrNull() ?: 300L) * 1000

    private fun mix(x0: Long): Long { var x = x0; x = (x xor (x ushr 30)) * -0x40a7b892e31b1a47L; x = (x xor (x ushr 27)) * -0x6b2fb644ecceee15L; return x xor (x ushr 31) }

    private fun wl1(g: Graph): LongArray {
        val uni = LongArray(g.n) { 0x1234567L }
        val r = dc.hashWlStableRound(g, uni, g.n + 2)
        return dc.hashWlRounds(g, uni, r)
    }

    /** Hash 2-WL on all ordered pairs until the number of pair classes is stable; returns the diagonal colours.
     *  [vcol] (optional) colours the diagonal. */
    private fun wl2(g: Graph, vcol: LongArray? = null): LongArray {
        val n = g.n
        val adj = Array(n) { BooleanArray(n) }.also { a -> for (u in 0 until n) for (v in g.adj[u]) a[u][v] = true }
        var c = LongArray(n * n) { i -> val u = i / n; val v = i % n; if (u == v) 1L + 10L * (vcol?.get(u) ?: 0L) else if (adj[u][v]) 2L else 3L }
        var classes = 3
        val ct = LongArray(n * n); val mu = LongArray(n * n); val mt = LongArray(n * n)
        while (true) {
            for (u in 0 until n) for (v in 0 until n) ct[v * n + u] = c[u * n + v]
            for (i in 0 until n * n) { mu[i] = mix(c[i] * 0x9E3779B97F4A7C15uL.toLong() + 17); mt[i] = mix(ct[i] + 0x632BE59BD9B4E019L) }
            val next = LongArray(n * n)
            for (u in 0 until n) { val ou = u * n
                for (v in 0 until n) { val ov = v * n; var s = 0L
                    for (w in 0 until n) s += mix(mu[ou + w] xor mt[ov + w])
                    next[ou + v] = mix(c[ou + v] * 31 + s) } }
            val k = next.toHashSet().size
            c = next
            if (k == classes) break
            classes = k
        }
        return LongArray(n) { c[it * n + it] }
    }

    private fun <T> classes(col: List<T>) = col.toHashSet().size
    /** every class of [a] lies inside one class of [b] */
    private fun <A, B> refines(a: List<A>, b: List<B>): Boolean {
        val m = HashMap<A, B>(); for (i in a.indices) { val p = m.putIfAbsent(a[i], b[i]); if (p != null && p != b[i]) return false }; return true
    }
    private fun <T> distinguishes(col: List<T>, nG: Int): Boolean =
        col.subList(0, nG).groupingBy { it }.eachCount() != col.subList(nG, col.size).groupingBy { it }.eachCount()

    private fun union(g: Graph, h: Graph): Graph {
        val n = g.n + h.n
        val adj = Array(n) { v -> if (v < g.n) g.adj[v].copyOf() else IntArray(h.adj[v - g.n].size) { h.adj[v - g.n][it] + g.n } }
        return Graph(n, adj, Array(n) { "$it" })
    }
    private fun writeDimacs(g: Graph, f: File) = f.printWriter().use { w ->
        w.println("p edge ${g.n} ${g.m}"); for (u in 0 until g.n) for (v in g.adj[u]) if (u < v) w.println("e ${u + 1} ${v + 1}") }

    private class Solve(val status: String, val orbits: Int?, val colour: String)
    /** our solver on the graph in [path]: 1-WL start first (layer A alone), PI start if that is not exact */
    private fun solve(path: String): Solve {
        for (pi in listOf(false, true)) {
            val r = try { dc.parityEquationsSeries(path, null, null, quiet = true, crossCheck = false, usePi = pi, computeOrbits = false,
                maxCandidates = 20_000, deadlineMs = deadlineMs, generalPrimes = true, cosetMode = true, solveOnOriginal = true) }
                catch (e: Throwable) { null }
            if (r != null && r.status == "EXACT") return Solve("EXACT", r.orbits, if (pi) "pi" else "wl1")
            if (pi) return Solve(r?.status ?: "ERROR", null, "pi")
        }
        error("unreachable")
    }

    private fun timed(f: () -> List<Any>): Pair<List<Any>, Long> { val t = System.nanoTime(); val r = f(); return r to (System.nanoTime() - t) / 1_000_000 }

    @Test fun partitionStrength() {
        val out = File(System.getenv("OUT") ?: return)
        if (!out.exists()) out.writeText("kind,name,n,m,classes_1wl,classes_2wl,classes_pi,orbits,pi_refines_2wl,wl2_refines_pi,ms_1wl,ms_2wl,ms_pi," +
            "solver,solver_colour,dist_1wl,dist_2wl,dist_pi,iso\n")
        val tmp = File(System.getenv("PS_TMP") ?: System.getProperty("java.io.tmpdir")).also { it.mkdirs() }
        val singles = System.getenv("PS_SINGLES")?.split(",")?.filter { it.isNotBlank() } ?: emptyList()
        val pairs = System.getenv("PS_PAIRS")?.split(",")?.filter { it.isNotBlank() }?.map { it.split("+") } ?: emptyList()
        val jobs = singles.map { listOf(it) } + pairs
        val done = out.readLines().drop(1).map { it.split(",")[1] }.toHashSet()   // resumable: rows already written are skipped
        for (job in jobs) {
            if (job.joinToString("+") { File(it).name } in done) continue
            val gs = job.map { GraphIO.loadDimacs(File(it).toPath()) }
            val u = if (gs.size == 1) gs[0] else union(gs[0], gs[1])
            val name = job.joinToString("+") { File(it).name }
            val (c1, t1) = timed { wl1(u).toList() }
            val (c2, t2) = if (u.n <= max2wl) timed { wl2(u).toList() } else (null to -1L)
            val (cp, tp) = try { timed { dc.piProjected(u).toList<Content>() } } catch (e: Throwable) { System.err.println("PI failed on $name: $e"); null to -1L }
            val uPath = if (gs.size == 1) job[0] else File(tmp, "$name.dimacs").also { writeDimacs(u, it) }.path
            val sU = if (System.getenv("PS_NO_SOLVE") == "1") Solve("SKIPPED", null, "") else solve(uPath)
            var iso = ""
            if (gs.size == 2 && sU.status != "SKIPPED") {
                val sG = solve(job[0]); val sH = solve(job[1])
                iso = if (sU.orbits == null || sG.orbits == null || sH.orbits == null) "unknown"
                    else if (sU.orbits == sG.orbits && sG.orbits == sH.orbits) "iso"
                    else if (sU.orbits == sG.orbits + sH.orbits) "non-iso" else "inconsistent(${sU.orbits},${sG.orbits},${sH.orbits})"
            }
            val nG = gs[0].n
            val row = listOf("${if (gs.size == 1) "single" else "pair"}", name, "${u.n}", "${u.m}",
                "${classes(c1)}", c2?.let { "${classes(it)}" } ?: "", cp?.let { "${classes(it)}" } ?: "", "${sU.orbits ?: ""}",
                if (c2 != null && cp != null) "${refines(cp, c2)}" else "", if (c2 != null && cp != null) "${refines(c2, cp)}" else "",
                "$t1", if (t2 >= 0) "$t2" else "", if (tp >= 0) "$tp" else "", sU.status, sU.colour,
                if (gs.size == 2) "${distinguishes(c1, nG)}" else "", if (gs.size == 2 && c2 != null) "${distinguishes(c2, nG)}" else "",
                if (gs.size == 2 && cp != null) "${distinguishes(cp, nG)}" else "", iso)
            out.appendText(row.joinToString(",") + "\n")
            println("PS ${row.joinToString(" ")}")
        }
    }

    /**
     * Starting colouring experiment (2026-10-03, referee question "why not 2-WL instead of PI?"): on each file, the
     * algebraic solver from three starting colourings -- plain refinement (1-WL), 2-WL, PI -- each handed to the solver
     * through piOverride; where the solver alone is not exact, the stabiliser chain from the same colouring (from 1-WL
     * only up to PS_CHAIN_WL1_MAX vertices: its negative searches are known to explode on chh). Env: PS_FILES (comma
     * list of paths), OUT (csv, resumable per file and colouring), PS_DEADLINE_S, PS_CHAIN_WL1_MAX [300].
     */
    @Test fun startingColouring() {
        val out = File(System.getenv("OUT") ?: return)
        if (!out.exists()) out.writeText("name,n,colour,classes,colour_ms,solver,solver_ms,chain,chain_aut,chain_ms,chain_queries\n")
        val done = out.readLines().drop(1).map { val p = it.split(","); p[0] + "/" + p[2] }.toHashSet()
        val files = System.getenv("PS_FILES")?.split(",")?.filter { it.isNotBlank() } ?: emptyList()
        val wl1ChainMax = System.getenv("PS_CHAIN_WL1_MAX")?.toIntOrNull() ?: 300
        val chain = PieceProfileTest()
        for (path in files) {
            val g = GraphIO.loadDimacs(File(path).toPath()); val name = File(path).name
            for (mode in listOf("wl1", "wl2", "pi")) {
                if ("$name/$mode" in done) continue
                val t0 = System.nanoTime()
                val col: Array<Content> = when (mode) {
                    "wl1" -> wl1(g).let { c -> Array(c.size) { Content.Num(c[it]) as Content } }
                    "wl2" -> wl2(g).let { c -> Array(c.size) { Content.Num(c[it]) as Content } }
                    else -> dc.piProjected(g)
                }
                val colMs = (System.nanoTime() - t0) / 1_000_000
                val classes = col.map { it.serialize() }.toHashSet().size
                val t1 = System.nanoTime()
                val r = try { dc.piOverride = col; dc.parityEquationsSeries(path, null, null, quiet = true, crossCheck = false, usePi = true,
                    computeOrbits = false, maxCandidates = 20_000, deadlineMs = deadlineMs, generalPrimes = true, cosetMode = true,
                    solveOnOriginal = true) } catch (e: Throwable) { null } finally { dc.piOverride = null }
                val solverMs = (System.nanoTime() - t1) / 1_000_000
                val status = r?.status?.replace(",", ";") ?: "ERROR"
                var chainStatus = ""; var chainAut = ""; var chainMs = ""; var queries = ""
                if (status != "EXACT" && (mode != "wl1" || g.n <= wl1ChainMax)) {
                    val t2 = System.nanoTime()
                    val o = chain.runChain(g, col, maxDepth = 200)
                    chainMs = "${(System.nanoTime() - t2) / 1_000_000}"
                    chainStatus = if (o.total != null && o.ok) "EXACT" else "NOT_EXACT"
                    chainAut = o.total?.let { "%.6g".format(it) } ?: ""
                    queries = Regex("two-sided queries in total: (\\d+)").find(o.log)?.groupValues?.get(1) ?: ""
                } else if (status != "EXACT") chainStatus = "SKIPPED"
                val row = listOf(name, "${g.n}", mode, "$classes", "$colMs", status, "$solverMs", chainStatus, chainAut, chainMs, queries)
                out.appendText(row.joinToString(",") + "\n"); println("SC ${row.joinToString(" ")}")
            }
        }
    }
}
