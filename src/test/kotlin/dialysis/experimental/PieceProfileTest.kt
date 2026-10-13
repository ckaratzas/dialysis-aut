package dialysis.experimental

import dialysis.content.Content
import dialysis.content.serialize
import dialysis.decomposition.defaultRootRule
import dialysis.decomposition.dialysisPerSpec
import dialysis.graph.Graph
import dialysis.refinement.colorRefine1WL
import dialysis.util.GraphIO
import org.junit.jupiter.api.Test
import java.io.File

/**
 * Christos, 2026-09-29: on the capped / exponential-|T_C| families (highly symmetric), does RECURSIVE decomposition
 * produce the same pieces over and over? If so, the equation system can be written over pieces instead of vertices.
 *
 * For each instance: PI colouring of G (dispatchColouring), then the recursion of [dialysis.decomposition.peel]
 * replayed with its depth recorded: at every call a QUOTIENT piece (tree + orphans of dialysisPerSpec from the
 * default root) and recursion into each remainder component; a BASE piece when the part is a tree or 1-WL-discrete.
 * Per depth: parts, pieces, distinct piece types by OUR key (size, edges, sorted degree sequence, multiset of PI
 * colours, and the same for the whole part), and -- as an ORACLE only -- distinct types by Traces certificate of the
 * PI-coloured induced piece, to see whether our key merges non-isomorphic pieces. Also: are sibling remainder
 * components isomorphic to each other (the "same decomposition repeats" question). Env PP_FILES, OUT.
 */
/** Deterministic depth budgets of the stabiliser chain, in solver work units (DecompositionCanonicalFormsTest.workBudget);
 *  calibrated 2026-09-30 on the laptop to the old 10 s / 60 s wall-clock passes (median 4.5e8 units/s over the
 *  depths that hit the 10 s limit on had, ag, pg, pp; range 0.5e8 .. 9e8). */
private const val DEFAULT_WORK1 = 4_500_000_000L
private const val DEFAULT_WORK2 = 27_000_000_000L
/** Cost cap of one relative net invariant evaluation (see relPlaneInv): all 680 branch triples at order 16. */
private const val REL_COST = 3L * 680 * 16 * 16 * 16

class PieceProfileTest {

    private val traces by lazy { dialysis.cl.TracesJni() }

    private class Part(val depth: Int, val verts: IntArray, val kind: String, val piece: IntArray, val siblings: Int)

    private fun key(g: Graph, verts: IntArray, col: Array<Content>): String {
        val set = verts.toHashSet()
        val deg = verts.map { v -> g.adj[v].count { it in set } }.sorted()
        val cols = verts.map { col[it].serialize() }.sorted()
        return "${verts.size}|${deg.sum() / 2}|${deg.hashCode()}|${cols.hashCode()}"
    }

    private fun oracle(g: Graph, verts: IntArray, col: Array<Content>): Int {
        if (verts.size <= 1) return verts.size
        val (h, _) = g.induced(verts)
        val byCol = verts.indices.groupBy { col[verts[it]].serialize() }.toSortedMap().values.map { it.toIntArray() }
        return traces.certificate(h, byCol).bytes.contentHashCode()
    }

    private val solver by lazy { DecompositionCanonicalFormsTest() }
    private val sliceTest by lazy { SliceGroupTest() }
    private fun h64(s: String): Long { var h = -0x3c5a2d1e7b9f4c11L; for (ch in s) { h = (h xor ch.code.toLong()) * 0x100000001b3L; h = h xor (h ushr 29) }; return h }
    // orbit-phase fingerprint (2026-10-05, see OrbitPhase.fingerprint): SC_FP=old = previous code path; SC_FP_THREADS (default 4)
    private val oldFp = System.getenv("SC_FP") == "old"
    private val fpPool by lazy { java.util.concurrent.ForkJoinPool(System.getenv("SC_FP_THREADS")?.toIntOrNull()?.coerceAtLeast(1) ?: 4) }
    private val FP_MARK = h64("fingerprint-mark")
    private fun mix64(x: Long): Long { var z = x + -0x61c8864680b583ebL; z = (z xor (z ushr 30)) * -0x40a7b892e31b1a47L; z = (z xor (z ushr 27)) * -0x6b2fb644ecceee15L; return z xor (z ushr 31) }
    private fun lg(x: Double?) = if (x == null || x <= 0) Double.NaN else Math.log(x) / Math.log(2.0)

    /** Recursive decomposition from a FIXED top root r (canonical given r); deeper levels use the default root rule. */
    private class P(val depth: Int, val verts: IntArray)
    private fun decompose(g: Graph, col: Array<Content>, topRoot: Int): List<P> {
        val out = mutableListOf<P>()
        fun rec(x: IntArray, depth: Int) {
            val (sub, _) = g.induced(x)
            val rc = Array(sub.n) { col[x[it]] }
            if (sub.n <= 1 || sub.m == sub.n - 1 || colorRefine1WL(sub, rc).isDiscrete()) { out.add(P(depth, x)); return }
            val r = if (depth == 0) x.indexOf(topRoot) else defaultRootRule(sub, rc)
            val d = dialysisPerSpec(sub, r)
            out.add(P(depth, (d.treeVerts.map { x[it] } + d.orphans.map { x[it] }).toIntArray()))
            for (c in d.remainderComps) rec(IntArray(c.size) { x[c[it]] }, depth + 1)
        }
        rec(IntArray(g.n) { it }, 0)
        return out
    }

    private fun signature(g: Graph, col: Array<Content>, ps: List<P>) = ps.map { "${it.depth}:${key(g, it.verts, col)}" }.sorted().joinToString(";")

    /**
     * Stage 1 of "equations over pieces" (Christos, 2026-09-29). For a root r of the smallest PI class, dialysis from r is
     * canonical given r, so Aut_r (automorphisms fixing r) permutes the pieces:  |Aut_r| <= |Aut(Q)| * prod |Aut(P_i)|,
     * Q = quotient graph (pieces as nodes coloured by (depth, type), connector edges), P_i = piece coloured by PI and by
     * the multiset of neighbouring piece types of each vertex. |Aut(Q)| and |Aut(P_i)| by OUR solver (parityAutFull);
     * |Aut| and |Aut_r| of G by Traces as an oracle only. Also: do all roots of the class give the same decomposition
     * signature (by our piece key)? Env PS_FILES, PS_ROOTS (max roots checked, default 64), OUT.
     */
    @Test fun pieceSystem() {
        val files = System.getenv("PS_FILES")?.split(",")?.map { it.trim() }?.filter { it.isNotEmpty() } ?: return
        val maxRoots = (System.getenv("PS_ROOTS") ?: "64").toInt()
        val out = File(System.getenv("OUT") ?: File(System.getProperty("java.io.tmpdir"), "piece_system.txt").path)
        for (path in files) {
            val t0 = System.currentTimeMillis()
            val g = GraphIO.loadDimacs(File(path).toPath())
            val col = dialysis.refinement.dispatchColouring(g).colouring
            val byCol = (0 until g.n).groupBy { col[it].serialize() }
            val rootClass = byCol.entries.minWith(compareBy({ it.value.size }, { it.key })).value.sorted()
            val sigs = rootClass.take(maxRoots).map { signature(g, col, decompose(g, col, it)) }.toSet().size
            val r0 = rootClass[0]
            val ps = decompose(g, col, r0)
            val pieceOf = IntArray(g.n) { -1 }; ps.forEachIndexed { i, p -> for (v in p.verts) pieceOf[v] = i }
            val ptype = ps.map { "${it.depth}:${key(g, it.verts, col)}" }
            // quotient graph Q
            val qAdj = Array(ps.size) { java.util.TreeSet<Int>() }
            for (u in 0 until g.n) for (w in g.adj[u]) { val a = pieceOf[u]; val b = pieceOf[w]; if (a != b) { qAdj[a].add(b); qAdj[b].add(a) } }
            val q = Graph(ps.size, Array(ps.size) { qAdj[it].toIntArray() }, Array(ps.size) { "$it" })
            val qCol = Array(ps.size) { Content.Num(h64(ptype[it] + (if (r0 in ps[it].verts) "|root" else ""))) as Content }
            val tq = System.currentTimeMillis(); val rq = solver.parityAutFull(q, qCol); val qS = (System.currentTimeMillis() - tq) / 1000.0
            val qAut = rq.autOrder ?: rq.autLog2?.let { Math.pow(2.0, it.toDouble()) }
            // pieces
            var sumLg = 0.0; var pieceExact = 0; var pieceStops = mutableMapOf<String, Int>(); var pieceMaxLg = 0.0; var pS = 0.0
            for ((i, p) in ps.withIndex()) {
                if (p.verts.size <= 1) { pieceExact++; continue }
                val (h, _) = g.induced(p.verts)
                val c = Array(h.n) { j -> val v = p.verts[j]
                    val nb = g.adj[v].filter { pieceOf[it] != i }.map { ptype[pieceOf[it]] }.sorted().joinToString(",")
                    Content.Num(h64(col[v].serialize() + "|" + nb + (if (v == r0) "|root" else ""))) as Content }
                val tp = System.currentTimeMillis(); val rp = solver.parityAutFull(h, c); pS += (System.currentTimeMillis() - tp) / 1000.0
                val a = rp.autOrder ?: rp.autLog2?.let { Math.pow(2.0, it.toDouble()) }
                if (rp.status == "EXACT" && a != null) { pieceExact++; sumLg += lg(a); pieceMaxLg = maxOf(pieceMaxLg, lg(a)) }
                else pieceStops.merge(rp.status.replace(Regex("\\(.*\\)"), ""), 1, Int::plus)
            }
            // oracle: |Aut(G)| and |Aut(G)_r0| (Traces, measurement only)
            val cells = byCol.toSortedMap().values.map { it.toIntArray() }
            val autG = traces.certifyAll(g, cells, getcanon = false).stats.autOrder
            val cellsR = listOf(intArrayOf(r0)) + byCol.toSortedMap().values.map { cl -> cl.filter { it != r0 }.toIntArray() }.filter { it.isNotEmpty() }
            val autR = traces.certifyAll(g, cellsR, getcanon = false).stats.autOrder
            val line = "== ${File(path).name} n=${g.n} PIclasses=${byCol.size} rootClass=${rootClass.size} rootsChecked=${minOf(maxRoots, rootClass.size)} distinctSignatures=$sigs pieces=${ps.size} depth=${ps.maxOf { it.depth }} pieceTypes=${ptype.toSet().size}\n" +
                "   Q: nodes=${q.n} edges=${q.m} ours=${rq.status} |Aut(Q)|=${qAut} (${qS}s)   pieces: exact ${pieceExact}/${ps.size} stops=$pieceStops maxlog2|Aut(P)|=${"%.1f".format(pieceMaxLg)} (${"%.1f".format(pS)}s)\n" +
                "   log2 bound = log2|Aut(Q)| + sum log2|Aut(P_i)| = ${"%.2f".format(lg(qAut) + sumLg)}   true log2|Aut_r| = ${"%.2f".format(lg(autR))}   (log2|Aut(G)| = ${"%.2f".format(lg(autG))}, orbit of r = ${"%.0f".format(autG / autR)})   ${(System.currentTimeMillis() - t0) / 1000.0}s"
            out.appendText(line + "\n"); println(line)
        }
    }

    // ───────────── Stage 2 (2026-09-29): decomposition-guided stabiliser chain, every level solved by OUR solver ─────────────

    /** Canonical hash-1-WL of G from PI colouring [col] with [marks] individualised (mark i -> its own colour). */
    private fun refined(g: Graph, col: Array<Content>, marks: List<Int>): LongArray {
        val c0 = LongArray(g.n) { h64(col[it].serialize()) }
        marks.forEachIndexed { i, v -> c0[v] = h64("mark$i") }
        var c = c0; var k = c.toSet().size
        while (true) {
            val nx = LongArray(g.n) { v -> var s = 0L; val xs = LongArray(g.adj[v].size) { c[g.adj[v][it]] }; xs.sort(); for (x in xs) s = s * 1000003L + x; h64("${c[v]}|$s") }
            val k2 = nx.toSet().size; c = nx; if (k2 == k) return c; k = k2
        }
    }
    private val unionStops = mutableListOf<String>()
    private val zeroReasons = sortedMapOf<String, Int>()
    private fun asContent(c: LongArray) = Array(c.size) { Content.Num(c[it]) as Content }

    /** Next root: lowest vertex of the smallest non-singleton refined class inside the LARGEST remainder part of the
     *  recursion so far (decomposition-guided); falls back to the whole graph's smallest non-singleton class. */
    private fun nextRoot(g: Graph, c: LongArray, part: IntArray, generalPosition: Boolean = false): Int? {
        // generalPosition (the last decomposition had NO remainder: planes, affine planes): the lowest vertex of the LARGEST
        // refined class, so the base points are in general position (the smallest class picks collinear points on planes:
        // pg2-9 needed 12 roots and 845k extension queries). Otherwise decomposition-guided: smallest class in the part.
        val cls = part.toList().groupBy { c[it] }.values.filter { it.size > 1 }.ifEmpty { (0 until g.n).groupBy { c[it] }.values.filter { it.size > 1 } }
        if (cls.isEmpty()) return null
        return if (generalPosition) cls.maxWith(compareBy<List<Int>>({ it.size }, { -it.min() })).min()
               else cls.minWith(compareBy({ it.size }, { it.min() })).min()
    }

    /** True iff [g] is the incidence graph of a projective plane: bipartite, sides of equal size N = q^2+q+1, every vertex
     *  of degree q+1, and every two vertices of one side have exactly one common neighbour (checked on the point side:
     *  the lines cover every pair of points exactly once; the dual statement then follows by counting). */
    private fun isProjectivePlane(g: Graph): Boolean {
        val side0 = g.bipartition()?.first ?: return false
        val pts = (0 until g.n).filter { it in side0 }; if (pts.size * 2 != g.n) return false
        val q = g.adj[pts[0]].size - 1
        if (q < 2 || pts.size != q * q + q + 1 || (0 until g.n).any { g.adj[it].size != q + 1 }) return false
        val idx = IntArray(g.n) { -1 }; pts.forEachIndexed { i, v -> idx[v] = i }
        val np = pts.size; val seen = java.util.BitSet(np * np)
        for (l in 0 until g.n) if (l !in side0) { val on = g.adj[l]
            for (a in on.indices) for (b in a + 1 until on.size) { val x = idx[on[a]] * np + idx[on[b]]; if (seen[x]) return false; seen[x] = true } }
        return true
    }

    /** Join/meet closure of [roots] in a projective plane's incidence graph: the smallest vertex set containing the roots
     *  and, for every two members of one side, their unique common neighbour (the line through two points, the meet of
     *  two lines). Refinement with the roots individualised makes every member of this closure a singleton. */
    private fun planeClosure(g: Graph, roots: List<Int>): BooleanArray {
        val inC = BooleanArray(g.n); val side0 = g.bipartition()!!.first
        val members = arrayOf(ArrayList<Int>(), ArrayList<Int>())
        val queue = ArrayDeque<Int>()
        fun add(v: Int) { if (!inC[v]) { inC[v] = true; queue.add(v) } }
        roots.forEach(::add)
        val mark = IntArray(g.n) { -1 }
        while (queue.isNotEmpty()) {
            val v = queue.removeFirst(); val sd = if (v in side0) 0 else 1
            for (w in g.adj[v]) mark[w] = v
            for (u in members[sd]) { for (w in g.adj[u]) if (mark[w] == v) { add(w); break } }
            members[sd].add(v)
        }
        return inC
    }

    /** Lowest vertex of the smallest non-singleton class among [vs], or null. */
    private fun smallestClassMin(c: LongArray, vs: Collection<Int>): Int? {
        val size = HashMap<Long, Int>(); for (x in c) size.merge(x, 1, Int::plus)
        return vs.filter { size.getValue(c[it]) > 1 }.groupBy { c[it] }.values.minWithOrNull(compareBy<List<Int>>({ it.size }, { it.min() }))?.min()
    }

    /** The line (maximum clique) through adjacent u, v in a block graph with 3 lines per vertex: u, v and the common
     *  neighbours with at least |C| - [slack] neighbours inside C = N(u) n N(v) (Lemma 1: slack 3 for Latin square graphs,
     *  Lemma 1': slack 5 for STS block graphs; the off-line common neighbours have at most 1 / 4). */
    private fun lineThrough(g: Graph, u: Int, v: Int, slack: Int): Set<Int> {
        val cn = g.adj[u].filter { java.util.Arrays.binarySearch(g.adj[v], it) >= 0 }.toHashSet()
        return cn.filter { w -> g.adj[w].count { it in cn } >= cn.size - slack }.toHashSet().also { it.add(u); it.add(v) }
    }

    /** SC_ROOT=random (DSS diagnostics): a uniformly random non-singleton vertex, seeded by SC_ROOT_SEED. Correctness of
     *  the chain does not depend on the root rule (it computes the orbit of whatever root it takes). */
    private val rootRnd by lazy { java.util.Random(System.getenv("SC_ROOT_SEED")?.toLongOrNull() ?: 1L) }
    private fun randomRoot(c: LongArray): Int? {
        val size = HashMap<Long, Int>(); for (x in c) size.merge(x, 1, Int::plus)
        val ns = c.indices.filter { size.getValue(c[it]) > 1 }
        return if (ns.isEmpty()) null else ns[rootRnd.nextInt(ns.size)]
    }

    /** SC_ROOT=lineframe (Theorem (Latin squares), CLOSURE_BOUND_SPEC): r1 a neighbour of r0, r2 a neighbour of r0 off the
     *  line l = l(r0, r1), then non-singleton cells of l. Null when it does not apply (the default rules take over). */
    private fun lineFrameRoot(g: Graph, c: LongArray, roots: List<Int>): Int? {
        if (roots.isEmpty()) return null
        val x = roots[0]
        if (roots.size == 1) return smallestClassMin(c, g.adj[x].toList())
        val l = lineThrough(g, x, roots[1], 3)
        if (roots.size == 2) return smallestClassMin(c, g.adj[x].filter { it !in l })
        return smallestClassMin(c, l)
    }

    /** SC_ROOT=pointframe (Theorem (STS)): r1 a neighbour of r0 (common point p, pencil P), r2 a common neighbour of r0, r1
     *  off P (pencil A = l(r0, r2)); then alternately t = a non-singleton block of P and t2 = a block of A adjacent to t
     *  (2 candidates: the blocks through the identified point of A and one of t's other points). */
    private fun pointFrameRoot(g: Graph, c: LongArray, roots: List<Int>): Int? {
        if (roots.isEmpty()) return null
        val x = roots[0]
        if (roots.size == 1) return smallestClassMin(c, g.adj[x].toList())
        val pen = lineThrough(g, x, roots[1], 5)
        if (roots.size == 2) return smallestClassMin(c, g.adj[x].filter { it !in pen && java.util.Arrays.binarySearch(g.adj[roots[1]], it) >= 0 })
        val a = lineThrough(g, x, roots[2], 5)
        val t = roots.drop(3).lastOrNull { it in pen }
        if (t != null) smallestClassMin(c, g.adj[t].filter { it in a && it != x })?.let { return it }
        return smallestClassMin(c, pen)
    }

    /** FRAME root rule for projective planes (2026-10-01, Prop. "start-up" in paper3): the next root is a non-singleton
     *  vertex that is neither in the join/meet closure of the roots nor incident with any member of it -- this gives a
     *  quadrangle within five roots (q >= 4); null if no such vertex (then any vertex outside the closure will do). Among
     *  the admissible vertices: the lowest one of the largest refined class. */
    private fun frameRoot(g: Graph, c: LongArray, roots: List<Int>): Int? {
        val clos = planeClosure(g, roots)
        val size = HashMap<Long, Int>(); for (v in 0 until g.n) size.merge(c[v], 1, Int::plus)
        // incident with no closure member; a singleton is allowed too (individualising it changes no colour but adds it
        // to the closure, which is what the start-up lemma counts) -- non-singletons are preferred
        val ok = (0 until g.n).filter { v -> !clos[v] && g.adj[v].none { clos[it] } }
        if (ok.isEmpty()) return null
        val nonSingle = ok.filter { size.getValue(c[it]) > 1 }
        if (nonSingle.isEmpty()) return ok.min()
        return nonSingle.groupBy { c[it] }.values.maxWith(compareBy<List<Int>>({ it.size }, { -it.min() })).min()
    }

    /** True iff s's dialysis is a NET: no remainder, one slice, >= 3 branches of equal size q >= 2, q^2 orphans each meeting
     *  every branch exactly once. The plane invariants read R_x from this structure and are only invariant when it holds:
     *  on affine planes the decomposition has no remainder and one slice but is not a net, and SliceGroupTest.rootInvariant
     *  then depends on the numbering (2026-09-30: split true orbits on ag2-7 / ag2-9, chain gave |Aut| = 42 for 98,784). */
    private fun isNet(g: Graph, s: Int): Boolean {
        val d = dialysisPerSpec(g, s)
        if (d.remainderComps.isNotEmpty() || d.slices.size != 1) return false
        val children = d.treeVerts.filter { d.depth[it] == 1 }.sorted(); val k = children.size
        if (k < 3) return false
        val branchOf = IntArray(g.n) { -1 }; children.forEachIndexed { i, ch -> branchOf[ch] = i }
        for (v in d.treeVerts.sortedBy { d.depth[it] }) if (d.depth[v] >= 2) branchOf[v] = branchOf[d.parent[v]]
        val sizes = IntArray(k); for (v in d.treeVerts) if (d.depth[v] >= 2) sizes[branchOf[v]]++
        val q = sizes[0]
        if (q < 2 || sizes.any { it != q } || d.orphans.size != q * q) return false
        val att = Array(d.orphans.size) { IntArray(k) { -1 } }
        for ((oi, o) in d.orphans.withIndex()) { val hit = IntArray(k)
            for (w in g.adj[o]) { val b = branchOf[w]; if (b < 0 || d.depth[w] < 2) return false; hit[b]++; att[oi][b] = w }
            if (hit.any { it != 1 }) return false }
        return fullNet(att, k, g.n)
    }

    /**
     * Net axiom (N2), 2026-10-03: two attachments in different branches have exactly one common orphan. With (N1) (every
     * orphan meets every branch once) and q^2 orphans this says that for every two branches X, Y the attachment pairs
     * (x, y) of the orphans are pairwise distinct; then every R_x : Y -> Z of the net invariants is a bijection read off
     * the slice alone. Without it R could be overwritten or left stale, i.e. depend on the numbering (cf. AG(2,7)).
     * On projective planes it always holds (Proposition net), so no plane result changes.
     */
    private fun fullNet(att: Array<IntArray>, k: Int, n: Int): Boolean {
        val seen = HashSet<Long>(att.size * 2)
        for (x in 0 until k) for (y in x + 1 until k) {
            seen.clear()
            for (a in att) if (!seen.add(a[x].toLong() * n + a[y])) return false
        }
        return true
    }

    /**
     * RELATIVE plane slice invariant (2026-09-29): invariant of (G, prefix, s) under automorphisms fixing the prefix, where
     * [c] is the refined colouring with the prefix individualised. s's decomposition must be a net (no remainder, one slice,
     * every orphan meeting every branch exactly once), else null. Per branch triple, over all 6 role assignments (row X,
     * column Y, symbol Z): branch colours and the multiset over row pairs x < x' of (colours of x, x'; multiset of the cycles
     * of R_x^-1 R_x' on Y, each as (length, sorted colours of its members)). Everything is a multiset of colour-labelled
     * structure read off s's net, so any automorphism fixing the prefix maps it onto sigma(s)'s value.
     */
    /** SC_THREADS > 1 (2026-10-02): relative plane invariants of a batch of vertices are evaluated in parallel. They are
     *  pure functions of (g, c, s) -- dialysisPerSpec and relPlaneInv use only local state -- and every caller consumes the
     *  values in the original vertex order, so the queries asked and every result are identical to the sequential run. */
    private val relThreads = System.getenv("SC_THREADS")?.toIntOrNull()?.coerceAtLeast(1) ?: 1
    private val relPool: java.util.concurrent.ForkJoinPool? = if (relThreads > 1) java.util.concurrent.ForkJoinPool(relThreads) else null
    /** batch size of the parallel evaluation: small, so that an early stop of the consumer wastes little */
    private val relBatch = if (relThreads > 1) 2 * relThreads else 1   // 1 = exactly the old one-at-a-time order
    private fun relPlaneInvAll(g: Graph, c: LongArray, vs: IntArray): Array<Long?> {
        val out = arrayOfNulls<Long>(vs.size); val pool = relPool
        if (pool == null || vs.size <= 1) { for (i in vs.indices) out[i] = relPlaneInv(g, c, vs[i]); return out }
        pool.submit { java.util.stream.IntStream.range(0, vs.size).parallel().forEach { i -> out[i] = relPlaneInv(g, c, vs[i]) } }.get()
        return out
    }

    private fun relPlaneInv(g: Graph, c: LongArray, s: Int): Long? {
        val d = dialysisPerSpec(g, s)
        if (d.remainderComps.isNotEmpty() || d.slices.size != 1) return null
        val children = d.treeVerts.filter { d.depth[it] == 1 }.sorted(); val k = children.size
        if (k < 3) return null
        val branchOf = IntArray(g.n) { -1 }; children.forEachIndexed { i, ch -> branchOf[ch] = i }
        for (v in d.treeVerts.sortedBy { d.depth[it] }) if (d.depth[v] >= 2) branchOf[v] = branchOf[d.parent[v]]
        val pts = List(k) { b -> d.treeVerts.filter { branchOf[it] == b && d.depth[it] >= 2 }.sorted() }
        val q = pts[0].size
        if (q < 2 || pts.any { it.size != q } || d.orphans.size != q * q) return null
        val idx = IntArray(g.n) { -1 }; for (pl in pts) pl.forEachIndexed { i, v -> idx[v] = i }
        val coord = Array(d.orphans.size) { IntArray(k) { -1 } }
        for ((oi, o) in d.orphans.withIndex()) for (w in g.adj[o]) { val b = branchOf[w]; if (b < 0 || d.depth[w] < 2 || coord[oi][b] != -1) return null; coord[oi][b] = idx[w] }
        if (coord.any { cd -> cd.any { it < 0 } }) return null
        if (!fullNet(coord, k, q)) return null   // net axiom (N2): every R_x below is a bijection
        val cB = LongArray(k) { c[children[it]] }; val cP = Array(k) { b -> LongArray(q) { c[pts[b][it]] } }
        val R = Array(q) { IntArray(q) }; val Rinv = Array(q) { IntArray(q) }; val seen = BooleanArray(q)
        val memBuf = LongArray(q); val cycBuf = LongArray(q); val pairBuf = LongArray(q * (q - 1) / 2)
        val tripleH = ArrayList<Long>()
        // 2026-09-30 speed (order-27 planes spent > 40 min here, once per candidate image): evaluate only a canonical
        // subset of the branch triples -- whole groups of triples with equal sorted branch-colour triple under c, taken in
        // increasing colour order until the cost cap below is reached. The branch colours are c-colours of the
        // root's children, preserved by every automorphism fixing the prefix, so the subset is canonical and the value
        // stays an invariant; the full multiset of branch colours is hashed in as well. (Only the smallest group was too
        // weak at order 16: 2.5x slower through extra fingerprints; all triples too slow at order 27.)
        fun key(a: Int, b: Int, cc: Int): Triple<Long, Long, Long> { val t = longArrayOf(cB[a], cB[b], cB[cc]); t.sort(); return Triple(t[0], t[1], t[2]) }
        val groupSize = HashMap<Triple<Long, Long, Long>, Int>()
        for (a in 0 until k) for (b in a + 1 until k) for (cc in b + 1 until k) groupSize.merge(key(a, b, cc), 1, Int::plus)
        val chosen = HashSet<Triple<Long, Long, Long>>(); var taken = 0
        // cost per triple ~ 3 q^3 (6 role choices x q^2/2 row pairs x q); all triples when that fits REL_COST (the cost of
        // all 680 triples at order 16, where the full invariant is what makes the witness search fast), else a canonical
        // subset of that cost (order 27: ~140 of 3,276 triples). Depends only on q, so root and candidates agree.
        val maxTriples = maxOf(1L, REL_COST / (3L * q * q * q))
        for (kk in groupSize.keys.sortedWith(compareBy({ it.first }, { it.second }, { it.third }))) { if (taken >= maxTriples) break; chosen.add(kk); taken += groupSize.getValue(kk) }
        for (a in 0 until k) for (b in a + 1 until k) for (cc in b + 1 until k) {
            if (key(a, b, cc) !in chosen) continue
            val roles = LongArray(6); var ri = 0
            for ((X, Y, Z) in listOf(Triple(a, b, cc), Triple(a, cc, b), Triple(b, a, cc), Triple(b, cc, a), Triple(cc, a, b), Triple(cc, b, a))) {
                for (cd in coord) { R[cd[X]][cd[Y]] = cd[Z]; Rinv[cd[X]][cd[Z]] = cd[Y] }
                // 2026-10-01: same value structure as before (sorted at every level), computed in reusable primitive buffers
                // with arithmetic mixing instead of per-cycle lists and string hashing (the inner loop runs ~q^3 per triple)
                val cPY = cP[Y]; val cPX = cP[X]; var pi = 0
                for (x in 0 until q) { val rInvX = Rinv[x]
                    for (x2 in x + 1 until q) { val rX2 = R[x2]
                        java.util.Arrays.fill(seen, false); var nc = 0
                        for (y0 in 0 until q) if (!seen[y0]) {
                            var y = y0; var len = 0
                            while (!seen[y]) { seen[y] = true; memBuf[len++] = cPY[y]; y = rInvX[rX2[y]] }
                            java.util.Arrays.sort(memBuf, 0, len)
                            var h = len.toLong() * -7046029254386353131L; for (i in 0 until len) h = h * 1000003L xor memBuf[i]
                            cycBuf[nc++] = h
                        }
                        java.util.Arrays.sort(cycBuf, 0, nc)
                        val lo = minOf(cPX[x], cPX[x2]); val hi = maxOf(cPX[x], cPX[x2])
                        var h = lo * 31L xor hi; for (i in 0 until nc) h = h * 1000003L xor cycBuf[i]
                        pairBuf[pi++] = h
                    }
                }
                java.util.Arrays.sort(pairBuf, 0, pi)
                var h = cB[X] * 1000003L xor cB[Y] * 7919L xor cB[Z]; for (i in 0 until pi) h = h * 1000003L xor pairBuf[i]
                roles[ri++] = h
            }
            roles.sort(); var h = 0x51L; for (z in roles) h = h * 1000003L xor z; tripleH.add(h)
        }
        tripleH.sort(); var h = c[s]; for (z in cB.sortedArray()) h = h * 1000003L xor z; for (z in tripleH) h = h * 1000003L xor z
        return h
    }

    /** Orbit phase at depth [kStar]: pulled by the batch solve of H = (G, r0..r_{k*-1}) (solved ONCE), it walks levels
     *  j = k*-1 .. 0; at level j the candidates s (refined colour of r_j at depth j) outside the current orbit, and per s the
     *  extension tuples (matching refined colours). Orbit closure under the verified generators of H plus every verified
     *  witness (all fix r0..r_{j-1}); a candidate whose tuples all answer "no" excludes its orbit under the known group. */
    private inner class OrbitPhase(val g: Graph, val col: Array<Content>, val roots: List<Int>, val kStar: Int, val globalInv: ((Int) -> Long?)? = null,
                                   val seedFor: ((List<Int>) -> List<IntArray>)? = null, val resetAt: Int = -1,
                                   val adaptiveR: Double = 0.0, val seedCount: Int = 0) {
        val known = mutableListOf<IntArray>(); var stabK = Double.NaN
        val orbitSize = IntArray(kStar); val candCount = IntArray(kStar); val testsAt = IntArray(kStar); val unknownAt = IntArray(kStar)
        val notes = mutableListOf<String>()
        private var j = kStar - 1
        private lateinit var cands: List<Int>; private lateinit var candIt: Iterator<Int>
        private var inOrb = BooleanArray(0); private var excluded = BooleanArray(0)
        private var curS = -1; private var curExt: Iterator<List<Int>>? = null; private var curAnyNull = false
        // fingerprint of curS not yet compared: it is only computed after curS's FIRST query answers "no" (2026-09-30: on
        // tori nearly every candidate is a positive settled by one query, and the eager fingerprint -- n refinements of n
        // vertices -- was > 90% of the time, grid-w-2-70 1,350 s at a discrete depth with 3 queries). Sound either way:
        // the fingerprint only ever excludes.
        private var curFpPending = false
        fun closure(start: Int): BooleanArray {
            val seen = BooleanArray(g.n); seen[start] = true; val q = ArrayDeque(listOf(start))
            while (q.isNotEmpty()) { val x = q.removeFirst(); for (h in known) { val y = h[x]; if (!seen[y]) { seen[y] = true; q.add(y) } } }
            return seen
        }
        private fun prefix() = roots.subList(0, j)
        private fun initLevel() {
            // SC_RESET (2026-10-05): pass 1 stops here and hands its verified generators to pass 2
            if (resetAt >= 0 && j == resetAt && j < kStar - 1) throw ChainReset(known.toList(), roots, j)
            // pass 2: generators of the known group K that fix this level's prefix pointwise (sound: verified automorphisms)
            seedFor?.invoke(prefix())?.forEach { h -> if (known.none { it.contentEquals(h) }) known.add(h) }
            val cj = refined(g, col, prefix()); val rj = roots[j]
            cands = (0 until g.n).filter { cj[it] == cj[rj] }; candIt = cands.iterator(); candCount[j] = cands.size; fpR = null; relCache.clear(); relTarget.clear()
            inOrb = closure(rj); excluded = BooleanArray(g.n); curS = -1; curExt = null; curAnyNull = false
        }
        private fun finishLevel() { orbitSize[j] = cands.count { inOrb[it] } }
        /** Invariant of (G, r0..r_{j-1}, s) under automorphisms fixing the prefix: the sorted multiset, over all t, of the
         *  refined colour multiset after individualising prefix + s + t. Different fingerprints prove s is not in r_j's orbit
         *  (2026-09-29: negative answers otherwise exhaust the whole extension tree -- pp-9-2 needed 1.4M queries). */
        private fun fingerprint(s: Int): LongArray {
            val pre = prefix()
            if (oldFp) return LongArray(g.n) { t -> val c = refined(g, col, pre + s + t); c.sort(); var h = 0x2545F4914F6CDD1DL; for (x in c) h = h * 1000003L xor x; h }.also { it.sort() }
            // 2026-10-05 (CLOSURE_BOUND_SPEC Phase 1(b), group Latin square graphs: n string-hashed refinements per candidate
            // took minutes on n = 6,561). Same invariant, computed faster: refine (prefix, s) ONCE, then per t mark t and refine
            // from that stable colouring -- the coarsest equitable refinement is the same partition as from scratch, and the
            // colour names are canonical, so equal/different fingerprints mean the same as before (up to 64-bit collisions,
            // which can only fail to exclude). Numeric hashing, t in parallel (deterministic: each t is independent).
            // SC_FP=old restores the previous code path.
            val base = refined(g, col, pre + s)
            val out = LongArray(g.n)
            fpPool.submit { java.util.stream.IntStream.range(0, g.n).parallel().forEach { t -> out[t] = fpOne(base, t) } }.get()
            return out.also { it.sort() }
        }
        private fun fpOne(base: LongArray, t: Int): Long {
            var c = base.copyOf(); c[t] = FP_MARK
            var k = distinct(c)
            while (true) {
                val nx = LongArray(g.n) { v -> var s = 0L; for (u in g.adj[v]) s += mix64(c[u]); mix64(c[v] * -0x61c8864680b583ebL xor s) }
                val k2 = distinct(nx); c = nx; if (k2 == k) break; k = k2
            }
            c.sort(); var h = 0x2545F4914F6CDD1DL; for (x in c) h = h * 1000003L xor x; return h
        }
        private fun distinct(c: LongArray): Int { val a = c.copyOf(); a.sort(); var k = if (a.isEmpty()) 0 else 1; for (i in 1 until a.size) if (a[i] != a[i - 1]) k++; return k }
        private var fpR: LongArray? = null
        /** Relative plane invariant cache for the current level (cleared per level: it depends on the prefix). */
        private val relCache = HashMap<Int, Long?>()
        val relInvOn = globalInv != null
        val fpExcluded = IntArray(kStar)
        /** relative plane invariant of each deeper root under ITS prefix (for the current level j; cleared per level) */
        private val relTarget = HashMap<Int, Long?>()
        // SC_PROGRESS=1 (2026-10-03): progress lines on stdout (output only; the computation is unchanged)
        private val progress = System.getenv("SC_PROGRESS") == "1"
        // SC_PRUNE=1 (2026-10-04, pp-27-6): automorphism pruning in the tuple search. At a node with image prefix img, the
        // known generators that fix img pointwise generate a subgroup K of Aut_(img); an element k of K maps the search tree
        // below image x onto the one below kx (k fixes img, preserves refinement and both invariants), so one image per
        // K-orbit suffices, for "yes" and for "no". Deterministic (generators in order found). Default off: bit-identical.
        private val prune = System.getenv("SC_PRUNE") == "1"
        // SC_NODE_INV=1 (2026-10-05, CLOSURE_BOUND_SPEC Phase 1(b)): node-invariant pruning at EVERY depth of the tuple search.
        // At a node the domain refinement cd and the image refinement ci are canonical (E), so an automorphism mapping the
        // domain prefix onto the image prefix gives equal colour multisets; different multisets prune the whole subtree with
        // no query. Default off: bit-identical.
        private val nodeInv = System.getenv("SC_NODE_INV") == "1"
        // SC_FP_AFTER=k (2026-10-05): the lazy fingerprint runs only after k "no" answers for the same candidate (default 1 =
        // previous behaviour). On group Latin square graphs a non-orbit candidate is refuted after ~1 query, and the
        // fingerprint (n refinements) then costs ~50 s per candidate and excludes nothing more.
        private val fpAfter = System.getenv("SC_FP_AFTER")?.toIntOrNull()?.coerceAtLeast(1) ?: 1
        private var curNo = 0
        private val resetDepth = (System.getenv("SC_RESET_DEPTH") ?: "2").toInt()
        val nodePruned = IntArray(kStar)
        // per refuted candidate (SC_NODE_INV only): deepest tuple depth reached (1 = the candidate node, kStar-j = a leaf) and
        // whether a leaf was queried -- the "c" of Condition A_c (CLOSURE_BOUND_SPEC)
        private var curMaxD = 0; private var curLeaves = 0
        // cost model (2026-10-05, SC_NODE_INV only): search nodes per tuple depth for the current candidate, aggregated per level
        // separately for refutations and for witnesses; effective branching = nodes(t+1) / nodes(t) within one candidate
        private val curNodesAt = IntArray(kStar + 2)
        inner class SearchStats { var count = 0; var sum = 0L; var max = 0; var maxBeta = 0.0; val atDepth = LongArray(kStar + 2)
            fun add() { val tot = curNodesAt.sum(); count++; sum += tot; if (tot > max) max = tot
                for (t in curNodesAt.indices) atDepth[t] += curNodesAt[t].toLong()
                for (t in 1 until curNodesAt.size - 1) if (curNodesAt[t] > 0) maxBeta = maxOf(maxBeta, curNodesAt[t + 1].toDouble() / curNodesAt[t]) }
            override fun toString() = if (count == 0) "-" else "n=$count nodes sum=$sum max=$max beta_max=${"%.2f".format(maxBeta)} perDepth=${atDepth.drop(1).dropLastWhile { it == 0L }}" }
        val refStats = Array(kStar) { SearchStats() }; val witStats = Array(kStar) { SearchStats() }
        val cutHist = Array(kStar) { sortedMapOf<Int, Int>() }; val leafRefuted = IntArray(kStar)
        private fun recordRefuted() {
            if (nodeInv) { cutHist[j].merge(curMaxD, 1, Int::plus); if (curLeaves > 0) leafRefuted[j]++; refStats[j].add() }
            // SC_RESET=adaptive (v2): reset right after the first COMPLETED refutation that needed search below depth 1 (v1 fired
            // on any deep search, including positive candidates whose witness search goes deep: a regression everywhere),
            // on a level whose class is >= R x the known orbit, if this pass found generators beyond its seeds
            if (adaptiveR > 0 && curMaxD >= resetDepth && known.size > seedCount && cands.size >= adaptiveR * cands.count { inOrb[it] })
                throw ChainReset(known.toList(), roots, j)
        }
        private fun sameMultiset(a: LongArray, b: LongArray): Boolean { val x = a.copyOf(); val y = b.copyOf(); x.sort(); y.sort(); return x.contentEquals(y) }
        private val t0p = System.currentTimeMillis(); private var lastP = 0L; private var recNodes = 0L
        private fun prog(msg: String, force: Boolean = false) { if (!progress) return; val now = System.currentTimeMillis()
            if (force || now - lastP > 30000) { lastP = now; println("PROGRESS %8.1fs level=%d %s recNodes=%d".format((now - t0p) / 1000.0, j, msg, recNodes)); System.out.flush() } }
        // SC_FASTNODE=1 (2026-10-06, stress test: ~0.3-0.6 s per search node = two string-hashed refinements from scratch).
        // Node checks only (not the colourings handed to the solver): the domain colouring of roots[0 until l] is cached per
        // l, and each image node refines its parent's stable colouring plus one mark (numeric hashing). Same partitions; the
        // names are canonical for the procedure, and domain and image use the same procedure, so an automorphism carries
        // one onto the other with equal names: every node makes the same pruning decision. Default off: bit-identical.
        private val fastNode = System.getenv("SC_FASTNODE") == "1"
        private val domCache = HashMap<Int, LongArray>()
        private fun fastRefine(c0: LongArray): LongArray {
            var c = c0; var k = distinct(c)
            while (true) {
                val nx = LongArray(g.n) { v -> var s = 0L; for (u in g.adj[v]) s += mix64(c[u]); mix64(c[v] * -0x61c8864680b583ebL xor s) }
                val k2 = distinct(nx); c = nx; if (k2 == k) return c; k = k2
            }
        }
        private fun extendCol(c: LongArray, v: Int, pos: Int): LongArray { val c0 = c.copyOf(); c0[v] = h64("node-mark$pos"); return fastRefine(c0) }
        /** Fast colouring of (G, col) with roots[0 until l] individualised, l <= kStar (cached; independent of the level j). */
        private fun domAt(l: Int): LongArray = domCache[l] ?: (if (l == 0) fastRefine(LongArray(g.n) { h64(col[it].serialize()) })
            else extendCol(domAt(l - 1), roots[l - 1], l - 1)).also { domCache[l] = it }
        // SC_FREESEARCH=1 (2026-10-06, stress test): decide each candidate s at level j by an individualisation-refinement search
        // of our own instead of image tuples of the chain's roots + solver queries. Domain path: r_j, then always the lowest vertex
        // of the smallest non-singleton cell (ties: smaller colour value), until discrete; cached per level. Image side: s, then
        // every vertex with the domain choice's colour, pruned by the node invariant and by orbits of known automorphisms that fix
        // the image prefix. A discrete leaf gives a bijection, checked edge by edge: an automorphism is a witness. Exhaustive, so
        // "none found" refutes s: any automorphism fixing the prefix with r_j -> s carries the domain path onto an image branch
        // with equal canonical colours at every node. Needs SC_FASTNODE (canonical incremental colourings). Default off.
        private val freeSearch = System.getenv("SC_FREESEARCH") == "1" && System.getenv("SC_FASTNODE") == "1"
        private var freeDomLevel = -1; private val freeDom = ArrayList<LongArray>(); private val freeDomV = ArrayList<Int>()
        private val sortedAdj by lazy { Array(g.n) { g.adj[it].copyOf().also { a -> a.sort() } } }
        private fun isAutomorphism(phi: IntArray): Boolean {
            val seen = BooleanArray(g.n); for (v in phi) { if (v < 0 || v >= g.n || seen[v]) return false; seen[v] = true }
            for (u in 0 until g.n) { val au = sortedAdj[phi[u]]; if (au.size != g.adj[u].size) return false
                for (w in g.adj[u]) if (java.util.Arrays.binarySearch(au, phi[w]) < 0) return false }
            return true
        }
        private fun cellChoice(c: LongArray): Int {   // lowest vertex of the smallest non-singleton cell, -1 if discrete
            val cnt = HashMap<Long, Int>(); for (x in c) cnt.merge(x, 1, Int::plus)
            var best: Long? = null; var bs = Int.MAX_VALUE
            for ((x, k) in cnt) if (k > 1 && (k < bs || (k == bs && x < best!!))) { bs = k; best = x }
            if (best == null) return -1
            for (v in 0 until g.n) if (c[v] == best) return v
            return -1
        }
        private fun freeDomain(t: Int): LongArray {   // domain colouring after r_j and t further choices
            if (freeDomLevel != j) { freeDomLevel = j; freeDom.clear(); freeDomV.clear(); freeDom.add(extendCol(domAt(j), roots[j], j)) }
            while (freeDom.size <= t) { val c = freeDom.last(); val v = cellChoice(c); check(v >= 0) { "freeDomain past discrete" }
                freeDomV.add(v); freeDom.add(extendCol(c, v, j + freeDom.size)) }
            return freeDom[t]
        }
        /** Witness automorphism (fixes the prefix, r_j -> s) or null (s refuted). */
        private fun freeDecide(s: Int): IntArray? {
            fun dfs(ic: LongArray, img: List<Int>, t: Int): IntArray? {
                val d = t + 1; if (d > curMaxD) curMaxD = d; if (d < curNodesAt.size) curNodesAt[d]++ else curNodesAt[curNodesAt.size - 1]++
                recNodes++; prog("free cand=$s depth=$d img=${img.drop(j)}")
                val dc = freeDomain(t)
                if (!sameMultiset(dc, ic)) { nodePruned[j]++; return null }
                if (cellChoice(dc) < 0) {   // discrete leaf: read off the bijection and verify it
                    curLeaves++
                    val byCol = HashMap<Long, Int>(g.n * 2); for (v in 0 until g.n) byCol[ic[v]] = v
                    val phi = IntArray(g.n) { v -> byCol[dc[v]] ?: -1 }
                    return if (isAutomorphism(phi) && phi[roots[j]] == s && (0 until j).all { phi[roots[it]] == roots[it] }) phi else null
                }
                freeDomain(t + 1); val dv = freeDomV[t]; val target = dc[dv]
                var orbRep: IntArray? = null
                if (prune) { val fix = known.filter { h -> img.all { h[it] == it } }
                    if (fix.isNotEmpty()) { val par = IntArray(g.n) { it }
                        fun find(x: Int): Int { var y = x; while (par[y] != y) { par[y] = par[par[y]]; y = par[y] }; return y }
                        for (h in fix) for (v in 0 until g.n) { val a = find(v); val b = find(h[v]); if (a != b) par[maxOf(a, b)] = minOf(a, b) }
                        orbRep = IntArray(g.n) { find(it) } } }
                val seenRep = HashSet<Int>()
                for (w in 0 until g.n) {
                    if (ic[w] != target) continue
                    if (orbRep != null && !seenRep.add(orbRep[w])) continue
                    val r = dfs(extendCol(ic, w, j + 1 + t), img + w, t + 1)
                    if (r != null) return r
                }
                return null
            }
            return dfs(extendCol(domAt(j), s, j), roots.subList(0, j) + s, 0)
        }
        private fun extTuples(s: Int): Sequence<List<Int>> {
            val pre = prefix(); val rj = roots[j]; val jj = j
            // 2026-09-30: image tuples filtered by the same invariants as the candidates. An automorphism mapping the root
            // prefix onto the image prefix maps r_level to an image with the SAME global plane invariant (Aut(G)-invariant)
            // and the SAME relative plane invariant (the canonical refined colours correspond, so relPlaneInv carries over);
            // null-ness (net or not) is invariant too. Without this, pp-16-6 spent 230,856 queries on POSITIVE candidates:
            // the colour class of r1 under (s) has 272 vertices of which 3 extend.
            return sequence {
                suspend fun SequenceScope<List<Int>>.rec(img: List<Int>, level: Int, par: LongArray?) {
                    if (level - jj > curMaxD) curMaxD = level - jj
                    if (level - jj < curNodesAt.size) curNodesAt[level - jj]++
                    if (level == kStar) {
                        if (nodeInv && !sameMultiset(if (fastNode) domAt(kStar) else refined(g, col, pre + rj + roots.subList(jj + 1, kStar)),
                                                     if (fastNode) extendCol(par!!, img.last(), kStar - 1) else refined(g, col, img))) { nodePruned[jj]++; return }
                        curLeaves++; yield(img.drop(pre.size + 1)); return }
                    recNodes++; prog("cand=$s tupleDepth=${level - jj} img=${img.drop(pre.size)}")
                    val cd = if (fastNode) domAt(level) else refined(g, col, pre + rj + roots.subList(jj + 1, level))
                    val ci = if (fastNode) extendCol(par!!, img.last(), level - 1) else refined(g, col, img)
                    if (nodeInv && !sameMultiset(cd, ci)) { nodePruned[jj]++; return }
                    val target = roots[level]
                    val gi = globalInv; val giT = gi?.invoke(target)
                    val rrT = if (relInvOn) relTarget.getOrPut(level) { relPlaneInv(g, cd, target) } else null
                    // lazily, as before: collect up to relBatch images that pass the (cached) global invariant, evaluate their
                    // relative invariants together, then recurse in vertex order; relBatch = 1 is the old sequential order
                    val batch = ArrayList<Int>(relBatch); var t = 0
                    // orbits of the known generators that fix the image prefix pointwise (SC_PRUNE)
                    var orbRep: IntArray? = null; var repSeen: BooleanArray? = null
                    if (prune) { val fix = known.filter { h -> img.all { h[it] == it } }
                        if (fix.isNotEmpty()) { val par = IntArray(g.n) { it }
                            fun find(x: Int): Int { var y = x; while (par[y] != y) { par[y] = par[par[y]]; y = par[y] }; return y }
                            for (h in fix) for (v in 0 until g.n) { val a = find(v); val b = find(h[v]); if (a != b) par[maxOf(a, b)] = minOf(a, b) }
                            orbRep = IntArray(g.n) { find(it) }; repSeen = BooleanArray(g.n) } }
                    while (t < g.n || batch.isNotEmpty()) {
                        while (t < g.n && batch.size < relBatch) { val tt = t++; if (ci[tt] == cd[target] && (gi == null || gi(tt) == giT)) {
                            val o = orbRep; val rs = repSeen
                            if (o != null && rs != null) { if (rs[o[tt]]) continue; rs[o[tt]] = true }
                            batch.add(tt) } }
                        if (batch.isEmpty()) break
                        val nextPar = if (fastNode) ci else null
                        if (!relInvOn) { for (x in batch) rec(img + x, level + 1, nextPar) }
                        else { val rel = relPlaneInvAll(g, ci, batch.toIntArray()); for (i in batch.indices) if (rel[i] == rrT) rec(img + batch[i], level + 1, nextPar) }
                        batch.clear()
                    }
                }
                rec(pre + s, jj + 1, if (fastNode) domAt(jj) else null)
            }
        }
        fun start(h: DecompositionCanonicalFormsTest.ParityResult) {
            stabK = h.autOrder ?: Double.NaN; known.addAll(h.generators ?: emptyList())
            if (j >= 0) initLevel()
        }
        /** Supplier for the batch: consume the answer to the previous image, return the next image or null. */
        fun next(ans: Boolean?, phi: IntArray?): Array<Content>? {
            if (j < 0) return null
            if (ans != null) prog("answer=$ans cand=$curS tests=${testsAt[j]}", force = true)
            when (ans) {
                true -> if (curS >= 0) {
                    val rj = roots[j]
                    if (phi == null || phi[rj] != curS || prefix().any { phi[it] != it }) { unknownAt[j]++; notes.add("witness missing or not fixing the prefix") }
                    else { known.add(phi); inOrb = closure(rj); if (nodeInv) witStats[j].add() }
                    curS = -1; curExt = null; curAnyNull = false
                }
                null -> if (curS >= 0) curAnyNull = true
                false -> if (curS >= 0 && curFpPending && ++curNo >= fpAfter) {
                    curFpPending = false
                    val fr = fpR ?: fingerprint(roots[j]).also { fpR = it }
                    if (!fingerprint(curS).contentEquals(fr)) { fpExcluded[j]++; recordRefuted(); val o = closure(curS); for (v in 0 until g.n) if (o[v]) excluded[v] = true
                        curS = -1; curExt = null; curAnyNull = false }
                }
            }
            while (true) {
                val e = curExt
                if (curS >= 0 && e != null && e.hasNext()) { testsAt[j]++; return asContent(refined(g, col, prefix() + curS + e.next())) }
                if (curS >= 0) {   // all tuples of curS answered "no" (or stopped)
                    if (curAnyNull) unknownAt[j]++ else { recordRefuted(); val o = closure(curS); for (v in 0 until g.n) if (o[v]) excluded[v] = true }
                    curS = -1; curExt = null; curAnyNull = false
                }
                var s0 = -1
                while (candIt.hasNext()) { val c = candIt.next(); if (!inOrb[c] && !excluded[c]) { s0 = c; break } }
                if (s0 >= 0) {
                    // cheap invariant first: a different fingerprint proves "not in the orbit" without any query
                    // cheapest first: the global net invariant is cached per vertex, the relative one costs a full evaluation
                    val gi = globalInv; val giR = gi?.invoke(roots[j])
                    if (gi != null && giR != null) { val gs = gi(s0); if (gs != null && gs != giR) { fpExcluded[j]++; val o = closure(s0); for (v in 0 until g.n) if (o[v]) excluded[v] = true; continue } }
                    if (relInvOn) {
                        val cj = refined(g, col, prefix())
                        val rr = relCache.getOrPut(roots[j]) { relPlaneInv(g, cj, roots[j]) }
                        if (rr != null && relPool != null && s0 !in relCache) {
                            // prefetch: s0 and the next open candidates (not yet in the orbit, not excluded) in one parallel batch
                            val ahead = ArrayList<Int>(relBatch).apply { add(s0) }
                            var p = cands.indexOf(s0) + 1
                            while (ahead.size < relBatch && p < cands.size) { val c2 = cands[p++]; if (!inOrb[c2] && !excluded[c2] && c2 !in relCache) ahead.add(c2) }
                            val vals = relPlaneInvAll(g, cj, ahead.toIntArray()); for (i in ahead.indices) relCache[ahead[i]] = vals[i]
                        }
                        if (rr != null) { val rs = relCache.getOrPut(s0) { relPlaneInv(g, cj, s0) }
                            if (rs != null && rs != rr) { fpExcluded[j]++; val o = closure(s0); for (v in 0 until g.n) if (o[v]) excluded[v] = true; continue } }
                    }
                    prog("start cand=$s0 (#${cands.indexOf(s0) + 1} of ${cands.size}, inOrb=${inOrb.count { it }}, excluded=${excluded.count { it }}, tests=${testsAt[j]})", force = true)
                    if (freeSearch) {
                        curMaxD = 0; curLeaves = 0; curNodesAt.fill(0)
                        val phi = freeDecide(s0)
                        if (phi != null) { known.add(phi); inOrb = closure(roots[j]); if (nodeInv) witStats[j].add(); prog("answer=true cand=$s0 (free search)", force = true) }
                        else { recordRefuted(); val o = closure(s0); for (v in 0 until g.n) if (o[v]) excluded[v] = true; prog("answer=false cand=$s0 (free search)", force = true) }
                        continue
                    }
                    curS = s0; curExt = extTuples(s0).iterator(); curAnyNull = false; curFpPending = true; curNo = 0; curMaxD = 0; curLeaves = 0; curNodesAt.fill(0); continue
                }
                finishLevel(); j--
                if (j < 0) return null
                initLevel()
            }
        }
    }

    /**
     * Env SC_FILES, SC_MAXDEPTH (default 6), SC_MINDEPTH (default 0), OUT. Per instance: base r0, r1, ... from the
     * decomposition. At depth k ONE batch solve of H = (G, r0..r_{k-1}): if its group phase is exact, the same solve answers
     * every orbit query of every level ([OrbitPhase]); otherwise go one root deeper. |Aut| = prod |orbit_j| * |Aut(H)|,
     * compared with Traces (oracle only).
     */
    @Test fun stabiliserChain() {
        val files = System.getenv("SC_FILES")?.split(",")?.map { it.trim() }?.filter { it.isNotEmpty() } ?: return
        val maxDepth = (System.getenv("SC_MAXDEPTH") ?: "6").toInt()
        // SC_MINDEPTH >= 1 forces at least one individualised root even where the solver is exact at depth 0: a
        // negative control for the two-sided orbit test (CFI: PI cannot separate twisted pairs, |Aut| = 1).
        val minDepth = (System.getenv("SC_MINDEPTH") ?: "0").toInt()
        // SC_NAIVE=1: CONTROL -- ignore the decomposition entirely; every root = lowest vertex of the smallest non-singleton
        // refined class of the whole graph (plain individualisation base), everything else unchanged.
        val naive = System.getenv("SC_NAIVE") == "1"
        // SC_PLANE=remove (Christos, 2026-09-29): when a root's decomposition has no remainder (planes, affine planes), remove
        // the root from the part and decompose the REST: G - {roots} is no longer homogeneous, so the recursion finds pieces
        // and the next root is chosen decomposition-guided in them. Default: the general-position rule on the whole graph.
        val planeRemove = System.getenv("SC_PLANE") == "remove"
        val out = File(System.getenv("OUT") ?: File(System.getProperty("java.io.tmpdir"), "stab_chain.txt").path)
        // SC_TRACE=1: print each step immediately with heap in use and process RSS (the result block is only written at the
        // end, so a memory kill otherwise leaves no trace of the step it died in)
        val trace = System.getenv("SC_TRACE") == "1"
        // SC_COLOUR=wl1 (2026-09-30): start from plain 1-WL instead of PI. Sound for every graph (the chain needs only an
        // Aut-invariant colouring; PI only makes it faster), and it avoids PI's O(n_sd^2) decomposition store, which is
        // the only thing that runs out of memory on the large triang / lattice / tori / Johnson graphs. On vertex-transitive
        // graphs PI cannot be finer than 1-WL anyway (every invariant colouring is one class).
        val wl1Colour = System.getenv("SC_COLOUR") == "wl1"
        val noTraces = System.getenv("SC_NO_TRACES") == "1"
        val tStart = System.currentTimeMillis()
        fun tr(what: String) { if (!trace) return
            val rt = Runtime.getRuntime(); val heap = (rt.totalMemory() - rt.freeMemory()) shr 20
            val rss = try { File("/proc/self/status").readLines().first { it.startsWith("VmRSS") }.split(Regex("\\s+"))[1].toLong() shr 10 } catch (e: Exception) { -1L }
            System.out.println("TRACE %7.1fs heap=%dM rss=%dM %s".format((System.currentTimeMillis() - tStart) / 1000.0, heap, rss, what)); System.out.flush() }
        for (path in files) {
            val t0 = System.currentTimeMillis()
            tr("load $path")
            val g0 = GraphIO.loadDimacs(File(path).toPath())
            // SC_COMPLEMENT=1 (2026-10-02): complement every dense pair of 1-WL classes first (Aut-preserving), then run the
            // whole chain -- colouring included -- on the sparser graph
            // affine planes (2026-10-02, Aff25): run the chain on the projective completion with the new elements marked, where
            // the frame rule and the net invariants apply (SC_AFFINE=0 disables)
            val affine = if (System.getenv("SC_AFFINE") != "0") affineCompletion(g0) else null
            if (affine != null) tr("affine plane: completed to a projective plane, n ${g0.n} -> ${affine.first.n}")
            val chiG = if (affine == null && System.getenv("SC_COMPLEMENT") == "1") colorRefine1WL(g0, dialysis.refinement.uniformSeed(g0.n)).color else null
            val g = affine?.first ?: if (chiG != null) complementDense(g0, chiG, ::tr) else g0
            tr("loaded n=${g.n} m=${g.m}; ${if (wl1Colour) "1-WL" else "PI"}")
            // when the complement was applied, G' is sparse (PI is cheap there) and usually disconnected: PI separates pieces
            // that 1-WL cannot, and from 1-WL the orbit phase has to refute candidates in the wrong pieces one by one
            // (tnn 182: 11 queries and 16 s from PI, > 20 min from 1-WL) -- so PI on G' regardless of SC_COLOUR
            val col0 = if (wl1Colour && g === g0) colorRefine1WL(g, dialysis.refinement.uniformSeed(g.n)).color
                      else dialysis.refinement.dispatchColouring(g).colouring
            // complement mode: Aut(G') = Aut(G) only for permutations that keep G's classes, so the colouring of G' is combined
            // with G's 1-WL classes and refined (G' can be disconnected, and then Aut(G') alone could mix pieces of different classes)
            val col = if (affine != null) colorRefine1WL(g, Array(g.n) { v -> Content.Num(fnv64(col0[v].serialize() + "|m" + affine.second[v])) }).color
                      else if (chiG == null) col0 else colorRefine1WL(g, Array(g.n) { v -> Content.Num(fnv64(col0[v].serialize() + "|" + chiG[v].serialize())) }).color
            tr("colouring done: ${col.map { it.serialize() }.toSet().size} classes")
            val sb = StringBuilder("== ${File(path).name} n=${g.n}${if (wl1Colour) " colour=1-WL" else ""}\n")
            // a complemented graph that falls apart is solved by combination: the pipeline itself only sees connected graphs
            val res = if (chiG != null && g !== g0 && componentsOf(g).size > 1) solveByComponents(g, chiG, maxDepth, ::tr)
                      else if (System.getenv("SC_RESET") == "1" || System.getenv("SC_RESET") == "adaptive") runChainWithReset(g, col, maxDepth, minDepth, naive, planeRemove, ::tr)
                      else runChain(g, col, maxDepth, minDepth, naive, planeRemove, ::tr)
            sb.append(res.log)
            if (chiG != null && g !== g0 && res.total != null) {
                // complement mode: every final generator must also be an automorphism of the ORIGINAL graph and keep its classes
                val edges0 = HashSet<Long>(); for (u in 0 until g0.n) for (v in g0.adj[u]) edges0.add(u.toLong() * g0.n + v)
                val bad = res.gens.count { p -> (0 until g0.n).any { u -> chiG[p[u]] != chiG[u] || g0.adj[u].any { v -> (p[u].toLong() * g0.n + p[v]) !in edges0 } } }
                sb.appendLine("   complement mode: ${res.gens.size - bad} of ${res.gens.size} generators verified on the original graph" + (if (bad > 0) "  ** FAILED **" else ""))
            }
            if (affine != null) {
                sb.appendLine("   affine plane: chain on its projective completion (n ${g0.n} -> ${g.n}), new elements marked")
                if (res.total != null) {
                    val edges0 = HashSet<Long>(); for (u in 0 until g0.n) for (v in g0.adj[u]) edges0.add(u.toLong() * g0.n + v)
                    val bad = res.gens.count { p -> (0 until g0.n).any { u -> p[u] >= g0.n || affine.second[p[u]] != affine.second[u] || g0.adj[u].any { v -> p[v] >= g0.n || (p[u].toLong() * g0.n + p[v]) !in edges0 } } }
                    sb.appendLine("   affine mode: ${res.gens.size - bad} of ${res.gens.size} generators verified on the original graph" + (if (bad > 0) "  ** FAILED **" else ""))
                }
            }
            if (res.total == null) { sb.appendLine("   no exact depth within $maxDepth"); out.appendText(sb.toString()); print(sb); continue }
            val total = res.total; val ok = res.ok
            // our time ends HERE: everything below is checking only (2026-10-01, Christos: keep the oracle separate)
            val ours = (System.currentTimeMillis() - t0) / 1000.0
            // known |Aut| where the file name says what the graph is (johnson-n-k, hypercube-d): a check without Traces
            val known = knownAut(File(path).name)
            val knownTxt = if (known == null) "" else "  formula ${"%.6g".format(known)} agree=${ok && Math.abs(total - known) <= 1e-9 * known}"
            // SC_NO_TRACES=1: no Traces in this run (the oracle is a separate job, uncoloured Traces: run_traces.sh).
            // Otherwise Traces on the UNCOLOURED graph -- an independent check, not one that shares our PI colouring.
            val trTxt = if (noTraces) "" else {
                tr("Traces check")
                val tt = System.currentTimeMillis()
                val trAut = traces.certifyAll(g, listOf(IntArray(g.n) { it }), getcanon = false).stats.autOrder
                "  Traces ${"%.6g".format(trAut)}  agree=${ok && Math.abs(total - trAut) <= 1e-9 * maxOf(1.0, trAut)}  traces ${(System.currentTimeMillis() - tt) / 1000.0}s"
            }
            sb.appendLine("   |Aut| = ${"%.6g".format(total)}${if (!ok) " (incomplete)" else ""}  ours ${ours}s$knownTxt$trTxt")
            out.appendText(sb.toString()); print(sb)
        }
    }

    class ChainOutcome(val total: Double?, val ok: Boolean, val log: String, val gens: List<IntArray> = emptyList())

    // ───────────── SC_RESET (Christos, 2026-10-05): stop the orbit phase at a level, restart the chain with what is known ─────────────
    /** Thrown by [OrbitPhase] in pass 1 at level [level]: [gens] are the verified automorphisms found so far. */
    class ChainReset(val gens: List<IntArray>, val roots: List<Int>, val level: Int) : RuntimeException(null, null, false, false)

    private val stabCache = HashMap<List<Int>, List<IntArray>>()
    /** Generators of a subgroup of K_(base) (pointwise stabiliser), K = <gens>: per base point a deterministic Schreier sample
     *  u_x * s * u_{s(x)}^-1 over the first 64 orbit points, at most 40 kept. Every element is a product of verified
     *  automorphisms fixing the prefix, so it is sound for orbit closure; it may generate a proper subgroup (efficiency only). */
    private fun stabiliserSample(gens: List<IntArray>, base: List<Int>): List<IntArray> {
        if (base.isEmpty()) return gens
        stabCache[base]?.let { return it }
        val up = stabiliserSample(gens, base.dropLast(1)); val b = base.last(); val n = gens.firstOrNull()?.size ?: return emptyList()
        val parent = IntArray(n) { -2 }; val via = IntArray(n) { -1 }; parent[b] = -1
        val order = ArrayList<Int>(); val q = ArrayDeque(listOf(b)); order.add(b)
        while (q.isNotEmpty()) { val x = q.removeFirst(); for ((i, s) in up.withIndex()) { val y = s[x]; if (parent[y] == -2) { parent[y] = x; via[y] = i; q.add(y); order.add(y) } } }
        val tr = HashMap<Int, IntArray>()
        fun u(x: Int): IntArray = tr.getOrPut(x) { if (x == b) IntArray(n) { it } else { val pu = u(parent[x]); val gg = up[via[x]]; IntArray(n) { gg[pu[it]] } } }
        val out = ArrayList<IntArray>(); val seen = HashSet<Int>()
        loop@ for (x in order.take(64)) for (s in up) {
            val ux = u(x); val uy = u(s[x]); val inv = IntArray(n); for (v in 0 until n) inv[uy[v]] = v
            val h = IntArray(n) { inv[s[ux[it]]] }
            if ((0 until n).all { h[it] == it }) continue
            check(base.all { h[it] == it }) { "stabiliserSample: element does not fix the base" }
            if (seen.add(h.contentHashCode())) out.add(h)
            if (out.size >= 40) break@loop
        }
        stabCache[base] = out; return out
    }
    /** Pass-2 root rule: the non-singleton refined class with the FEWEST orbits of the known group K_(roots) (one orbit =
     *  Condition A certified there), ties to the larger class; inside it the lowest vertex of the largest K-orbit. */
    private fun knownGroupRoot(g: Graph, c: LongArray, k: List<IntArray>): Int? {
        val par = IntArray(g.n) { it }
        fun find(x: Int): Int { var y = x; while (par[y] != y) { par[y] = par[par[y]]; y = par[y] }; return y }
        for (h in k) for (v in 0 until g.n) { val a = find(v); val bb = find(h[v]); if (a != bb) par[maxOf(a, bb)] = minOf(a, bb) }
        val cls = (0 until g.n).groupBy { c[it] }.values.filter { it.size > 1 }
        if (cls.isEmpty()) return null
        val best = cls.minWith(compareBy<List<Int>>({ cl -> cl.map { find(it) }.toSet().size }, { -it.size }, { it.min() }))
        val orbs = best.groupBy { find(it) }.values
        return orbs.maxWith(compareBy<List<Int>>({ it.size }, { -it.min() })).min()
    }
    /** SC_RESET=adaptive: every pass may stop at the first level whose candidate class is >= SC_RESET_R (default 4) x the known
     *  orbit of its root, right after its first deep refutation; the verified generators seed the next pass. At most SC_RESET_MAX (default 1)
     *  resets; the last pass runs to the end. */
    private fun runChainAdaptiveReset(g: Graph, col: Array<Content>, maxDepth: Int, minDepth: Int, naive: Boolean, planeRemove: Boolean, tr: (String) -> Unit): ChainOutcome {
        val r = (System.getenv("SC_RESET_R") ?: "4").toDouble(); val maxResets = (System.getenv("SC_RESET_MAX") ?: "1").toInt()
        val edges = HashSet<Long>(); for (u in 0 until g.n) for (v in g.adj[u]) edges.add(u.toLong() * g.n + v)
        fun isAut(p: IntArray) = p.size == g.n && p.toSet().size == g.n && (0 until g.n).all { u -> g.adj[u].all { v -> (p[u].toLong() * g.n + p[v]) in edges } }
        var seeds = emptyList<IntArray>(); val head = StringBuilder(); var solveFrom = 0
        val skip = System.getenv("SC_RESET_SKIP") == "1"
        for (pass in 1..maxResets + 1) {
            val t = System.currentTimeMillis(); stabCache.clear()
            try {
                val res = runChain(g, col, maxDepth, minDepth, naive, planeRemove, tr, seeds = seeds, adaptiveR = if (pass <= maxResets) r else 0.0, solveFrom = solveFrom)
                head.append("   RESET adaptive: pass $pass ran to the end (${"%.1f".format((System.currentTimeMillis() - t) / 1000.0)}s); log of the last pass below\n")
                return ChainOutcome(res.total, res.ok, head.toString() + res.log, res.gens)
            } catch (e: ChainReset) {
                val good = e.gens.filter(::isAut); val rejected = e.gens.size - good.size
                head.append("   RESET adaptive: pass $pass roots=${e.roots} stopped at level ${e.level} after ${"%.1f".format((System.currentTimeMillis() - t) / 1000.0)}s, ${good.size} verified generators" + (if (rejected > 0) " ($rejected REJECTED)" else "") + "\n")
                tr("reset: pass $pass stopped at level ${e.level}, ${good.size} generators")
                seeds = good
                if (skip) solveFrom = maxOf(0, e.roots.size - 2)
            }
        }
        error("unreachable")
    }
    /** SC_RESET=1: pass 1 stops at level SC_RESET_LEVEL (default 1); its generators are re-verified on G and seed pass 2. */
    internal fun runChainWithReset(g: Graph, col: Array<Content>, maxDepth: Int, minDepth: Int, naive: Boolean, planeRemove: Boolean, tr: (String) -> Unit): ChainOutcome {
        if (System.getenv("SC_RESET") == "adaptive") return runChainAdaptiveReset(g, col, maxDepth, minDepth, naive, planeRemove, tr)
        val level = (System.getenv("SC_RESET_LEVEL") ?: "1").toInt()
        val t1 = System.currentTimeMillis()
        val reset = try { return runChain(g, col, maxDepth, minDepth, naive, planeRemove, tr, resetAt = level) } catch (e: ChainReset) { e }
        val s1 = (System.currentTimeMillis() - t1) / 1000.0
        val edges = HashSet<Long>(); for (u in 0 until g.n) for (v in g.adj[u]) edges.add(u.toLong() * g.n + v)
        val good = reset.gens.filter { p -> p.toSet().size == g.n && (0 until g.n).all { u -> g.adj[u].all { v -> (p[u].toLong() * g.n + p[v]) in edges } } }
        tr("reset: pass 1 stopped at level ${reset.level} (roots ${reset.roots}) after ${s1}s, ${good.size}/${reset.gens.size} generators verified")
        stabCache.clear()
        val r2 = runChain(g, col, maxDepth, minDepth, naive, planeRemove, tr, seeds = good,
                          solveFrom = if (System.getenv("SC_RESET_SKIP") == "1") maxOf(0, reset.roots.size - 2) else 0)
        val head = "   RESET: pass 1 roots=${reset.roots} stopped at level ${reset.level} after ${"%.1f".format(s1)}s with ${good.size} verified generators" +
            (if (good.size < reset.gens.size) " (${reset.gens.size - good.size} REJECTED)" else "") + "; pass 2 below\n"
        return ChainOutcome(r2.total, r2.ok, head + r2.log, r2.gens)
    }

    /** One instance of the chain (see [stabiliserChain]): |Aut| = prod |orbit_j| * |Aut(H)| by our solver only, or total = null
     *  when no depth up to [maxDepth] is exact. [col] = PI colouring. No Traces in here. */
    /** If [g] is the incidence graph of an affine plane of order q >= 2 (q^2 points of degree q+1, q^2+q lines of degree q,
     *  bipartite, two points on exactly one line), return its projective completion: one new point per parallel class of
     *  lines (ids n..n+q) joined to the lines of its class, and one new line (id n+q+1) through the new points; together with
     *  marker colours 0 = point, 1 = line, 2 = point at infinity, 3 = line at infinity. Every automorphism of the affine plane
     *  extends uniquely to the completion and fixes the line at infinity, and every marker-preserving automorphism of the
     *  completion restricts to one of the affine plane, so |Aut(G)| = |Aut(P, markers)|. Null if [g] is not an affine plane. */
    internal fun affineCompletion(g: Graph): Pair<Graph, IntArray>? {
        val deg = IntArray(g.n) { g.adj[it].size }; val ds = deg.toSet()
        if (ds.size != 2) return null
        val q = ds.min(); if (q < 2 || ds.max() != q + 1) return null
        val pts = (0 until g.n).filter { deg[it] == q + 1 }; val lines = (0 until g.n).filter { deg[it] == q }
        if (pts.size != q * q || lines.size != q * q + q) return null
        val isPt = BooleanArray(g.n); for (v in pts) isPt[v] = true
        if ((0 until g.n).any { u -> g.adj[u].any { v -> isPt[u] == isPt[v] } }) return null
        val seen = IntArray(g.n) { -1 }
        for (p in pts) { var c = 0
            for (l in g.adj[p]) for (x in g.adj[l]) if (x != p) { if (seen[x] == p) return null; seen[x] = p; c++ }
            if (c != q * q - 1) return null }                       // every other point exactly once: two points, one line
        val cls = IntArray(g.n) { -1 }; var k = 0
        for (l in lines) { if (cls[l] >= 0) continue
            val meets = HashSet<Int>(); for (x in g.adj[l]) for (m in g.adj[x]) meets.add(m)
            for (m in lines) if (cls[m] < 0 && (m == l || m !in meets)) cls[m] = k
            k++ }
        if (k != q + 1 || (0 until k).any { c -> lines.count { cls[it] == c } != q }) return null
        val n2 = g.n + q + 2; val inf = g.n + q + 1
        val adj = Array(n2) { ArrayList<Int>() }
        for (u in 0 until g.n) for (v in g.adj[u]) adj[u].add(v)
        for (l in lines) { adj[l].add(g.n + cls[l]); adj[g.n + cls[l]].add(l) }
        for (c in 0..q) { adj[g.n + c].add(inf); adj[inf].add(g.n + c) }
        val marker = IntArray(n2) { v -> when { v == inf -> 3; v >= g.n -> 2; isPt[v] -> 0; else -> 1 } }
        return Graph(n2, Array(n2) { adj[it].sorted().toIntArray() }, Array(n2) { if (it < g.n) g.names[it] else "inf$it" }) to marker
    }

    /** Connected components of [g], each as a sorted vertex array. */
    private fun componentsOf(g: Graph): List<IntArray> {
        val seen = BooleanArray(g.n); val out = ArrayList<IntArray>()
        for (s0 in 0 until g.n) { if (seen[s0]) continue
            val c = ArrayList<Int>(); val st = ArrayDeque(listOf(s0)); seen[s0] = true
            while (st.isNotEmpty()) { val x = st.removeLast(); c.add(x); for (y in g.adj[x]) if (!seen[y]) { seen[y] = true; st.addLast(y) } }
            out.add(c.sorted().toIntArray()) }
        return out
    }

    /** The colouring a connected piece starts from: its PI colouring combined with the colours [chi] it inherits, refined.
     *  Both parts are canonical, so isomorphic coloured pieces get the same colour histogram. */
    private fun pieceColouring(sub: Graph, chi: Array<Content>): Array<Content> {
        val pi = dialysis.refinement.dispatchColouring(sub).colouring
        return colorRefine1WL(sub, Array(sub.n) { v -> Content.Num(fnv64(pi[v].serialize() + "|" + chi[v].serialize())) }).color
    }

    /** Combination (2026-10-02, Christos): a disconnected graph is never handed to the pipeline. Every component -- a
     *  connected graph -- is solved by the chain on its own; the components are grouped by coloured isomorphism (exact test:
     *  the chain on the union of two pieces, which are isomorphic iff a generator maps one onto the other); and
     *  |Aut| = prod over types |Aut(C)|^k * k!. Generators: the first copy's own generators, and for every further copy the
     *  map exchanging it with the first copy. [chi] are the colours every map must preserve. */
    private fun solveByComponents(g: Graph, chi: Array<Content>, maxDepth: Int, tr: (String) -> Unit): ChainOutcome {
        val sb = StringBuilder(); val comps = componentsOf(g)
        val pieces = comps.map { c -> val (sub, _) = g.induced(c); val sc = Array(c.size) { chi[c[it]] }; Triple(c, sub, pieceColouring(sub, sc)) }
        fun key(i: Int) = pieces[i].let { (c, sub, col) -> "${c.size}/${sub.m}/" + col.map { it.serialize() }.sorted().hashCode() }
        val types = ArrayList<MutableList<Pair<Int, IntArray?>>>()       // per type: (piece index, isomorphism first copy -> piece)
        val byKey = HashMap<String, MutableList<Int>>()                    // key -> indices of types with that key
        var ok = true
        for (i in pieces.indices) {
            var placed = false
            for (t in byKey[key(i)].orEmpty()) {
                val a = pieces[types[t][0].first]; val b = pieces[i]; val na = a.first.size
                val uAdj = Array(na + b.first.size) { v -> if (v < na) a.second.adj[v].copyOf() else IntArray(b.second.adj[v - na].size) { b.second.adj[v - na][it] + na } }
                val u = Graph(uAdj.size, uAdj, Array(uAdj.size) { "$it" })
                val uCol = Array(u.n) { if (it < na) a.third[it] else b.third[it - na] }
                val r = runChain(u, uCol, maxDepth, 0, false, false, tr)
                // an unfinished isomorphism test must not split one type into two (the k! factor would be lost): give up
                if (r.total == null) { sb.appendLine("   combination: isomorphism test of two components not exact within $maxDepth"); return ChainOutcome(null, false, sb.toString()) }
                val swap = r.gens.firstOrNull { p -> p[0] >= na }
                if (swap != null) { types[t].add(i to IntArray(na) { swap[it] - na }); placed = true; break }
            }
            if (!placed) { types.add(mutableListOf(i to null)); byKey.getOrPut(key(i)) { mutableListOf() }.add(types.size - 1) }
        }
        var total = 1.0; val gens = ArrayList<IntArray>()
        for ((t, members) in types.withIndex()) {
            val (c0, sub0, col0) = pieces[members[0].first]
            val r = runChain(sub0, col0, maxDepth, 0, false, false, tr)
            if (r.total == null) { sb.appendLine("   component type $t (${c0.size} vertices): no exact depth within $maxDepth"); return ChainOutcome(null, false, sb.toString()) }
            ok = ok && r.ok
            val k = members.size; var kf = 1.0; for (j in 2..k) kf *= j
            total *= Math.pow(r.total, k.toDouble()) * kf
            sb.appendLine("   component type $t: ${c0.size} vertices, |Aut| = ${"%.6g".format(r.total)}, $k cop${if (k == 1) "y" else "ies"}")
            for (p0 in r.gens) gens.add(IntArray(g.n) { it }.also { p -> for (x in c0.indices) p[c0[x]] = c0[p0[x]] })
            for ((idx, phi) in members.drop(1)) { val ci = pieces[idx].first
                gens.add(IntArray(g.n) { it }.also { p -> for (x in c0.indices) { p[c0[x]] = ci[phi!![x]]; p[ci[phi[x]]] = c0[x] } }) }
        }
        sb.appendLine("   combination: ${comps.size} components, ${types.size} types; |Aut| = prod |Aut(C)|^k k! = ${"%.6g".format(total)}")
        return ChainOutcome(total, ok, sb.toString(), gens)
    }

    private fun fnv64(s: String): Long { var h = -0x340d631b7bdddcdbL; for (ch in s) { h = h xor ch.code.toLong(); h *= 0x100000001b3L }; return h }

    /** Replace every pair of colour classes of [col] (and every class's internal edges) that is more than half full by its
     *  complement. For an invariant [col], a colour-preserving permutation preserves the edges between (or inside) classes iff
     *  it preserves the non-edges, so Aut(G, col) = Aut(G', col) = Aut(G): the result is an exact, sparser stand-in for G. */
    internal fun complementDense(g: Graph, col: Array<Content>, tr: (String) -> Unit = {}): Graph {
        val keyOf = HashMap<Content, Int>(); val cls = IntArray(g.n) { keyOf.getOrPut(col[it]) { keyOf.size } }
        val k = keyOf.size; val size = LongArray(k); for (c in cls) size[c]++
        val members = Array(k) { ArrayList<Int>() }; for (v in 0 until g.n) members[cls[v]].add(v)
        val cnt = HashMap<Long, Long>()
        for (u in 0 until g.n) for (v in g.adj[u]) if (u < v) { val a = minOf(cls[u], cls[v]); val b = maxOf(cls[u], cls[v]); cnt.merge(a.toLong() * k + b, 1L, Long::plus) }
        val flip = HashSet<Long>()
        for ((key, e) in cnt) { val a = (key / k).toInt(); val b = (key % k).toInt()
            val possible = if (a == b) size[a] * (size[a] - 1) / 2 else size[a] * size[b]
            // only between classes of at least two vertices (a pair of singletons carries no symmetry to expose)
            if (size[a] >= 2 && size[b] >= 2 && 2 * e > possible) flip.add(key) }
        if (flip.isEmpty()) { tr("complement: no dense class pair"); return g }
        val adj = Array(g.n) { u ->
            val out = ArrayList<Int>(); val cu = cls[u]
            for (v in g.adj[u]) { val a = minOf(cu, cls[v]).toLong(); val b = maxOf(cu, cls[v]).toLong(); if (a * k + b !in flip) out.add(v) }
            for (b in 0 until k) { val key = minOf(cu, b).toLong() * k + maxOf(cu, b); if (key !in flip) continue
                for (v in members[b]) if (v != u && java.util.Arrays.binarySearch(g.adj[u], v) < 0) out.add(v) }
            out.sort(); out.toIntArray() }
        val g2 = Graph(g.n, adj, g.names)
        // applied only when it removes at least half of the edges (tnn: -96%); a mild sparsification (chh: -22%) did not help
        if (2L * g2.m > g.m) { tr("complement: ${flip.size} dense class pairs, m ${g.m} -> ${g2.m}: less than half removed, not applied"); return g }
        tr("complement: ${flip.size} dense class pairs of ${cnt.size}, m ${g.m} -> ${g2.m}")
        return g2
    }

    internal fun runChain(g: Graph, col: Array<Content>, maxDepth: Int = 20, minDepth: Int = 0, naive: Boolean = false,
                         planeRemove: Boolean = false, tr: (String) -> Unit = {}, seeds: List<IntArray> = emptyList(), resetAt: Int = -1,
                         adaptiveR: Double = 0.0, solveFrom: Int = 0): ChainOutcome {
        val seedStab: ((List<Int>) -> List<IntArray>)? = if (seeds.isEmpty()) null else { pre -> stabiliserSample(seeds, pre) }
        val solveFromEnv = System.getenv("SC_SOLVE_FROM")?.toIntOrNull() ?: 0
        val sb = StringBuilder()
        // Plane slice invariant (SliceGroupTest.rootInvariant: cycle types of the net's Latin-square permutations, Aut(G)-
        // invariant, exact orbit partition on 47/47 planes) as an extra fingerprint -- bipartite graphs only, cached per
        // vertex, null when the root's decomposition is not a net (then no filter from it).
        val side0 = g.bipartition()?.first
        // projective planes: frame root rule while it applies (closure-based general position), see frameRoot
        val planeMode = System.getenv("SC_FRAME") != "0" && isProjectivePlane(g)
        // Roots come from peeling G (= dialysis when G is bipartite). 2026-10-02: dialysis of sd(G) also gave no gain on tnn
        // 416/806 (no exact depth within 32 either way: individualisation itself barely splits tnn). 2026-10-01 ablation: taking them from recursive
        // dialysis of sd(G) instead gave the same depth on all 29 instances at equal cost, so that variant was removed.
        val giCache = HashMap<Int, Long?>()
        val globalInv: ((Int) -> Long?)? = if (side0 == null) null else { v -> giCache.getOrPut(v) {
            if (!isNet(g, v)) null else try { sliceTest.rootInvariant(g, v, side0, withSide = false) } catch (e: Exception) { null } } }
        var phase: OrbitPhase? = null; var total = Double.NaN; var ok = false
        val roots = mutableListOf<Int>()
        // two-pass group budget per depth: a short one first (a depth that does not work fails fast and we go deeper),
        // the long one only if no depth was exact under the short budget. Roots are deterministic, so both passes agree.
        // 2026-09-30: DETERMINISTIC depth budget. The two passes are budgets of solver WORK (refinement visits plus
        // search / pair-table steps, see DecompositionCanonicalFormsTest.workBudget), not seconds, so the depth the
        // chain takes is the same on every machine and every run. SC_BUDGET=time restores the old 10 s / 60 s passes.
        val timeBudget = System.getenv("SC_BUDGET") == "time"
        val work1 = System.getenv("SC_WORK1")?.toLongOrNull() ?: DEFAULT_WORK1
        val work2 = System.getenv("SC_WORK2")?.toLongOrNull() ?: DEFAULT_WORK2
        // SC_GROUP_ONLY=1 (2026-10-11, diagnostics): stop at the first depth whose group phase is exact (|Aut(H)| known), with
        // no orbit phase -- measures the exact depth k alone (use with SC_QUERY_MS=1)
        val groupOnly = System.getenv("SC_GROUP_ONLY") == "1"; var groupDone = false
        for ((budgetMs, workBudget) in listOf(10_000L to work1, 60_000L to work2)) {
        if (phase != null || groupDone) break
        roots.clear(); var part = IntArray(g.n) { it }; var generalPos = false
        // remove mode: sibling pieces of the last decomposition of the rest; the next roots are taken one per piece
        // (pp-9-2 minus a vertex = a 91-piece + 9 identical 10-vertex pieces, the pencil lines: recursing into ONE piece
        // gave collinear roots 19..25, one root per piece gives points on different lines = general position)
        var siblings = ArrayDeque<IntArray>()
        sb.appendLine(if (timeBudget) "   group budget ${budgetMs / 1000}s per depth:" else "   group budget ${workBudget} work units per depth:")
        for (k in 0..maxDepth) {
            tr("depth $k: refine, roots=$roots")
            val c = refined(g, col, roots)
            tr("depth $k: OrbitPhase")
            val ph = OrbitPhase(g, col, roots.toList(), k, globalInv, seedStab, resetAt, adaptiveR, seeds.size)
            tr("depth $k: solve (${c.toSet().size} refined classes)")
            val ts = System.currentTimeMillis()
            // SC_RESET_SKIP (2026-10-05): pass 2 does not attempt level solves below solveFrom (pass 1 showed they stop on the
            // budget); roots are still chosen at every depth. Sound: any exact depth gives |Aut|.
            // SC_SOLVE_FROM=k (2026-10-06): attempt level solves only from depth k on (roots are still chosen at every depth);
            // sound: any exact depth gives |Aut|. Used to test "break the base symmetry with roots, then algebra".
            val r = if (k < maxOf(solveFrom, solveFromEnv)) DecompositionCanonicalFormsTest.ParityResult().also { it.status = "SKIPPED" }
                    else if (k < minDepth) solver.parityAutFull(g, asContent(c))
                    else if (timeBudget) solver.parityIsoBatch(g, asContent(c), ph::next, deadlineMs = budgetMs, onGroup = { ph.start(it) })
                    else solver.parityIsoBatch(g, asContent(c), ph::next, deadlineMs = Long.MAX_VALUE, onGroup = { ph.start(it) }, workBudget = workBudget)
            sb.appendLine("   depth $k: roots=$roots refinedClasses=${c.toSet().size} mu=${c.toList().groupingBy { it }.eachCount().values.maxOrNull() ?: 0} singletons=${c.toList().groupingBy { it }.eachCount().values.count { it == 1 }} ours=${r.status} |Aut(H)|=${r.autOrder} maxT=${r.maxT} maxBase=${r.maxBaseLen} groupWork=${solver.groupWork}${if (planeMode) " closure=${planeClosure(g, roots).count { it }}/${g.n}" else ""} (${"%.1f".format((System.currentTimeMillis() - ts) / 1000.0)}s)")
            tr("depth $k: ${r.status} |Aut(H)|=${r.autOrder} maxT=${r.maxT}")
            if (groupOnly && r.autOrder != null) { sb.appendLine("   group-only: exact group phase at depth $k"); groupDone = true; break }
            if (r.status == "EXACT" && r.autOrder != null && k >= minDepth) {
                phase = ph; ok = ph.unknownAt.all { it == 0 }
                total = r.autOrder!!; for (jj in 0 until k) total *= ph.orbitSize[jj]
                for (jj in k - 1 downTo 0) sb.appendLine("   orbit of r$jj=${roots[jj]}: ${ph.orbitSize[jj]} of ${ph.candCount[jj]} candidates, ${ph.testsAt[jj]} two-sided queries, ${ph.fpExcluded[jj]} ruled out by fingerprint${if (ph.nodePruned[jj] > 0) ", ${ph.nodePruned[jj]} nodes pruned by invariant" else ""}${if (ph.cutHist[jj].isNotEmpty()) "; refuted candidates by cut depth ${ph.cutHist[jj]}, ${ph.leafRefuted[jj]} needed a leaf query" else ""}${if (ph.unknownAt[jj] > 0) " (${ph.unknownAt[jj]} unresolved)" else ""}")
                if (ph.refStats.any { it.count > 0 } || ph.witStats.any { it.count > 0 })
                    for (jj in k - 1 downTo 0) sb.appendLine("   search r$jj: refutations ${ph.refStats[jj]}; witnesses ${ph.witStats[jj]}")
                ph.notes.take(3).forEach { sb.appendLine("      note: $it") }
                sb.appendLine("   generators known at the end: ${ph.known.size}; two-sided queries in total: ${ph.testsAt.sum()}")
                break
            }
            if (planeRemove) { while (siblings.isNotEmpty() && siblings.first().any { it in roots }) siblings.removeFirst()
                if (siblings.isNotEmpty()) part = siblings.removeFirst() }
            tr("depth $k: next root")
            val nr = (when (System.getenv("SC_ROOT")) { "lineframe" -> lineFrameRoot(g, c, roots); "pointframe" -> pointFrameRoot(g, c, roots); "random" -> randomRoot(c); else -> null })
                ?: (if (planeMode && generalPos && roots.isNotEmpty()) frameRoot(g, c, roots) else null)
                ?: (if (seedStab != null) knownGroupRoot(g, c, seedStab(roots)) else null)
                ?: nextRoot(g, c, part, generalPos) ?: break
            tr("depth $k: root $nr, decompose part of ${part.size}")
            // decomposition from the new root inside the current part: continue in its largest remainder component
            val (sub, _) = g.induced(part); val local = part.indexOf(nr)
            val d = dialysisPerSpec(sub, if (local >= 0) local else 0)
            generalPos = d.remainderComps.isEmpty()
            part = d.remainderComps.maxByOrNull { it.size }?.let { cc -> IntArray(cc.size) { part[cc[it]] } } ?: part
            if (naive) { part = IntArray(g.n) { it }; generalPos = false }
            else if (planeRemove && generalPos) {   // generalPos = the last decomposition had no remainder
                // trick: drop the individualised roots and decompose the REST OF THE WHOLE GRAPH; its remainder pieces become
                // the sibling list (recomputed only when used up), and the next roots are taken one per sibling piece
                val rest = (0 until g.n).filter { it != nr && it !in roots }.toIntArray()
                if (siblings.isEmpty() && rest.isNotEmpty()) {
                    val (sub3, _) = g.induced(rest); val rc3 = Array(sub3.n) { col[rest[it]] }
                    val d3 = dialysisPerSpec(sub3, defaultRootRule(sub3, rc3))
                    val pieces = d3.remainderComps.map { cc -> IntArray(cc.size) { rest[cc[it]] } }.sortedWith(compareBy<IntArray>({ -it.size }, { it.min() }))
                    if (pieces.size >= 2) siblings = ArrayDeque(pieces)
                }
                part = if (rest.isNotEmpty()) rest else part
                generalPos = false
            }
            roots.add(nr)
        }
        }
        return ChainOutcome(if (phase == null) null else total, ok, sb.toString(), phase?.known?.toList() ?: emptyList())
    }

    /** Johnson graph J(n, k): the k-subsets of {0..n-1}, adjacent iff they share k-1 elements. Vertex ids are a seeded
     *  random permutation of the lexicographic order, so the numbering does not hand the structure to the solver. */
    internal fun johnsonGraph(n: Int, k: Int, seed: Long = 1000L * n + k): Graph {
        val subsets = mutableListOf<Int>()
        for (mask in 0 until (1 shl n)) if (Integer.bitCount(mask) == k) subsets.add(mask)
        val perm = subsets.indices.shuffled(java.util.Random(seed))
        val id = HashMap<Int, Int>(); subsets.forEachIndexed { i, s -> id[s] = perm[i] }
        val adj = Array(subsets.size) { mutableListOf<Int>() }
        for (s in subsets) for (a in 0 until n) if (s and (1 shl a) != 0) for (b in 0 until n) if (s and (1 shl b) == 0)
            adj[id.getValue(s)].add(id.getValue(s xor (1 shl a) or (1 shl b)))
        return Graph(subsets.size, Array(subsets.size) { adj[it].sorted().toIntArray() }, Array(subsets.size) { "$it" })
    }

    /** Writes graphs/johnson/johnson-n-k (DIMACS) for the family sweep: k = 3..6, n from 2k up to about 1,000 vertices.
     *  (k = 2 is the triang family: J(m, 2) = line graph of K_m.) Env JOHNSON_DIR (default graphs/johnson). */
    @Test fun johnsonGenerate() {
        val dir = File(System.getenv("JOHNSON_DIR") ?: "graphs/johnson"); dir.mkdirs()
        val specs = (6..18).map { it to 3 } + (8..14).map { it to 4 } + (10..13).map { it to 5 } + (12..13).map { it to 6 }
        for ((n, k) in specs) {
            val g = johnsonGraph(n, k)
            // no comment line: the series campaign reads the 'p edge' header from the FIRST line
            val sb = StringBuilder("p edge ${g.n} ${g.m}\n")
            for (u in 0 until g.n) for (w in g.adj[u]) if (u < w) sb.append("e ${u + 1} ${w + 1}\n")
            File(dir, "johnson-$n-$k").writeText(sb.toString())
            println("johnson-$n-$k n=${g.n} m=${g.m}")
        }
    }

    /** Small Johnson graphs through the chain, checked against the closed form |Aut(J(n,k))| = n! (x2 when n = 2k) --
     *  no Traces anywhere. */
    @Test fun johnsonChainSmall() {
        for ((n, k) in listOf(6 to 3, 7 to 3, 8 to 3, 8 to 4, 9 to 4)) {
            val g = johnsonGraph(n, k)
            val col = dialysis.refinement.dispatchColouring(g).colouring
            val res = runChain(g, col)
            val want = knownAut("johnson-$n-$k")!!
            println("J($n,$k) n=${g.n}: |Aut| = ${res.total} (formula $want) ok=${res.ok}\n${res.log}")
            // plain check(): throws under JUnit and under scripts/TestMethodRunner (no JUnit on that classpath)
            check(res.total != null && res.ok) { "J($n,$k): no exact depth / unresolved orbit queries" }
            check(Math.abs(res.total!! - want) <= 1e-9 * want) { "J($n,$k): |Aut| = ${res.total}, expected $want" }
        }
    }

    /**
     * Planes, vertex removal (Christos, 2026-09-30): remove ONE random vertex v and run the chain (our solver only) on
     * G - v. Reported per instance: v, |Aut(G - v)| ours vs Traces on G - v; the chain's levels with candidates outside the
     * orbit and its two-sided query total (the cost that blows up on the whole plane); and as a Traces-only oracle
     * |Aut(G)|, the orbit of v and |Aut(G)_v| (for a plane G - v determines G, so Aut(G - v) should be Aut(G)_v).
     * Env RV_FILES, RV_SEED (default 1), SC_MAXDEPTH (default 32), OUT.
     */
    @Test fun removeVertexChain() {
        val files = System.getenv("RV_FILES")?.split(",")?.map { it.trim() }?.filter { it.isNotEmpty() } ?: return
        val seed = (System.getenv("RV_SEED") ?: "1").toLong()
        val maxDepth = (System.getenv("SC_MAXDEPTH") ?: "32").toInt()
        val out = File(System.getenv("OUT") ?: File(System.getProperty("java.io.tmpdir"), "remove_vertex.txt").path)
        for (path in files) {
            val t0 = System.currentTimeMillis()
            val g = GraphIO.loadDimacs(File(path).toPath()); val name = File(path).name
            val v = java.util.Random(seed * 1_000_003L + name.hashCode()).nextInt(g.n)
            val rest = (0 until g.n).filter { it != v }.toIntArray()
            val (h, _) = g.induced(rest)
            val col = dialysis.refinement.dispatchColouring(h).colouring
            val res = runChain(h, col, maxDepth = maxDepth)
            val tChain = (System.currentTimeMillis() - t0) / 1000.0
            val lv = Regex("""orbit of r\d+=\d+: (\d+) of (\d+) candidates, (\d+) two-sided queries""").findAll(res.log).map { it.groupValues.drop(1).map(String::toInt) }.toList()
            val nonOrbit = lv.count { it[0] < it[1] }; val queries = lv.sumOf { it[2] }
            // oracle only
            val hCells = (0 until h.n).groupBy { col[it].serialize() }.toSortedMap().values.map { it.toIntArray() }
            val trH = traces.certifyAll(h, hCells, getcanon = false).stats.autOrder
            val gAll = traces.certifyAll(g, listOf(IntArray(g.n) { it }), getcanon = false)
            val orbV = gAll.orbits.count { it == gAll.orbits[v] }
            val stabV = gAll.stats.autOrder / orbV
            val ours = res.total
            val agree = ours != null && res.ok && Math.abs(ours - trH) <= 1e-9 * maxOf(1.0, trH)
            val line = "== $name n=${g.n} removed v=$v (${if (g.bipartition()?.first?.contains(v) == true) "side 0" else "side 1"})\n" +
                "   ours |Aut(G-v)| = ${ours?.let { "%.6g".format(it) } ?: "NO EXACT DEPTH"}${if (ours != null && !res.ok) " (incomplete)" else ""}  Traces ${"%.6g".format(trH)}  agree=$agree  " +
                "levels=${lv.size} nonOrbitLevels=$nonOrbit queries=$queries  chain ${tChain}s\n" +
                "   oracle: |Aut(G)| = ${"%.6g".format(gAll.stats.autOrder)}, orbit of v = $orbV, |Aut(G)_v| = ${"%.6g".format(stabV)}, Aut(G-v) = Aut(G)_v: ${Math.abs(trH - stabV) <= 1e-9 * maxOf(1.0, stabV)}\n"
            out.appendText(line + res.log.lines().filter { "depth" in it && "EXACT" in it || "orbit of" in it }.joinToString("\n") { "      $it" } + "\n"); print(line)
        }
    }

    /**
     * Local Lenz–Barlotti invariant of a projective plane given as its incidence graph (Christos's option 2, 2026-09-30).
     * For a vertex x, read x's OWN side as the points (so a duality, which swaps the sides, maps x's value to its image's
     * value) and for every line L count the (x, L)-perspectivities: |Γ(x,L)| = 1 + #{A' on xA : the unique map fixing x
     * and every point of L with A -> A' is a collineation}, A a fixed point off L and off x. Value = the sorted multiset of
     * (x on L?, |Γ(x,L)|) over all lines. Everything is defined from incidence alone, so it is Aut(G)-invariant. Returns
     * null if G is not a projective plane (bipartite, both sides n, every two points on exactly one line).
     */
    inner class PlaneLB(val g: Graph) {
        val side0 = g.bipartition()?.first
        private val ok: Boolean
        private val pts = arrayOfNulls<IntArray>(2); private val idx = IntArray(g.n) { -1 }
        private var q = 0; private var np = 0
        private val join = arrayOfNulls<IntArray>(2)   // [side][a*np+b] = line index (in the other side) through points a, b
        init {
            var good = side0 != null
            if (good) {
                val s0 = (0 until g.n).filter { it in side0!! }.toIntArray(); val s1 = (0 until g.n).filter { it !in side0!! }.toIntArray()
                good = s0.size == s1.size
                if (good) { pts[0] = s0; pts[1] = s1; np = s0.size; s0.forEachIndexed { i, v -> idx[v] = i }; s1.forEachIndexed { i, v -> idx[v] = i }
                    q = g.adj[s0[0]].size - 1
                    good = q >= 2 && np == q * q + q + 1 && (0 until g.n).all { g.adj[it].size == q + 1 }
                }
                if (good) for (s in 0..1) {
                    val j = IntArray(np * np) { -1 }
                    for (l in pts[1 - s]!!) { val on = g.adj[l].map { idx[it] }
                        for (a in on) for (b in on) if (a != b) { if (j[a * np + b] != -1) good = false; j[a * np + b] = idx[l] } }
                    join[s] = j
                }
            }
            ok = good
        }
        /** points (indices) on line index l, when side s is the points */
        private fun onLine(s: Int, l: Int) = g.adj[pts[1 - s]!![l]].map { idx[it] }
        private fun linesThrough(s: Int, p: Int) = g.adj[pts[s]!![p]].map { idx[it] }
        fun invariant(x: Int): Long? {
            if (!ok) return null
            val s = if (x in side0!!) 0 else 1; val P = idx[x]; val jn = join[s]!!
            val onL = Array(np) { onLine(s, it).toIntArray() }
            val lineSet = Array(np) { BooleanArray(np).also { b -> for (p in onL[it]) b[p] = true } }
            fun meet(l1: Int, l2: Int): Int { for (p in onL[l1]) if (lineSet[l2][p]) return p; return -1 }
            val sigma = IntArray(np)
            val counts = ArrayList<Long>()
            for (L in 0 until np) {
                val flag = lineSet[L][P]
                val A = (0 until np).first { it != P && !lineSet[L][it] }
                val m = jn[P * np + A]
                val B = (0 until np).first { it != P && !lineSet[L][it] && !lineSet[m][it] }
                var good = 0
                for (A2 in onL[m]) {
                    if (A2 == A || A2 == P || lineSet[L][A2]) continue
                    // sigma: P and the points of L fixed; A -> A2; X off m: sigma(X) = PX meet line(AX meet L, A2); X on m via B
                    java.util.Arrays.fill(sigma, -1); sigma[P] = P; for (p in onL[L]) sigma[p] = p; sigma[A] = A2
                    fun img(X: Int, Y: Int, Y2: Int): Int {   // image of X using a known pair Y -> Y2 (X, Y not collinear with P)
                        val t = meet(jn[X * np + Y], L); val l2 = if (t == Y2) -1 else jn[t * np + Y2]
                        return if (l2 < 0) -1 else meet(jn[P * np + X], l2)
                    }
                    val B2 = img(B, A, A2); if (B2 < 0) continue; sigma[B] = B2
                    var bad = false
                    for (X in 0 until np) { if (sigma[X] >= 0) continue
                        val y = if (lineSet[m][X]) img(X, B, B2) else img(X, A, A2)
                        if (y < 0) { bad = true; break }; sigma[X] = y }
                    if (bad) continue
                    val hit = BooleanArray(np); for (X in 0 until np) { if (hit[sigma[X]]) { bad = true; break }; hit[sigma[X]] = true }
                    if (bad) continue
                    // collineation check: every line maps onto a line
                    for (l in 0 until np) { val on = onL[l]; val a = sigma[on[0]]; val b = sigma[on[1]]; if (a == b) { bad = true; break }
                        val li = jn[a * np + b]; for (k in 2 until on.size) if (!lineSet[li][sigma[on[k]]]) { bad = true; break }
                        if (bad) break }
                    if (!bad) good++
                }
                counts.add((if (flag) 1L shl 32 else 0L) or (good + 1).toLong())
            }
            counts.sort(); var h = 0x4C42L; for (c in counts) h = h * 1000003L xor c
            return h
        }
    }

    /**
     * Separation check for [PlaneLB] at the top level (oracle: Traces orbits of Aut(G), dualities included): per orbit up
     * to 2 representatives; reports whether the invariant is constant on each orbit (soundness spot check) and how many
     * orbits it separates, next to the existing global plane invariant (rootInvariant). Env PL_FILES, OUT.
     */
    @Test fun planeLBDiag() {
        val files = System.getenv("PL_FILES")?.split(",")?.map { it.trim() }?.filter { it.isNotEmpty() } ?: return
        val out = File(System.getenv("OUT") ?: File(System.getProperty("java.io.tmpdir"), "plane_lb.txt").path)
        for (path in files) {
            val t0 = System.currentTimeMillis()
            val g = GraphIO.loadDimacs(File(path).toPath())
            val tr = traces.certifyAll(g, listOf(IntArray(g.n) { it }), getcanon = false)
            val orbits = (0 until g.n).groupBy { tr.orbits[it] }.values.toList()
            val lb = PlaneLB(g); val side0 = lb.side0
            val reps = orbits.map { it.take(2) }
            val lbVal = HashMap<Int, Long?>(); val giVal = HashMap<Int, Long?>()
            val tl = System.currentTimeMillis()
            for (r in reps) for (v in r) lbVal[v] = lb.invariant(v)
            val lbS = (System.currentTimeMillis() - tl) / 1000.0 / reps.sumOf { it.size }
            for (r in reps) for (v in r) giVal[v] = if (side0 != null && isNet(g, v)) try { sliceTest.rootInvariant(g, v, side0, withSide = false) } catch (e: Exception) { null } else null
            fun sep(m: Map<Int, Long?>): String {
                val unsound = reps.count { r -> r.map { m[it] }.toSet().size > 1 }
                val classes = reps.map { m[it[0]] }.toSet().size
                return "sound=${unsound == 0} separates $classes of ${orbits.size} orbits"
            }
            val line = "== ${File(path).name} n=${g.n} |Aut|=${"%.6g".format(tr.stats.autOrder)} orbits=${orbits.size} (sizes ${orbits.map { it.size }.sorted()})\n" +
                "   LB (x,L)-perspectivities: ${sep(lbVal)}  (${"%.2f".format(lbS)} s/vertex)   global plane inv: ${sep(giVal)}   (${(System.currentTimeMillis() - t0) / 1000.0}s)\n"
            out.appendText(line); print(line)
        }
    }

    /** Small hypercubes Q_3..Q_7 through the chain, checked against |Aut(Q_d)| = 2^d d! -- no Traces anywhere.
     *  (The family files are written by scripts/gen_hypercube.py; this test builds the graphs in memory.) */
    @Test fun hypercubeChainSmall() {
        for (d in 3..7) {
            val n = 1 shl d; val perm = (0 until n).shuffled(java.util.Random(1000L * d + 7))
            val adj = Array(n) { mutableListOf<Int>() }
            for (v in 0 until n) for (b in 0 until d) adj[perm[v]].add(perm[v xor (1 shl b)])
            val g = Graph(n, Array(n) { adj[it].sorted().toIntArray() }, Array(n) { "$it" })
            val col = dialysis.refinement.dispatchColouring(g).colouring
            val res = runChain(g, col)
            val want = knownAut("hypercube-$d")!!
            println("Q_$d n=$n: |Aut| = ${res.total} (formula $want) ok=${res.ok}\n${res.log}")
            check(res.total != null && res.ok) { "Q_$d: no exact depth / unresolved orbit queries" }
            check(Math.abs(res.total!! - want) <= 1e-9 * want) { "Q_$d: |Aut| = ${res.total}, expected $want" }
        }
    }

    /** |Aut| known in closed form from the file name: johnson-n-k -> n! (x2 when n = 2k, complementation);
     *  hypercube-d -> 2^d d! (the hyperoctahedral group). */
    private fun knownAut(name: String): Double? {
        Regex("""hypercube-(\d+)""").find(name)?.let { h -> val d = h.groupValues[1].toInt()
            var f = Math.pow(2.0, d.toDouble()); for (i in 2..d) f *= i; return f }
        val m = Regex("""johnson-(\d+)-(\d+)""").find(name) ?: return null
        val n = m.groupValues[1].toInt(); val k = m.groupValues[2].toInt()
        var f = 1.0; for (i in 2..n) f *= i
        return if (2 * k == n) 2 * f else f
    }

    /**
     * SOUNDNESS DIAGNOSTIC for the orbit filters (2026-09-30: the chain gave |Aut| = 42 instead of 98,784 on ag2-7 with
     * 6 fingerprint exclusions and 0 queries). For prefixes [], [0], [0,1]: Traces orbits of (G, PI, prefix individualised)
     * as the oracle; per filter (global plane invariant as used by the chain, relative plane invariant, 2-vertex
     * fingerprint) count the orbits on which the filter takes more than one value -- any such orbit makes the filter
     * unsound (it can exclude a true orbit member). Env ID_FILES, OUT.
     */
    @Test fun invDiag() {
        val files = System.getenv("ID_FILES")?.split(",")?.map { it.trim() }?.filter { it.isNotEmpty() } ?: return
        val out = File(System.getenv("OUT") ?: File(System.getProperty("java.io.tmpdir"), "inv_diag.txt").path)
        for (path in files) {
            val g = GraphIO.loadDimacs(File(path).toPath())
            val col = dialysis.refinement.dispatchColouring(g).colouring
            val side0 = g.bipartition()?.first
            val sb = StringBuilder("== ${File(path).name} n=${g.n}\n")
            val gi = HashMap<Int, Long?>()
            fun globalInv(v: Int): Long? = gi.getOrPut(v) { if (side0 == null || !isNet(g, v)) null else
                try { sliceTest.rootInvariant(g, v, side0, withSide = false) } catch (e: Exception) { null } }
            for (pre in listOf(listOf(), listOf(0), listOf(0, 1))) {
                val c = refined(g, col, pre)
                val cells = (0 until g.n).groupBy { if (it in pre) "p${pre.indexOf(it)}" else "c${c[it]}" }.toSortedMap().values.map { it.toIntArray() }
                val orb = traces.certifyAll(g, cells, getcanon = false).orbits
                fun fp(s: Int): Long { val a = LongArray(g.n) { t -> val x = refined(g, col, pre + s + t); x.sort(); var h = 0x2545F4914F6CDD1DL; for (y in x) h = h * 1000003L xor y; h }; a.sort(); var h = 7L; for (y in a) h = h * 1000003L xor y; return h }
                val filters = listOf<Pair<String, (Int) -> Long?>>("global" to { v -> globalInv(v) }, "relative" to { v -> relPlaneInv(g, c, v) }, "fingerprint" to { v -> fp(v) })
                val verts = (0 until g.n).filter { it !in pre && (0 until g.n).count { u -> c[u] == c[it] } > 1 }
                val orbits = verts.groupBy { orb[it] }.values.filter { it.size > 1 }
                sb.append("   prefix $pre: ${orbits.size} non-trivial orbits")
                for ((name, f) in filters) {
                    val vals = verts.associateWith { f(it) }
                    val nonNull = vals.values.count { it != null }
                    val bad = orbits.count { o -> o.mapNotNull { vals[it] }.toSet().size > 1 }
                    sb.append(" | $name: defined on $nonNull/${verts.size}, splits $bad orbits")
                }
                sb.appendLine()
            }
            out.appendText(sb.toString()); print(sb)
        }
    }

    /**
     * Planes as equations after removing a vertex (Christos, 2026-09-29) -- MEASUREMENT. Point v (vertex 0); the q+1 lines
     * through v split the other points into pencil pieces P_l = N(l) - v. Every non-pencil line meets every piece once (a net),
     * so two pieces are never constrained pairwise; the coupling is ternary (collinearity). Per plane:
     *  - D_l: refinement-consistent maps P_l -> P_m (base inside P_l, image tuples in P_m, colours of (G, v, l, base) vs
     *    (G, v, m, images) compared prefix by prefix) -- sound: every automorphism fixing v gives (sigma l, sigma|P_l).
     *  - identity-target part D_l^id (candidates of Aut_{v,l} on P_l) and, for the first three pencil lines, the triples
     *    (b1, b2, b3) with b3 FORCED by collinearity from (b1, b2), kept if well defined and in D_3^id; group? abelian?
     *  - |Aut_v| by Traces (oracle). Env PL_FILES, OUT.
     */
    @Test fun planePieces() {
        val files = System.getenv("PL_FILES")?.split(",")?.map { it.trim() }?.filter { it.isNotEmpty() } ?: return
        val out = File(System.getenv("OUT") ?: File(System.getProperty("java.io.tmpdir"), "plane_pieces.txt").path)
        for (path in files) {
            val t0 = System.currentTimeMillis()
            val g = GraphIO.loadDimacs(File(path).toPath())
            val col = dialysis.refinement.dispatchColouring(g).colouring
            val v = 0
            val pencil = g.adj[v].sorted()
            val piece = pencil.associateWith { l -> g.adj[l].filter { it != v }.sorted() }
            val q = piece.values.first().size
            val pos = IntArray(g.n) { -1 }; for ((_, pts) in piece) pts.forEachIndexed { i, p -> pos[p] = i }
            val lineOf = IntArray(g.n) { -1 }; for ((l, pts) in piece) for (p in pts) lineOf[p] = l
            // candidate maps P_l -> P_m: base = (v, l, points of P_l until P_l is discrete), images (v, m, ...)
            fun domain(l: Int, m: Int): List<IntArray> {
                val src = piece.getValue(l); val dst = piece.getValue(m)
                val base = mutableListOf(v, l)
                val prefCol = ArrayList<LongArray>()
                while (true) {
                    val c = refined(g, col, base); val on = LongArray(q) { c[src[it]] }; prefCol.add(on)
                    val blocks = src.indices.groupBy { on[it] }.values.filter { it.size > 1 }
                    if (blocks.isEmpty() || base.size > 8) break
                    base.add(src[blocks.first().min()])
                }
                val sortedPref = prefCol.map { it.sorted() }
                val outL = mutableListOf<IntArray>()
                fun dfs(img: MutableList<Int>) {
                    val d = img.size - 2
                    val c = refined(g, col, img); val on = LongArray(q) { c[dst[it]] }
                    if (on.sorted() != sortedPref[d]) return
                    if (d == prefCol.size - 1) {
                        val where = HashMap<Long, Int>(); on.forEachIndexed { i, x -> where[x] = i }
                        if (where.size == q) outL.add(IntArray(q) { i -> where.getValue(prefCol[d][i]) }); return
                    }
                    val want = prefCol[d][pos[base[d + 2]]]
                    for (i in 0 until q) if (on[i] == want && dst[i] !in img) { img.add(dst[i]); dfs(img); img.removeAt(img.size - 1) }
                }
                dfs(mutableListOf(v, m))
                return outL
            }
            val dom = pencil.associateWith { l -> pencil.associateWith { m -> domain(l, m) } }
            val sizes = pencil.map { l -> dom.getValue(l).values.sumOf { it.size } }
            val idSizes = pencil.map { l -> dom.getValue(l).getValue(l).size }
            // triple coupling on the first three pencil lines (identity targets)
            val (l1, l2, l3) = Triple(pencil[0], pencil[1], pencil[2])
            val adjSet = Array(g.n) { g.adj[it].toHashSet() }
            fun lineThrough(a: Int, b: Int) = g.adj[a].first { it in adjSet[b] && it != v && it !in pencil }
            fun meet(t: Int, l: Int) = g.adj[t].first { lineOf[it] == l }
            val d3 = dom.getValue(l3).getValue(l3).map { it.toList() }.toHashSet()
            val triples = mutableListOf<Triple<IntArray, IntArray, IntArray>>()
            for (b1 in dom.getValue(l1).getValue(l1)) for (b2 in dom.getValue(l2).getValue(l2)) {
                val b3 = IntArray(q) { -1 }; var ok = true
                loop@ for (i in 0 until q) for (j in 0 until q) {
                    val a = piece.getValue(l1)[i]; val b = piece.getValue(l2)[j]
                    val c = meet(lineThrough(a, b), l3)
                    val a2 = piece.getValue(l1)[b1[i]]; val bb2 = piece.getValue(l2)[b2[j]]
                    val c2 = meet(lineThrough(a2, bb2), l3)
                    val ci = pos[c]; val ci2 = pos[c2]
                    if (b3[ci] == -1) b3[ci] = ci2 else if (b3[ci] != ci2) { ok = false; break@loop }
                }
                if (ok && b3.all { it >= 0 } && b3.toList() in d3) triples.add(Triple(b1, b2, b3))
            }
            fun comp(x: IntArray, y: IntArray) = IntArray(q) { x[y[it]] }
            val key = { t: Triple<IntArray, IntArray, IntArray> -> t.first.toList() + t.second.toList() + t.third.toList() }
            val tset = triples.map(key).toHashSet()
            val closed = triples.all { x -> triples.all { y -> key(Triple(comp(x.first, y.first), comp(x.second, y.second), comp(x.third, y.third))) in tset } }
            val abelian = closed && triples.all { x -> triples.all { y -> key(Triple(comp(x.first, y.first), comp(x.second, y.second), comp(x.third, y.third))) ==
                                                                         key(Triple(comp(y.first, x.first), comp(y.second, x.second), comp(y.third, x.third))) } }
            val cells = listOf(intArrayOf(v)) + (0 until g.n).filter { it != v }.groupBy { col[it].serialize() }.toSortedMap().values.map { it.toIntArray() }
            val autV = traces.certifyAll(g, cells, getcanon = false).stats.autOrder
            val line = "== ${File(path).name} q=$q |Aut_v|=${"%.6g".format(autV)}  |D_l| (all targets) min/max ${sizes.min()}/${sizes.max()}  |D_l^id| min/max ${idSizes.min()}/${idSizes.max()}" +
                "  triples(l1,l2,l3)=${triples.size} of |D1^id|*|D2^id|=${idSizes[0] * idSizes[1]}  group=$closed abelian=$abelian  (${(System.currentTimeMillis() - t0) / 1000.0}s)"
            out.appendText(line + "\n"); println(line)
        }
    }

    @Test fun pieceProfile() {
        val files = System.getenv("PP_FILES")?.split(",")?.map { it.trim() }?.filter { it.isNotEmpty() } ?: return
        val out = File(System.getenv("OUT") ?: File(System.getProperty("java.io.tmpdir"), "piece_profile.txt").path)
        for (path in files) {
            val t0 = System.currentTimeMillis()
            val g = GraphIO.loadDimacs(File(path).toPath())
            val col = dialysis.refinement.dispatchColouring(g).colouring
            val piClasses = col.map { it.serialize() }.toSet().size
            val parts = mutableListOf<Part>()
            fun rec(x: IntArray, depth: Int, siblings: Int) {
                val (sub, _) = g.induced(x)
                val rc = Array(sub.n) { col[x[it]] }
                val isTree = sub.n <= 1 || sub.m == sub.n - 1
                if (isTree || colorRefine1WL(sub, rc).isDiscrete()) { parts.add(Part(depth, x, "BASE", x, siblings)); return }
                val r = defaultRootRule(sub, rc)
                val d = dialysisPerSpec(sub, r)
                val piece = (d.treeVerts.map { x[it] } + d.orphans.map { x[it] }).toIntArray()
                parts.add(Part(depth, x, "QUOT", piece, siblings))
                for (c in d.remainderComps) rec(IntArray(c.size) { x[c[it]] }, depth + 1, d.remainderComps.size)
            }
            rec(IntArray(g.n) { it }, 0, 1)
            val sb = StringBuilder()
            sb.appendLine("== ${File(path).name} n=${g.n} m=${g.m} PI classes=$piClasses parts=${parts.size} depth=${parts.maxOf { it.depth }} (${(System.currentTimeMillis() - t0) / 1000.0}s)")
            for ((dep, ps) in parts.groupBy { it.depth }.toSortedMap()) {
                val pieceKeys = ps.map { key(g, it.piece, col) }
                val partKeys = ps.map { key(g, it.verts, col) }
                val pieceOracle = ps.map { oracle(g, it.piece, col) }
                val partOracle = ps.map { oracle(g, it.verts, col) }
                val sizes = ps.map { it.piece.size }.groupingBy { it }.eachCount().toSortedMap()
                val topMult = pieceKeys.groupingBy { it }.eachCount().values.maxOrNull() ?: 0
                sb.appendLine("   depth $dep: parts ${ps.size} (${ps.count { it.kind == "BASE" }} BASE), part sizes ${ps.map { it.verts.size }.groupingBy { it }.eachCount().toSortedMap()}, piece sizes $sizes")
                sb.appendLine("      distinct piece types: ours ${pieceKeys.toSet().size}, oracle ${pieceOracle.toSet().size}; distinct part types: ours ${partKeys.toSet().size}, oracle ${partOracle.toSet().size}; largest multiplicity $topMult")
            }
            out.appendText(sb.toString()); print(sb)
        }
    }
}
