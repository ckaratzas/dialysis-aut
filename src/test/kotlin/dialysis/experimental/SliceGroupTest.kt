package dialysis.experimental

import dialysis.content.serialize
import dialysis.decomposition.dialysisPerSpec
import dialysis.util.GraphIO
import org.junit.jupiter.api.Test
import java.io.File

/**
 * Projective planes (2026-09-27, Christos): does the dialysis SLICE form a group?
 *
 * For each plane and root r, [dialysisPerSpec] gives the tree, the orphans and the slices. Checked, not
 * assumed: no remainder, and every orphan attaches to exactly one vertex of every tree branch (a branch =
 * the attachments below one child of the root), i.e. the slice is a transversal design / net.
 * For branches A, B, C each a in A gives a bijection pi_a: B -> C (b -> the attachment in C of the orphan
 * through a and b). The Latin square is a group isotope iff S = { pi_a pi_a0^-1 } is closed under
 * composition (then S is a regular group on C). S's isomorphism signature (abelian?, element orders) is
 * recorded. Env: PP_DIR, PP_ONLY (names), ROOTS (all | k = first k vertices of each side), TRIPLES
 * (all | fixA = branches 0,1 with every C), OUT (csv).
 */
class SliceGroupTest {

    @Test fun sliceGroupCheck() {
        val dir = File(System.getenv("PP_DIR") ?: "graphs/pp")
        val only = System.getenv("PP_ONLY")?.split(",")?.map { it.trim() }?.filter { it.isNotEmpty() }?.toSet()
        val rootsMode = System.getenv("ROOTS") ?: "all"
        val triplesMode = System.getenv("TRIPLES") ?: "fixA"
        val out = File(System.getenv("OUT") ?: File(System.getProperty("java.io.tmpdir"), "slice_group.csv").path)
        val done = if (out.exists()) out.readLines().drop(1).map { it.split(",")[0] }.toHashSet() else hashSetOf()
        if (!out.exists()) out.writeText("plane,q,roots,roots_side0,roots_no_remainder,roots_one_slice,roots_net,triples,triples_group,roots_all_group,roots_side0_all_group,roots_side1_all_group,group_signatures,signatures_at_group_roots,seconds\n")
        val files = dir.listFiles()!!.filter { it.isFile && (only == null || it.name in only) }
            .sortedWith(compareBy({ it.name.split("-")[1].toInt() }, { it.name.split("-").getOrNull(2)?.toIntOrNull() ?: 0 }))
        for (f in files) {
            if (f.name in done) continue
            val t0 = System.currentTimeMillis()
            val g = GraphIO.loadDimacs(f.toPath())
            val (side0, side1) = g.bipartition() ?: error("${f.name} not bipartite")
            val roots = when (rootsMode) {
                "all" -> (0 until g.n).toList()
                else -> { val k = rootsMode.toInt(); side0.sorted().take(k) + side1.sorted().take(k) }
            }
            var noRem = 0; var oneSlice = 0; var net = 0; var triples = 0L; var triplesGroup = 0L
            var allGroup = 0; var allGroup0 = 0; var allGroup1 = 0; var q = -1
            val sigs = sortedMapOf<String, Int>(); val rootSigs = sortedMapOf<String, Int>()
            for (r in roots) {
                val dec = dialysisPerSpec(g, r)
                if (dec.remainderComps.isNotEmpty()) continue
                noRem++
                if (dec.slices.size == 1) oneSlice++
                // branch of a tree vertex = its ancestor at depth 1
                val branchOf = IntArray(g.n) { -1 }
                val children = dec.treeVerts.filter { dec.depth[it] == 1 }.sorted()
                children.forEachIndexed { i, c -> branchOf[c] = i }
                for (v in dec.treeVerts.sortedBy { dec.depth[it] }) if (dec.depth[v] >= 2) branchOf[v] = branchOf[dec.parent[v]]
                val k = children.size
                val pts = List(k) { b -> dec.treeVerts.filter { branchOf[it] == b && dec.depth[it] >= 2 }.sorted() }
                val qq = pts[0].size
                if (pts.any { it.size != qq } || dec.orphans.size != qq * qq) continue
                val idx = IntArray(g.n) { -1 }; for (p in pts) p.forEachIndexed { i, v -> idx[v] = i }
                // coord[o][b] = index of o's unique attachment in branch b
                val coord = Array(dec.orphans.size) { IntArray(k) { -1 } }
                var isNet = true
                for ((oi, o) in dec.orphans.withIndex()) for (w in g.adj[o]) {
                    val b = branchOf[w]
                    if (b < 0 || dec.depth[w] < 2 || coord[oi][b] != -1) { isNet = false } else coord[oi][b] = idx[w]
                }
                if (!isNet || coord.any { c -> c.any { it < 0 } }) continue
                net++; q = qq
                val allTrip = (0 until k).flatMap { a -> (a + 1 until k).flatMap { b -> (b + 1 until k).map { c -> Triple(a, b, c) } } }
                val fixTrip = (2 until k).map { c -> Triple(0, 1, c) }
                // adaptive: the fixA triples first; only a root passing all of them gets the full check
                var rootAll = true
                fun isGroupTriple(a: Int, b: Int, c: Int): String? {
                    // pi[x][y] = z
                    val pi = Array(qq) { IntArray(qq) { -1 } }
                    for (cd in coord) pi[cd[a]][cd[b]] = cd[c]
                    val inv0 = IntArray(qq); for (y in 0 until qq) inv0[pi[0][y]] = y
                    val s = List(qq) { x -> List(qq) { z -> pi[x][inv0[z]] } }   // s_x = pi_x o pi_0^-1 on C
                    val sset = s.toHashSet()
                    val closed = s.all { u -> s.all { v -> List(qq) { u[v[it]] } in sset } }
                    if (!closed) return null
                    run {
                        val abelian = s.all { u -> s.all { v -> List(qq) { u[v[it]] } == List(qq) { v[u[it]] } } }
                        val id = List(qq) { it }
                        val orders = s.map { u -> var p = u; var o = 1; while (p != id) { p = List(qq) { u[p[it]] }; o++ }; o }.groupingBy { it }.eachCount().toSortedMap()
                        return (if (abelian) "abelian" else "nonabelian") + "[" + orders.entries.joinToString(" ") { "${it.key}:${it.value}" } + "]"
                    }
                }
                val first = if (triplesMode == "adaptive") fixTrip else if (triplesMode == "all") allTrip else fixTrip
                val tested = HashSet<Triple<Int, Int, Int>>(); val here = mutableListOf<String>()
                fun runTriples(ts: List<Triple<Int, Int, Int>>) {
                    for (t in ts) {
                        if (!tested.add(t)) continue
                        triples++
                        val sig = isGroupTriple(t.first, t.second, t.third)
                        if (sig != null) { triplesGroup++; sigs[sig] = (sigs[sig] ?: 0) + 1; here.add(sig) } else rootAll = false
                    }
                }
                runTriples(first)
                if (triplesMode == "adaptive" && rootAll) runTriples(allTrip)
                if (rootAll) { allGroup++; if (r in side0) allGroup0++ else allGroup1++; for (x in here.toSet()) rootSigs[x] = (rootSigs[x] ?: 0) + 1 }
            }
            val sec = (System.currentTimeMillis() - t0) / 1000.0
            val line = "${f.name},$q,${roots.size},${roots.count { it in side0 }},$noRem,$oneSlice,$net,$triples,$triplesGroup,$allGroup,$allGroup0,$allGroup1,\"${sigs.entries.joinToString("; ") { "${it.key}x${it.value}" }}\",\"${rootSigs.entries.joinToString("; ") { "${it.key}@${it.value}roots" }}\",$sec"
            out.appendText(line + "\n")
            println("SLICE $line")
        }
    }

    private fun mix(h: Long, x: Long): Long { var z = h xor (x + -0x61c8864680b583ebL + (h shl 6) + (h ushr 2)); z = (z xor (z ushr 30)) * -0x40a7b892e31b1a47L; z = (z xor (z ushr 27)) * -0x6b2fb644ecceee15L; return z xor (z ushr 31) }
    private fun hashSorted(xs: LongArray): Long { xs.sort(); var h = 0x1234L; for (x in xs) h = mix(h, x); return h }

    /**
     * Per-root SLICE INVARIANT for projective planes (2026-09-27): for every unordered branch triple and each of its
     * 3 choices of row branch X (columns Y, symbols Z), the multiset over row pairs x < x' of the cycle type of
     * R_x^-1 R_x' (a permutation of Y). Unchanged by relabelling columns / symbols (conjugation) and by swapping the
     * roles of Y and Z (inverse / conjugate), so the per-root hash over all triples is independent of vertex numbering,
     * hence Aut-invariant. Compared with the number of Aut orbits. Env INV_FILES, OUT.
     */
    @Test fun sliceInvariantPartition() {
        val files = System.getenv("INV_FILES")?.split(",")?.map { it.trim() } ?: return
        val out = File(System.getenv("OUT") ?: File(System.getProperty("java.io.tmpdir"), "slice_inv.csv").path)
        if (!out.exists()) out.writeText("plane,n,q,invariant_classes,invariant_class_sizes,side_split,seconds\n")
        for (path in files) {
            val t0 = System.currentTimeMillis()
            val g = GraphIO.loadDimacs(File(path).toPath())
            val (side0, _) = g.bipartition()!!
            val inv = LongArray(g.n)
            val threads = System.getenv("INV_THREADS")?.toIntOrNull() ?: 12
            val pool = java.util.concurrent.ForkJoinPool(threads)
            pool.submit { java.util.stream.IntStream.range(0, g.n).parallel().forEach { r -> inv[r] = rootInvariant(g, r, side0) } }.get()
            pool.shutdown()
            System.getenv("COL_DIR")?.let { d -> File(d).mkdirs(); File(d, File(path).name + ".col").writeText(inv.joinToString("\n")) }
            val classes = (0 until g.n).groupBy { inv[it] }.values.map { it.size }.groupingBy { it }.eachCount().toSortedMap()
            val nCls = inv.toSet().size
            val sideSplit = (0 until g.n).groupBy { inv[it] }.values.all { cl -> cl.all { it in side0 } || cl.none { it in side0 } }
            val sec = (System.currentTimeMillis() - t0) / 1000.0
            val line = "${File(path).name},${g.n},${(g.n / 2)},${nCls},\"$classes\",$sideSplit,$sec"
            out.appendText(line + "\n"); println("INV $line")
        }
    }

    /** [withSide] = false drops the point/line side term: then the value is invariant under ALL automorphisms, dualities
     *  included (2026-09-29: with the side term it is invariant only under side-preserving automorphisms, and used as an
     *  orbit fingerprint it halved |Aut| of the self-dual planes pp-9-1 and pp-9-4). */
    internal fun rootInvariant(g: dialysis.graph.Graph, r: Int, side0: Set<Int>, withSide: Boolean = true): Long {
                val dec = dialysisPerSpec(g, r)
                val branchOf = IntArray(g.n) { -1 }
                val children = dec.treeVerts.filter { dec.depth[it] == 1 }.sorted()
                children.forEachIndexed { i, c -> branchOf[c] = i }
                for (v in dec.treeVerts.sortedBy { dec.depth[it] }) if (dec.depth[v] >= 2) branchOf[v] = branchOf[dec.parent[v]]
                val k = children.size
                val pts = List(k) { b -> dec.treeVerts.filter { branchOf[it] == b && dec.depth[it] >= 2 }.sorted() }
                val q = pts[0].size
                val idx = IntArray(g.n) { -1 }; for (p in pts) p.forEachIndexed { i, v -> idx[v] = i }
                val coord = Array(dec.orphans.size) { o -> IntArray(k).also { c -> for (w in g.adj[dec.orphans[o]]) c[branchOf[w]] = idx[w] } }
                val tripleH = LongArray(k * (k - 1) * (k - 2) / 6); var ti = 0
                val R = Array(q) { IntArray(q) }; val Rinv = Array(q) { IntArray(q) }
                val seen = BooleanArray(q); val cyc = IntArray(q); val pairH = LongArray(q * (q - 1) / 2)
                for (a in 0 until k) for (b in a + 1 until k) for (c in b + 1 until k) {
                    val roles = LongArray(3)
                    for ((ri, xyz) in listOf(intArrayOf(a, b, c), intArrayOf(b, a, c), intArrayOf(c, a, b)).withIndex()) {
                        val (X, Y, Z) = Triple(xyz[0], xyz[1], xyz[2])
                        for (cd in coord) { R[cd[X]][cd[Y]] = cd[Z]; Rinv[cd[X]][cd[Z]] = cd[Y] }
                        var pi = 0
                        for (x in 0 until q) for (x2 in x + 1 until q) {
                            java.util.Arrays.fill(seen, false); var nc = 0
                            for (y0 in 0 until q) if (!seen[y0]) { var y = y0; var len = 0; while (!seen[y]) { seen[y] = true; len++; y = Rinv[x][R[x2][y]] }; cyc[nc++] = len }
                            java.util.Arrays.sort(cyc, 0, nc); var h = 77L; for (j in 0 until nc) h = mix(h, cyc[j].toLong()); pairH[pi++] = h
                        }
                        roles[ri] = hashSorted(pairH.copyOf(pi))
                    }
                    tripleH[ti++] = hashSorted(roles)
                }
                return if (withSide) mix(hashSorted(tripleH), if (r in side0) 1L else 2L) else hashSorted(tripleH)
    }

    // ───────────── slice helpers ─────────────
    private val tracesJni by lazy { dialysis.cl.TracesJni() }

    /**
     * Generic slice invariant of root v under colouring [col]: for every slice of dialysisPerSpec(h, v), the Traces
     * canonical certificate of the small coloured "slice graph" (orphans, their attachments, and each attachment's
     * branch = its depth-1 ancestor; edges orphan-attachment and attachment-branch), cells ordered by the invariant
     * key (role, depth, current colour). Depends only on (h, v, col) up to isomorphism -> Aut(h, col)-invariant.
     */
    private fun sliceInvariant(h: dialysis.graph.Graph, v: Int, col: LongArray): Long {
        val d = dialysisPerSpec(h, v)
        val anc = IntArray(h.n) { -1 }
        for (x in d.treeVerts.sortedBy { d.depth[it] }) anc[x] = when { d.depth[x] == 1 -> x; d.depth[x] >= 2 -> anc[d.parent[x]]; else -> -1 }
        val parts = LongArray(d.slices.size)
        for ((si, sl) in d.slices.withIndex()) {
            val orph = sl.orphans.toHashSet(); val att = sl.attachments.toHashSet()
            val verts = LinkedHashSet<Int>(); sl.orphans.forEach { verts.add(it) }; sl.attachments.forEach { verts.add(it) }
            sl.attachments.forEach { if (anc[it] >= 0) verts.add(anc[it]) }
            val list = verts.toIntArray(); val loc = HashMap<Int, Int>(); list.forEachIndexed { i, x -> loc[x] = i }
            val nb = Array(list.size) { java.util.TreeSet<Int>() }
            fun add(a: Int, b: Int) { if (a != b) { nb[a].add(b); nb[b].add(a) } }
            for (o in sl.orphans) for (w in h.adj[o]) if (w in att) add(loc.getValue(o), loc.getValue(w))
            for (a in sl.attachments) if (anc[a] >= 0) add(loc.getValue(a), loc.getValue(anc[a]))
            val g2 = dialysis.graph.Graph(list.size, Array(list.size) { nb[it].toIntArray() }, Array(list.size) { "$it" })
            val key = LongArray(list.size) { i -> val x = list[i]
                val role = (if (x in orph) 1L else 0L) or (if (x in att) 2L else 0L) or (if (anc[x] == x) 4L else 0L)
                mix(mix(role, d.depth[x].toLong()), col[x]) }
            val cellsByKey = list.indices.groupBy { key[it] }.toSortedMap()
            val cells = cellsByKey.values.map { it.toIntArray() }
            val cert = if (list.size <= 1) byteArrayOf(list.size.toByte()) else sliceGraphValue(g2, cells, key)
            var hh = mix(sl.level.toLong(), list.size.toLong()); for (k in cellsByKey.keys) hh = mix(hh, k * 31 + cellsByKey.getValue(k).size)
            for (b in cert) hh = mix(hh, b.toLong())
            parts[si] = hh
        }
        var hr = mix(col[v], hashSorted(parts)); hr = mix(hr, d.remainderComps.size.toLong()); for (c in d.remainderComps.map { it.size }.sorted()) hr = mix(hr, c.toLong())
        return hr
    }

    // ── slice-graph value (2026-09-28, Christos: "slice invariant i mean parity/coset") ──
    // SLICE_INV = traces (default): Traces canonical certificate of the coloured slice graph.
    //             parity: our series parity/coset solver ONLY, in invariant mode (no Traces): EXACT -> hash of |Aut| and
    //                     the multiset of (cell key, orbit size); STOP -> one constant ("unresolved").
    // Both are isomorphism invariants of the coloured slice graph (checked by sliceParityDiag with Traces as the oracle).
    private var sliceInvMode = System.getenv("SLICE_INV") ?: "traces"
    /** Diagnostic sink: when set, every parity-mode slice graph records (Traces cert hash, solver status, value hash, detail). */
    private var diagSink: MutableList<Array<String>>? = null
    private val parity by lazy { DecompositionCanonicalFormsTest() }
    private val sliceInvNodeCap = (System.getenv("SLICE_INV_NODES") ?: "5000").toLong()
    val sliceInvCalls = java.util.concurrent.atomic.AtomicLong(); val sliceInvExact = java.util.concurrent.atomic.AtomicLong()
    val sliceInvStops = java.util.concurrent.ConcurrentHashMap<String, Long>(); val sliceInvNanos = java.util.concurrent.atomic.AtomicLong()

    private fun sliceGraphValue(g2: dialysis.graph.Graph, cells: List<IntArray>, key: LongArray): ByteArray {
        if (sliceInvMode == "traces") return tracesJni.certificate(g2, cells).bytes
        val t0 = System.nanoTime(); sliceInvCalls.incrementAndGet()
        try {
            // Our solver only, no Traces (Christos, 2026-09-28: Traces has no polynomial bound on a slice). The solver runs in
            // invariant mode (parityAutOf), so EXACT vs STOP and the STOP status depend only on the coloured slice graph up to
            // isomorphism. EXACT -> hash(|Aut|, multiset of (colour key, orbit size)); STOP -> one constant.
            val c = wl1(g2, key)
            val r = parity.parityAutOf(g2, Array(g2.n) { dialysis.content.Content.Num(c[it]) }, nodeCap = sliceInvNodeCap)
            diagSink?.add(arrayOf(tracesJni.certificate(g2, cells).bytes.contentHashCode().toString(), r.status, "${r.autOrder}", "${r.orbits}", "${g2.n}", r.stopDetail.take(120)))
            val h: Long
            if (r.status == "EXACT" && r.autOrder != null) {
                sliceInvExact.incrementAndGet()
                val aut = r.autOrder!!
                val autKey = if (aut < 1e15) Math.round(aut) else Math.round(Math.log10(aut) * 1e6) xor Long.MIN_VALUE
                val orb = r.orbitOf
                h = if (orb == null) mix(mix(0xA7L, autKey), -7L) else {
                    val size = HashMap<Int, Int>(); for (x in orb) size[x] = (size[x] ?: 0) + 1
                    mix(mix(0xA7L, autKey), hashSorted(LongArray(g2.n) { mix(key[it], size.getValue(orb[it]).toLong()) }))
                }
            } else {
                sliceInvStops.merge(r.status, 1L, Long::plus)
                // one constant for EVERY stop: whether the solver stops is invariant, but which stop kind it reports first
                // depends on the order the base family is explored in (triang-17: STOP_BASE_FAMILY vs STOP_BASE_TOO_LONG on
                // isomorphic copies gave 26 cells at depth 0 against 2 orbits, 2026-09-29).
                h = 0x57L
            }
            return java.nio.ByteBuffer.allocate(8).putLong(h).array()
        } finally { sliceInvNanos.addAndGet(System.nanoTime() - t0) }
    }

    private fun sliceInvStats() = if (sliceInvMode == "traces") "traces" else
        "$sliceInvMode nodecap=$sliceInvNodeCap calls=${sliceInvCalls.get()} exact=${sliceInvExact.get()} stops=${sliceInvStops} solver_s=${"%.1f".format(sliceInvNanos.get() / 1e9)}"

    private fun classCount(c: LongArray) = c.toSet().size

    private fun wl1(h: dialysis.graph.Graph, c0: LongArray): LongArray {
        var c = c0.copyOf(); var k = classCount(c)
        while (true) {
            val nx = LongArray(h.n) { v -> mix(c[v], hashSorted(LongArray(h.adj[v].size) { c[h.adj[v][it]] })) }
            val k2 = classCount(nx); c = nx; if (k2 == k) return c; k = k2
        }
    }

    /** 1-WL, then repeatedly: new colour = (colour, slice invariant under current colours), 1-WL, until stable. */
    private fun sliceRefine(h: dialysis.graph.Graph, c0: LongArray, maxRounds: Int = 20): LongArray {
        var c = wl1(h, c0); var k = classCount(c)
        repeat(maxRounds) {
            val cc = c
            val size = HashMap<Long, Int>(); for (x in cc) size[x] = (size[x] ?: 0) + 1
            // singletons stay singletons whatever their invariant: skip them (decision depends only on cell sizes)
            val nx = LongArray(h.n) { v -> if (size.getValue(cc[v]) == 1) cc[v] else mix(cc[v], sliceInvariant(h, v, cc)) }
            c = wl1(h, nx); val k2 = classCount(c); if (k2 == k) return c; k = k2
        }
        return c
    }

    /** Fair baseline (2026-09-28): Traces given the SAME PI colouring our solver starts from (cells in PI-colour
     *  serialised order), getcanon=false (group + orbits only, the same task). One instance per JVM: on timeout the
     *  native call cannot be interrupted, so the JVM halts. Env TP_FILE, TP_TIMEOUT_S, TP_UNCOLOURED=1 for no colouring. */
    @Test fun tracesWithPi() {
        val path = System.getenv("TP_FILE") ?: return
        val timeout = (System.getenv("TP_TIMEOUT_S") ?: "300").toLong()
        val g = GraphIO.loadDimacs(File(path).toPath())
        val t0 = System.currentTimeMillis()
        val cells: List<IntArray>
        if (System.getenv("TP_UNCOLOURED") == "1") cells = listOf(IntArray(g.n) { it }) else {
            val col = dialysis.refinement.dispatchColouring(g).colouring
            cells = (0 until g.n).groupBy { col[it].serialize() }.toSortedMap().values.map { it.toIntArray() }
        }
        val tPi = (System.currentTimeMillis() - t0) / 1000.0
        val res = java.util.concurrent.atomic.AtomicReference<String>()
        val th = Thread { val r = tracesJni.certifyAll(g, cells, getcanon = false); res.set("aut=${r.stats.autOrder} orbits=${r.stats.numOrbits} nodes=${r.stats.treeNodes}") }.apply { isDaemon = true }
        val t1 = System.currentTimeMillis(); th.start(); th.join(timeout * 1000)
        val tT = (System.currentTimeMillis() - t1) / 1000.0
        val line = "TP ${File(path).name} colouring=${if (System.getenv("TP_UNCOLOURED") == "1") "none" else "PI"} cells=${cells.size} pi_s=$tPi traces_s=$tT result=${res.get() ?: "TIMEOUT(${timeout}s)"}"
        println(line); File(System.getenv("TP_OUT") ?: "/dev/null").appendText(line + "\n")
        System.out.flush()
        if (res.get() == null) Runtime.getRuntime().halt(0)
    }

    // ───────────── Is the refinement-derived candidate set T_C always a group? (2026-09-28) ─────────────
    private fun parseG6(line: String): dialysis.graph.Graph {
        val n = line[0].code - 63
        val nb = Array(n) { mutableListOf<Int>() }
        var k = 0
        fun bit(idx: Int): Int { val c = line[1 + idx / 6].code - 63; return (c shr (5 - idx % 6)) and 1 }
        for (j in 1 until n) for (i in 0 until j) { if (bit(k) == 1) { nb[i].add(j); nb[j].add(i) }; k++ }
        return dialysis.graph.Graph(n, Array(n) { nb[it].sorted().toIntArray() }, Array(n) { "$it" })
    }

    /** Candidate restrictions to class [c] exactly as the solver builds them (rule 0 base until C discrete, admissible =
     *  same colour multiset on C at every prefix depth), with 1-WL from [chi]. Returns (T, base discretises V?). */
    private class TooMany : RuntimeException()
    private fun candidateSet(h: dialysis.graph.Graph, chi: LongArray, c: IntArray, cap: Int = 20000): Pair<Set<List<Int>>, Boolean> {
        fun ref(tuple: List<Int>): LongArray = wl1(h, LongArray(h.n) { v -> val i = tuple.indexOf(v); if (i >= 0) mix(chi[v], 1000L + i) else chi[v] })
        val pos = HashMap<Int, Int>(); c.forEachIndexed { i, v -> pos[v] = i }
        val base = mutableListOf(c[0]); val refC = mutableListOf<LongArray>()
        while (true) {
            val col = ref(base); refC.add(LongArray(c.size) { col[c[it]] })
            val blocks = c.indices.groupBy { refC.last()[it] }
            if (blocks.values.all { it.size == 1 }) break
            base.add(c[blocks.values.first { it.size > 1 }.min()])
        }
        val discreteV = classCount(ref(base)) == h.n
        val sortedRef = refC.map { it.sorted() }
        val out = HashSet<List<Int>>()
        fun dfs(t: MutableList<Int>) {
            val d = t.size
            if (d > 0) {
                val col = ref(t); val onC = LongArray(c.size) { col[c[it]] }
                if (onC.sorted() != sortedRef[d - 1]) return
                if (d == base.size) { val where = HashMap<Long, Int>(); onC.forEachIndexed { i, x -> where[x] = i }; out.add(List(c.size) { where.getValue(refC.last()[it]) }); if (out.size > cap) throw TooMany(); return }
                val want = refC[d - 1][pos.getValue(base[d])]
                for (i in c.indices) if (onC[i] == want && c[i] !in t) { t.add(c[i]); dfs(t); t.removeAt(t.size - 1) }
            } else for (v in c) { t.add(v); dfs(t); t.removeAt(t.size - 1) }
        }
        dfs(mutableListOf())
        return out to discreteV
    }

    /** T is a group iff the group generated by a greedy generating set S of T equals T (BFS closure by right
     *  multiplication with S, aborted as soon as it leaves T). O(|T| |S| n). */
    private fun isGroupFast(t: Set<List<Int>>, n: Int): Boolean {
        val id = List(n) { it }
        if (id !in t) return false
        fun comp(x: List<Int>, y: List<Int>) = List(n) { x[y[it]] }
        val gens = mutableListOf<List<Int>>(); var k = hashSetOf(id)
        for (x in t) if (x !in k) {
            gens.add(x)
            val cl = hashSetOf(id); val q = ArrayDeque(listOf(id))
            while (q.isNotEmpty()) { val y = q.removeFirst(); for (g in gens) { val z = comp(y, g); if (z !in t) return false; if (cl.add(z)) q.add(z) } }
            k = cl
        }
        return k.size == t.size
    }

    // ───────────── Survey (2026-09-28): measure for "slices needed" + sliceIR on every family ─────────────
    private class SirResult(val status: String, val aut: Double, val baseLen: Int, val gens: Int, val refinements: Int)

    /** The [sliceIR] algorithm as a function, with a deadline (throws on timeout -> status STOP_TIME). */
    private fun sliceIRSolve(h: dialysis.graph.Graph, deadline: Long, chi: LongArray? = null): SirResult {
        var refinements = 0
        class Timeout : RuntimeException()
        fun refine(tuple: List<Int>): LongArray {
            if (System.currentTimeMillis() > deadline) throw Timeout()
            refinements++
            return sliceRefine(h, LongArray(h.n) { v -> val i = tuple.indexOf(v); val c0 = chi?.get(v) ?: 0L; if (i >= 0) mix(c0, 1000L + i) else c0 })
        }
        try {
            val base = mutableListOf<Int>(); val P = mutableListOf(refine(emptyList()))
            while (classCount(P.last()) < h.n) {
                val cells = (0 until h.n).groupBy { P.last()[it] }.values.filter { it.size > 1 }
                base.add(cells.maxBy { it.size }.min()); P.add(refine(base))
            }
            val L = base.size
            val sortedP = P.map { it.sorted() }
            fun isAut(sig: IntArray) = (0 until h.n).all { u -> h.adj[u].all { x -> java.util.Arrays.binarySearch(h.adj[sig[u]], sig[x]) >= 0 } }
            val leafRef = P[L]
            fun extendsTo(tuple: List<Int>): IntArray? {
                val d = tuple.size - 1
                val c = refine(tuple)
                if (c.sorted() != sortedP[d + 1]) return null
                if (d + 1 == L) {
                    val where = HashMap<Long, Int>(); for (v in 0 until h.n) where[c[v]] = v
                    val sig = IntArray(h.n) { v -> where[leafRef[v]] ?: return null }
                    return if (isAut(sig)) sig else null
                }
                val want = P[d + 1][base[d + 1]]
                for (u in 0 until h.n) if (c[u] == want) { val r = extendsTo(tuple + u); if (r != null) return r }
                return null
            }
            val gens = mutableListOf<IntArray>(); val orbitSizes = IntArray(L)
            for (d in L - 1 downTo 0) {
                fun orbitOf(x: Int): Set<Int> {
                    val gs = gens.filter { g -> (0 until d).all { g[base[it]] == base[it] } }
                    val seen = hashSetOf(x); val q = ArrayDeque(listOf(x))
                    while (q.isNotEmpty()) { val y = q.removeFirst(); for (g in gs) if (seen.add(g[y])) q.add(g[y]) }
                    return seen
                }
                val want = P[d][base[d]]
                var orbit = orbitOf(base[d])
                for (w in (0 until h.n).filter { P[d][it] == want }) if (w !in orbit) {
                    val sig = extendsTo(base.subList(0, d) + w)
                    if (sig != null) { gens.add(sig); orbit = orbitOf(base[d]) }
                }
                orbitSizes[d] = orbit.size
            }
            return SirResult("EXACT", orbitSizes.fold(1.0) { a, b -> a * b }, L, gens.size, refinements)
        } catch (e: Timeout) { return SirResult("STOP_TIME", Double.NaN, -1, -1, refinements) }
    }

    /** Baseline |Aut| and #orbits via a SEPARATE dreadnaut process (Traces mode), killed on timeout. An in-JVM timed
     *  Traces call cannot be stopped and later ran concurrently with slice-refinement Traces calls -> native SIGSEGV
     *  (2026-09-28); a subprocess never overlaps them. */
    private fun tracesTimed(h: dialysis.graph.Graph, cells: List<IntArray>, timeoutS: Long): Pair<Double, Int>? {
        val sb = StringBuilder("At -a -m n=${h.n} g\n")
        for (v in 0 until h.n) { sb.append(h.adj[v].filter { it > v }.joinToString(" ")); sb.append(if (v < h.n - 1) ";\n" else ".\n") }
        if (cells.size > 1) sb.append("f=[" + cells.joinToString("|") { c -> c.joinToString(",") } + "]\n")
        sb.append("x q\n")
        val pb = ProcessBuilder("dreadnaut").redirectErrorStream(true)
        val pr = pb.start()
        val outText = StringBuilder()
        val rd = Thread { pr.inputStream.bufferedReader().forEachLine { outText.appendLine(it) } }.apply { isDaemon = true; start() }
        try { pr.outputStream.bufferedWriter().use { it.write(sb.toString()) } } catch (e: java.io.IOException) { }
        if (!pr.waitFor(timeoutS, java.util.concurrent.TimeUnit.SECONDS)) { pr.destroyForcibly(); pr.waitFor(); return null }
        rd.join(2000)
        val m = Regex("(\\d+) orbits?; grpsize=([0-9.e+]+)").find(outText.toString()) ?: return null
        return m.groupValues[2].toDouble() to m.groupValues[1].toInt()
    }

    /** Base colouring "PI where it pays": 1-WL refinement of PI(h) . At least as fine as both PI and plain 1-WL; Aut-invariant. */
    private fun piBase(h: dialysis.graph.Graph): LongArray {
        val pi = dialysis.refinement.dispatchColouring(h).colouring
        val seed = LongArray(h.n) { mix(0x51L, pi[it].serialize().hashCode().toLong() * 1_000_003L + pi[it].serialize().length) }
        return wl1(h, seed)
    }

}
