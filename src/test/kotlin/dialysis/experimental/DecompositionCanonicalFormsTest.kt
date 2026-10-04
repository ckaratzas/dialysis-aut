package dialysis.experimental

import dialysis.Utils
import dialysis.cl.TracesJni
import dialysis.content.Content
import dialysis.content.serialize
import dialysis.decomposition.dialysisPerSpec
import dialysis.graph.Graph
import dialysis.refinement.colorRefine1WL
import dialysis.refinement.dispatchColouring
import dialysis.util.GraphIO
import org.junit.jupiter.api.Test
import java.io.File

/**
 * Christos's playground utility (2026-09-25): walks the SAME recursion as [dialysis.decomposition.peel]
 * (same BASE stop rule, same [dialysisPerSpec], same root rule) but keeps each call's LEVEL and
 * CONNECTOR edges, then computes Traces canonical forms of:
 *
 * 1. every piece -- the induced subgraph `G[piece]` (QUOTIENT: tree + orphans; BASE pieces are
 *    reported too, marked BASE);
 * 2. per recursion level, the CONNECTOR GRAPH: all connector edges of every call at that level
 *    (each an edge between that call's QUOTIENT tree and one of its remainder components), on just
 *    their endpoint vertices. Its colouring always separates the two roles (tree side = cell 0,
 *    remainder side = cell 1).
 *
 * Per form it prints n, m, |Aut| and #orbits (from the same Traces search), an 8-hex hash of the
 * Traces certificate (equal hash <=> isomorphic, up to hash collision), and the canonical adjacency
 * itself: row i = the canonical positions adjacent to canonical position i.
 *
 * Knobs to play with: [COLOUR_BY_PI] (colour piece vertices / connector endpoints by their PI colour,
 * cells in PI-colour value order, on top of the role split for connectors) and each test's
 * `forcedRoot`. TEMPORARY diagnostic, per this repo's convention.
 */
class DecompositionCanonicalFormsTest {

    private val COLOUR_BY_PI = false

    private val traces = TracesJni()

    private class Call(
        val id: Int,
        val level: Int,
        val parentCall: Int?,
        val vertices: IntArray,
        val kind: String,
        val root: Int?,
        val treeVerts: IntArray,
        val orphans: IntArray,
        /** (tree vertex, remainder vertex), ORIGINAL ids. */
        val connectors: List<Pair<Int, Int>>,
        /** The restricted-PI colour class the root was picked from (ORIGINAL ids): for the default
         *  rule the smallest class of this call's subgraph, for a forced root that root's own class.
         *  Empty for BASE pieces. */
        val candidateClass: IntArray = IntArray(0),
        /** "forced" or "default" (smallest class, least index); "-" for BASE. */
        val rootRule: String = "-",
        /** How many restricted-PI classes of this call's subgraph share the SMALLEST size -- when > 1
         *  the default rule's choice among them is by first appearance (vertex order), NOT canonical,
         *  even if [candidateClass] itself is a singleton. */
        val tiedSmallestClasses: Int = 0,
    )

    /** Mirrors [dialysis.decomposition.peel] step for step, recording level/parent/connectors. */
    private fun decompose(
        g: Graph,
        x: IntArray,
        colouring: Array<Content>,
        rootRule: (Graph, Array<Content>) -> Int,
        level: Int,
        parentCall: Int?,
        out: MutableList<Call>,
    ) {
        val (sub, _) = g.induced(x)
        val newToOld = x
        val restricted = Array(sub.n) { colouring[newToOld[it]] }
        val isTreeSub = sub.n <= 1 || sub.m == sub.n - 1
        if (isTreeSub || colorRefine1WL(sub, restricted).isDiscrete()) {
            out.add(Call(out.size, level, parentCall, x.copyOf(), "BASE", null, IntArray(0), IntArray(0), emptyList()))
            return
        }
        val localRoot = rootRule(sub, restricted)
        val candidateClass = (0 until sub.n).filter { restricted[it] == restricted[localRoot] }.map { newToOld[it] }.toIntArray()
        val ruleLabel = if (localRoot == dialysis.decomposition.defaultRootRule(sub, restricted)) "default" else "forced"
        val classSizes = (0 until sub.n).groupingBy { restricted[it] }.eachCount().values
        val tied = classSizes.count { it == classSizes.min() }
        val dec = dialysisPerSpec(sub, localRoot)
        val tree = IntArray(dec.treeVerts.size) { newToOld[dec.treeVerts[it]] }
        val orphans = IntArray(dec.orphans.size) { newToOld[dec.orphans[it]] }
        val connectors = dec.connectorEdges.map { (t, r) -> newToOld[t] to newToOld[r] }
        val id = out.size
        out.add(Call(id, level, parentCall, tree + orphans, "QUOTIENT", newToOld[localRoot], tree, orphans, connectors, candidateClass, ruleLabel, tied))
        for (comp in dec.remainderComps) {
            decompose(g, IntArray(comp.size) { newToOld[comp[it]] }, colouring, rootRule, level + 1, id, out)
        }
    }

    private class Form(val n: Int, val m: Int, val autOrder: Double, val orbits: Int, val hash: String, val adjacency: List<List<Int>>, val cert: dialysis.cl.Certificate,
        /** Traces canonical labelling: lab[pos] = local vertex at canonical position pos. */
        val lab: IntArray = IntArray(0))

    /** Traces canonical form of [h] under [cells] (must be in a canonical order already). */
    private fun canonicalForm(h: Graph, cells: List<IntArray>): Form {
        if (h.n <= 1) return Form(h.n, 0, 1.0, h.n, "trivial-${h.n}", List(h.n) { emptyList() }, dialysis.cl.Certificate(byteArrayOf(h.n.toByte())))
        val res = traces.certifyAll(h, cells)
        val lab = res.canonicalLabeling
        val posOf = IntArray(h.n)
        lab.forEachIndexed { pos, v -> posOf[v] = pos }
        // Rows are canonical positions; each row lists canonical positions -- ordering Traces'
        // canonical indices is exactly what makes this a FORM (independent of input numbering).
        val adjacency = List(h.n) { pos -> h.adj[lab[pos]].map { posOf[it] }.sorted() }
        val certificate = traces.certificate(h, cells)
        val digest = java.security.MessageDigest.getInstance("SHA-256").digest(certificate.bytes)
        val hash = digest.take(4).joinToString("") { "%02x".format(it) }
        val orbits = res.orbits.toSet().size
        return Form(h.n, h.m, res.stats.autOrder, orbits, hash, adjacency, certificate, lab)
    }

    /** Cells for vertices of [h] ([origOf] = original id per local id): one cell, or PI colour classes
     *  in PI-colour VALUE order (canonical), optionally after an outer role split. */
    private fun cellsFor(h: Graph, origOf: IntArray, baseline: Array<Content>, role: IntArray? = null): List<IntArray> {
        val keyOf: (Int) -> Pair<Int, Content?> = { v -> (role?.get(v) ?: 0) to (if (COLOUR_BY_PI) baseline[origOf[v]] else null) }
        val groups = (0 until h.n).groupBy(keyOf)
        val ordered = groups.keys.sortedWith(compareBy<Pair<Int, Content?>> { it.first }.thenComparator { a, b ->
            val ca = a.second; val cb = b.second
            if (ca == null || cb == null) 0 else ca.compareTo(cb)
        })
        return ordered.map { groups.getValue(it).toIntArray() }
    }

    /**
     * GLUED form of a QUOTIENT piece (Christos, 2026-09-25): the piece's own vertices plus the
     * remainder-side endpoints of its connectors; edges = G's edges inside the piece + the connector
     * edges (remainder-internal edges, even between two endpoints, are NOT included). Traces cells are
     * the roles in fixed order: 0 = tree, 1 = orphan, 2 = remainder endpoint (split further by PI
     * colour if [COLOUR_BY_PI]). This is what separates r2-0068 roots 32 vs 33, whose piece and
     * connector-graph forms are identical.
     */
    private fun gluedForm(g: Graph, c: Call, baseline: Array<Content>): Form? {
        if (c.kind != "QUOTIENT") return null
        val endpoints = LinkedHashSet<Int>()
        for ((_, r) in c.connectors) endpoints.add(r)
        val origOf = c.vertices + endpoints.toIntArray()
        val local = HashMap<Int, Int>().apply { origOf.forEachIndexed { i, v -> put(v, i) } }
        val inPiece = c.vertices.toHashSet()
        val buckets = Array(origOf.size) { mutableListOf<Int>() }
        for (u in c.vertices) for (w in g.adj[u]) if (w in inPiece) buckets[local.getValue(u)].add(local.getValue(w))
        for ((t, r) in c.connectors) {
            val a = local.getValue(t); val b = local.getValue(r)
            buckets[a].add(b); buckets[b].add(a)
        }
        val h = Graph(origOf.size, Array(origOf.size) { buckets[it].distinct().sorted().toIntArray() }, Array(origOf.size) { origOf[it].toString() })
        val treeSet = c.treeVerts.toHashSet()
        val role = IntArray(h.n) { i -> val v = origOf[i]; if (v in treeSet) 0 else if (v in inPiece) 1 else 2 }
        return canonicalForm(h, cellsFor(h, origOf, baseline, role))
    }

    private class PieceResult(val call: Call, val form: Form, val glued: Form?)

    private fun printForm(indent: String, f: Form) {
        println("${indent}n=${f.n} m=${f.m} |Aut|=${"%.6g".format(f.autOrder)} orbits=${f.orbits} cert=${f.hash}")
        println("${indent}canonical adjacency: " + f.adjacency.withIndex().joinToString("  ") { (i, row) -> "$i:$row" })
    }

    private fun run(path: String, forcedRoot: Int? = null) {
        val g = GraphIO.loadDimacs(File(path).toPath())
        val baseline = dispatchColouring(g).colouring
        val rootRule = dialysis.viz.topLevelForcedRootRule(forcedRoot, g.n)
        val calls = mutableListOf<Call>()
        decompose(g, IntArray(g.n) { it }, baseline, rootRule, 0, null, calls)

        println("==== $path (top-level root=${forcedRoot ?: "default"}, COLOUR_BY_PI=$COLOUR_BY_PI) -- Traces canonical forms ====")
        println("n=${g.n} m=${g.m} pieces=${calls.size} levels=${calls.maxOf { it.level } + 1}")

        println("--- PIECES (recursion order) ---")
        val pieceForms = mutableListOf<PieceResult>()
        for (c in calls) {
            val (h, _) = g.induced(c.vertices)
            val f = canonicalForm(h, cellsFor(h, c.vertices, baseline))
            val gl = gluedForm(g, c, baseline)
            pieceForms.add(PieceResult(c, f, gl))
            val shape = if (c.kind == "QUOTIENT") " root=${c.root} (${c.rootRule}) candidate class=${c.candidateClass.toList()} (tied smallest classes: ${c.tiedSmallestClasses}) tree=${c.treeVerts.size} orphans=${c.orphans.size} connectors=${c.connectors.size}" else ""
            println("piece #${c.id} level=${c.level} parent=${c.parentCall ?: "-"} ${c.kind} |V|=${c.vertices.size}$shape")
            println("   vertices: ${c.vertices.toList()}")
            printForm("   ", f)
            if (gl != null) {
                println("   GLUED piece + connectors (cells: tree | orphan | remainder endpoint; ${c.connectors.map { it.second }.toSet().size} endpoints):")
                printForm("      ", gl)
            }
        }

        printSortedPieceForms(pieceForms)

        println("--- CONNECTOR GRAPH PER LEVEL (cell 0 = QUOTIENT-tree side, cell 1 = remainder side) ---")
        for (level in 0..calls.maxOf { it.level }) {
            val edges = calls.filter { it.level == level }.flatMap { it.connectors }
            if (edges.isEmpty()) {
                println("level $level: no connector edges")
                continue
            }
            val endpoints = LinkedHashSet<Int>()
            for ((t, r) in edges) { endpoints.add(t); endpoints.add(r) }
            val origOf = endpoints.toIntArray()
            val local = HashMap<Int, Int>().apply { origOf.forEachIndexed { i, v -> put(v, i) } }
            val buckets = Array(origOf.size) { mutableListOf<Int>() }
            for ((t, r) in edges) {
                val a = local.getValue(t); val b = local.getValue(r)
                buckets[a].add(b); buckets[b].add(a)
            }
            val h = Graph(origOf.size, Array(origOf.size) { buckets[it].distinct().sorted().toIntArray() }, Array(origOf.size) { origOf[it].toString() })
            val treeSide = edges.map { it.first }.toSet()
            val role = IntArray(h.n) { if (origOf[it] in treeSide) 0 else 1 }
            val f = canonicalForm(h, cellsFor(h, origOf, baseline, role))
            val callsHere = calls.filter { it.level == level && it.connectors.isNotEmpty() }.map { "#${it.id}" }
            println("level $level: from QUOTIENT piece(s) ${callsHere.joinToString(",")}; tree-side ${treeSide.size}, remainder-side ${h.n - treeSide.size} endpoints")
            println("   edges (original ids, tree-remainder): ${edges.joinToString(" ") { (t, r) -> "$t-$r" }}")
            printForm("   ", f)
        }
        println("========================================================")
    }

    /** Pieces sorted by Traces certificate (byte-lexicographic [dialysis.cl.Certificate] order --
     *  a pure function of the canonical form, so the order is comparable across roots). Pieces with
     *  the same form are merged into one row with a multiplicity. */
    private fun printSortedPieceForms(pieceForms: List<PieceResult>) {
        println("--- PIECES SORTED BY CANONICAL FORM (certificate order) ---")
        println(String.format("%-10s %4s %4s %5s %12s %6s %-9s %s", "cert", "n", "m", "mult", "|Aut|", "orbits", "kind", "pieces (#id@level root(rule) in candidate class, glued cert)"))
        for ((_, group) in pieceForms.groupBy { it.form.hash }.entries.sortedWith { a, b -> a.value[0].form.cert.compareTo(b.value[0].form.cert) }) {
            val f = group[0].form
            println(String.format("%-10s %4d %4d %5d %12s %6d %-9s %s", f.hash, f.n, f.m, group.size, "%.6g".format(f.autOrder), f.orbits,
                group.map { it.call.kind }.toSet().joinToString(","), group.joinToString("  ") { describe(it) }))
        }
    }

    private fun describe(p: PieceResult): String {
        val c = p.call
        return if (c.kind == "QUOTIENT") "#${c.id}@L${c.level} root=${c.root}(${c.rootRule}) in ${c.candidateClass.toList()} [tied=${c.tiedSmallestClasses}] glued=${p.glued!!.hash}" else "#${c.id}@L${c.level}"
    }

    /** Piece forms for one top-level root, uncoloured/coloured per [COLOUR_BY_PI]. */
    private fun pieceFormsFor(g: Graph, baseline: Array<Content>, forcedRoot: Int?): List<PieceResult> {
        val calls = mutableListOf<Call>()
        decompose(g, IntArray(g.n) { it }, baseline, dialysis.viz.topLevelForcedRootRule(forcedRoot, g.n), 0, null, calls)
        return calls.map { c -> val (h, _) = g.induced(c.vertices); PieceResult(c, canonicalForm(h, cellsFor(h, c.vertices, baseline)), gluedForm(g, c, baseline)) }
    }

    /**
     * Side-by-side comparison across top-level roots: one row per distinct piece form (sorted by
     * certificate), one column per root giving how many pieces of that form the root's decomposition
     * has. `*` marks a form that does NOT appear with the same multiplicity under every root.
     */
    private fun compareRoots(path: String, roots: List<Int?>) {
        val g = GraphIO.loadDimacs(File(path).toPath())
        val baseline = dispatchColouring(g).colouring
        val perRoot = roots.map { it to pieceFormsFor(g, baseline, it) }
        val rootName: (Int?) -> String = { it?.toString() ?: "default" }

        println("==== $path -- piece canonical forms across top-level roots ${roots.map(rootName)} (COLOUR_BY_PI=$COLOUR_BY_PI) ====")
        fun table(title: String, formOf: (PieceResult) -> Form?) {
            val formByHash = LinkedHashMap<String, Form>()
            for ((_, pf) in perRoot) for (p in pf) formOf(p)?.let { formByHash.putIfAbsent(it.hash, it) }
            val sorted = formByHash.values.sortedWith { a, b -> a.cert.compareTo(b.cert) }
            println("--- $title ---")
            val header = StringBuilder(String.format("%-1s %-10s %4s %4s %12s", "", "cert", "n", "m", "|Aut|"))
            for (r in roots) header.append(String.format(" %9s", "root=" + rootName(r)))
            println(header)
            for (f in sorted) {
                val counts = perRoot.map { (_, pf) -> pf.count { formOf(it)?.hash == f.hash } }
                val row = StringBuilder(String.format("%-1s %-10s %4d %4d %12s", if (counts.toSet().size > 1) "*" else "", f.hash, f.n, f.m, "%.6g".format(f.autOrder)))
                for (cnt in counts) row.append(String.format(" %9s", if (cnt == 0) "-" else cnt.toString()))
                println(row)
            }
        }
        table("PIECE forms (induced G[piece], uncoloured unless COLOUR_BY_PI)") { it.form }
        table("GLUED forms (QUOTIENT piece + connector edges; cells tree | orphan | remainder endpoint)") { it.glued }
        for ((r, pf) in perRoot) {
            println("root=${rootName(r)}: ${pf.size} pieces, level-0 piece cert=${pf[0].form.hash}, level-0 glued cert=${pf[0].glued?.hash ?: "-"}")
            for (p in pf) {
                if (p.call.kind != "QUOTIENT") continue
                println("   ${p.form.hash} ${describe(p)}")
            }
        }
        println("========================================================")
    }

    @Test fun r2_0068_compareRoots() = compareRoots("graphs/cfi-rigid-r2/cfi-rigid-r2-0068-03-1", listOf(11, 48, 51, 54, null))
    @Test fun r2_0068_compareRoots_32_33() = compareRoots("graphs/cfi-rigid-r2/cfi-rigid-r2-0068-03-1", listOf(32, 33, 0, 63))

    /**
     * Verification (Christos, 2026-09-25): are the level-0 pieces for top-level roots 11 and 48 on
     * r2-0068 really non-isomorphic? The level-0 piece depends only on (G, root) -- [dialysisPerSpec]
     * makes no tie-break -- so if 11 and 48 were in one Aut(G) orbit the two pieces would HAVE to be
     * isomorphic. Checks: (a) the cells handed to Traces are one uncoloured cell; (b) basic invariants;
     * (c) Traces certificate is stable under 5 random relabellings of each piece (usage sanity);
     * (d) Traces orbits of the WHOLE uncoloured G: are 11 and 48 orbit-mates?; (e) dumps both pieces
     * as edge lists for an independent check outside Traces (networkx VF2).
     */
    @Test
    fun r2_0068_verifyRoot11VsRoot48() {
        val g = GraphIO.loadDimacs(File("graphs/cfi-rigid-r2/cfi-rigid-r2-0068-03-1").toPath())
        val baseline = dispatchColouring(g).colouring
        val outDir = File(System.getProperty("java.io.tmpdir"), "dialysis-verify-11-48").apply { mkdirs() }
        val certs = HashMap<Int, String>()
        for (root in listOf(11, 48)) {
            val calls = mutableListOf<Call>()
            decompose(g, IntArray(g.n) { it }, baseline, dialysis.viz.topLevelForcedRootRule(root, g.n), 0, null, calls)
            val first = calls[0]
            check(first.level == 0 && first.root == root)
            val (h, _) = g.induced(first.vertices)
            val cells = cellsFor(h, first.vertices, baseline)
            val f = canonicalForm(h, cells)
            certs[root] = f.hash
            println("root=$root: first piece |V|=${h.n} m=${h.m} tree=${first.treeVerts.size} orphans=${first.orphans.size} cells handed to Traces=${cells.size} (sizes ${cells.map { it.size }})")
            println("   degree sequence: ${(0 until h.n).map { h.adj[it].size }.sorted()}")
            println("   cert=${f.hash} |Aut|=${f.autOrder} orbits=${f.orbits}")
            val relabelCerts = (1..5).map { seed ->
                val perm = (0 until h.n).shuffled(kotlin.random.Random(seed)).toIntArray()
                val hp = h.relabeled(perm)
                canonicalForm(hp, listOf(IntArray(hp.n) { it })).hash
            }
            println("   cert under 5 random relabellings: $relabelCerts -> all equal original: ${relabelCerts.all { it == f.hash }}")
            File(outDir, "root$root.edges").printWriter().use { w ->
                for (u in 0 until h.n) for (v in h.adj[u]) if (u < v) w.println("$u $v")
            }
            File(outDir, "root$root.n").writeText(h.n.toString())
        }
        println("certs equal: ${certs[11] == certs[48]}")
        val whole = traces.certifyAll(g, listOf(IntArray(g.n) { it }), getcanon = false)
        println("whole G uncoloured: |Aut|=${whole.stats.autOrder} orbits=${whole.stats.numOrbits}; orbit(11)=${whole.orbits[11]} orbit(48)=${whole.orbits[48]} -> same orbit: ${whole.orbits[11] == whole.orbits[48]}")
        println("orbit of 11: ${(0 until g.n).filter { whole.orbits[it] == whole.orbits[11] }}; orbit of 48: ${(0 until g.n).filter { whole.orbits[it] == whole.orbits[48] }}")
        println("edge lists written to $outDir")
    }

    /**
     * Trace why two top-level roots [a], [b] give identical piece / connector / glued forms although
     * they may not be Aut(G) orbit-mates (Christos, 2026-09-25, r2-0144 roots 20 vs 49):
     * (1) Traces orbits of uncoloured G, and certificates of G with the root individualised;
     * (2) per call id, which vertices differ between the two decompositions;
     * (3) CUMULATIVE structure up to level k: all pieces of level <= k (in-piece edges) + connector
     *     edges of level <= k with their endpoints; cells by (level, role) in value order, roles:
     *     root (optional) < tree < orphan < BASE < endpoint-only. Since in-piece edges + connectors
     *     are all of G's edges, the deepest k is G itself with its decomposition marked -- with the
     *     root marked, equality there would mean an automorphism mapping a -> b.
     */
    private fun traceRoots(path: String, a: Int, b: Int) {
        val g = GraphIO.loadDimacs(File(path).toPath())
        val baseline = dispatchColouring(g).colouring
        println("==== $path -- trace roots $a vs $b ====")
        val whole = traces.certifyAll(g, listOf(IntArray(g.n) { it }), getcanon = false)
        println("uncoloured G: |Aut|=${"%.6g".format(whole.stats.autOrder)} orbits=${whole.stats.numOrbits}; orbit($a)==orbit($b): ${whole.orbits[a] == whole.orbits[b]}")
        val indiv = { r: Int -> canonicalForm(g, listOf(intArrayOf(r), (0 until g.n).filter { it != r }.toIntArray())).hash }
        println("cert(G, $a individualised)=${indiv(a)}  cert(G, $b individualised)=${indiv(b)}")

        val calls = listOf(a, b).map { r -> mutableListOf<Call>().also { decompose(g, IntArray(g.n) { it }, baseline, dialysis.viz.topLevelForcedRootRule(r, g.n), 0, null, it) } }
        println("--- per call id: vertex differences (root $a vs root $b) ---")
        for (i in 0 until maxOf(calls[0].size, calls[1].size)) {
            val ca = calls[0].getOrNull(i); val cb = calls[1].getOrNull(i)
            if (ca == null || cb == null) { println("#$i exists only for root ${if (ca == null) b else a}"); continue }
            val va = ca.vertices.toSet(); val vb = cb.vertices.toSet()
            val ta = ca.treeVerts.toSet(); val tb = cb.treeVerts.toSet()
            val same = va == vb && ta == tb && ca.connectors.toSet() == cb.connectors.toSet()
            println("#$i L${ca.level}/L${cb.level} ${ca.kind}/${cb.kind}: " + if (same) "IDENTICAL (vertices, tree, connectors)" else
                "only-$a ${(va - vb).sorted()} only-$b ${(vb - va).sorted()}; tree only-$a ${(ta - tb).sorted()} only-$b ${(tb - ta).sorted()}; connectors only-$a ${(ca.connectors.toSet() - cb.connectors.toSet())} only-$b ${(cb.connectors.toSet() - ca.connectors.toSet())}")
        }

        println("--- cumulative structure up to level k: cert(root $a) vs cert(root $b) ---")
        val maxLevel = calls.maxOf { cs -> cs.maxOf { it.level } }
        for (k in 0..maxLevel) {
            for (markRoot in listOf(false, true)) {
                val certs = calls.mapIndexed { idx, cs -> cumulativeForm(g, cs, k, if (markRoot) listOf(a, b)[idx] else null) }
                println("k=$k root marked=$markRoot: ${certs[0].hash} vs ${certs[1].hash} (n=${certs[0].n}/${certs[1].n} m=${certs[0].m}/${certs[1].m}) -> ${if (certs[0].hash == certs[1].hash) "SAME" else "DIFFERENT"}")
            }
        }
        println("========================================================")
    }

    private fun cumulativeForm(g: Graph, calls: List<Call>, k: Int, root: Int?): Form {
        val key = HashMap<Int, Pair<Int, Int>>()   // vertex -> (level, role)
        val edges = mutableListOf<Pair<Int, Int>>()
        for (c in calls.filter { it.level <= k }) {
            val tree = c.treeVerts.toHashSet()
            val inPiece = c.vertices.toHashSet()
            for (v in c.vertices) key[v] = c.level to (if (c.kind == "BASE") 3 else if (v in tree) 1 else 2)
            for (u in c.vertices) for (w in g.adj[u]) if (w in inPiece && u < w) edges.add(u to w)
            edges.addAll(c.connectors)
        }
        for ((_, r) in edges) if (r !in key) key[r] = Int.MAX_VALUE to 4
        if (root != null) key[root] = -1 to 0
        val origOf = key.keys.toIntArray()
        val local = HashMap<Int, Int>().apply { origOf.forEachIndexed { i, v -> put(v, i) } }
        val buckets = Array(origOf.size) { mutableListOf<Int>() }
        for ((u, w) in edges) { val x = local.getValue(u); val y = local.getValue(w); buckets[x].add(y); buckets[y].add(x) }
        val h = Graph(origOf.size, Array(origOf.size) { buckets[it].distinct().sorted().toIntArray() }, Array(origOf.size) { origOf[it].toString() })
        val groups = (0 until h.n).groupBy { key.getValue(origOf[it]) }
        val cells = groups.keys.sortedWith(compareBy({ it.first }, { it.second })).map { groups.getValue(it).toIntArray() }
        return canonicalForm(h, cells)
    }

    @Test fun r2_0144_traceRoots_20_49() = traceRoots("graphs/cfi-rigid-r2/cfi-rigid-r2-0144-01-1", 20, 49)
    /** A cumulative structure together with what is needed to read an isomorphism off its form. */
    private class Cumulative(val form: Form, val origOf: IntArray, val key: Map<Int, Pair<Int, Int>>, val edges: Set<Pair<Int, Int>>)

    /** Same construction as [cumulativeForm] (pieces with [include] true: in-piece edges + their
     *  connectors; cells by (level, role) in value order; optional root cell), keeping the pieces. */
    private fun cumulative(g: Graph, calls: List<Call>, include: (Call) -> Boolean, root: Int?, dropConnector: (Int, Int) -> Boolean = { _, _ -> false }): Cumulative {
        val key = HashMap<Int, Pair<Int, Int>>()
        val edges = LinkedHashSet<Pair<Int, Int>>()
        for (c in calls.filter(include)) {
            val tree = c.treeVerts.toHashSet()
            val inPiece = c.vertices.toHashSet()
            for (v in c.vertices) key[v] = c.level to (if (c.kind == "BASE") 3 else if (v in tree) 1 else 2)
            for (u in c.vertices) for (w in g.adj[u]) if (w in inPiece && u < w) edges.add(u to w)
            for ((t, r) in c.connectors) if (!dropConnector(t, r)) edges.add(minOf(t, r) to maxOf(t, r))
        }
        for ((u, w) in edges) { if (u !in key) key[u] = Int.MAX_VALUE to 4; if (w !in key) key[w] = Int.MAX_VALUE to 4 }
        if (root != null) key[root] = -1 to 0
        val origOf = key.keys.toIntArray()
        val local = HashMap<Int, Int>().apply { origOf.forEachIndexed { i, v -> put(v, i) } }
        val buckets = Array(origOf.size) { mutableListOf<Int>() }
        for ((u, w) in edges) { val x = local.getValue(u); val y = local.getValue(w); buckets[x].add(y); buckets[y].add(x) }
        val h = Graph(origOf.size, Array(origOf.size) { buckets[it].distinct().sorted().toIntArray() }, Array(origOf.size) { origOf[it].toString() })
        val groups = (0 until h.n).groupBy { key.getValue(origOf[it]) }
        val cells = groups.keys.sortedWith(compareBy({ it.first }, { it.second })).map { groups.getValue(it).toIntArray() }
        return Cumulative(canonicalForm(h, cells), origOf, key, edges)
    }

    private val roleName = mapOf(0 to "root", 1 to "tree", 2 to "orphan", 3 to "BASE", 4 to "endpoint")
    private fun keyName(k: Pair<Int, Int>?) = if (k == null) "absent" else if (k.second == 4) "endpoint" else if (k.second == 0) "root" else "L${k.first}-${roleName[k.second]}"

    /**
     * Smart search for the level where the decompositions from roots [a] and [b] stop being
     * isomorphic (Christos, 2026-09-25).
     *
     * MONOTONE: the structure up to level k is recoverable from the one up to k+1 (keep the vertices
     * coloured with levels <= k and their incident edges, recolour the far ends as endpoints; colours
     * are literal level numbers), so any colour-preserving isomorphism at k+1 restricts to one at k:
     * SAME(k+1) => SAME(k). Hence binary search, ~log2(levels) Traces calls per root, instead of a
     * linear scan. Root is always marked (cell of its own).
     *
     * Then: (a) CULPRIT pieces -- structure up to k*-1 plus ONE level-k* piece at a time (matched by
     * call id); (b) WITNESS -- the explicit isomorphism phi at k*-1 read off Traces' canonical
     * labellings (phi(labA[p]) = labB[p]); which vertices it moves, and which level-k* roles/edges it
     * fails to carry over. phi is ONE isomorphism among possibly many; Traces' DIFFERENT at k* says
     * every one of them fails, the listed failures are just this one's.
     */
    private fun findInconsistentLevel(path: String, a: Int, b: Int, crossCheckLinear: Boolean = false): Int? {
        val g = loadForTrace(path)
        val baseline = dispatchColouring(g).colouring
        val calls = listOf(a, b).map { r -> mutableListOf<Call>().also { decompose(g, IntArray(g.n) { it }, baseline, dialysis.viz.topLevelForcedRootRule(r, g.n), 0, null, it) } }
        val roots = listOf(a, b)
        val maxLevel = calls.maxOf { cs -> cs.maxOf { it.level } }
        var tracesCalls = 0
        val cache = HashMap<Int, Boolean>()
        fun same(k: Int): Boolean = cache.getOrPut(k) {
            val (ca, cb) = (0..1).map { cumulative(g, calls[it], { c -> c.level <= k }, roots[it]) }
            tracesCalls += 2
            ca.form.hash == cb.form.hash
        }

        println("==== $path -- inconsistency level, roots $a vs $b (levels 0..$maxLevel) ====")
        if (same(maxLevel)) {
            println("SAME up to the deepest level $maxLevel with the root marked: the two rooted decompositions are isomorphic (so $a, $b are orbit-mates). Traces calls: $tracesCalls")
            println("========================================================")
            return null
        }
        var lo = 0; var hi = maxLevel          // invariant: DIFFERENT at hi; answer in [lo, hi]
        while (lo < hi) {
            val mid = (lo + hi) / 2
            if (same(mid)) lo = mid + 1 else hi = mid
        }
        val kStar = lo
        println("first inconsistent level k* = $kStar (binary search, levels probed: ${cache.keys.sorted()}, Traces calls: $tracesCalls vs ${2 * (maxLevel + 1)} for a linear scan)")
        if (crossCheckLinear) {
            val linear = (0..maxLevel).first { !same(it) }
            println("linear cross-check: first DIFFERENT level = $linear -> ${if (linear == kStar) "agrees" else "DISAGREES"}")
        }
        if (kStar == 0) {
            println("differs already at level 0 (the root's own piece + connectors): nothing above it to extend")
            println("========================================================")
            return 0
        }

        println("--- culprit pieces: structure up to level ${kStar - 1} + ONE level-$kStar piece ---")
        val idsAtK = calls[0].filter { it.level == kStar }.map { it.id }
        for (id in idsAtK) {
            val cb = calls[1].getOrNull(id)
            if (cb == null || cb.level != kStar) { println("#$id: no matching level-$kStar call with the same id under root $b"); continue }
            val (ca2, cb2) = (0..1).map { cumulative(g, calls[it], { c -> c.level < kStar || c.id == id }, roots[it]) }
            val ca = calls[0][id]
            println("#$id ${ca.kind} |V|=${ca.vertices.size} connectors=${ca.connectors.size}: ${if (ca2.form.hash == cb2.form.hash) "SAME (extends)" else "DIFFERENT <- culprit"}")
        }

        println("--- witness: isomorphism phi at level ${kStar - 1} (root $a structure -> root $b structure) ---")
        val (pa, pb) = (0..1).map { cumulative(g, calls[it], { c -> c.level < kStar }, roots[it]) }
        check(pa.form.hash == pb.form.hash) { "level ${kStar - 1} should be SAME" }
        val phi = HashMap<Int, Int>()
        for (pos in pa.form.lab.indices) phi[pa.origOf[pa.form.lab[pos]]] = pb.origOf[pb.form.lab[pos]]
        val badEdges = pa.edges.count { (u, w) -> val x = phi.getValue(u); val y = phi.getValue(w); (minOf(x, y) to maxOf(x, y)) !in pb.edges }
        val moved = phi.entries.filter { it.key != it.value }.sortedBy { it.key }
        println("phi is a valid isomorphism at level ${kStar - 1}: ${badEdges == 0 && phi.all { (u, v) -> pa.key[u] == pb.key[v] }} (edges not preserved: $badEdges)")
        println("phi moves ${moved.size} of ${phi.size} vertices: " + moved.joinToString(" ") { "${it.key}->${it.value}" })

        val (fa, fb) = (0..1).map { cumulative(g, calls[it], { c -> c.level <= kStar }, roots[it]) }
        val roleFail = phi.entries.filter { (u, v) -> fa.key[u] != fb.key[v] }
        println("at level $kStar, phi breaks ${roleFail.size} role(s): " + roleFail.joinToString(" ") { (u, v) -> "$u[${keyName(fa.key[u])}]->$v[${keyName(fb.key[v])}]" })
        val edgeFail = fa.edges.filter { (u, w) -> u in phi && w in phi }.filter { (u, w) -> val x = phi.getValue(u); val y = phi.getValue(w); (minOf(x, y) to maxOf(x, y)) !in fb.edges }
        println("at level $kStar, phi breaks ${edgeFail.size} edge(s) between already-mapped vertices: " + edgeFail.joinToString(" ") { (u, w) -> "$u-$w -> ${phi[u]}-${phi[w]}" })
        println("========================================================")
        return kStar
    }

    /** True iff [peel] would stop at [x] with a BASE piece (tree-shaped or 1-WL-discrete). */
    private fun isBaseComponent(g: Graph, x: IntArray, colouring: Array<Content>): Boolean {
        val (sub, _) = g.induced(x)
        return sub.n <= 1 || sub.m == sub.n - 1 || colorRefine1WL(sub, Array(sub.n) { colouring[x[it]] }).isDiscrete()
    }

    /** ONE [peel] step on component [x] with the given ORIGINAL-id [root] (ignored for a BASE
     *  component): the call it produces + its remainder components (ORIGINAL ids). */
    private fun step(g: Graph, x: IntArray, colouring: Array<Content>, root: Int?, level: Int, parentCall: Int?, id: Int): Pair<Call, List<IntArray>> {
        if (root == null || isBaseComponent(g, x, colouring)) {
            return Call(id, level, parentCall, x.copyOf(), "BASE", null, IntArray(0), IntArray(0), emptyList()) to emptyList()
        }
        val (sub, _) = g.induced(x)
        val localOf = HashMap<Int, Int>().apply { x.forEachIndexed { i, v -> put(v, i) } }
        val restricted = Array(sub.n) { colouring[x[it]] }
        val localRoot = localOf.getValue(root)
        val dec = dialysisPerSpec(sub, localRoot)
        val tree = IntArray(dec.treeVerts.size) { x[dec.treeVerts[it]] }
        val orphans = IntArray(dec.orphans.size) { x[dec.orphans[it]] }
        val connectors = dec.connectorEdges.map { (t, r) -> x[t] to x[r] }
        val candidateClass = (0 until sub.n).filter { restricted[it] == restricted[localRoot] }.map { x[it] }.toIntArray()
        val rule = if (localRoot == dialysis.decomposition.defaultRootRule(sub, restricted)) "default" else "guided"
        val classSizes = (0 until sub.n).groupingBy { restricted[it] }.eachCount().values
        val tied = classSizes.count { it == classSizes.min() }
        val call = Call(id, level, parentCall, tree + orphans, "QUOTIENT", root, tree, orphans, connectors, candidateClass, rule, tied)
        return call to dec.remainderComps.map { comp -> IntArray(comp.size) { x[comp[it]] } }
    }

    /** The vertices the default rule could legitimately pick in [x]: every vertex of every
     *  restricted-PI class of the SMALLEST size (the rule's only non-canonical part is choosing
     *  among these by vertex order). */
    private fun legitimateRoots(g: Graph, x: IntArray, colouring: Array<Content>): List<Int> {
        val byColour = x.toList().groupBy { colouring[it] }
        val minSize = byColour.values.minOf { it.size }
        return byColour.values.filter { it.size == minSize }.flatten()
    }

    /**
     * phi-GUIDED decomposition (Christos, 2026-09-25). Root [a]'s decomposition is the ordinary one
     * ([decompose], default rule). Root [b]'s is rebuilt LEVEL BY LEVEL so that it stays isomorphic to
     * [a]'s: for each of [a]'s level-L calls (in call order) it tries unmatched level-L remainder
     * components on [b]'s side and, for each, root candidates in tiers --
     *   tier 1: legitimate default-rule choices ([legitimateRoots]) with the same PI colour as [a]'s root,
     *   tier 2: other legitimate choices,
     *   tier 3 (only if [allowOutsideRule]): any vertex of the component --
     * accepting the first (component, root) for which the cumulative structure (everything < L, the
     * already-matched level-L pieces, and this piece; cells by level/role, top root marked) has the
     * SAME Traces form as [a]'s. BASE components have no root to choose.
     *
     * If every level matches, the deepest structure is G itself with the root marked, so SAME there
     * PROVES an automorphism mapping a -> b. If some level-L call has no matching (component, root),
     * the inconsistency is structural w.r.t. the tried candidates, not a tie-break artefact. Greedy:
     * a choice accepted early is never revisited.
     */
    private class BudgetExhausted(msg: String) : RuntimeException(msg)
    /** Base colouring PI of G: [dialysis.refinement.initialPhase] on G itself, for every graph. */
    internal fun piProjected(g: Graph): Array<Content> {
        return dialysis.refinement.initialPhase(g, dialysis.refinement.uniformSeed(g.n)).color
    }

    /** A budget or structural stop raised deep inside the series solver, with a precise reason. */
    private class StopReason(val status: String, val detail: String) : RuntimeException(detail)

    /**
     * [aIn]/[bIn] null = auto-pick: a = the default rule's top-level root, b = another member of its
     * level-0 candidate class. Budget: at most [maxTracesCalls] cumulative-structure Traces calls and
     * [deadlineMs] wall-clock ms for the guided search; exhausting either stops with a partial report.
     */
    private fun guidedDecomposition(path: String, aIn: Int?, bIn: Int?, allowOutsideRule: Boolean = true,
                                    maxTracesCalls: Int = Int.MAX_VALUE, deadlineMs: Long = Long.MAX_VALUE) {
        val t0 = System.currentTimeMillis()
        val elapsed = { "${(System.currentTimeMillis() - t0) / 1000.0}s" }
        val g = loadForTrace(path)
        println("[${elapsed()}] loaded $path n=${g.n} m=${g.m}")
        val baseline = dispatchColouring(g).colouring
        println("[${elapsed()}] PI colouring: ${baseline.toHashSet().size} classes")
        val a: Int; val b: Int
        if (aIn == null || bIn == null) {
            val (sub, _) = g.induced(IntArray(g.n) { it })
            a = aIn ?: dialysis.decomposition.defaultRootRule(sub, baseline)
            b = bIn ?: (0 until g.n).first { it != a && baseline[it] == baseline[a] }
            println("auto-picked roots: a=$a (default rule), b=$b (same level-0 candidate class, size ${(0 until g.n).count { baseline[it] == baseline[a] }})")
        } else { a = aIn; b = bIn }
        val callsA = mutableListOf<Call>().also { decompose(g, IntArray(g.n) { it }, baseline, dialysis.viz.topLevelForcedRootRule(a, g.n), 0, null, it) }
        val maxLevel = callsA.maxOf { it.level }
        println("[${elapsed()}] root $a decomposition: ${callsA.size} pieces, levels 0..$maxLevel")
        var tracesCalls = 0
        val deadline = if (deadlineMs == Long.MAX_VALUE) Long.MAX_VALUE else System.currentTimeMillis() + deadlineMs
        fun hash(calls: List<Call>, include: (Call) -> Boolean, root: Int): String {
            if (tracesCalls >= maxTracesCalls) throw BudgetExhausted("Traces-call budget $maxTracesCalls used up")
            if (System.currentTimeMillis() > deadline) throw BudgetExhausted("deadline ${deadlineMs}ms passed")
            tracesCalls++
            return cumulative(g, calls, include, root).form.hash
        }
        try {
            guidedSearch(g, baseline, callsA, maxLevel, a, b, allowOutsideRule, ::hash, elapsed) { tracesCalls }
        } catch (e: BudgetExhausted) {
            println("[${elapsed()}] BUDGET EXHAUSTED: ${e.message} -- partial result above (Traces calls: $tracesCalls)")
            println("========================================================")
        }
    }

    private fun guidedSearch(g: Graph, baseline: Array<Content>, callsA: List<Call>, maxLevel: Int, a: Int, b: Int, allowOutsideRule: Boolean,
                             hash: (List<Call>, (Call) -> Boolean, Int) -> String, elapsed: () -> String, tracesCallsNow: () -> Int) {
        println("==== phi-GUIDED decomposition: root $a (default rule) vs root $b (guided), levels 0..$maxLevel ====")
        val callsB = mutableListOf<Call>()
        val (c0, comps0) = step(g, IntArray(g.n) { it }, baseline, b, 0, null, 0)
        callsB.add(c0)
        var pending = comps0.map { c0.id to it }
        val sameAt0 = hash(callsA, { it.level == 0 }, a) == hash(callsB, { it.level == 0 }, b)
        println("level 0: forced roots $a / $b -> ${if (sameAt0) "SAME" else "DIFFERENT"}")
        if (!sameAt0) { println("fails at level 0 already (nothing to guide)"); println("========================================================"); return }

        var overrides = 0; var outsideRule = 0
        for (level in 1..maxLevel) {
            val aCalls = callsA.filter { it.level == level }
            if (aCalls.size != pending.size) {
                println("level $level: STRUCTURAL MISMATCH -- root $a has ${aCalls.size} calls, root $b has ${pending.size} components")
                println("========================================================"); return
            }
            val doneA = HashSet<Int>()
            val unmatched = pending.toMutableList()
            val next = mutableListOf<Pair<Int, IntArray>>()
            for (ca in aCalls) {
                val tA = hash(callsA, { it.level < level || it.id in doneA || it.id == ca.id }, a)
                val rootPi = ca.root?.let { baseline[it] }
                var accepted: Triple<Pair<Int, IntArray>, Pair<Call, List<IntArray>>, Int>? = null
                search@ for (pc in unmatched) {
                    val comp = pc.second
                    val base = isBaseComponent(g, comp, baseline)
                    if (base != (ca.kind == "BASE")) continue
                    val tiers: List<Pair<Int, List<Int?>>> = if (base) listOf(1 to listOf(null)) else {
                        val legit = legitimateRoots(g, comp, baseline)
                        val t1 = legit.filter { baseline[it] == rootPi }
                        val t2 = legit.filter { baseline[it] != rootPi }
                        val t3 = if (allowOutsideRule) comp.filter { it !in legit.toHashSet() } else emptyList()
                        listOf(1 to t1, 2 to t2, 3 to t3)
                    }
                    for ((tier, cands) in tiers) for (r in cands) {
                        val attempt = step(g, comp, baseline, r, level, pc.first, callsB.size)
                        val trial = callsB + attempt.first
                        // callsB holds only levels <= level, and at this level only already-matched pieces
                        if (hash(trial, { it.level <= level }, b) == tA) {
                            accepted = Triple(pc, attempt, tier); break@search
                        }
                    }
                }
                if (accepted == null) {
                    println("level $level: NO (component, root) on root $b's side matches root $a's call #${ca.id} (${ca.kind} |V|=${ca.vertices.size} root=${ca.root}) -> STRUCTURAL inconsistency at level $level")
                    println("   tried ${unmatched.size} unmatched component(s), sizes ${unmatched.map { it.second.size }}; Traces calls so far: ${tracesCallsNow()}")
                    println("========================================================"); return
                }
                val (pc, attempt, tier) = accepted
                unmatched.remove(pc)
                val cb = attempt.first
                callsB.add(cb)
                for (comp in attempt.second) next.add(cb.id to comp)
                doneA.add(ca.id)
                if (cb.kind == "QUOTIENT") {
                    val (sub, _) = g.induced(pc.second)
                    val defaultRoot = pc.second[dialysis.decomposition.defaultRootRule(sub, Array(sub.n) { baseline[pc.second[it]] })]
                    if (cb.root != defaultRoot) overrides++
                    if (tier == 3) outsideRule++
                    println("[${elapsed()}] level $level: A #${ca.id} root=${ca.root} <-> B #${cb.id} root=${cb.root} (default rule would pick $defaultRoot${if (cb.root != defaultRoot) ", OVERRIDDEN" else ""}; tier $tier${if (tier == 3) " = OUTSIDE the rule's choices" else ""}) |V|=${cb.vertices.size}")
                } else {
                    println("[${elapsed()}] level $level: A #${ca.id} BASE <-> B #${cb.id} BASE |V|=${cb.vertices.size}")
                }
            }
            pending = next
        }
        val finalSame = hash(callsA, { true }, a) == hash(callsB, { true }, b)
        println("--- all $maxLevel levels matched; deepest structure (= all of G, root marked) SAME: $finalSame")
        println("root overrides vs default rule: $overrides; choices outside the rule: $outsideRule; Traces calls: ${tracesCallsNow()}")
        if (finalSame) {
            val orbits = traces.certifyAll(g, listOf(IntArray(g.n) { it }), getcanon = false).orbits
            println("=> proves an automorphism mapping $a -> $b; Traces orbit check: orbit($a)==orbit($b): ${orbits[a] == orbits[b]}")
        }
        println("========================================================")
    }

    /**
     * Levels [lo]..[hi] only (Christos, 2026-09-25: r2-3600 roots 4 vs 371, where the guided run had
     * matched levels 0..46 with NO overrides, so root [b]'s default decomposition is the guided one
     * there). (1) per level in range: multiset of piece forms and of glued forms, [a] vs [b];
     * (2) cumulative: probe [hi] (= all of G with root marked when hi is the deepest level); if
     * DIFFERENT, binary search in [lo, hi] for the first non-isomorphic level, TAKING level lo-1 as
     * SAME (from the guided run -- stated in the output, not re-checked). Deadline-bounded.
     */
    private fun checkLevelRange(path: String, a: Int, b: Int, lo: Int, hi: Int, deadlineMs: Long) {
        val t0 = System.currentTimeMillis()
        val elapsed = { "${(System.currentTimeMillis() - t0) / 1000.0}s" }
        val g = GraphIO.loadDimacs(File(path).toPath())
        val baseline = dispatchColouring(g).colouring
        val calls = listOf(a, b).map { r -> mutableListOf<Call>().also { decompose(g, IntArray(g.n) { it }, baseline, dialysis.viz.topLevelForcedRootRule(r, g.n), 0, null, it) } }
        println("==== $path -- levels $lo..$hi, roots $a vs $b (depths: ${calls[0].maxOf { it.level }} / ${calls[1].maxOf { it.level }}) ====")
        println("[${elapsed()}] decompositions: ${calls[0].size} / ${calls[1].size} pieces")

        println("--- (1) per level: piece forms and glued forms as multisets ---")
        var levelMismatches = 0
        for (level in lo..hi) {
            val (pa, pb) = calls.map { cs -> cs.filter { it.level == level } }
            val formsA = pa.map { c -> val (h, _) = g.induced(c.vertices); canonicalForm(h, cellsFor(h, c.vertices, baseline)).hash }.groupingBy { it }.eachCount()
            val formsB = pb.map { c -> val (h, _) = g.induced(c.vertices); canonicalForm(h, cellsFor(h, c.vertices, baseline)).hash }.groupingBy { it }.eachCount()
            val gluedA = pa.mapNotNull { gluedForm(g, it, baseline)?.hash }.groupingBy { it }.eachCount()
            val gluedB = pb.mapNotNull { gluedForm(g, it, baseline)?.hash }.groupingBy { it }.eachCount()
            val ok = formsA == formsB && gluedA == gluedB
            if (!ok) levelMismatches++
            println("level $level: pieces ${pa.size}/${pb.size}, piece forms ${if (formsA == formsB) "equal" else "DIFFER $formsA vs $formsB"}, glued forms ${if (gluedA == gluedB) "equal" else "DIFFER $gluedA vs $gluedB"}")
        }
        println("[${elapsed()}] per-level mismatches in $lo..$hi: $levelMismatches")

        println("--- (2) cumulative structure (root marked), assuming level ${lo - 1} SAME from the guided run ---")
        val deadline = t0 + deadlineMs
        val cache = HashMap<Int, Boolean>()
        fun same(k: Int): Boolean = cache.getOrPut(k) {
            if (System.currentTimeMillis() > deadline) throw BudgetExhausted("deadline ${deadlineMs}ms passed")
            val (ha, hb) = (0..1).map { cumulative(g, calls[it], { c -> c.level <= k }, listOf(a, b)[it]).form.hash }
            println("[${elapsed()}] probe level $k: ${if (ha == hb) "SAME" else "DIFFERENT"} ($ha vs $hb)")
            ha == hb
        }
        try {
            if (same(hi)) {
                println("level $hi SAME -> no non-isomorphic level in $lo..$hi" + if (hi == calls[0].maxOf { it.level }) "; deepest level = all of G with root marked => automorphism $a -> $b" else "")
            } else {
                var l = lo; var h = hi
                while (l < h) { val mid = (l + h) / 2; if (same(mid)) l = mid + 1 else h = mid }
                println("first NON-ISOMORPHIC level in $lo..$hi: $l (probes: ${cache.keys.sorted()})")
            }
        } catch (e: BudgetExhausted) {
            println("[${elapsed()}] BUDGET EXHAUSTED: ${e.message}; probes done: ${cache.toSortedMap()}")
        }
        println("========================================================")
    }

    @Test
    fun r2_3600_orbitCheck_4_371() {
        val g = GraphIO.loadDimacs(File("graphs/cfi-rigid-r2/cfi-rigid-r2-3600-01-1").toPath())
        val t0 = System.currentTimeMillis()
        val whole = traces.certifyAll(g, listOf(IntArray(g.n) { it }), getcanon = false)
        println("r2-3600 uncoloured G: |Aut|=${"%.6g".format(whole.stats.autOrder)} orbits=${whole.stats.numOrbits}; orbit(4)==orbit(371): ${whole.orbits[4] == whole.orbits[371]} (${System.currentTimeMillis() - t0} ms)")
    }

    /** ONE cumulative probe (root marked) at level PROBE_LEVEL (env var) for r2-3600 roots 4 vs 371 --
     *  meant to be run one process per level by an outer shell loop with its own timeout, since a
     *  Traces call cannot be interrupted from the JVM. No-op when PROBE_LEVEL is unset. */
    @Test
    fun r2_3600_probeLevel() {
        val k = System.getenv("PROBE_LEVEL")?.toIntOrNull() ?: return
        val g = GraphIO.loadDimacs(File("graphs/cfi-rigid-r2/cfi-rigid-r2-3600-01-1").toPath())
        val baseline = dispatchColouring(g).colouring
        val roots = listOf(4, 371)
        val calls = roots.map { r -> mutableListOf<Call>().also { decompose(g, IntArray(g.n) { it }, baseline, dialysis.viz.topLevelForcedRootRule(r, g.n), 0, null, it) } }
        val t0 = System.currentTimeMillis()
        val cs = (0..1).map { cumulative(g, calls[it], { c -> c.level <= k }, roots[it]) }
        val verdict = if (cs[0].form.hash == cs[1].form.hash) "SAME" else "DIFFERENT"
        println("PROBE level=$k $verdict ${cs[0].form.hash} vs ${cs[1].form.hash} n=${cs[0].form.n} m=${cs[0].form.m} traces_ms=${System.currentTimeMillis() - t0}")
    }

    /**
     * PAIRWISE level windows (Christos, 2026-09-26): for each k, the structure made of the pieces of
     * levels k and k+1 ONLY (in-piece edges + their connectors + far endpoints; cells by (level, role);
     * top root marked only in window 0-1, where it lives). Much smaller than the cumulative structure.
     * SOUND one way: the window is colour-definable inside the cumulative structure up to k+1, so a
     * DIFFERENT window proves the first cumulative non-isomorphic level is <= k+1; SAME windows prove
     * nothing globally (a twist spanning more than two levels passes every window). Roots below the top
     * level are the default rule's (one root per piece, no candidates explored).
     */
    private fun scanLevelWindows(path: String, a: Int, b: Int, width: Int = 2) {
        val t0 = System.currentTimeMillis()
        val g = loadForTrace(path)
        val baseline = dispatchColouring(g).colouring
        val roots = listOf(a, b)
        val calls = roots.map { r -> mutableListOf<Call>().also { decompose(g, IntArray(g.n) { it }, baseline, dialysis.viz.topLevelForcedRootRule(r, g.n), 0, null, it) } }
        val maxLevel = calls.minOf { cs -> cs.maxOf { it.level } }
        println("==== $path -- level windows of width $width, roots $a vs $b, levels 0..$maxLevel (setup ${(System.currentTimeMillis() - t0) / 1000.0}s) ====")
        val different = mutableListOf<Int>()
        for (k in 0..maxLevel - width + 1) {
            val t = System.currentTimeMillis()
            val last = k + width - 1
            val cs = (0..1).map { cumulative(g, calls[it], { c -> c.level in k..last }, if (k == 0) roots[it] else null) }
            val same = cs[0].form.hash == cs[1].form.hash
            if (!same) different.add(k)
            println("WINDOW $k-$last: ${if (same) "SAME" else "DIFFERENT"} n=${cs[0].form.n}/${cs[1].form.n} m=${cs[0].form.m}/${cs[1].form.m} ${cs[0].form.hash} vs ${cs[1].form.hash} traces_ms=${System.currentTimeMillis() - t}")
        }
        println("DIFFERENT windows: ${different.map { "$it-${it + width - 1}" }}" + if (different.isNotEmpty()) " -> first cumulative non-isomorphic level <= ${different.first() + width - 1}" else "")
        println("========================================================")
    }

    @Test fun r2_3600_windows_4_371() = scanLevelWindows("graphs/cfi-rigid-r2/cfi-rigid-r2-3600-01-1", 4, 371)
    @Test fun r2_0504_windows_322_472() = scanLevelWindows("graphs/cfi-rigid-r2/cfi-rigid-r2-0504-01-1", 322, 472)
    @Test fun r2_0144_windows3_20_49() = scanLevelWindows("graphs/cfi-rigid-r2/cfi-rigid-r2-0144-01-1", 20, 49, width = 3)
    @Test fun r2_0504_windows3_322_472() = scanLevelWindows("graphs/cfi-rigid-r2/cfi-rigid-r2-0504-01-1", 322, 472, width = 3)
    /** Windows [j, end] with fixed [end] and start j = 0..end: which start levels still see the
     *  difference? (root marked only when j = 0, where it lives). */
    private fun anchoredWindows(path: String, a: Int, b: Int, end: Int) {
        val g = loadForTrace(path)
        val baseline = dispatchColouring(g).colouring
        val roots = listOf(a, b)
        val calls = roots.map { r -> mutableListOf<Call>().also { decompose(g, IntArray(g.n) { it }, baseline, dialysis.viz.topLevelForcedRootRule(r, g.n), 0, null, it) } }
        println("==== $path -- windows [j, $end], roots $a vs $b ====")
        for (j in 0..end) {
            for (markRoot in if (j == 0) listOf(true, false) else listOf(false)) {
                val cs = (0..1).map { cumulative(g, calls[it], { c -> c.level in j..end }, if (markRoot) roots[it] else null) }
                println("WINDOW $j-$end${if (j == 0) " (root marked=$markRoot)" else ""}: ${if (cs[0].form.hash == cs[1].form.hash) "SAME" else "DIFFERENT"} n=${cs[0].form.n} m=${cs[0].form.m}")
            }
        }
        println("========================================================")
    }

    @Test fun r2_0504_anchored_end9() = anchoredWindows("graphs/cfi-rigid-r2/cfi-rigid-r2-0504-01-1", 322, 472, 9)
    @Test fun r2_0144_anchored_end2() = anchoredWindows("graphs/cfi-rigid-r2/cfi-rigid-r2-0144-01-1", 20, 49, 2)

    @Test fun r2_3600_windows3_4_371() = scanLevelWindows("graphs/cfi-rigid-r2/cfi-rigid-r2-3600-01-1", 4, 371, width = 3)

    @Test fun r2_3600_levels_47_63() = checkLevelRange("graphs/cfi-rigid-r2/cfi-rigid-r2-3600-01-1", 4, 371, 47, 63, 8 * 60_000L)

    private fun loadForTrace(path: String): Graph {
        return GraphIO.loadDimacs(File(path).toPath())
    }

    /**
     * Full anomaly trace for one instance (Christos, 2026-09-26, t2 family): orbit check, auto-picked roots (a = default rule's top root, b = another member of its level-0
     * candidate class), binary-search inconsistency level + culprit + witness, phi-guided
     * decomposition, and windows [j, k*] anchored at the inconsistency level.
     */
    private fun traceInstance(path: String, orbitCheckMaxN: Int = 2500) {
        val g0 = GraphIO.loadDimacs(File(path).toPath())
        val g = loadForTrace(path)
        println("######## $path: original n=${g0.n} m=${g0.m} bipartite=${g0.bipartition() != null} -> traced graph n=${g.n} m=${g.m} bipartite=${g.bipartition() != null} ########")
        val baseline = dispatchColouring(g).colouring
        val (sub, _) = g.induced(IntArray(g.n) { it })
        val a = dialysis.decomposition.defaultRootRule(sub, baseline)
        val cls = (0 until g.n).filter { baseline[it] == baseline[a] }
        val b = cls.firstOrNull { it != a }
        println("PI classes=${baseline.toHashSet().size}; default root a=$a (${if (a < g0.n) "original" else "subdivision"} vertex), its class $cls")
        if (g.n <= orbitCheckMaxN) {
            val t = System.currentTimeMillis()
            val o = traces.certifyAll(g, listOf(IntArray(g.n) { it }), getcanon = false)
            println("Traces uncoloured: |Aut|=${"%.6g".format(o.stats.autOrder)} orbits=${o.stats.numOrbits}" + (if (b != null) "; orbit(a)==orbit(b): ${o.orbits[a] == o.orbits[b]}" else "") + " (${System.currentTimeMillis() - t} ms)")
        } else println("orbit check skipped (n > $orbitCheckMaxN)")
        if (b == null) { println("level-0 candidate class is a singleton: no second root to compare"); return }
        val kStar = findInconsistentLevel(path, a, b, crossCheckLinear = true)
        guidedDecomposition(path, a, b)
        if (kStar != null && kStar > 0) anchoredWindows(path, a, b, kStar)
    }

    /**
     * Connector LEVEL SPANS (Christos, 2026-09-26): a connector goes from the tree of a level-L piece
     * to a vertex of its remainder, and that vertex lands in whatever piece the recursion later puts
     * it in -- level L+d for some d >= 1, not necessarily L+1. Reports, for the default decomposition
     * from [root]: the span histogram d -> #connectors, the source-level x target-level counts, and,
     * if [focusLevel] is given, where the connectors INTO the focus level's pieces come from.
     * No Traces calls. Every edge of G is in-piece or a connector, so this is all cross-level coupling.
     */
    private fun connectorSpans(path: String, root: Int, focusLevel: Int? = null) {
        val g = loadForTrace(path)
        val baseline = dispatchColouring(g).colouring
        val calls = mutableListOf<Call>().also { decompose(g, IntArray(g.n) { it }, baseline, dialysis.viz.topLevelForcedRootRule(root, g.n), 0, null, it) }
        val levelOf = IntArray(g.n) { -1 }
        for (c in calls) for (v in c.vertices) levelOf[v] = c.level
        val spans = sortedMapOf<Int, Int>()
        val matrix = sortedMapOf<Int, java.util.TreeMap<Int, Int>>()
        var total = 0
        for (c in calls) for ((_, r) in c.connectors) {
            val d = levelOf[r] - c.level
            spans.merge(d, 1, Int::plus)
            matrix.getOrPut(c.level) { java.util.TreeMap() }.merge(levelOf[r], 1, Int::plus)
            total++
        }
        val inPiece = calls.sumOf { c -> val set = c.vertices.toHashSet(); c.vertices.sumOf { u -> g.adj[u].count { it in set && u < it } } }
        println("==== $path root=$root: ${calls.size} pieces, levels 0..${calls.maxOf { it.level }}; edges: in-piece $inPiece + connectors $total = ${inPiece + total} (G has ${g.m}) ====")
        println("connector span d = level(target) - level(source): " + spans.entries.joinToString("  ") { (d, n) -> "d=$d:$n" } +
            "   (d>1: ${spans.filterKeys { it > 1 }.values.sum()} of $total = ${"%.1f".format(100.0 * spans.filterKeys { it > 1 }.values.sum() / total)}%, max d=${spans.lastKey()})")
        println("source level -> {target level: #connectors}:")
        for ((src, tg) in matrix) println("   L$src -> " + tg.entries.joinToString(" ") { (t, n) -> "L$t:$n" })
        if (focusLevel != null) {
            val into = sortedMapOf<Int, Int>()
            for (c in calls) for ((_, r) in c.connectors) if (levelOf[r] == focusLevel) into.merge(c.level, 1, Int::plus)
            println("connectors INTO level $focusLevel come from: " + into.entries.joinToString(" ") { (src, n) -> "L$src:$n" })
            val intoFromZero = calls.filter { it.level == 0 }.flatMap { it.connectors }.filter { levelOf[it.second] == focusLevel }
            println("   of which DIRECTLY from level 0: ${intoFromZero.size} ${intoFromZero.take(20)}")
        }
        println("========================================================")
    }

    @Test fun spans_r2_0144() { connectorSpans("graphs/cfi-rigid-r2/cfi-rigid-r2-0144-01-1", 20, 2); connectorSpans("graphs/cfi-rigid-r2/cfi-rigid-r2-0144-01-1", 49, 2) }
    @Test fun spans_r2_0504() { connectorSpans("graphs/cfi-rigid-r2/cfi-rigid-r2-0504-01-1", 322, 9); connectorSpans("graphs/cfi-rigid-r2/cfi-rigid-r2-0504-01-1", 472, 9) }
    @Test fun spans_t2_0216() { connectorSpans("graphs/cfi-rigid-t2/cfi-rigid-t2-0216-01-1", 216, 8); connectorSpans("graphs/cfi-rigid-t2/cfi-rigid-t2-0216-01-1", 862, 8) }
    @Test fun spans_r2_3600() { connectorSpans("graphs/cfi-rigid-r2/cfi-rigid-r2-3600-01-1", 4, 56) }

    /**
     * Isolate the connectors INTO level [k] (Christos, 2026-09-26): with the cumulative structure up to
     * [k] (root marked) DIFFERENT for roots [a] vs [b], remove groups of connectors into level k --
     * by source level, all of them, then each single L[src]->L[k] edge (leave-one-out) and each one kept
     * alone (leave-one-in) -- and report SAME/DIFFERENT. Single-edge tests need both roots to have the
     * SAME list of such edges (checked).
     */
    private fun isolateConnectorsInto(path: String, a: Int, b: Int, k: Int, src: Int) {
        val g = loadForTrace(path)
        val baseline = dispatchColouring(g).colouring
        val roots = listOf(a, b)
        val calls = roots.map { r -> mutableListOf<Call>().also { decompose(g, IntArray(g.n) { it }, baseline, dialysis.viz.topLevelForcedRootRule(r, g.n), 0, null, it) } }
        val levelOf = calls.map { cs -> IntArray(g.n) { -1 }.also { lv -> for (c in cs) for (v in c.vertices) lv[v] = c.level } }
        val into = (0..1).map { i -> calls[i].filter { it.level < k }.flatMap { c -> c.connectors.map { e -> Triple(c.level, e.first, e.second) } }.filter { levelOf[i][it.third] == k } }
        val bySrc = (0..1).map { i -> into[i].groupBy { it.first }.mapValues { it.value.size }.toSortedMap() }
        println("==== $path -- connectors into level $k, roots $a vs $b ====")
        println("connectors into L$k by source level: root $a ${bySrc[0]}, root $b ${bySrc[1]}")

        fun test(label: String, drop: (Int, Int, Int) -> Boolean) {   // drop(sideIndex, t, r)
            val cs = (0..1).map { i -> cumulative(g, calls[i], { c -> c.level <= k }, roots[i]) { t, r -> drop(i, t, r) } }
            println(String.format("%-58s %s  (n=%d/%d m=%d/%d)", label, if (cs[0].form.hash == cs[1].form.hash) "SAME" else "DIFFERENT", cs[0].form.n, cs[1].form.n, cs[0].form.m, cs[1].form.m))
        }
        val intoSet = (0..1).map { i -> into[i].map { it.second to it.third }.toSet() }
        val srcEdges = (0..1).map { i -> into[i].filter { it.first == src }.map { it.second to it.third } }
        test("nothing removed") { _, _, _ -> false }
        test("remove L$src->L$k (${srcEdges[0].size}/${srcEdges[1].size} edges)") { i, t, r -> (t to r) in srcEdges[i].toSet() }
        for (other in bySrc[0].keys.filter { it != src }) {
            val es = (0..1).map { i -> into[i].filter { it.first == other }.map { it.second to it.third }.toSet() }
            test("remove L$other->L$k (${es[0].size}/${es[1].size} edges)") { i, t, r -> (t to r) in es[i] }
        }
        test("remove ALL connectors into L$k (${intoSet[0].size}/${intoSet[1].size})") { i, t, r -> (t to r) in intoSet[i] }

        // OUTGOING connectors of the level-k pieces (to deeper endpoints) and endpoints they SHARE with
        // connectors from shallower levels: a coupling path L_src -> x <- L_k through a deeper vertex x.
        val outgoing = (0..1).map { i -> calls[i].filter { it.level == k }.flatMap { it.connectors }.toSet() }
        test("remove OUTGOING connectors of L$k (${outgoing[0].size}/${outgoing[1].size})") { i, t, r -> (t to r) in outgoing[i] }
        test("remove incoming AND outgoing of L$k") { i, t, r -> (t to r) in intoSet[i] || (t to r) in outgoing[i] }
        for (i in 0..1) {
            val shallowByEndpoint = calls[i].filter { it.level < k }.flatMap { c -> c.connectors.map { e -> e.second to (c.level to e.first) } }.groupBy({ it.first }, { it.second })
            val shared = outgoing[i].filter { (_, x) -> x in shallowByEndpoint }
            println("root ${roots[i]}: ${shared.size} of ${outgoing[i].size} outgoing L$k connectors end at a deeper vertex x that ALSO receives connectors from shallower levels:")
            for ((t, x) in shared) println("   L$k $t -> x=$x (level ${levelOf[i][x]}) <- " + shallowByEndpoint.getValue(x).joinToString(" ") { (lv, s0) -> "L$lv:$s0" })
        }
        val sharedFromSrc = (0..1).map { i ->
            val srcEndpoints = calls[i].filter { it.level == src }.flatMap { it.connectors }.map { it.second }.toSet()
            outgoing[i].filter { it.second in srcEndpoints }.toSet()
        }
        test("remove outgoing L$k connectors whose endpoint also gets an L$src connector (${sharedFromSrc[0].size}/${sharedFromSrc[1].size})") { i, t, r -> (t to r) in sharedFromSrc[i] }

        val sameList = srcEdges[0].toSet() == srcEdges[1].toSet()
        println("L$src->L$k edge lists identical for both roots: $sameList")
        if (!sameList) { println("   root $a: ${srcEdges[0]}\n   root $b: ${srcEdges[1]}"); println("========================================================"); return }
        val tree0 = (0..1).map { i -> calls[i].filter { it.level == k }.flatMap { it.treeVerts.toList() }.toSet() }
        println("--- single L$src->L$k edges (target role in L$k piece: tree/orphan, per root) ---")
        for ((t, r) in srcEdges[0]) {
            val roleA = if (r in tree0[0]) "tree" else "orphan"; val roleB = if (r in tree0[1]) "tree" else "orphan"
            val cs1 = (0..1).map { i -> cumulative(g, calls[i], { c -> c.level <= k }, roots[i]) { tt, rr -> tt == t && rr == r } }
            val cs2 = (0..1).map { i -> cumulative(g, calls[i], { c -> c.level <= k }, roots[i]) { tt, rr -> (tt to rr) in srcEdges[i].toSet() && !(tt == t && rr == r) } }
            println(String.format("edge %4d-%-4d target %-6s/%-6s  remove only this: %-9s  keep only this (other L$src->L$k removed): %s", t, r, roleA, roleB,
                if (cs1[0].form.hash == cs1[1].form.hash) "SAME" else "DIFFERENT", if (cs2[0].form.hash == cs2[1].form.hash) "SAME" else "DIFFERENT"))
        }
        println("========================================================")
    }

    /** Minimal-cause search among the OUTGOING connectors of level [k]: each single outgoing edge
     *  removed alone, then the explicit edge set [candidate] removed (on both roots). */
    private fun outgoingLeaveOneOut(path: String, a: Int, b: Int, k: Int, candidate: Set<Pair<Int, Int>>) {
        val g = loadForTrace(path)
        val baseline = dispatchColouring(g).colouring
        val roots = listOf(a, b)
        val calls = roots.map { r -> mutableListOf<Call>().also { decompose(g, IntArray(g.n) { it }, baseline, dialysis.viz.topLevelForcedRootRule(r, g.n), 0, null, it) } }
        val levelOf = calls.map { cs -> IntArray(g.n) { -1 }.also { lv -> for (c in cs) for (v in c.vertices) lv[v] = c.level } }
        val outgoing = calls[0].filter { it.level == k }.flatMap { it.connectors }
        check(outgoing.toSet() == calls[1].filter { it.level == k }.flatMap { it.connectors }.toSet()) { "outgoing L$k lists differ between roots" }
        fun same(drop: Set<Pair<Int, Int>>): Boolean {
            val cs = (0..1).map { i -> cumulative(g, calls[i], { c -> c.level <= k }, roots[i]) { t, r -> (t to r) in drop } }
            return cs[0].form.hash == cs[1].form.hash
        }
        println("==== $path -- outgoing L$k connectors, leave-one-out (roots $a vs $b) ====")
        val fixers = outgoing.filter { same(setOf(it)) }
        println("single outgoing edges whose removal ALONE makes it SAME: ${fixers.size} of ${outgoing.size}: " +
            fixers.joinToString(" ") { (t, x) -> "$t->$x(L${levelOf[0][x]})" })
        // Inclusion-minimal fixing set: start from all outgoing connectors whose far end ALSO receives a
        // level-0 connector (under either root), put each edge back if the structures stay SAME.
        val l0Ends = (0..1).flatMap { i -> calls[i].filter { it.level == 0 }.flatMap { it.connectors }.map { it.second } }.toSet()
        val start = outgoing.filter { it.second in l0Ends }.toSet()
        println("start set (outgoing L$k edges whose far end also receives an L0 connector under either root): ${start.size} edges -> ${if (same(start)) "SAME" else "DIFFERENT"}")
        if (same(start)) {
            val drop = start.toMutableSet()
            for (e in start) { drop.remove(e); if (!same(drop)) drop.add(e) }
            println("inclusion-MINIMAL set of outgoing L$k connectors whose removal makes it SAME: ${drop.size} edges")
            for ((t, x) in drop.sortedBy { it.second }) {
                val src = (0..1).map { i -> calls[i].flatMap { c -> c.connectors.filter { it.second == x }.map { "L${c.level}:${it.first}" } } }
                println("   $t -> x=$x (level ${levelOf[0][x]})   x also receives: root $a ${src[0].filter { !it.startsWith("L$k:") }} | root $b ${src[1].filter { !it.startsWith("L$k:") }}")
            }
            println("check: removing exactly this set -> ${if (same(drop)) "SAME" else "DIFFERENT"}; putting back any one edge -> " +
                drop.map { e -> if (same(drop - e)) "SAME" else "DIFFERENT" }.toSet())
        }
        println("remove candidate set $candidate: ${if (same(candidate)) "SAME" else "DIFFERENT"}")
        for (e in candidate) println("   remove only ${e.first}->${e.second}: ${if (same(setOf(e))) "SAME" else "DIFFERENT"}")
        for (x in candidate.map { it.second }.toSet()) {
            val src = (0..1).map { i -> calls[i].flatMap { c -> c.connectors.filter { it.second == x }.map { "L${c.level}:${it.first}" } } }
            println("   x=$x (L${levelOf[0][x]}/L${levelOf[1][x]}) receives connectors: root $a ${src[0]} | root $b ${src[1]}")
        }
        println("========================================================")
    }

    /**
     * Which connectors from the PREVIOUS levels 0..k-1 must be removed (on both roots, by edge identity)
     * so the cumulative structure up to [k] (root marked) becomes isomorphic? The level-k pieces and
     * their own connectors are left untouched. Tries growing candidate tiers, the first SAME tier is
     * shrunk greedily to an inclusion-minimal set (each edge put back if the result stays SAME).
     */
    private fun previousLevelsMinimalCut(path: String, a: Int, b: Int, k: Int, hubs: Set<Int>) {
        val g = loadForTrace(path)
        val baseline = dispatchColouring(g).colouring
        val roots = listOf(a, b)
        val calls = roots.map { r -> mutableListOf<Call>().also { decompose(g, IntArray(g.n) { it }, baseline, dialysis.viz.topLevelForcedRootRule(r, g.n), 0, null, it) } }
        val levelOf = calls.map { cs -> IntArray(g.n) { -1 }.also { lv -> for (c in cs) for (v in c.vertices) lv[v] = c.level } }
        val srcLevel = calls.map { cs -> HashMap<Pair<Int, Int>, Int>().also { m -> for (c in cs) for (e in c.connectors) m[e] = c.level } }
        val prev = (0..1).map { i -> calls[i].filter { it.level < k }.flatMap { it.connectors }.toSet() }
        val union = prev[0] + prev[1]
        val outEnds = (0..1).flatMap { i -> calls[i].filter { it.level == k }.flatMap { it.connectors }.map { it.second } }.toSet()
        var tracesCalls = 0
        fun same(drop: Set<Pair<Int, Int>>): Boolean {
            tracesCalls += 2
            val cs = (0..1).map { i -> cumulative(g, calls[i], { c -> c.level <= k }, roots[i]) { t, r -> (t to r) in drop } }
            return cs[0].form.hash == cs[1].form.hash
        }
        println("==== $path -- minimal cut among connectors of levels 0..${k - 1} (roots $a vs $b, structure up to L$k) ====")
        println("connectors from levels < $k: root $a ${prev[0].size}, root $b ${prev[1].size}, identical sets: ${prev[0] == prev[1]}")
        val tiers = listOf(
            "ending at hubs $hubs" to union.filter { it.second in hubs }.toSet(),
            "ending at any far end of L$k's outgoing connectors" to union.filter { it.second in outEnds }.toSet(),
            "ending deeper than L$k" to union.filter { (_, r) -> levelOf[0][r] > k }.toSet(),
            "ALL connectors of levels < $k" to union,
        )
        var chosen: Set<Pair<Int, Int>>? = null
        for ((label, set) in tiers) {
            val ok = same(set)
            println("remove connectors $label (${set.size}): ${if (ok) "SAME" else "DIFFERENT"}")
            if (ok) { chosen = set; break }
        }
        if (chosen == null) { println("no tier makes it SAME"); println("========================================================"); return }
        val drop = chosen.toMutableSet()
        var passes = 0
        do {   // repeat until a full pass puts nothing back: then no single edge can be restored
            passes++
            var changed = false
            for (e in drop.sortedWith(compareBy({ -(levelOf[0][it.second]) }, { it.first }))) {
                drop.remove(e)
                if (same(drop)) changed = true else drop.add(e)
            }
        } while (changed)
        println("inclusion-MINIMAL set: ${drop.size} connectors from previous levels ($passes passes, Traces calls: $tracesCalls)")
        println(String.format("   %-12s %-22s %-22s %s", "edge", "source level (216/862)", "far end x (level)", "x role in the structure"))
        for (e in drop.sortedWith(compareBy({ it.second }, { it.first }))) {
            val (t, x) = e
            val sl = "${srcLevel[0][e] ?: "-"}/${srcLevel[1][e] ?: "-"}"
            val role = if (levelOf[0][x] > k) "endpoint (deeper piece)" else "L${levelOf[0][x]} piece vertex"
            println(String.format("   %-12s %-22s %-22s %s", "$t->$x", sl, "$x (L${levelOf[0][x]}/L${levelOf[1][x]})", role))
        }
        println("check: removing exactly this set -> ${if (same(drop)) "SAME" else "DIFFERENT"}; putting back any one -> ${drop.map { if (same(drop - it)) "SAME" else "DIFFERENT" }.toSet()}")
        println("========================================================")
    }

    /**
     * DOT drawing of the L(k-1) -> L(k) break (Christos, 2026-09-26), both roots side by side: the
     * loose ends [hubs], the [critical] level-k edges into them (bold blue), the level-k vertices
     * they start from and the shortest paths joining those inside the level-k piece (dashed blue),
     * and every connector from levels < k into the hubs, source coloured by its level. Written to
     * the DOT_OUT env var (default: java.io.tmpdir/l7_l8_break.dot).
     */
    private fun drawBreakDot(path: String, a: Int, b: Int, k: Int, hubs: List<Int>, critical: List<Pair<Int, Int>>) {
        val g = loadForTrace(path)
        val baseline = dispatchColouring(g).colouring
        val roots = listOf(a, b)
        val calls = roots.map { r -> mutableListOf<Call>().also { decompose(g, IntArray(g.n) { it }, baseline, dialysis.viz.topLevelForcedRootRule(r, g.n), 0, null, it) } }
        val colourOf = mapOf(0 to "#e05050", 1 to "#f0a030", 2 to "#d8c040", 3 to "#b0d040", 4 to "#80c060", 5 to "#60b080", 6 to "#40a040", 7 to "#a0e0a0", k to "#5080e0")
        val sb = StringBuilder()
        sb.append("graph L${k - 1}_to_L$k {\n  graph [rankdir=TB, fontname=\"Helvetica\", fontsize=12, nodesep=0.25, ranksep=0.6, label=\"")
        sb.append("$path  --  structure up to L${k - 1}: SAME, up to L$k: DIFFERENT\\nbold blue = the ${critical.size} L$k edges whose removal makes up-to-L$k SAME;  grey = loose ends (not in any piece up to L$k);  dashed = path inside the L$k piece")
        sb.append("\", labelloc=t];\n  node [shape=circle, style=filled, fontname=\"Helvetica\", fontsize=10, width=0.45, fixedsize=true];\n")
        for ((side, root) in roots.withIndex()) {
            val cs = calls[side]
            val levelOf = IntArray(g.n) { -1 }.also { lv -> for (c in cs) for (v in c.vertices) lv[v] = c.level }
            val pieceK = cs.filter { it.level == k }
            val inPiece = pieceK.flatMap { it.vertices.toList() }.toHashSet()
            val id = { v: Int -> "r${root}_$v" }
            sb.append("  subgraph cluster_$root {\n    label=\"root $root\"; fontsize=14; color=\"#999999\";\n")
            val nodes = LinkedHashSet<Int>()
            val edges = mutableListOf<Triple<Int, Int, String>>()
            for (h in hubs) {
                nodes.add(h)
                for (c in cs.filter { it.level < k }) for ((t, x) in c.connectors) if (x == h) { nodes.add(t); edges.add(Triple(t, h, "color=\"#444444\"")) }
            }
            val starts = critical.map { it.first }
            for ((t, h) in critical) { nodes.add(t); edges.add(Triple(t, h, "color=\"#2050d0\", penwidth=3")) }
            // shortest paths inside the level-k piece between consecutive critical start vertices
            val sub = inPiece
            fun bfsPath(s0: Int, t0: Int): List<Int> {
                val prev = HashMap<Int, Int>(); val q = ArrayDeque<Int>(); q.add(s0); prev[s0] = s0
                while (q.isNotEmpty()) { val v = q.removeFirst(); if (v == t0) break; for (w in g.adj[v]) if (w in sub && w !in prev) { prev[w] = v; q.add(w) } }
                if (t0 !in prev) return emptyList()
                val out = mutableListOf(t0); var cur = t0; while (cur != s0) { cur = prev.getValue(cur); out.add(cur) }; return out.reversed()
            }
            val pathEdges = HashSet<Pair<Int, Int>>()
            for (i in 0 until starts.size - 1) {
                val pth = bfsPath(starts[i], starts[i + 1])
                for (j in 0 until pth.size - 1) { nodes.add(pth[j]); nodes.add(pth[j + 1]); pathEdges.add(minOf(pth[j], pth[j + 1]) to maxOf(pth[j], pth[j + 1])) }
            }
            for ((u, w) in pathEdges) edges.add(Triple(u, w, "color=\"#2050d0\", style=dashed"))
            for (v in nodes) {
                val lv = levelOf[v]
                val isLoose = lv > k
                val fill = if (isLoose) "#cccccc" else colourOf[lv] ?: "#dddddd"
                val shape = if (isLoose) ", shape=doublecircle, width=0.55" else ""
                val lbl = if (isLoose) "$v\\nloose" else "$v\\nL$lv"
                sb.append("    ${id(v)} [label=\"$lbl\", fillcolor=\"$fill\"$shape];\n")
            }
            for ((u, w, st) in edges) sb.append("    ${id(u)} -- ${id(w)} [$st];\n")
            sb.append("  }\n")
        }
        sb.append("}\n")
        val out = File(System.getenv("DOT_OUT") ?: File(System.getProperty("java.io.tmpdir"), "l7_l8_break.dot").path)
        out.writeText(sb.toString())
        println("DOT written to ${out.absolutePath}")
    }

    /**
     * Individualise each vertex of [cls] in turn (PI colouring + v in its own cell), refine by 1-WL and
     * by PI ([dialysis.refinement.initialPhase]), and compare the results canonically (Christos,
     * 2026-09-26: is the class [40, 55, 175, 210] of t2-0216 separated by individualisation?).
     * Fingerprint = multiset of (colour, cell size) -- colours are content-addressed / canonical, so
     * two orbit-mates always give equal fingerprints; different fingerprints PROVE different orbits.
     * Also: how the other class members split, and the exact Traces certificate of G with v individualised.
     */
    private fun individualizeClass(path: String, cls: List<Int>) {
        val g = loadForTrace(path)
        val baseline = dispatchColouring(g).colouring
        val members = (0 until g.n).filter { baseline[it] == baseline[cls[0]] }
        println("==== $path -- individualise each of $cls (n=${g.n}) ====")
        println("PI class of ${cls[0]}: $members -> given list is exactly one PI class: ${members.toSet() == cls.toSet()}")
        val piCells = (0 until g.n).groupBy { baseline[it] }.values.sortedBy { it.min() }.map { it.toIntArray() }
        fun fp(col: Array<Content>): String {
            val ms = col.toList().groupingBy { it }.eachCount().entries.map { (c, n) -> c.serialize() + "#" + n }.sorted().joinToString("|")
            return java.security.MessageDigest.getInstance("SHA-256").digest(ms.toByteArray()).take(4).joinToString("") { "%02x".format(it) }
        }
        println(String.format("%-6s %9s %-10s %9s %-10s %-10s  %s", "v", "1WL cls", "1WL fp", "PI cls", "PI fp", "Traces", "how the OTHER class members split (1-WL | PI)"))
        for (v in cls) {
            val seed = Array<Content>(g.n) { if (it == v) Content.Tup(listOf(baseline[it], Content.Str("IND"))) else baseline[it] }
            val wl = colorRefine1WL(g, seed)
            val pi = dialysis.refinement.initialPhase(g, seed)
            val others = cls.filter { it != v }
            val splitWl = others.groupBy { wl.color[it] }.values.map { it.sorted() }
            val splitPi = others.groupBy { pi.color[it] }.values.map { it.sorted() }
            // exact: Traces certificate with PI cells in value order and v split off first
            val cells = listOf(intArrayOf(v)) + piCells.map { c -> c.filter { it != v }.toIntArray() }.filter { it.isNotEmpty() }
            val cert = canonicalForm(g, cells).hash
            println(String.format("%-6d %9d %-10s %9d %-10s %-10s  %s | %s", v, wl.cells.size, fp(wl.color), pi.cells.size, fp(pi.color), cert, splitWl, splitPi))
        }
        println("========================================================")
    }

    /** Individualise PAIRS (x in its own cell "IND1", y in "IND2") and compare 1-WL / PI fingerprints
     *  across pairs: equal fingerprints = refinement cannot tell the pairs apart; different = it can
     *  (and that proves the pairs are in different orbits of Aut acting on ordered pairs). */
    private fun individualizePairs(path: String, pairs: List<Pair<Int, Int>>) {
        val g = loadForTrace(path)
        val baseline = dispatchColouring(g).colouring
        fun fp(col: Array<Content>): String {
            val ms = col.toList().groupingBy { it }.eachCount().entries.map { (c, n) -> c.serialize() + "#" + n }.sorted().joinToString("|")
            return java.security.MessageDigest.getInstance("SHA-256").digest(ms.toByteArray()).take(4).joinToString("") { "%02x".format(it) }
        }
        println("==== $path -- individualise ordered pairs (x=IND1, y=IND2) ====")
        println(String.format("%-12s %8s %-10s %8s %-10s", "(x, y)", "1WL cls", "1WL fp", "PI cls", "PI fp"))
        for ((x, y) in pairs) {
            val seed = Array<Content>(g.n) { v -> when (v) { x -> Content.Tup(listOf(baseline[v], Content.Str("IND1"))); y -> Content.Tup(listOf(baseline[v], Content.Str("IND2"))); else -> baseline[v] } }
            val wl = colorRefine1WL(g, seed)
            val pi = dialysis.refinement.initialPhase(g, seed)
            println(String.format("%-12s %8d %-10s %8d %-10s", "($x, $y)", wl.cells.size, fp(wl.color), pi.cells.size, fp(pi.color)))
        }
        println("========================================================")
    }

    @Test fun t2_0216_individualize_pairs() {
        val cls = listOf(40, 55, 175, 210)
        val inClass = cls.flatMap { x -> cls.filter { it != x }.map { x to it } }
        val rootMember = listOf(216, 862).flatMap { r -> cls.map { r to it } }
        individualizePairs("graphs/cfi-rigid-t2/cfi-rigid-t2-0216-01-1", inClass + rootMember)
    }

    // ─────────────────────────── parity equations over GF(2) ───────────────────────────

    private fun sha64(x: String): Long {
        val d = java.security.MessageDigest.getInstance("SHA-256").digest(x.toByteArray())
        var r = 0L; for (i in 0 until 8) r = (r shl 8) or (d[i].toLong() and 0xff); return r
    }

    private fun mix64(x0: Long): Long {   // splitmix64 finaliser
        var x = x0 + -0x61c8864680b583ebL
        x = (x xor (x ushr 30)) * -0x40a7b892e31b1a47L
        x = (x xor (x ushr 27)) * -0x6b2fb644ecceee15L
        return x xor (x ushr 31)
    }

    /** Hash-based 1-WL, canonical BY CONSTRUCTION (colour = hash of own colour + commutative sum of
     *  neighbour hashes), so colours are comparable across different seeds when run for the SAME
     *  number of rounds [rounds]. Returns (colours, round at which the partition stopped changing). */
    private fun hashWl(g: Graph, seed: LongArray, rounds: Int, stopWhenStable: Boolean = false): Pair<LongArray, Int> {
        var col = seed.copyOf()
        var classes = col.toHashSet().size
        var stableAt = -1
        val nb = LongArray(g.n)
        for (r in 1..rounds) {
            for (v in 0 until g.n) { var sum = 0L; for (w in g.adj[v]) sum += mix64(col[w]); nb[v] = sum }
            val next = LongArray(g.n) { v -> mix64(col[v] * 0x9E3779B97F4A7C15uL.toLong() + nb[v]) }
            val c = next.toHashSet().size
            col = next
            if (stableAt < 0 && c == classes) stableAt = r
            classes = c
            if (stopWhenStable && stableAt >= 0) break
        }
        return col to stableAt
    }

    /** Small GF(2) helpers on bit vectors packed in LongArray. */
    private class Gf2System(val nVars: Int) {
        val words = (nVars + 63) / 64
        val rows = mutableListOf<Pair<LongArray, Boolean>>()   // (coefficients, rhs)
        fun add(coeff: LongArray, rhs: Boolean) { rows.add(coeff to rhs) }
        /** Gaussian elimination; returns (rank, consistent, one solution or null). */
        fun solve(): Triple<Int, Boolean, BooleanArray?> {
            val m = rows.map { it.first.copyOf() to it.second }.toMutableList()
            val pivotCol = IntArray(m.size) { -1 }
            var rank = 0
            for (col in 0 until nVars) {
                val w = col / 64; val bit = 1L shl (col % 64)
                val p = (rank until m.size).firstOrNull { (m[it].first[w] and bit) != 0L } ?: continue
                val tmp = m[p]; m[p] = m[rank]; m[rank] = tmp
                for (i in m.indices) if (i != rank && (m[i].first[w] and bit) != 0L) {
                    val a = m[i].first; val b = m[rank].first
                    for (j in 0 until words) a[j] = a[j] xor b[j]
                    m[i] = a to (m[i].second xor m[rank].second)
                }
                pivotCol[rank] = col; rank++
            }
            val consistent = (rank until m.size).none { i -> m[i].second && m[i].first.all { it == 0L } }
            if (!consistent) return Triple(rank, false, null)
            val x = BooleanArray(nVars)
            for (i in 0 until rank) x[pivotCol[i]] = m[i].second   // free variables = 0
            return Triple(rank, true, x)
        }
    }

    /**
     * EXACT parity-equation solver for Aut(G) (Christos, 2026-09-26). Steps:
     * 1. PI classes; per class C (base b = min), individualise each member v and hash-refine for a
     *    common number of rounds T; candidate restriction tau_s (the only way an automorphism sending
     *    b -> s can act on C) maps v to the unique w in C with colour_s(w) == colour_b(v). FAITHFUL iff
     *    always unique.
     * 2. T_C = {tau_s}: checked to be an elementary abelian 2-group; coordinates over GF(2)^k.
     * 3. per pair of classes joined by edges (and per class with internal edges): allowed (s,t) keep
     *    all those edges; checked to be a SUBGROUP -> its dual gives linear equations.
     * Every automorphism solves the system and every solution is an automorphism (it preserves all
     * edges), so the solution space IS Aut(G): |Aut| = 2^(nVars - rank). The orbit query "a -> b"
     * adds the equations fixing class(a)'s coordinates to tau with tau(a) = b.
     */
    /** Outcome of one [parityEquations] run (status = EXACT, or which check stopped it). */
    class ParityResult {
        var status = "RUNNING"; var n = 0; var m = 0; var piClasses = 0; var nonSingleton = 0; var classSizes = ""
        var tRounds = 0; var unfaithful = 0; var excluded = 0; var notGroup = 0; var nonSubgroup = 0
        var autStr = ""; var autOrder: Double? = null
        var nVars = 0; var nEqs = 0; var autLog2: Int? = null; var query = ""; var queryVerdict = ""; var explicitAutOk: Boolean? = null
        var seconds = 0.0
        /** Number of orbits of Aut(G) on vertices, from explicit enumeration of every automorphism (null if not computed). */
        var orbits: Int? = null; var enumeratedAuts = 0; var enumeratedAllVerified: Boolean? = null
        /** Orbits restricted to the ORIGINAL vertices 0..n0-1. */
        var orbitsOriginal: Int? = null
        /** Orbit representative per vertex (union-find root), when orbits were computed. */
        var orbitOf: IntArray? = null
        /** Which structural assumption / budget stopped the solver, with specifics (empty if EXACT). */
        var stopDetail = ""
        /** Complexity quantities (2026-09-28): longest base sequence, largest candidate set |T_C|, largest pair table
         *  |T1| x |T2| considered, and DFS nodes over the series levels. */
        var maxBaseLen = 0; var maxT = 0; var maxPairTable = 0L; var dfsNodes = 0L
        /** Two-sided mode: an explicit, edge-verified isomorphism H -> H' (as a permutation of V), when one exists. */
        var witnessMap: IntArray? = null
        /** Coset path: the verified generators of the group it computed (each preserves the base colouring). */
        var generators: List<IntArray>? = null
    }

    private fun parityEquations(path: String, a: Int?, b: Int?, quiet: Boolean = false, crossCheck: Boolean = true): ParityResult {
        val res = ParityResult()
        val say: (String) -> Unit = { if (!quiet) println(it) }
        val t0 = System.currentTimeMillis()
        val el = { "${(System.currentTimeMillis() - t0) / 1000.0}s" }
        val g = loadForTrace(path)
        val baseline = dispatchColouring(g).colouring
        val classes = (0 until g.n).groupBy { baseline[it] }.values.map { it.sorted().toIntArray() }.filter { it.size > 1 }
        say("==== $path -- PARITY EQUATIONS for Aut(G) (n=${g.n} m=${g.m}) ====")
        var a = a; var b = b
        if (a == null && b == null) {   // auto-pick: default root and another member of its PI class
            val (sub0, _) = g.induced(IntArray(g.n) { it })
            val r = dialysis.decomposition.defaultRootRule(sub0, baseline)
            val mate = (0 until g.n).firstOrNull { it != r && baseline[it] == baseline[r] }
            if (mate != null) { a = r; b = mate } else {
                val cls = (0 until g.n).groupBy { baseline[it] }.values.filter { it.size > 1 }.minByOrNull { it.min() }
                if (cls != null) { a = cls.sorted()[0]; b = cls.sorted()[1] }
            }
        }
        say("[${el()}] PI: ${baseline.toHashSet().size} classes, non-singleton: ${classes.size}, sizes ${classes.groupingBy { it.size }.eachCount().toSortedMap()}")
        val seedBase = LongArray(g.n) { sha64(baseline[it].serialize()) }
        fun seedWith(v: Int) = seedBase.copyOf().also { it[v] = mix64(it[v] xor 0x5EED5EEDL) }
        // pass 1: common round count
        var tRounds = 0
        val cap = g.n + 2
        for (c in classes) for (v in c) { val (_, st) = hashWl(g, seedWith(v), cap, stopWhenStable = true); tRounds = maxOf(tRounds, st) }
        say("[${el()}] common hash-WL round count T=$tRounds")
        res.n = g.n; res.m = g.m; res.piClasses = baseline.toHashSet().size; res.nonSingleton = classes.size
        res.classSizes = classes.groupingBy { it.size }.eachCount().toSortedMap().toString(); res.tRounds = tRounds
        // pass 2: per class, colours of class members under each individualisation
        val classOf = IntArray(g.n) { -1 }; classes.forEachIndexed { i, c -> for (v in c) classOf[v] = i }
        val posIn = IntArray(g.n) { -1 }; classes.forEach { c -> c.forEachIndexed { i, v -> posIn[v] = i } }
        val taus = ArrayList<List<IntArray>>()   // per class: list over targets s (position) of permutation of positions
        var unfaithful = 0
        var excludedTotal = 0
        for (c in classes) {
            val colOf = c.map { v -> val (col, _) = hashWl(g, seedWith(v), tRounds); LongArray(c.size) { col[c[it]] } }
            val base = colOf[0]
            val perms = mutableListOf<IntArray>()
            var ok = base.toSet().size == c.size
            var excluded = 0
            for (sIdx in c.indices) {
                val cs = colOf[sIdx]
                // colours on C under "s individualised" must be the same multiset as under "base
                // individualised", else NO automorphism sends base -> s: s is excluded (sound).
                if (cs.sorted() != base.sorted()) { excluded++; continue }
                val where = HashMap<Long, Int>().apply { cs.forEachIndexed { i, x -> put(x, i) } }
                perms.add(IntArray(c.size) { i -> where.getValue(base[i]) })
            }
            if (excluded > 0) excludedTotal += excluded
            if (!ok) {
                unfaithful++
                val split = base.toList().groupingBy { it }.eachCount().values.sortedDescending()
                say("   UNFAITHFUL class size ${c.size} ${c.toList()}: individualising base ${c[0]} splits it into blocks of sizes $split")
            }
            taus.add(if (ok) perms else emptyList())
        }
        say("[${el()}] candidate restrictions computed; UNFAITHFUL classes (base not split to singletons): $unfaithful; targets s excluded (no automorphism can send base -> s): $excludedTotal")
        res.unfaithful = unfaithful; res.excluded = excludedTotal
        if (unfaithful > 0) { say("-> not exact on this graph: stopping"); say("========================================================"); res.status = "STOP_UNFAITHFUL"; res.seconds = (System.currentTimeMillis() - t0) / 1000.0; return res }
        // group structure per class
        fun compose(p: IntArray, q: IntArray) = IntArray(p.size) { p[q[it]] }   // p after q
        val coords = ArrayList<Map<List<Int>, Long>>()   // per class: permutation -> bit vector (k <= 62)
        val kOf = IntArray(classes.size)
        var notGroup = 0
        for ((ci, perms) in taus.withIndex()) {
            val set = perms.map { it.toList() }.toSet()
            val id = List(perms[0].size) { it }
            val isGroup = id in set && perms.all { p -> perms.all { q -> compose(p, q).toList() in set } } &&
                perms.all { p -> compose(p, p).toList() == id } && perms.all { p -> perms.all { q -> compose(p, q).contentEquals(compose(q, p)) } }
            if (!isGroup) { notGroup++; coords.add(emptyMap()); continue }
            val span = LinkedHashMap<List<Int>, Long>().apply { put(id, 0L) }
            var k = 0
            for (p in perms) if (p.toList() !in span) {
                val add = span.entries.map { (q, v) -> compose(p, q.toIntArray()).toList() to (v or (1L shl k)) }
                for ((q, v) in add) span[q] = v
                k++
            }
            kOf[ci] = k; coords.add(span)
        }
        say("[${el()}] classes that are NOT elementary abelian 2-groups: $notGroup; GF(2) dims per class: ${kOf.toList().groupingBy { it }.eachCount().toSortedMap()}")
        res.notGroup = notGroup
        if (notGroup > 0) { say("-> not linear on this graph: stopping"); say("========================================================"); res.status = "STOP_NOT_ELEM_ABELIAN_2GROUP"; res.seconds = (System.currentTimeMillis() - t0) / 1000.0; return res }
        val offset = IntArray(classes.size); var nVars = 0
        for (i in classes.indices) { offset[i] = nVars; nVars += kOf[i] }
        val sys = Gf2System(nVars)
        // constraints per pair of classes joined by edges (singletons are fixed points)
        val pairEdges = HashMap<Pair<Int, Int>, MutableList<Pair<Int, Int>>>()
        var fixedMismatch = 0
        for (u in 0 until g.n) for (w in g.adj[u]) if (u < w) {
            val cu = classOf[u]; val cw = classOf[w]
            if (cu < 0 && cw < 0) continue
            val key = if (cu <= cw) cu to cw else cw to cu
            pairEdges.getOrPut(key) { mutableListOf() }.add(if (cu <= cw) u to w else w to u)
        }
        var nonSubgroup = 0
        for ((key, es) in pairEdges) {
            val (c1, c2) = key
            val edgeSet = es.map { (x, y) -> minOf(x, y) to maxOf(x, y) }.toHashSet()
            val list1: List<Pair<List<Int>, Long>> = if (c1 >= 0) coords[c1].entries.map { it.key to it.value } else listOf(emptyList<Int>() to 0L)
            val list2: List<Pair<List<Int>, Long>> = if (c2 >= 0 && c2 != c1) coords[c2].entries.map { it.key to it.value } else listOf(emptyList<Int>() to 0L)
            val allowed = mutableListOf<Long>()
            val k1 = if (c1 >= 0) kOf[c1] else 0
            for ((p1, v1) in list1) for ((p2, v2) in list2) {
                val img = { x: Int -> val cx = classOf[x]
                    when { cx < 0 -> x; cx == c1 -> classes[c1][p1[posIn[x]]]; else -> classes[c2][p2[posIn[x]]] } }
                if (es.all { (x, y) -> val a2 = img(x); val b2 = img(y); (minOf(a2, b2) to maxOf(a2, b2)) in edgeSet }) allowed.add(v1 or (v2 shl k1))
            }
            val mBits = k1 + (if (c2 >= 0 && c2 != c1) kOf[c2] else 0)
            val aset = allowed.toHashSet()
            if (aset.isEmpty()) { fixedMismatch++; continue }
            val isSub = 0L in aset && aset.all { x -> aset.all { y -> (x xor y) in aset } }
            if (!isSub) { nonSubgroup++; continue }
            // dual: all y with parity(y & x) = 0 for all x in S; add a basis of them as equations
            val dualBasis = mutableListOf<Long>()
            val spanD = hashSetOf(0L)
            for (y in 1L until (1L shl mBits)) {
                if (y in spanD) continue
                if (aset.all { x -> java.lang.Long.bitCount(x and y) % 2 == 0 }) {
                    dualBasis.add(y); spanD.addAll(spanD.map { it xor y })
                }
            }
            for (y in dualBasis) {
                val row = LongArray(sys.words)
                for (bit in 0 until mBits) if ((y shr bit) and 1L == 1L) {
                    val varIdx = if (bit < k1) offset[c1] + bit else offset[c2] + (bit - k1)
                    row[varIdx / 64] = row[varIdx / 64] or (1L shl (varIdx % 64))
                }
                sys.add(row, false)
            }
        }
        say("[${el()}] variables: $nVars, equations: ${sys.rows.size}; class pairs with NO allowed combination: $fixedMismatch; non-subgroup constraints: $nonSubgroup")
        res.nonSubgroup = nonSubgroup; res.nVars = nVars; res.nEqs = sys.rows.size
        if (nonSubgroup > 0) { say("-> not linear on this graph: stopping"); say("========================================================"); res.status = "STOP_NON_SUBGROUP"; res.seconds = (System.currentTimeMillis() - t0) / 1000.0; return res }
        val (rank, _, _) = sys.solve()
        say("[${el()}] rank=$rank -> solution space dimension ${nVars - rank} -> |Aut(G)| = 2^${nVars - rank}")
        res.autLog2 = nVars - rank
        val traces = if (crossCheck && g.n <= 2500) traces.certifyAll(g, listOf(IntArray(g.n) { it }), getcanon = false).stats.autOrder else null
        if (traces != null) say("   cross-check: Traces |Aut| = ${"%.6g".format(traces)}")
        if (a != null && b != null) {
            val ca = classOf[a]
            res.query = "$a->$b"
            if (ca < 0 || classOf[b] != ca) { say("orbit query $a -> $b: not in the same PI class -> NOT orbit-mates"); res.queryVerdict = "NOT_SAME_PI_CLASS" }
            else {
                val entry = coords[ca].entries.firstOrNull { (p, _) -> classes[ca][p[posIn[a]]] == b }
                if (entry == null) { say("orbit query $a -> $b: no candidate restriction sends $a to $b -> NOT orbit-mates"); res.queryVerdict = "NOT_ORBIT_MATES(excluded)" }
                else {
                    val q = Gf2System(nVars); q.rows.addAll(sys.rows)
                    for (bit in 0 until kOf[ca]) {
                        val row = LongArray(q.words); val vi = offset[ca] + bit
                        row[vi / 64] = row[vi / 64] or (1L shl (vi % 64))
                        q.add(row, (entry.value shr bit) and 1L == 1L)
                    }
                    val (_, consistent, sol) = q.solve()
                    say("orbit query $a -> $b: parity system ${if (consistent) "SOLVABLE -> orbit-mates" else "INCONSISTENT -> NOT orbit-mates"}")
                    res.queryVerdict = if (consistent) "ORBIT_MATES" else "NOT_ORBIT_MATES"
                    if (consistent && sol != null) {
                        val sigma = IntArray(g.n) { it }
                        for ((ci, c) in classes.withIndex()) {
                            var v = 0L; for (bit in 0 until kOf[ci]) if (sol[offset[ci] + bit]) v = v or (1L shl bit)
                            val perm = coords[ci].entries.first { it.value == v }.key
                            for ((i, x) in c.withIndex()) sigma[x] = c[perm[i]]
                        }
                        val isAut = (0 until g.n).all { u -> g.adj[u].all { w -> g.adj[sigma[u]].contains(sigma[w]) } }
                        say("   explicit solution checked as an automorphism of G: $isAut; sigma($a) = ${sigma[a]}")
                        res.explicitAutOk = isAut
                    }
                }
            }
        }
        say("[${el()}] ========================================================")
        res.status = "EXACT"; res.seconds = (System.currentTimeMillis() - t0) / 1000.0
        return res
    }

    /**
     * Parity-equation campaign over one cfi-rigid family (env FAMILY, e.g. "r2"; CAP = max effective n,
     * default 5000; OUT = CSV path, appended). Instances sorted by size. Traces cross-check (uncoloured |Aut|) for n <= 2000 on a separate thread with a 60 s
     * timeout; after one timeout, cross-checks are disabled for the rest of the family (a native
     * Traces call cannot be interrupted). One CSV row per instance, flushed immediately.
     */
    @Test
    fun parityCampaign() {
        val family = System.getenv("FAMILY") ?: return
        val cap = System.getenv("CAP")?.toIntOrNull() ?: 5000
        val out = File(System.getenv("OUT") ?: File(System.getProperty("java.io.tmpdir"), "parity_campaign.csv").path)
        val dir = File(System.getenv("DIR")?.let { "graphs/$it" } ?: "graphs/cfi-rigid-$family")
        val filesAll = dir.walkTopDown().filter { it.isFile && !it.name.startsWith(".") }.mapNotNull { f ->
            try { val h = f.bufferedReader().use { it.readLine() }?.trim()?.split(Regex("\\s+")) ?: return@mapNotNull null
                  if (h.size < 4 || h[0] != "p") null else Triple(f, h[2].toInt(), h[3].toInt()) } catch (e: Exception) { null }
        }.sortedWith(compareBy({ it.second }, { it.first.name })).toList()
        val lim = System.getenv("LIMIT")?.toIntOrNull()
        // 2026-10-01: INSTANCES (comma list) or INSTANCES_FILE (one name per line) restrict the run BEFORE any graph is
        // loaded -- the size filter below loads every candidate file, which a per-instance JVM must not pay each time
        val onlyList = (System.getenv("INSTANCES")?.split(",") ?: emptyList()) +
            (System.getenv("INSTANCES_FILE")?.let { File(it).readLines() } ?: emptyList())
        val onlySet = onlyList.map { it.trim() }.filter { it.isNotEmpty() }.toHashSet()
        val underCap = (if (onlySet.isEmpty()) filesAll else filesAll.filter { it.first.name in onlySet }).filter { (f, n0, m0) -> val g0 = GraphIO.loadDimacs(f.toPath()); (if (g0.bipartition() != null) n0 else n0 + m0) <= cap }
        val files = if (lim == null || underCap.size <= lim) underCap else (0 until lim).map { underCap[it * (underCap.size - 1) / (lim - 1)] }.distinct()
        val deadlineMs = System.getenv("DEADLINE_S")?.toLongOrNull()?.let { it * 1000 } ?: Long.MAX_VALUE
        val done = if (out.exists()) out.readLines().drop(1).map { it.split(",")[1] }.toHashSet() else hashSetOf()
        if (!out.exists()) out.writeText("family,instance,n_orig,m_orig,n,m,pi_classes,nonsingleton,class_sizes,T,excluded,unfaithful,not_group,non_subgroup,vars,eqs,aut_log2,traces_aut,agree,query,query_verdict,explicit_aut_ok,status,seconds,orbits,enumerated_auts,enumerated_all_verified,orbits_original,stop_detail,max_base,max_T,max_pair,dfs_nodes\n")
        val only: Set<String>? = onlySet.ifEmpty { null }
        var tracesDisabled = System.getenv("NO_TRACES") == "1"   // resume runs: an abandoned native Traces call can exhaust the memcap
        val pool = java.util.concurrent.Executors.newSingleThreadExecutor { r -> Thread(r).apply { isDaemon = true } }
        for ((f, n0, m0) in files) {
            if (f.name in done) continue
            if (only != null && only != setOf("") && f.name !in only) continue
            val g0 = GraphIO.loadDimacs(f.toPath())
            val eff = if (g0.bipartition() != null) g0.n else g0.n + g0.m
            if (eff > cap) continue
            val r = try { when (System.getenv("SOLVER")) {
                "gfp" -> parityEquationsGFp(f.path, null, null, quiet = true, crossCheck = false)
                "z3" -> parityEquationsZ3(f.path, null, null, quiet = true, crossCheck = false)
                "series" -> parityEquationsSeries(f.path, null, null, quiet = true, crossCheck = false)
                "seriespi" -> parityEquationsSeries(f.path, null, null, quiet = true, crossCheck = false, usePi = true)
                "seriescanon" -> parityEquationsSeries(f.path, null, null, quiet = true, crossCheck = false, computeOrbits = true, piCanonicalCopy = true)
                "seriesgen" -> parityEquationsSeries(f.path, null, null, quiet = true, crossCheck = false, computeOrbits = true, usePi = true, deadlineMs = deadlineMs)
                "seriesgenp" -> parityEquationsSeries(f.path, null, null, quiet = true, crossCheck = false, computeOrbits = true, usePi = true, deadlineMs = deadlineMs, generalPrimes = true)
                "seriesfull" -> {
                    fun series(usePiArg: Boolean, dlArg: Long) = parityEquationsSeries(f.path, null, null, quiet = true, crossCheck = false, computeOrbits = false,
                    // SERIES_COLOUR=wl1 (Christos, 2026-10-01): start from canonical 1-WL instead of PI -- enough on cfi-rigid
                    // t2/s2, where PI was nearly all of the time
                    usePi = usePiArg, deadlineMs = dlArg, generalPrimes = true, cosetMode = true,
                    irFallback = System.getenv("IR_FALLBACK") != "0", maxCandidates = System.getenv("MAX_CAND")?.toIntOrNull() ?: 20_000,
                    // count budgets, env-overridable for large machines (2026-09-29): base length, DFS nodes, pair-table size
                    maxBase = System.getenv("MAX_BASE")?.toIntOrNull() ?: 12, maxNodes = System.getenv("MAX_NODES")?.toIntOrNull() ?: 200_000,
                    maxPairTable = System.getenv("MAX_PAIR")?.toLongOrNull() ?: 3_000_000L,
                    solveOnOriginal = System.getenv("ORIGINAL") != "0", nonSolvableStage = System.getenv("NONSOLV") != "0")
                    val colourMode = System.getenv("SERIES_COLOUR") ?: "pi"
                    if (colourMode != "auto") series(colourMode != "wl1", deadlineMs)
                    else {
                        // COLOUR=auto (2026-10-02, paper sec:when): probe from plain 1-WL; escalate to PI only when the solver
                        // stops because individualising a short base does not break a class (STOP_BASE_TOO_LONG) or on the
                        // budget; a STOP_TOO_MANY_CANDIDATES / not-solvable stop means genuine symmetry, where PI equals 1-WL
                        // in practice, so it goes to the chain without paying for PI. The decision and the probe time are
                        // recorded in stop_detail ("auto: ..."), seconds = probe + PI attempt.
                        val probeMs = System.getenv("PROBE_S")?.toLongOrNull()?.let { it * 1000 } ?: deadlineMs
                        val t0p = System.currentTimeMillis()
                        val r1 = series(false, probeMs)
                        val probeS = (System.currentTimeMillis() - t0p) / 1000.0
                        val escalate = r1.status.startsWith("STOP_BASE_TOO_LONG") || r1.status == "STOP_TIME"
                        if (r1.status == "EXACT") r1.also { it.stopDetail = "auto: 1-WL exact (probe ${probeS}s)" }
                        else if (!escalate) r1.also { it.stopDetail = "auto: 1-WL ${it.status} after ${probeS}s, no escalation | ${it.stopDetail}" }
                        else {
                            // 2026-10-02: compute PI first and compare its class count with refinement's (PI only splits classes
                            // of the stable colouring, so equal counts = equal partitions). Equal: a second solve would stop
                            // exactly as the probe did (same input, deterministic), so go to the chain at once -- on planes, ag,
                            // pg the probe stops on time and PI changes nothing (measured: pp lost 300 s per instance).
                            val t0pi = System.currentTimeMillis()
                            val piCol = try { piProjected(GraphIO.loadDimacs(f.toPath())) } catch (e: Throwable) { System.gc(); null }
                            val piCount = piCol?.toHashSet()?.size ?: -1
                            val piS = (System.currentTimeMillis() - t0pi) / 1000.0
                            if (piCount == r1.piClasses) r1.also { it.stopDetail = "auto: PI equals refinement ($piCount classes, ${piS}s), no second solve; 1-WL ${it.status} after ${probeS}s | ${it.stopDetail}"; it.seconds += piS }
                            else {
                                // PI can fail (out of memory on large dense graphs, e.g. had-sw-112): keep the probe's result then
                                val r2 = if (piCol == null) null else try { piOverride = piCol; series(true, deadlineMs) } catch (e: Throwable) { System.gc(); null } finally { piOverride = null }
                                if (r2 == null || r2.status.startsWith("ERROR")) r1.also { it.stopDetail = "auto: escalation to PI failed (${r2?.stopDetail ?: "out of memory"}), 1-WL ${it.status} after ${probeS}s | ${it.stopDetail}"; it.seconds += piS }
                                else r2.also { it.stopDetail = "auto: escalated to PI after 1-WL ${r1.status} in ${probeS}s" + (if (it.stopDetail.isNotBlank()) " | ${it.stopDetail}" else ""); it.seconds += probeS + piS }
                            }
                        }
                    }
                }
                else -> parityEquations(f.path, null, null, quiet = true, crossCheck = false) } } catch (e: Throwable) {
                // 2026-10-01: report the ROOT cause (an ExecutionException only wraps a worker thread's error) and the stack
                var root: Throwable = e; while (root.cause != null && root.cause !== root) root = root.cause!!
                System.err.println("ERROR on ${f.name}: ${e.javaClass.simpleName} <- root cause ${root.javaClass.name}: ${root.message}")
                root.printStackTrace()
                ParityResult().also { it.status = "ERROR_${e.javaClass.simpleName}"; it.stopDetail = "root cause ${root.javaClass.simpleName}: ${root.message?.take(200)}" } }
            var tracesAut = ""
            if (!tracesDisabled && r.status.startsWith("EXACT") && r.n in 1..2000) {
                val g = if (System.getenv("SOLVER") == "seriesfull" && System.getenv("ORIGINAL") != "0") GraphIO.loadDimacs(f.toPath()) else loadForTrace(f.path)
                val fut = pool.submit<Double> { traces.certifyAll(g, listOf(IntArray(g.n) { it }), getcanon = false).stats.autOrder }
                tracesAut = try { fut.get(60, java.util.concurrent.TimeUnit.SECONDS).toString() } catch (e: java.util.concurrent.TimeoutException) {
                    tracesDisabled = true; "TIMEOUT" }
            }
            val ourAut = r.autOrder ?: r.autLog2?.let { Math.pow(2.0, it.toDouble()) }
            val agree = if (ourAut != null && tracesAut.isNotEmpty() && tracesAut != "TIMEOUT")
                (Math.abs(ourAut - tracesAut.toDouble()) <= 1e-9 * maxOf(1.0, Math.abs(ourAut))).toString() else ""
            val row = listOf(family, f.name, n0, m0, r.n, r.m, r.piClasses, r.nonSingleton, "\"${r.classSizes}\"", r.tRounds, r.excluded, r.unfaithful,
                r.notGroup, r.nonSubgroup, r.nVars, r.nEqs, if (r.autStr.isNotEmpty()) r.autStr else (r.autLog2 ?: ""), tracesAut, agree, r.query, r.queryVerdict, r.explicitAutOk ?: "", r.status, r.seconds, r.orbits ?: "", r.enumeratedAuts, r.enumeratedAllVerified ?: "", r.orbitsOriginal ?: "", "\"" + r.stopDetail.replace("\"", "'") + "\"", r.maxBaseLen, r.maxT, r.maxPairTable, r.dfsNodes)
            out.appendText(row.joinToString(",") + "\n")
            println("CAMPAIGN $family ${f.name}: ${r.status} aut=2^${r.autLog2} traces=$tracesAut agree=$agree query=${r.query} ${r.queryVerdict} ${r.seconds}s")
        }
    }

    // ─────────────────────────── parity equations over GF(p), p in {2, 3} ───────────────────────────

    /** Exactly [rounds] rounds of the same canonical hash-1-WL as [hashWl] (neighbour hashes mixed
     *  once per vertex per round -- identical values, n mixes instead of 2m). */
    internal fun hashWlRounds(g: Graph, seed: LongArray, rounds: Int): LongArray {
        work += rounds.toLong() * (g.n + adjTotal(g))
        var col = seed.copyOf()
        val mixed = LongArray(g.n)
        repeat(rounds) {
            for (v in 0 until g.n) mixed[v] = mix64(col[v])
            val next = LongArray(g.n)
            for (v in 0 until g.n) { var sum = 0L; for (w in g.adj[v]) sum += mixed[w]; next[v] = mix64(col[v] * 0x9E3779B97F4A7C15uL.toLong() + sum) }
            col = next
        }
        return col
    }

    /** Round at which the partition of [hashWlRounds] stops changing (first r with #classes(r) == #classes(r-1)). */
    internal fun hashWlStableRound(g: Graph, seed: LongArray, cap: Int): Int {
        val perRound = g.n + adjTotal(g)
        var col = seed.copyOf()
        var classes = col.toHashSet().size
        val mixed = LongArray(g.n)
        for (r in 1..cap) {
            work += perRound
            for (v in 0 until g.n) mixed[v] = mix64(col[v])
            val next = LongArray(g.n)
            for (v in 0 until g.n) { var sum = 0L; for (w in g.adj[v]) sum += mixed[w]; next[v] = mix64(col[v] * 0x9E3779B97F4A7C15uL.toLong() + sum) }
            col = next
            val c = col.toHashSet().size
            if (c == classes) return r
            classes = c
        }
        return cap
    }

    /** Dense Gaussian elimination mod a prime [p]. Rows = coefficient IntArray (length nVars) + rhs. */
    private class ModPSystem(val p: Int, val nVars: Int) {
        val rows = mutableListOf<Pair<IntArray, Int>>()
        fun add(coeff: IntArray, rhs: Int) { rows.add(coeff to ((rhs % p) + p) % p) }
        private fun inv(a: Int): Int { var r = 1; repeat(p - 2) { r = r * a % p }; return r }   // Fermat
        fun solve(): Triple<Int, Boolean, IntArray?> {
            val m = rows.map { it.first.copyOf() to it.second }.toMutableList()
            val pivotCol = IntArray(m.size) { -1 }
            var rank = 0
            for (col in 0 until nVars) {
                val piv = (rank until m.size).firstOrNull { m[it].first[col] != 0 } ?: continue
                val t = m[piv]; m[piv] = m[rank]; m[rank] = t
                val iv = inv(m[rank].first[col])
                val pr = m[rank].first; for (j in 0 until nVars) pr[j] = pr[j] * iv % p
                m[rank] = pr to (m[rank].second * iv % p)
                for (i in m.indices) if (i != rank && m[i].first[col] != 0) {
                    val f = m[i].first[col]; val a = m[i].first
                    for (j in 0 until nVars) if (pr[j] != 0) a[j] = ((a[j] - f * pr[j]) % p + p) % p
                    m[i] = a to (((m[i].second - f * m[rank].second) % p + p) % p)
                }
                pivotCol[rank] = col; rank++
            }
            val consistent = (rank until m.size).none { i -> m[i].second != 0 && m[i].first.all { it == 0 } }
            if (!consistent) return Triple(rank, false, null)
            val x = IntArray(nVars)
            for (i in 0 until rank) x[pivotCol[i]] = m[i].second
            lastRref = m.take(rank).map { it.first }; lastPivots = pivotCol.take(rank); lastRhs = m.take(rank).map { it.second }
            return Triple(rank, true, x)
        }
        private var lastRref: List<IntArray> = emptyList(); private var lastPivots: List<Int> = emptyList(); private var lastRhs: List<Int> = emptyList()
        /** Rank/consistency of (this system after a consistent [solve]) + [extra] rows, without redoing the
         *  base elimination: extra rows are reduced against the stored RREF, then eliminated among themselves. */
        fun extend(extra: List<Pair<IntArray, Int>>): Pair<Int, Boolean> {
            val red = extra.map { (row0, rhs0) ->
                val row = row0.copyOf(); var rhs = ((rhs0 % p) + p) % p
                for ((i, pc) in lastPivots.withIndex()) { val f = row[pc]; if (f != 0) { val pr = lastRref[i]; for (j in 0 until nVars) if (pr[j] != 0) row[j] = ((row[j] - f * pr[j]) % p + p) % p; rhs = ((rhs - f * lastRhs[i]) % p + p) % p } }
                row to rhs
            }
            val small = ModPSystem(p, nVars); for ((r, h) in red) small.add(r, h)
            val (r2, ok, _) = small.solve()
            return (lastPivots.size + r2) to ok
        }
        /** Basis of the homogeneous solution space (call after a consistent [solve]). */
        fun nullBasis(): List<IntArray> {
            val pivots = lastPivots.toHashSet()
            return (0 until nVars).filter { it !in pivots }.map { free ->
                val v = IntArray(nVars); v[free] = 1
                for ((i, pc) in lastPivots.withIndex()) v[pc] = ((-lastRref[i][free]) % p + p) % p
                v
            }
        }
    }

    /** One class's candidate group T_C over GF(p)^k: permutation (positions in C) <-> coordinates. */
    private class ClassGroup(val p: Int, val k: Int, val perms: List<List<Int>>, val coordOf: Map<List<Int>, IntArray>) {
        fun permOf(x: IntArray): List<Int> = perms.first { coordOf.getValue(it).contentEquals(x) }
    }

    /** Dual (annihilator) basis of a set S of vectors in GF(p)^m: all y with y.x = 0 (mod p) for x in S,
     *  reduced to a linearly independent basis. Enumerates p^m candidates (m is tiny here). */
    /** Reduced row basis of span(S) over GF(p), built incrementally (at most m rows kept): O(|S| m^2). */
    private fun rowBasis(p: Int, m: Int, s: Collection<IntArray>): List<IntArray> {
        val basisRows = mutableListOf<IntArray>(); val pivotOf = mutableListOf<Int>()
        if (m == 0) return basisRows
        for (x0 in s) {
            val x = IntArray(m) { ((x0[it] % p) + p) % p }
            for ((bi, br) in basisRows.withIndex()) { val pc = pivotOf[bi]; val f = x[pc]; if (f != 0) for (j in 0 until m) x[j] = ((x[j] - f * br[j]) % p + p) % p }
            val pc = (0 until m).firstOrNull { x[it] != 0 } ?: continue
            var inv = 1; repeat(p - 2) { inv = inv * x[pc] % p }
            for (j in 0 until m) x[j] = x[j] * inv % p
            for (br in basisRows) { val f = br[pc]; if (f != 0) for (j in 0 until m) br[j] = ((br[j] - f * x[j]) % p + p) % p }
            basisRows.add(x); pivotOf.add(pc)
            if (basisRows.size == m) break
        }
        return basisRows
    }

    private fun dualBasis(p: Int, m: Int, s: Collection<IntArray>): List<IntArray> {
        // Annihilator of span(S) in GF(p)^m = null space of the matrix whose rows are the vectors of S.
        if (m == 0) return emptyList()
        val sys = ModPSystem(p, m)
        for (x in rowBasis(p, m, s)) sys.add(x, 0)   // at most m rows: a huge S costs O(|S| m^2)
        val (_, ok, _) = sys.solve()
        check(ok) { "homogeneous system cannot be inconsistent" }
        return sys.nullBasis()
    }

    /** The old brute-force dual (kept only for the regression check against [dualBasis]). */
    private fun dualBasisBrute(p: Int, m: Int, s: Collection<IntArray>): List<IntArray> {
        val basis = mutableListOf<IntArray>()
        val total = Math.pow(p.toDouble(), m.toDouble()).toInt()
        val sys = ModPSystem(p, m)
        for (code in 1 until total) {
            val y = IntArray(m); var c = code; for (i in 0 until m) { y[i] = c % p; c /= p }
            if (s.any { x -> (0 until m).sumOf { x[it] * y[it] } % p != 0 }) continue
            val trial = ModPSystem(p, m); trial.rows.addAll(sys.rows); trial.add(y, 0)
            if (trial.solve().first > sys.solve().first) { sys.add(y, 0); basis.add(y) }
        }
        return basis
    }

    /**
     * GF(p) generalisation of [parityEquations] (Christos, 2026-09-26, for d3/z3's Z3 gadgets):
     * - per PI class a BASE SEQUENCE b1, b2, ... is individualised (distinct marks per position) until
     *   the class splits into singletons; candidate restrictions are indexed by the images of the base
     *   sequence, pruned level by level (an image prefix must reproduce the base prefix's colour multiset
     *   on C and give the next image the base's next colour). Each run uses the base prefix's own
     *   stable round count -- isomorphic runs agree round by round, so this is sound AND complete.
     * - T_C (the candidate restrictions) must be an elementary abelian p-group, p in {2, 3}.
     * - pair constraints: same prime -> subgroup of GF(p)^(k1+k2), dual -> equations; different primes
     *   -> must be a product A x B (checked), giving unary subgroup constraints on each side.
     * - one GF(p) system per prime; |Aut| = prod p^(dim_p). Orbit query a -> b: the candidates sending
     *   a to b form a coset x0 + H (H = stabiliser of a in T_C) -> affine equations y.x = y.x0, y in dual(H).
     * Stops (never guesses) when a check fails.
     */
    private fun parityEquationsGFp(path: String, aIn: Int?, bIn: Int?, quiet: Boolean = false, crossCheck: Boolean = true): ParityResult {
        val res = ParityResult()
        val say: (String) -> Unit = { if (!quiet) println(it) }
        val t0 = System.currentTimeMillis()
        val el = { "${(System.currentTimeMillis() - t0) / 1000.0}s" }
        fun stop(status: String): ParityResult { res.status = status; res.seconds = (System.currentTimeMillis() - t0) / 1000.0; say("-> $status"); return res }
        val g = loadForTrace(path)
        val baseline = dispatchColouring(g).colouring
        val classes = (0 until g.n).groupBy { baseline[it] }.values.map { it.sorted().toIntArray() }.filter { it.size > 1 }
        res.n = g.n; res.m = g.m; res.piClasses = baseline.toHashSet().size; res.nonSingleton = classes.size
        res.classSizes = classes.groupingBy { it.size }.eachCount().toSortedMap().toString()
        say("==== $path -- GF(p) PARITY EQUATIONS (n=${g.n} m=${g.m}) ====")
        say("[${el()}] PI: ${res.piClasses} classes, non-singleton ${classes.size}, sizes ${res.classSizes}")
        var a = aIn; var b = bIn
        if (a == null && b == null) {
            val (sub0, _) = g.induced(IntArray(g.n) { it })
            val r = dialysis.decomposition.defaultRootRule(sub0, baseline)
            val mate = (0 until g.n).firstOrNull { it != r && baseline[it] == baseline[r] }
            if (mate != null) { a = r; b = mate } else classes.minByOrNull { it.min() }?.let { a = it[0]; b = it[1] }
        }
        val seedBase = LongArray(g.n) { sha64(baseline[it].serialize()) }
        fun seedFor(tuple: List<Int>) = seedBase.copyOf().also { s -> tuple.forEachIndexed { i, v -> s[v] = mix64(s[v] xor (0x5EED0000L + i)) } }
        val cap = g.n + 2
        val classOf = IntArray(g.n) { -1 }; classes.forEachIndexed { i, c -> for (v in c) classOf[v] = i }
        val posIn = IntArray(g.n) { -1 }; classes.forEach { c -> c.forEachIndexed { i, v -> posIn[v] = i } }

        // 1. candidate restrictions per class
        val groups = ArrayList<ClassGroup>()
        var maxBase = 0; var excluded = 0
        for (c in classes) {
            val base = mutableListOf(c[0])
            val prefT = mutableListOf<Int>(); val prefCol = mutableListOf<LongArray>()   // per depth d: T and colours on C
            while (true) {
                val sd = seedFor(base); val t = hashWlStableRound(g, sd, cap); val col = hashWlRounds(g, sd, t)
                prefT.add(t); prefCol.add(LongArray(c.size) { col[c[it]] })
                val blocks = c.indices.groupBy { prefCol.last()[it] }
                if (blocks.values.all { it.size == 1 }) break
                if (base.size >= 4) { res.unfaithful++; break }
                base.add(c[blocks.values.first { it.size > 1 }.min()])
            }
            if (res.unfaithful > 0) return stop("STOP_BASE_TOO_LONG (class ${c.toList()})")
            maxBase = maxOf(maxBase, base.size)
            val depth = base.size
            val sortedPref = prefCol.map { it.sorted() }
            val perms = mutableListOf<List<Int>>()
            fun dfs(tuple: MutableList<Int>) {
                val d = tuple.size
                if (d > 0) {
                    val col = hashWlRounds(g, seedFor(tuple), prefT[d - 1]); val onC = LongArray(c.size) { col[c[it]] }
                    if (onC.sorted() != sortedPref[d - 1]) { excluded++; return }
                    if (d == depth) {
                        val where = HashMap<Long, Int>().apply { onC.forEachIndexed { i, x -> put(x, i) } }
                        perms.add(List(c.size) { i -> where.getValue(prefCol[depth - 1][i]) }); return
                    }
                    // next image must have, under this prefix, the colour the base's next vertex has under the base prefix
                    val want = prefCol[d - 1][posIn[base[d]]]
                    for (i in c.indices) if (onC[i] == want && c[i] !in tuple) { tuple.add(c[i]); dfs(tuple); tuple.removeAt(tuple.size - 1) }
                } else for (s in c) { tuple.add(s); dfs(tuple); tuple.removeAt(tuple.size - 1) }
            }
            dfs(mutableListOf())
            // group structure
            val set = perms.toSet()
            val id = List(c.size) { it }
            fun comp(x: List<Int>, y: List<Int>) = List(x.size) { x[y[it]] }
            val order = set.size
            val p = when { order == 1 -> 2; Integer.bitCount(order) == 1 -> 2; generateSequence(1) { it * 3 }.takeWhile { it <= order }.last() == order -> 3; else -> 0 }
            fun pow(x: List<Int>, e: Int): List<Int> { var r = id; repeat(e) { r = comp(x, r) }; return r }
            val ok = p != 0 && id in set && set.all { x -> set.all { y -> comp(x, y) in set && comp(x, y) == comp(y, x) } } && set.all { pow(it, p) == id }
            if (!ok) { res.notGroup++; say("   class ${c.toList()}: candidate set of size $order is NOT an elementary abelian 2- or 3-group"); continue }
            val coord = LinkedHashMap<List<Int>, IntArray>().apply { put(id, IntArray(0)) }
            var k = 0
            for (x in set) if (x !in coord) {
                val old = coord.entries.toList(); coord.clear()
                for (e in 0 until p) { val xe = pow(x, e); for ((h, v) in old) coord[comp(xe, h)] = v + e }
                k++
            }
            val full = coord.mapValues { (_, v) -> if (v.size == k) v else v + IntArray(k - v.size) }
            groups.add(ClassGroup(p, k, set.toList(), full))
        }
        res.excluded = excluded
        say("[${el()}] candidate groups built; longest base sequence $maxBase; excluded image prefixes $excluded; NOT elementary abelian: ${res.notGroup}")
        if (res.notGroup > 0) return stop("STOP_NOT_ELEM_ABELIAN_P_GROUP")
        say("   primes/dims: " + groups.groupingBy { "p=${it.p},k=${it.k}" }.eachCount().toSortedMap())

        // 2. variables per prime
        val offset = IntArray(classes.size); val nVarsP = HashMap<Int, Int>()
        for ((i, gr) in groups.withIndex()) if (gr.k > 0) { offset[i] = nVarsP.getOrDefault(gr.p, 0); nVarsP[gr.p] = offset[i] + gr.k }
        val systems = nVarsP.mapValues { (p, nv) -> ModPSystem(p, nv) }
        fun addEq(cls: Int, y: IntArray, rhs: Int, into: Map<Int, ModPSystem> = systems) {
            val gr = groups[cls]; val row = IntArray(nVarsP.getValue(gr.p)); for (j in 0 until gr.k) row[offset[cls] + j] = y[j]; into.getValue(gr.p).add(row, rhs)
        }
        // 3. pair constraints
        val pairEdges = HashMap<Pair<Int, Int>, MutableList<Pair<Int, Int>>>()
        for (u in 0 until g.n) for (w in g.adj[u]) if (u < w) {
            val cu = classOf[u]; val cw = classOf[w]
            if (cu < 0 && cw < 0) continue
            val key = if (cu <= cw) cu to cw else cw to cu
            pairEdges.getOrPut(key) { mutableListOf() }.add(u to w)
        }
        var nonSub = 0; var nonProduct = 0; var empty = 0
        for ((key, es) in pairEdges) {
            val (c1, c2) = key
            val edgeSet = es.map { (x, y) -> minOf(x, y) to maxOf(x, y) }.toHashSet()
            val g1 = if (c1 >= 0) groups[c1] else null
            val g2 = if (c2 >= 0 && c2 != c1) groups[c2] else null
            val l1 = g1?.perms ?: listOf(emptyList()); val l2 = g2?.perms ?: listOf(emptyList())
            val allowed = mutableListOf<Pair<List<Int>, List<Int>>>()
            for (p1 in l1) for (p2 in l2) {
                val img = { x: Int -> val cx = classOf[x]; when { cx < 0 -> x; cx == c1 -> classes[c1][p1[posIn[x]]]; else -> classes[c2][p2[posIn[x]]] } }
                if (es.all { (x, y) -> val u2 = img(x); val w2 = img(y); (minOf(u2, w2) to maxOf(u2, w2)) in edgeSet }) allowed.add(p1 to p2)
            }
            if (allowed.isEmpty()) { empty++; continue }
            val v1 = allowed.map { (p1, _) -> if (g1 != null) g1.coordOf.getValue(p1) else IntArray(0) }
            val v2 = allowed.map { (_, p2) -> if (g2 != null) g2.coordOf.getValue(p2) else IntArray(0) }
            val k1 = g1?.k ?: 0; val k2 = g2?.k ?: 0
            if (g1 != null && g2 != null && g1.p == g2.p) {
                val p = g1.p
                val vs = allowed.indices.map { v1[it] + v2[it] }
                val keys = vs.map { it.toList() }.toHashSet()
                val closed = IntArray(k1 + k2).toList() in keys && vs.all { x -> vs.all { y -> List(x.size) { (x[it] + y[it]) % p } in keys } }
                if (!closed) { nonSub++; continue }
                for (y in dualBasis(p, k1 + k2, vs)) {
                    val row = IntArray(nVarsP.getValue(p))
                    for (j in 0 until k1) row[offset[c1] + j] = y[j]; for (j in 0 until k2) row[offset[c2] + j] = y[k1 + j]
                    systems.getValue(p).add(row, 0)
                }
            } else {
                // different primes (or one side trivial): allowed must be the product of its projections
                val proj1 = v1.map { it.toList() }.toSet(); val proj2 = v2.map { it.toList() }.toSet()
                if (allowed.size != proj1.size * proj2.size) { nonProduct++; continue }
                for ((gr, cls, proj) in listOf(Triple(g1, c1, proj1), Triple(g2, c2, proj2))) {
                    if (gr == null || gr.k == 0) continue
                    val pv = proj.map { it.toIntArray() }
                    val closed = IntArray(gr.k).toList() in proj && pv.all { x -> pv.all { y -> List(gr.k) { (x[it] + y[it]) % gr.p } in proj } }
                    if (!closed) { nonSub++; continue }
                    for (y in dualBasis(gr.p, gr.k, pv)) addEq(cls, y, 0)
                }
            }
        }
        res.nonSubgroup = nonSub + nonProduct
        res.nVars = nVarsP.values.sum(); res.nEqs = systems.values.sumOf { it.rows.size }
        say("[${el()}] variables per prime $nVarsP, equations ${res.nEqs}; empty pair constraints $empty; non-subgroup $nonSub; non-product (mixed primes) $nonProduct")
        if (empty > 0) return stop("STOP_EMPTY_CONSTRAINT")
        if (res.nonSubgroup > 0) return stop("STOP_NON_SUBGROUP")

        // 4. solve
        val dims = systems.mapValues { (_, sys) -> sys.nVars - sys.solve().first }
        val autOrder = dims.entries.fold(1.0) { acc, (p, d) -> acc * Math.pow(p.toDouble(), d.toDouble()) }
        res.autLog2 = null
        res.autStr = if (dims.isEmpty()) "1" else dims.entries.joinToString("*") { (p, d) -> "$p^$d" }
        res.autOrder = autOrder
        say("[${el()}] |Aut(G)| = ${res.autStr} = ${"%.6g".format(autOrder)}")
        if (crossCheck && g.n <= 2500) say("   cross-check: Traces |Aut| = ${"%.6g".format(traces.certifyAll(g, listOf(IntArray(g.n) { it }), getcanon = false).stats.autOrder)}")

        // 5. orbit query
        if (a != null && b != null) {
            res.query = "$a->$b"
            val ca = classOf[a]
            if (ca < 0 || classOf[b] != ca) { res.queryVerdict = "NOT_SAME_PI_CLASS" }
            else {
                val gr = groups[ca]
                val toB = gr.perms.filter { classes[ca][it[posIn[a]]] == b }
                if (toB.isEmpty()) res.queryVerdict = "NOT_ORBIT_MATES(excluded)"
                else {
                    val x0 = gr.coordOf.getValue(toB[0])
                    val stab = gr.perms.filter { it[posIn[a]] == posIn[a] }.map { gr.coordOf.getValue(it) }
                    val q = systems.mapValues { (p, sys) -> ModPSystem(p, sys.nVars).also { it.rows.addAll(sys.rows) } }
                    if (gr.k > 0) for (y in dualBasis(gr.p, gr.k, stab)) addEq(ca, y, (0 until gr.k).sumOf { y[it] * x0[it] }, q)
                    val sols = q.mapValues { it.value.solve() }
                    val consistent = sols.values.all { it.second }
                    res.queryVerdict = if (consistent) "ORBIT_MATES" else "NOT_ORBIT_MATES"
                    if (consistent) {
                        val sigma = IntArray(g.n) { it }
                        for ((ci, c) in classes.withIndex()) {
                            val grc = groups[ci]
                            val x = if (grc.k == 0) IntArray(0) else IntArray(grc.k) { j -> sols.getValue(grc.p).third!![offset[ci] + j] }
                            val perm = grc.permOf(x)
                            for ((i, v) in c.withIndex()) sigma[v] = c[perm[i]]
                        }
                        res.explicitAutOk = sigma[a] == b && (0 until g.n).all { u -> g.adj[u].all { w -> g.adj[sigma[u]].contains(sigma[w]) } }
                    }
                }
            }
            say("orbit query ${res.query}: ${res.queryVerdict}${res.explicitAutOk?.let { " (explicit automorphism verified: $it)" } ?: ""}")
        }
        res.status = "EXACT"; res.seconds = (System.currentTimeMillis() - t0) / 1000.0
        say("[${el()}] ========================================================")
        return res
    }

    /** Candidate restrictions per PI class via base sequences (same construction as in
     *  [parityEquationsGFp]); returns null for a class needing a base longer than 4. */
    private fun candidateRestrictions(g: Graph, c: IntArray, seedFor: (List<Int>) -> LongArray, posIn: IntArray, cap: Int, excludedCounter: IntArray, maxBase: Int = 4,
                                      maxCandidates: Int = Int.MAX_VALUE, deadline: Long = Long.MAX_VALUE, baseRule: Int = 0): List<List<Int>>? {
        val base = mutableListOf(c[0])
        val prefT = mutableListOf<Int>(); val prefCol = mutableListOf<LongArray>()
        while (true) {
            val sd = seedFor(base); val t = hashWlStableRound(g, sd, cap); val col = hashWlRounds(g, sd, t)
            prefT.add(t); prefCol.add(LongArray(c.size) { col[c[it]] })
            val blocks = c.indices.groupBy { prefCol.last()[it] }
            if (blocks.values.all { it.size == 1 }) break
            if (base.size >= maxBase) return null
            // baseRule 0 (default): lowest vertex of the first non-singleton block. Retry rules, used only when rule 0
            // fails: 1 = LARGEST non-singleton block (on projective planes rule 0 picks collinear points and never
            // reaches a frame; the largest cell yields points in general position), 2 = smallest block. Any base is sound.
            val nonTriv = blocks.values.filter { it.size > 1 }
            base.add(c[(when (baseRule) { 1 -> nonTriv.maxBy { it.size }; 2 -> nonTriv.minBy { it.size }; else -> nonTriv.first() }).min()])
        }
        val depth = base.size; lastBaseLen = depth; lastBase = base.toList()
        val sortedPref = prefCol.map { it.sorted() }
        val perms = mutableListOf<List<Int>>()
        var nodes = 0L
        fun dfs(tuple: MutableList<Int>) {
            val d = tuple.size
            if (overBudget(deadline)) throw StopReason("STOP_TIME", "time budget exceeded while building candidates for a class of size ${c.size} (base length $depth)")
            if (++nodes > candidateNodeCap) throw StopReason("STOP_CANDIDATE_NODES", "class of size ${c.size}: more than $candidateNodeCap partial candidate maps (base length $depth)")
            if (perms.size > maxCandidates) throw StopReason("STOP_TOO_MANY_CANDIDATES", "class of size ${c.size}: more than $maxCandidates candidate restrictions (base length $depth)")
            if (d > 0) {
                val col = hashWlRounds(g, seedFor(tuple), prefT[d - 1]); val onC = LongArray(c.size) { col[c[it]] }
                if (onC.sorted() != sortedPref[d - 1]) { excludedCounter[0]++; return }
                if (d == depth) {
                    val where = HashMap<Long, Int>().apply { onC.forEachIndexed { i, x -> put(x, i) } }
                    perms.add(List(c.size) { i -> where.getValue(prefCol[depth - 1][i]) }); return
                }
                val want = prefCol[d - 1][posIn[base[d]]]
                for (i in c.indices) if (onC[i] == want && c[i] !in tuple) { tuple.add(c[i]); dfs(tuple); tuple.removeAt(tuple.size - 1) }
            } else for (s0 in c) { tuple.add(s0); dfs(tuple); tuple.removeAt(tuple.size - 1) }
        }
        dfs(mutableListOf())
        return perms.distinct()
    }

    /**
     * Isomorphism-invariant candidate restrictions (Christos, 2026-09-28: a solver STOP must not depend on vertex
     * numbering, so it can serve as a slice invariant without Traces). [candidateRestrictions] starts its base at the
     * lowest-numbered member and extends it with the lowest-numbered member of the first split block; on had-sw-20's
     * slice graphs that made the outcome (EXACT vs STOP_NOT_A_GROUP) differ between isomorphic copies.
     *
     * Here the base FAMILY is canonical: the first base vertex ranges over all of C, and each extension ranges over all
     * members of the first non-singleton block in canonical colour order (the hash colours are canonical functions of
     * (g, seed) up to isomorphism). T_C is computed for every sequence of the family, as a set of vertex maps of C; if
     * the sets differ the class stops with STOP_BASE_DEPENDENT. Every stop condition (family size, base length,
     * candidate count, DFS nodes, disagreement) is a function of the graph up to isomorphism. Polynomial for fixed caps.
     */
    private fun candidateRestrictionsInvariant(g: Graph, c: IntArray, seedFor: (List<Int>) -> LongArray, posIn: IntArray, cap: Int,
                                               excludedCounter: IntArray, maxBase: Int, maxCandidates: Int): List<List<Int>> {
        val familyCap = maxOf(64, 4 * c.size)
        val family = mutableListOf<List<Int>>()
        fun grow(base: List<Int>) {
            val sd = seedFor(base); val t = hashWlStableRound(g, sd, cap); val col = hashWlRounds(g, sd, t)
            val blocks = c.indices.groupBy { col[c[it]] }
            if (blocks.values.all { it.size == 1 }) {
                family.add(base)
                if (family.size > familyCap) throw StopReason("STOP_BASE_FAMILY", "class of size ${c.size}: more than $familyCap canonical base sequences")
                return
            }
            if (base.size >= maxBase) throw StopReason("STOP_BASE_TOO_LONG(>$maxBase)", "class of size ${c.size}: individualising $maxBase base vertices does not split it")
            val next = blocks.entries.filter { it.value.size > 1 }.minBy { it.key }.value
            for (i in next) grow(base + c[i])
        }
        for (b in c) grow(listOf(b))
        lastBaseLen = family.maxOf { it.size }
        var tc: Set<List<Int>>? = null
        for (beta in family) {
            val t = candidatesForBase(g, c, seedFor, posIn, cap, excludedCounter, beta, maxCandidates).toSet()
            if (tc == null) tc = t
            else if (t != tc) throw StopReason("STOP_BASE_DEPENDENT", "class of size ${c.size}: candidate sets differ between canonical base sequences (|T| ${tc.size} vs ${t.size})")
        }
        return tc!!.toList()
    }

    /** The DFS of [candidateRestrictions] for a GIVEN base sequence [base] (all members of [c]); same exclusion rule. */
    private fun candidatesForBase(g: Graph, c: IntArray, seedFor: (List<Int>) -> LongArray, posIn: IntArray, cap: Int,
                                  excludedCounter: IntArray, base: List<Int>, maxCandidates: Int): List<List<Int>> {
        val prefT = ArrayList<Int>(); val prefCol = ArrayList<LongArray>()
        for (k in 1..base.size) {
            val sd = seedFor(base.subList(0, k)); val t = hashWlStableRound(g, sd, cap); val col = hashWlRounds(g, sd, t)
            prefT.add(t); prefCol.add(LongArray(c.size) { col[c[it]] })
        }
        val depth = base.size
        val sortedPref = prefCol.map { it.sorted() }
        val perms = mutableListOf<List<Int>>()
        var nodes = 0L
        fun dfs(tuple: MutableList<Int>) {
            val d = tuple.size
            if (++nodes > candidateNodeCap) throw StopReason("STOP_CANDIDATE_NODES", "class of size ${c.size}: more than $candidateNodeCap partial candidate maps (base length $depth)")
            if (perms.size > maxCandidates) throw StopReason("STOP_TOO_MANY_CANDIDATES", "class of size ${c.size}: more than $maxCandidates candidate restrictions (base length $depth)")
            if (d > 0) {
                val col = hashWlRounds(g, seedFor(tuple), prefT[d - 1]); val onC = LongArray(c.size) { col[c[it]] }
                if (onC.sorted() != sortedPref[d - 1]) { excludedCounter[0]++; return }
                if (d == depth) {
                    val where = HashMap<Long, Int>().apply { onC.forEachIndexed { i, x -> put(x, i) } }
                    perms.add(List(c.size) { i -> where.getValue(prefCol[depth - 1][i]) }); return
                }
                val want = prefCol[d - 1][posIn[base[d]]]
                for (i in c.indices) if (onC[i] == want && c[i] !in tuple) { tuple.add(c[i]); dfs(tuple); tuple.removeAt(tuple.size - 1) }
            } else for (s0 in c) { tuple.add(s0); dfs(tuple); tuple.removeAt(tuple.size - 1) }
        }
        dfs(mutableListOf())
        return perms.distinct()
    }

    /**
     * Z3 x| Z2 solver for d3/z3 (Christos, 2026-09-26). Per class, candidate set T_C must be N_C x| Q_C:
     * N_C = {x : x^3 = id} an elementary abelian 3-group (translations), index 1 or 2 (Q_C = sign flip).
     * Layer 1 (GF(2)): sign bit per class with |Q_C| = 2; each pair constraint projected to signs must be a
     * subgroup of Z2 x Z2 -> GF(2) equations; enumerate sign solutions (<= 2^12).
     * Layer 2 (GF(3), per sign solution): elements of sign s are n o r_s (r_s a fixed representative);
     * with signs fixed, the allowed (n1, n2) of each pair must be a COSET -> affine GF(3) equations.
     * |Aut| = sum over consistent sign solutions of 3^dim. Orbit query a -> b: per sign solution, the
     * elements of class(a) with that sign sending a to b must form a coset -> affine equations.
     * Every automorphism satisfies both layers; every solution preserves all edges -> exact. Stops on
     * any failed check.
     */
    private fun parityEquationsZ3(path: String, aIn: Int?, bIn: Int?, quiet: Boolean = false, crossCheck: Boolean = true): ParityResult {
        val res = ParityResult()
        val say: (String) -> Unit = { if (!quiet) println(it) }
        val t0 = System.currentTimeMillis()
        val el = { "${(System.currentTimeMillis() - t0) / 1000.0}s" }
        fun stop(status: String): ParityResult { res.status = status; res.seconds = (System.currentTimeMillis() - t0) / 1000.0; say("-> $status"); return res }
        val g = loadForTrace(path)
        val baseline = dispatchColouring(g).colouring
        val classes = (0 until g.n).groupBy { baseline[it] }.values.map { it.sorted().toIntArray() }.filter { it.size > 1 }
        res.n = g.n; res.m = g.m; res.piClasses = baseline.toHashSet().size; res.nonSingleton = classes.size
        res.classSizes = classes.groupingBy { it.size }.eachCount().toSortedMap().toString()
        say("==== $path -- Z3 x| Z2 PARITY EQUATIONS (n=${g.n} m=${g.m}) ====")
        say("[${el()}] PI: ${res.piClasses} classes, non-singleton ${classes.size}, sizes ${res.classSizes}")
        var a = aIn; var b = bIn
        if (a == null && b == null) {
            val (sub0, _) = g.induced(IntArray(g.n) { it })
            val r = dialysis.decomposition.defaultRootRule(sub0, baseline)
            val mate = (0 until g.n).firstOrNull { it != r && baseline[it] == baseline[r] }
            if (mate != null) { a = r; b = mate } else classes.minByOrNull { it.min() }?.let { a = it[0]; b = it[1] }
        }
        val seedBase = LongArray(g.n) { sha64(baseline[it].serialize()) }
        val seedFor = { tuple: List<Int> -> seedBase.copyOf().also { s0 -> tuple.forEachIndexed { i, v -> s0[v] = mix64(s0[v] xor (0x5EED0000L + i)) } } }
        val classOf = IntArray(g.n) { -1 }; classes.forEachIndexed { i, c -> for (v in c) classOf[v] = i }
        val posIn = IntArray(g.n) { -1 }; classes.forEach { c -> c.forEachIndexed { i, v -> posIn[v] = i } }
        val excl = IntArray(1)

        // per class: N (translations, GF(3)^k coords), optional sign representative r
        class Z3Class(val k: Int, val nCoord: Map<List<Int>, IntArray>, val rep: List<Int>?, val all: List<List<Int>>)
        fun comp(x: List<Int>, y: List<Int>) = List(x.size) { x[y[it]] }
        fun inverse(x: List<Int>): List<Int> { val r = IntArray(x.size); x.forEachIndexed { i, v -> r[v] = i }; return r.toList() }
        val zc = ArrayList<Z3Class>()
        for (c in classes) {
            val perms = candidateRestrictions(g, c, seedFor, posIn, g.n + 2, excl) ?: return stop("STOP_BASE_TOO_LONG")
            val id = List(c.size) { it }
            val set = perms.toSet()
            val isGroup = id in set && set.all { x -> set.all { y -> comp(x, y) in set } }
            val nSet = set.filter { comp(it, comp(it, it)) == id }.toSet()
            val nOk = nSet.all { x -> nSet.all { y -> comp(x, y) in nSet && comp(x, y) == comp(y, x) } }
            val order3 = generateSequence(1) { it * 3 }.takeWhile { it <= nSet.size }.last() == nSet.size
            val index = if (nSet.isEmpty()) 0 else set.size / nSet.size
            if (!isGroup || !nOk || !order3 || set.size % nSet.size != 0 || index !in 1..2) {
                res.notGroup++; say("   class ${c.toList()}: |T|=${set.size}, |N|=${nSet.size} -- not of the form Z3^k x| (Z2 or 1)"); continue
            }
            val coord = LinkedHashMap<List<Int>, IntArray>().apply { put(id, IntArray(0)) }
            var k = 0
            for (x in nSet) if (x !in coord) {
                val old = coord.entries.toList(); coord.clear()
                for (e in 0 until 3) { var xe = id; repeat(e) { xe = comp(x, xe) }; for ((h, v) in old) coord[comp(xe, h)] = v + e }
                k++
            }
            val rep = if (index == 2) set.first { it !in nSet } else null
            zc.add(Z3Class(k, coord, rep, set.toList()))
        }
        res.excluded = excl[0]
        say("[${el()}] candidate sets: NOT of form Z3^k x| Z2: ${res.notGroup}; excluded image prefixes ${excl[0]}; (k, sign) counts: " +
            zc.groupingBy { "k=${it.k},sign=${it.rep != null}" }.eachCount().toSortedMap())
        if (res.notGroup > 0) return stop("STOP_NOT_Z3_SEMIDIRECT")
        // element -> (sign, GF(3) coords of its translation part)
        fun decompose(ci: Int, x: List<Int>): Pair<Int, IntArray> {
            val z = zc[ci]
            z.nCoord[x]?.let { return 0 to it }
            val n = comp(x, inverse(z.rep!!))   // x = n o rep
            return 1 to z.nCoord.getValue(n)
        }
        // pair edge lists
        val pairEdges = HashMap<Pair<Int, Int>, MutableList<Pair<Int, Int>>>()
        for (u in 0 until g.n) for (w in g.adj[u]) if (u < w) {
            val cu = classOf[u]; val cw = classOf[w]
            if (cu < 0 && cw < 0) continue
            pairEdges.getOrPut(if (cu <= cw) cu to cw else cw to cu) { mutableListOf() }.add(u to w)
        }
        // allowed element pairs per pair constraint (computed once)
        val allowedByPair = HashMap<Pair<Int, Int>, List<Pair<List<Int>, List<Int>>>>()
        for ((key, es) in pairEdges) {
            val (c1, c2) = key
            val edgeSet = es.map { (x, y) -> minOf(x, y) to maxOf(x, y) }.toHashSet()
            val l1 = if (c1 >= 0) zc[c1].all else listOf(emptyList()); val l2 = if (c2 >= 0 && c2 != c1) zc[c2].all else listOf(emptyList())
            val allowed = mutableListOf<Pair<List<Int>, List<Int>>>()
            for (p1 in l1) for (p2 in l2) {
                val img = { x: Int -> val cx = classOf[x]; when { cx < 0 -> x; cx == c1 -> classes[c1][p1[posIn[x]]]; else -> classes[c2][p2[posIn[x]]] } }
                if (es.all { (x, y) -> val u2 = img(x); val w2 = img(y); (minOf(u2, w2) to maxOf(u2, w2)) in edgeSet }) allowed.add(p1 to p2)
            }
            if (allowed.isEmpty()) return stop("STOP_EMPTY_CONSTRAINT")
            allowedByPair[key] = allowed
        }
        // layer 1: signs over GF(2)
        val signIdx = IntArray(classes.size) { -1 }; var nSign = 0
        for (i in classes.indices) if (zc[i].rep != null) signIdx[i] = nSign++
        val signSys = ModPSystem(2, maxOf(nSign, 1))
        var badSign = 0
        for ((key, allowed) in allowedByPair) {
            val (c1, c2) = key
            val s1 = c1 >= 0 && signIdx[c1] >= 0; val s2 = c2 >= 0 && c2 != c1 && signIdx[c2] >= 0
            if (!s1 && !s2) continue
            val pairs = allowed.map { (p1, p2) -> listOf(if (s1) decompose(c1, p1).first else 0, if (s2) decompose(c2, p2).first else 0) }.toSet()
            val closed = listOf(0, 0) in pairs && pairs.all { x -> pairs.all { y -> listOf((x[0] + y[0]) % 2, (x[1] + y[1]) % 2) in pairs } }
            if (!closed) { badSign++; continue }
            for (y in dualBasis(2, 2, pairs.map { it.toIntArray() })) {
                val row = IntArray(signSys.nVars)
                if (s1) row[signIdx[c1]] = (row[signIdx[c1]] + y[0]) % 2
                if (s2) row[signIdx[c2]] = (row[signIdx[c2]] + y[1]) % 2
                if (row.any { it != 0 }) signSys.add(row, 0) else if (y[0] != 0 || y[1] != 0) { if (!s1 && y[0] != 0 || !s2 && y[1] != 0) Unit }
            }
        }
        if (badSign > 0) return stop("STOP_SIGN_NOT_SUBGROUP")
        val (signRank, _, signPart) = signSys.solve()
        val signNull = if (nSign == 0) emptyList() else signSys.nullBasis()
        say("[${el()}] sign layer: $nSign sign bits, rank $signRank, ${signNull.size} free -> ${1 shl signNull.size} sign solution(s)")
        if (signNull.size > 12) return stop("STOP_TOO_MANY_SIGN_SOLUTIONS")
        val signSolutions = (0 until (1 shl signNull.size)).map { mask ->
            val v = signPart!!.copyOf(); signNull.forEachIndexed { j, nb -> if ((mask shr j) and 1 == 1) for (i in v.indices) v[i] = (v[i] + nb[i]) % 2 }; v }
        // layer 2 per sign solution
        val offset = IntArray(classes.size); var nVars = 0
        for (i in classes.indices) { offset[i] = nVars; nVars += zc[i].k }
        res.nVars = nVars + nSign
        fun signOf(ci: Int, sv: IntArray) = if (signIdx[ci] >= 0) sv[signIdx[ci]] else 0
        /** Affine equations y.x = y.x0 for the COSET [vs] (null if not a coset). */
        fun affineEqs(m: Int, vs: List<IntArray>): List<Pair<IntArray, Int>>? {
            if (vs.isEmpty()) return null
            val x0 = vs[0]; val d = vs.map { v -> IntArray(m) { ((v[it] - x0[it]) % 3 + 3) % 3 } }
            val keys = d.map { it.toList() }.toHashSet()
            if (!(IntArray(m).toList() in keys && d.all { x -> d.all { y -> List(m) { (x[it] + y[it]) % 3 } in keys } })) return null
            return dualBasis(3, m, d).map { y -> y to ((0 until m).sumOf { y[it] * x0[it] } % 3) }
        }
        fun buildSystem(sv: IntArray): ModPSystem? {
            val sys = ModPSystem(3, maxOf(nVars, 1))
            for ((key, allowed) in allowedByPair) {
                val (c1, c2) = key
                val k1 = if (c1 >= 0) zc[c1].k else 0; val k2 = if (c2 >= 0 && c2 != c1) zc[c2].k else 0
                val vs = allowed.mapNotNull { (p1, p2) ->
                    val d1 = if (c1 >= 0) decompose(c1, p1) else 0 to IntArray(0)
                    val d2 = if (c2 >= 0 && c2 != c1) decompose(c2, p2) else 0 to IntArray(0)
                    if ((c1 >= 0 && d1.first != signOf(c1, sv)) || (c2 >= 0 && c2 != c1 && d2.first != signOf(c2, sv))) null else d1.second + d2.second
                }
                if (k1 + k2 == 0) { if (vs.isEmpty()) return null; continue }
                val eqs = affineEqs(k1 + k2, vs) ?: return null
                for ((y, rhs) in eqs) {
                    val row = IntArray(sys.nVars)
                    for (j in 0 until k1) row[offset[c1] + j] = y[j]; for (j in 0 until k2) row[offset[c2] + j] = y[k1 + j]
                    sys.add(row, rhs)
                }
            }
            return sys
        }
        var autOrder = 0.0; var nonCoset = 0
        val systemsBySign = signSolutions.map { sv -> sv to buildSystem(sv) }
        for ((_, sys) in systemsBySign) {
            if (sys == null) { nonCoset++; continue }
            val (rank, ok, _) = sys.solve()
            if (ok) autOrder += Math.pow(3.0, (nVars - rank).toDouble())
        }
        res.nEqs = systemsBySign.sumOf { it.second?.rows?.size ?: 0 }
        res.autOrder = autOrder
        res.autStr = "%.6g".format(autOrder)
        say("[${el()}] GF(3) layer: $nVars translation variables; sign solutions infeasible/non-coset: $nonCoset -> |Aut(G)| = ${res.autStr}")
        if (crossCheck && g.n <= 2500) say("   cross-check: Traces |Aut| = ${"%.6g".format(traces.certifyAll(g, listOf(IntArray(g.n) { it }), getcanon = false).stats.autOrder)}")
        if (a != null && b != null) {
            res.query = "$a->$b"
            val ca = classOf[a]
            if (ca < 0 || classOf[b] != ca) res.queryVerdict = "NOT_SAME_PI_CLASS"
            else {
                val toB = zc[ca].all.filter { classes[ca][it[posIn[a]]] == b }
                var found: Pair<IntArray, IntArray>? = null
                for ((sv, sys) in systemsBySign) {
                    if (sys == null) continue
                    val cands = toB.map { decompose(ca, it) }.filter { it.first == signOf(ca, sv) }.map { it.second }
                    if (cands.isEmpty()) continue
                    val q = ModPSystem(3, sys.nVars); q.rows.addAll(sys.rows)
                    if (zc[ca].k > 0) {
                        val eqs = affineEqs(zc[ca].k, cands) ?: continue
                        for ((y, rhs) in eqs) { val row = IntArray(q.nVars); for (j in 0 until zc[ca].k) row[offset[ca] + j] = y[j]; q.add(row, rhs) }
                    }
                    val (_, ok, x) = q.solve()
                    if (ok) { found = sv to x!!; break }
                }
                res.queryVerdict = if (found != null) "ORBIT_MATES" else if (toB.isEmpty()) "NOT_ORBIT_MATES(excluded)" else "NOT_ORBIT_MATES"
                if (found != null) {
                    val (sv, x) = found
                    val sigma = IntArray(g.n) { it }
                    for ((ci, c) in classes.withIndex()) {
                        val z = zc[ci]; val s0 = signOf(ci, sv); val coords = IntArray(z.k) { x[offset[ci] + it] }
                        val n = z.nCoord.entries.first { it.value.contentEquals(coords) }.key
                        val perm = if (s0 == 0) n else comp(n, z.rep!!)
                        for ((i, v) in c.withIndex()) sigma[v] = c[perm[i]]
                    }
                    res.explicitAutOk = sigma[a] == b && (0 until g.n).all { u -> g.adj[u].all { w -> g.adj[sigma[u]].contains(sigma[w]) } }
                }
            }
            say("orbit query ${res.query}: ${res.queryVerdict}${res.explicitAutOk?.let { " (explicit automorphism verified: $it)" } ?: ""}")
        }
        res.status = if (nonCoset > 0) "EXACT_WITH_NONCOSET_SIGNS" else "EXACT"
        if (nonCoset > 0) say("   NOTE: $nonCoset sign solution(s) gave a non-coset translation constraint -> those were NOT counted; result is not certified")
        res.seconds = (System.currentTimeMillis() - t0) / 1000.0
        say("[${el()}] ========================================================")
        return res
    }

    /** Diagnostics for the 35 stops: base growth per class (up to [maxBase]) and candidate-set structure. */
    private fun diagnoseStops(path: String, maxBase: Int) {
        val g = loadForTrace(path)
        val baseline = dispatchColouring(g).colouring
        val classes = (0 until g.n).groupBy { baseline[it] }.values.map { it.sorted().toIntArray() }.filter { it.size > 1 }
        val seedBase = LongArray(g.n) { sha64(baseline[it].serialize()) }
        val seedFor = { tuple: List<Int> -> seedBase.copyOf().also { s0 -> tuple.forEachIndexed { i, v -> s0[v] = mix64(s0[v] xor (0x5EED0000L + i)) } } }
        val posIn = IntArray(g.n) { -1 }; classes.forEach { c -> c.forEachIndexed { i, v -> posIn[v] = i } }
        println("==== $path -- stop diagnostics ====")
        for (c in classes) {
            val base = mutableListOf(c[0]); val pattern = mutableListOf<List<Int>>()
            var split = false
            while (base.size <= maxBase) {
                val sd = seedFor(base); val t = hashWlStableRound(g, sd, g.n + 2); val col = hashWlRounds(g, sd, t)
                val blocks = c.indices.groupBy { col[c[it]] }.values
                pattern.add(blocks.map { it.size }.sortedDescending())
                if (blocks.all { it.size == 1 }) { split = true; break }
                base.add(c[blocks.first { it.size > 1 }.min()])
            }
            val needsLong = !split || base.size > 4
            val perms = if (split) candidateRestrictions(g, c, seedFor, posIn, g.n + 2, IntArray(1)) else null
            var groupInfo = ""
            if (perms != null) {
                val id = List(c.size) { it }
                fun comp(x: List<Int>, y: List<Int>) = List(x.size) { x[y[it]] }
                fun order(x: List<Int>): Int { var r = x; var k = 1; while (r != id) { r = comp(x, r); k++ }; return k }
                val set = perms.toSet()
                val isGroup = id in set && set.all { x -> set.all { y -> comp(x, y) in set } }
                val abelian = set.all { x -> set.all { y -> comp(x, y) == comp(y, x) } }
                val orders = set.groupingBy { order(it) }.eachCount().toSortedMap()
                val elemAb = isGroup && abelian && orders.keys.all { it == 1 || it == 2 } || isGroup && abelian && orders.keys.all { it == 1 || it == 3 }
                if (!elemAb) groupInfo = "|T|=${set.size} group=$isGroup abelian=$abelian element orders=$orders"
            }
            if (needsLong || groupInfo.isNotEmpty())
                println("class size ${c.size} ${c.toList()}: base length ${base.size}${if (split) "" else "+ (NOT split by $maxBase)"}, block sizes per base length $pattern ${if (groupInfo.isNotEmpty()) "| $groupInfo" else ""}")
        }
        println("========================================================")
    }

    // ─────────── generic two-layer solver: T_C = N_C . Q_C, N_C elementary abelian p, Q_C elementary abelian q ───────────

    private object Perm {
        fun comp(x: List<Int>, y: List<Int>) = List(x.size) { x[y[it]] }      // x after y
        fun inv(x: List<Int>): List<Int> { val r = IntArray(x.size); x.forEachIndexed { i, v -> r[v] = i }; return r.toList() }
        fun id(n: Int) = List(n) { it }
        fun pow(x: List<Int>, e: Int): List<Int> { var r = id(x.size); repeat(e) { r = comp(x, r) }; return r }
        /** Closure of [gens] under composition (+ conjugation by [conj] if given): a (normal) subgroup. */
        fun closure(n: Int, gens: Collection<List<Int>>, conj: Collection<List<Int>> = emptyList()): Set<List<Int>> {
            val out = LinkedHashSet<List<Int>>().apply { add(id(n)) }
            val queue = ArrayDeque<List<Int>>(); for (x in gens) if (out.add(x)) queue.add(x)
            val conjInv = conj.map { inv(it) }
            while (queue.isNotEmpty()) {
                val x = queue.removeFirst()
                val next = gens.map { comp(x, it) } + conj.indices.map { i -> comp(conj.elementAt(i), comp(x, conjInv[i])) }
                for (y in next) if (out.add(y)) queue.add(y)
                // closure under products with everything found so far is implied by generator products for finite groups
            }
            return out
        }
        /** Closure of [gens] under composition, or null as soon as it exceeds [cap] elements. */
        fun closureCapped(n: Int, gens: List<List<Int>>, cap: Int): Set<List<Int>>? {
            val out = LinkedHashSet<List<Int>>().apply { add(id(n)) }
            val queue = ArrayDeque<List<Int>>(); for (x in gens) if (out.add(x)) queue.add(x)
            if (out.size > cap) return null
            while (queue.isNotEmpty()) {
                val x = queue.removeFirst()
                for (gg in gens) { val y = comp(x, gg); if (out.add(y)) { if (out.size > cap) return null; queue.add(y) } }
            }
            return out
        }
        /** EXACT group test in O(|T| * |S|^2) instead of O(|T|^2): grow a generating set S <= T greedily; T is a
         *  group iff every closure <S> stays inside T and the final <S> equals T (then T = <S>). */
        fun isGroup(t: Set<List<Int>>, n: Int): Boolean {
            if (id(n) !in t) return false
            val gens = mutableListOf<List<Int>>(); var span: Set<List<Int>> = setOf(id(n))
            for (x in t) if (x !in span) {
                gens.add(x)
                span = closureCapped(n, gens, t.size) ?: return false
                if (!t.containsAll(span)) return false
            }
            return span.size == t.size
        }
        fun generators(t: Set<List<Int>>, n: Int): List<List<Int>> {
            val gens = mutableListOf<List<Int>>(); var span: Set<List<Int>> = setOf(id(n))
            for (x in t) if (x !in span) { gens.add(x); span = closure(n, gens) ; if (span.size == t.size) break }
            return gens
        }
        fun isElemAbelian(s: Set<List<Int>>, p: Int, n: Int) = s.all { x -> pow(x, p) == id(n) } && s.all { x -> s.all { y -> comp(x, y) == comp(y, x) } }
        fun primeOf(order: Int): Int? = when {
            order == 1 -> 1
            Integer.bitCount(order) == 1 -> 2
            generateSequence(1) { it * 3 }.takeWhile { it <= order }.last() == order -> 3
            else -> null
        }
        /** GF(p) coordinates of an elementary abelian p-group (as a map element -> vector). */
        fun coords(s: Set<List<Int>>, p: Int, n: Int): Map<List<Int>, IntArray> {
            var coord = LinkedHashMap<List<Int>, IntArray>().apply { put(id(n), IntArray(0)) }
            for (x in s) if (x !in coord) {
                val next = LinkedHashMap<List<Int>, IntArray>()
                for (e in 0 until p) { val xe = pow(x, e); for ((h, v) in coord) next[comp(xe, h)] = v + e }
                coord = next
            }
            return coord
        }
    }

    private class Layered(val nSet: Set<List<Int>>, val p: Int, val nCoord: Map<List<Int>, IntArray>, val q: Int,
                          val cosetRep: Map<List<Int>, List<Int>>,   // element -> representative of its coset x N
                          val qCoord: Map<List<Int>, IntArray>,     // representative -> GF(q) coords of the coset
                          val all: List<List<Int>>) {
        val kp get() = nCoord.values.firstOrNull()?.size ?: 0
        val kq get() = qCoord.values.firstOrNull()?.size ?: 0
        fun split(x: List<Int>): Pair<IntArray, IntArray> { val r = cosetRep.getValue(x); return qCoord.getValue(r) to nCoord.getValue(Perm.comp(x, Perm.inv(r))) }
    }

    /** Find N normal, elementary abelian, with T/N elementary abelian; try T, the order-3 part, Frattini T^p[T,T]. */
    private fun layer(t: Set<List<Int>>, n: Int): Layered? {
        val id = Perm.id(n)
        if (!Perm.isGroup(t, n)) return null
        val gens = Perm.generators(t, n)
        val candidatesN = mutableListOf<Set<List<Int>>>()
        Perm.primeOf(t.size)?.let { if (Perm.isElemAbelian(t, if (it == 1) 2 else it, n)) candidatesN.add(t) }
        t.filter { Perm.pow(it, 3) == id }.toSet().let { if (it.size > 1) candidatesN.add(it) }
        for (pp in listOf(2, 3)) {
            val seeds = gens.map { Perm.pow(it, pp) } + gens.flatMap { x -> gens.map { y -> Perm.comp(Perm.comp(x, y), Perm.comp(Perm.inv(x), Perm.inv(y))) } }
            candidatesN.add(Perm.closure(n, seeds.filter { it != id }, gens))
        }
        for (nSet in candidatesN) {
            val p = Perm.primeOf(nSet.size) ?: continue
            val pp = if (p == 1) 2 else p
            if (!Perm.isElemAbelian(nSet, pp, n)) continue
            if (!t.all { x -> nSet.all { m -> Perm.comp(Perm.comp(x, m), Perm.inv(x)) in nSet } }) continue    // normal
            // cosets
            val rep = HashMap<List<Int>, List<Int>>()
            val reps = mutableListOf<List<Int>>()
            for (x in t) if (x !in rep) { val coset = nSet.map { Perm.comp(x, it) }; val r = coset.minWith(compareBy<List<Int>> { it.toString() }); reps.add(r); for (y in coset) rep[y] = r }
            val qOrder = reps.size
            val q = Perm.primeOf(qOrder) ?: continue
            val qq = if (q == 1) 2 else q
            // quotient must be elementary abelian: products of reps land in the right coset, commute, exponent q
            val qOk = reps.all { a -> reps.all { b -> rep.getValue(Perm.comp(a, b)) == rep.getValue(Perm.comp(b, a)) } } && reps.all { rep.getValue(Perm.pow(it, qq)) == rep.getValue(id) }
            if (!qOk) continue
            // quotient coordinates via coset reps
            var qc = LinkedHashMap<List<Int>, IntArray>().apply { put(rep.getValue(id), IntArray(0)) }
            for (r in reps) if (r !in qc) {
                val next = LinkedHashMap<List<Int>, IntArray>()
                for (e in 0 until qq) { val re = Perm.pow(r, e); for ((h, v) in qc) next[rep.getValue(Perm.comp(re, h))] = v + e }
                qc = next
            }
            if (qc.size != qOrder) continue
            return Layered(nSet, pp, Perm.coords(nSet, pp, n), qq, rep, qc, t.toList())
        }
        return null
    }

    /**
     * Generic two-layer parity solver (Christos, 2026-09-26, "fix the 35 stops"). Per PI class, candidate
     * group T_C (base sequences up to [maxBase]) split as N_C . Q_C ([layer]). Layer 1: quotient
     * coordinates over GF(q) -- each pair's allowed quotient pairs must be a subgroup -> linear; its
     * solutions are enumerated (<= 2^16). Layer 2, per quotient solution: each pair's allowed N-parts must
     * be a coset -> affine over GF(p). |Aut| = sum over quotient solutions of p^dim. All N_C share one
     * prime p and all non-trivial Q_C one prime q (checked). Exact; stops on any failed check.
     */
    private fun parityEquationsLayered(path: String, aIn: Int?, bIn: Int?, quiet: Boolean = false, crossCheck: Boolean = true, maxBase: Int = 12): ParityResult {
        val res = ParityResult()
        val say: (String) -> Unit = { if (!quiet) println(it) }
        val t0 = System.currentTimeMillis()
        val el = { "${(System.currentTimeMillis() - t0) / 1000.0}s" }
        fun stop(status: String): ParityResult { res.status = status; res.seconds = (System.currentTimeMillis() - t0) / 1000.0; say("-> $status"); return res }
        val g = loadForTrace(path)
        val baseline = dispatchColouring(g).colouring
        val classes = (0 until g.n).groupBy { baseline[it] }.values.map { it.sorted().toIntArray() }.filter { it.size > 1 }
        res.n = g.n; res.m = g.m; res.piClasses = baseline.toHashSet().size; res.nonSingleton = classes.size
        res.classSizes = classes.groupingBy { it.size }.eachCount().toSortedMap().toString()
        say("==== $path -- LAYERED PARITY EQUATIONS (n=${g.n} m=${g.m}) ====")
        say("[${el()}] PI: ${res.piClasses} classes, non-singleton ${classes.size}, sizes ${res.classSizes}")
        var a = aIn; var b = bIn
        if (a == null && b == null) {
            val (sub0, _) = g.induced(IntArray(g.n) { it })
            val r = dialysis.decomposition.defaultRootRule(sub0, baseline)
            val mate = (0 until g.n).firstOrNull { it != r && baseline[it] == baseline[r] }
            if (mate != null) { a = r; b = mate } else classes.minByOrNull { it.min() }?.let { a = it[0]; b = it[1] }
        }
        val seedBase = LongArray(g.n) { sha64(baseline[it].serialize()) }
        val seedFor = { tuple: List<Int> -> seedBase.copyOf().also { s0 -> tuple.forEachIndexed { i, v -> s0[v] = mix64(s0[v] xor (0x5EED0000L + i)) } } }
        val classOf = IntArray(g.n) { -1 }; classes.forEachIndexed { i, c -> for (v in c) classOf[v] = i }
        val posIn = IntArray(g.n) { -1 }; classes.forEach { c -> c.forEachIndexed { i, v -> posIn[v] = i } }
        val excl = IntArray(1)
        val lay = ArrayList<Layered>()
        for (c in classes) {
            val perms = candidateRestrictions(g, c, seedFor, posIn, g.n + 2, excl, maxBase) ?: return stop("STOP_BASE_TOO_LONG(>$maxBase)")
            val l = layer(perms.toSet(), c.size)
            if (l == null) { res.notGroup++; say("   class size ${c.size}: |T|=${perms.size} has no N with elementary abelian N and T/N"); continue }
            lay.add(l)
        }
        res.excluded = excl[0]
        if (res.notGroup > 0) return stop("STOP_NO_LAYERING")
        val ps = lay.filter { it.kp > 0 }.map { it.p }.toSet(); val qs = lay.filter { it.kq > 0 }.map { it.q }.toSet()
        say("[${el()}] layering: N primes $ps, quotient primes $qs; (|N|,|Q|) counts " + lay.groupingBy { "(${it.nSet.size},${it.qCoord.size})" }.eachCount().toSortedMap())
        if (ps.size > 1 || qs.size > 1) return stop("STOP_MIXED_PRIMES")
        val p = ps.firstOrNull() ?: 2; val q = qs.firstOrNull() ?: 2
        val offP = IntArray(classes.size); val offQ = IntArray(classes.size); var nP = 0; var nQ = 0
        for (i in classes.indices) { offP[i] = nP; nP += lay[i].kp; offQ[i] = nQ; nQ += lay[i].kq }
        res.nVars = nP + nQ
        // allowed element pairs per edge-joined class pair
        val pairEdges = HashMap<Pair<Int, Int>, MutableList<Pair<Int, Int>>>()
        for (u in 0 until g.n) for (w in g.adj[u]) if (u < w) {
            val cu = classOf[u]; val cw = classOf[w]
            if (cu < 0 && cw < 0) continue
            pairEdges.getOrPut(if (cu <= cw) cu to cw else cw to cu) { mutableListOf() }.add(u to w)
        }
        val allowedByPair = HashMap<Pair<Int, Int>, List<Pair<List<Int>, List<Int>>>>()
        for ((key, es) in pairEdges) {
            val (c1, c2) = key
            val edgeSet = es.map { (x, y) -> minOf(x, y) to maxOf(x, y) }.toHashSet()
            val l1 = if (c1 >= 0) lay[c1].all else listOf(emptyList()); val l2 = if (c2 >= 0 && c2 != c1) lay[c2].all else listOf(emptyList())
            val allowed = mutableListOf<Pair<List<Int>, List<Int>>>()
            for (p1 in l1) for (p2 in l2) {
                val img = { x: Int -> val cx = classOf[x]; when { cx < 0 -> x; cx == c1 -> classes[c1][p1[posIn[x]]]; else -> classes[c2][p2[posIn[x]]] } }
                if (es.all { (x, y) -> val u2 = img(x); val w2 = img(y); (minOf(u2, w2) to maxOf(u2, w2)) in edgeSet }) allowed.add(p1 to p2)
            }
            if (allowed.isEmpty()) return stop("STOP_EMPTY_CONSTRAINT")
            allowedByPair[key] = allowed
        }
        fun rowP(sz: Int, c1: Int, c2: Int, k1: Int, k2: Int, y: IntArray, off: IntArray): IntArray {
            val row = IntArray(sz); for (j in 0 until k1) row[off[c1] + j] = y[j]; for (j in 0 until k2) row[off[c2] + j] = y[k1 + j]; return row
        }
        // layer 1: quotient
        val qSys = ModPSystem(q, maxOf(nQ, 1))
        for ((key, allowed) in allowedByPair) {
            val (c1, c2) = key
            val k1 = if (c1 >= 0) lay[c1].kq else 0; val k2 = if (c2 >= 0 && c2 != c1) lay[c2].kq else 0
            if (k1 + k2 == 0) continue
            val vs = allowed.map { (p1, p2) -> (if (c1 >= 0) lay[c1].split(p1).first else IntArray(0)) + (if (c2 >= 0 && c2 != c1) lay[c2].split(p2).first else IntArray(0)) }
            val keys = vs.map { it.toList() }.toHashSet()
            val closed = List(k1 + k2) { 0 } in keys && vs.all { x -> vs.all { y -> List(k1 + k2) { (x[it] + y[it]) % q } in keys } }
            if (!closed) return stop("STOP_QUOTIENT_NOT_SUBGROUP")
            for (y in dualBasis(q, k1 + k2, vs)) qSys.add(rowP(qSys.nVars, c1, c2, k1, k2, y, offQ), 0)
        }
        val (qRank, _, qPart) = qSys.solve()
        val qNull = if (nQ == 0) emptyList() else qSys.nullBasis()
        say("[${el()}] quotient layer: $nQ vars over GF($q), rank $qRank, ${qNull.size} free")
        if (Math.pow(q.toDouble(), qNull.size.toDouble()) > 65536) return stop("STOP_TOO_MANY_QUOTIENT_SOLUTIONS(${q}^${qNull.size})")
        val qSolutions = mutableListOf(qPart!!.copyOf())
        for (nb in qNull) { val more = mutableListOf<IntArray>(); for (base0 in qSolutions) for (e in 1 until q) more.add(IntArray(base0.size) { (base0[it] + e * nb[it]) % q }); qSolutions.addAll(more) }
        fun qOf(ci: Int, qv: IntArray) = IntArray(lay[ci].kq) { qv[offQ[ci] + it] }
        fun affineEqs(pr: Int, m: Int, vs: List<IntArray>): List<Pair<IntArray, Int>>? {
            if (vs.isEmpty()) return null
            val x0 = vs[0]; val d = vs.map { v -> IntArray(m) { ((v[it] - x0[it]) % pr + pr) % pr } }
            val keys = d.map { it.toList() }.toHashSet()
            if (!(List(m) { 0 } in keys && d.all { x -> d.all { y -> List(m) { (x[it] + y[it]) % pr } in keys } })) return null
            return dualBasis(pr, m, d).map { y -> y to ((0 until m).sumOf { y[it] * x0[it] } % pr) }
        }
        var nonCoset = 0
        val qInvolved = { key: Pair<Int, Int> -> (key.first >= 0 && lay[key.first].kq > 0) || (key.second >= 0 && key.second != key.first && lay[key.second].kq > 0) }
        /** Equations of one pair for quotient solution [qv] (null = infeasible). */
        fun pairEqs(key: Pair<Int, Int>, allowed: List<Pair<List<Int>, List<Int>>>, qv: IntArray?): List<Pair<IntArray, Int>>? {
            val (c1, c2) = key
            val k1 = if (c1 >= 0) lay[c1].kp else 0; val k2 = if (c2 >= 0 && c2 != c1) lay[c2].kp else 0
            val vs = allowed.mapNotNull { (p1, p2) ->
                val s1 = if (c1 >= 0) lay[c1].split(p1) else IntArray(0) to IntArray(0)
                val s2 = if (c2 >= 0 && c2 != c1) lay[c2].split(p2) else IntArray(0) to IntArray(0)
                if (qv != null && ((c1 >= 0 && !s1.first.contentEquals(qOf(c1, qv))) || (c2 >= 0 && c2 != c1 && !s2.first.contentEquals(qOf(c2, qv))))) null else s1.second + s2.second
            }
            if (vs.isEmpty()) return null
            if (k1 + k2 == 0) return emptyList()
            val eqs = affineEqs(p, k1 + k2, vs) ?: run { nonCoset++; return null }
            return eqs.map { (y, rhs) -> rowP(maxOf(nP, 1), c1, c2, k1, k2, y, offP) to rhs }
        }
        val baseN = ModPSystem(p, maxOf(nP, 1))
        for ((key, allowed) in allowedByPair) if (!qInvolved(key)) {
            val eqs = pairEqs(key, allowed, null) ?: return stop(if (nonCoset > 0) "STOP_N_PART_NOT_COSET" else "STOP_EMPTY_CONSTRAINT")
            for ((r, h) in eqs) baseN.add(r, h)
        }
        val (baseRank, baseOk, _) = baseN.solve()
        if (!baseOk) return stop("STOP_BASE_N_INCONSISTENT")
        val varPairs = allowedByPair.filterKeys { qInvolved(it) }
        fun extraRows(qv: IntArray): List<Pair<IntArray, Int>>? {
            val out = mutableListOf<Pair<IntArray, Int>>()
            for ((key, allowed) in varPairs) out.addAll(pairEqs(key, allowed, qv) ?: return null)
            return out
        }
        var aut = 0.0; var feasibleSolutions = 0
        for (qv in qSolutions) {
            val extra = extraRows(qv) ?: continue
            val (r, ok) = baseN.extend(extra)
            if (ok) { feasibleSolutions++; aut += Math.pow(p.toDouble(), (nP - r).toDouble()) }
        }
        say("[${el()}] N base: ${baseN.rows.size} eqs (rank $baseRank), ${varPairs.size} quotient-dependent pairs; feasible quotient solutions $feasibleSolutions")
        /** Full system for one quotient solution (only built when a solution vector is needed). */
        fun fullSystem(qv: IntArray): ModPSystem? {
            val sys = ModPSystem(p, maxOf(nP, 1)); sys.rows.addAll(baseN.rows)
            for ((r, h) in extraRows(qv) ?: return null) sys.add(r, h)
            return sys
        }
        if (nonCoset > 0) return stop("STOP_N_PART_NOT_COSET")
        res.autOrder = aut; res.autStr = "%.6g".format(aut); res.nEqs = qSys.rows.size + baseN.rows.size
        say("[${el()}] N layer over GF($p): $nP vars, ${qSolutions.size} quotient solution(s) -> |Aut(G)| = ${res.autStr}")
        if (crossCheck && g.n <= 2500) say("   cross-check: Traces |Aut| = ${"%.6g".format(traces.certifyAll(g, listOf(IntArray(g.n) { it }), getcanon = false).stats.autOrder)}")
        if (a != null && b != null) {
            res.query = "$a->$b"
            val ca = classOf[a]
            if (ca < 0 || classOf[b] != ca) res.queryVerdict = "NOT_SAME_PI_CLASS" else {
                val toB = lay[ca].all.filter { classes[ca][it[posIn[a]]] == b }
                var found: Pair<IntArray, IntArray>? = null
                for (qv in qSolutions) {
                    val cands = toB.map { lay[ca].split(it) }.filter { it.first.contentEquals(qOf(ca, qv)) }.map { it.second }
                    if (cands.isEmpty()) continue
                    val qs2 = fullSystem(qv) ?: continue
                    if (lay[ca].kp > 0) {
                        val eqs = affineEqs(p, lay[ca].kp, cands) ?: continue
                        for ((y, rhs) in eqs) { val row = IntArray(qs2.nVars); for (j in 0 until lay[ca].kp) row[offP[ca] + j] = y[j]; qs2.add(row, rhs) }
                    }
                    val (_, ok, x) = qs2.solve()
                    if (ok) { found = qv to x!!; break }
                }
                res.queryVerdict = if (found != null) "ORBIT_MATES" else if (toB.isEmpty()) "NOT_ORBIT_MATES(excluded)" else "NOT_ORBIT_MATES"
                if (found != null) {
                    val (qv, x) = found
                    val sigma = IntArray(g.n) { it }
                    for ((ci, c) in classes.withIndex()) {
                        val l = lay[ci]
                        val qc = qOf(ci, qv); val nc = IntArray(l.kp) { x[offP[ci] + it] }
                        val r = l.qCoord.entries.first { it.value.contentEquals(qc) }.key
                        val nEl = l.nCoord.entries.first { it.value.contentEquals(nc) }.key
                        val perm = Perm.comp(nEl, r)
                        for ((i, v) in c.withIndex()) sigma[v] = c[perm[i]]
                    }
                    res.explicitAutOk = sigma[a] == b && (0 until g.n).all { u -> g.adj[u].all { w -> g.adj[sigma[u]].contains(sigma[w]) } }
                }
            }
            say("orbit query ${res.query}: ${res.queryVerdict}${res.explicitAutOk?.let { " (explicit automorphism verified: $it)" } ?: ""}")
        }
        res.status = "EXACT"; res.seconds = (System.currentTimeMillis() - t0) / 1000.0
        say("[${el()}] ========================================================")
        return res
    }

    /** Per class: a normal series T = N_0 > N_1 > ... > N_L = 1, factor N_(l-1)/N_l elementary abelian
     *  with prime [primes][l] (possibly trivial), and every element's digit vector per level. */
    private class Series(val elems: List<List<Int>>, val digits: Map<List<Int>, List<IntArray>>, val k: IntArray,
                         val na: Map<Int, List<List<Int>>> = emptyMap()) {   // non-abelian level -> factor elements (index 0 = id)
        val byDigits: Map<String, List<Int>> = elems.associateBy { key(digits.getValue(it)) }
        /** Digit lookup by object IDENTITY first (the allowed pairs hold the very list objects of [elems]); falls back to the
         *  content-hashed map. Profile 2026-09-29: content hashing of permutation lists was over half of the witness search. */
        private val byId = java.util.IdentityHashMap<List<Int>, List<IntArray>>().also { m -> for (x in elems) m[x] = digits.getValue(x) }
        fun dig(x: List<Int>): List<IntArray> = byId[x] ?: digits.getValue(x)
        companion object { fun key(d: List<IntArray>) = d.joinToString("|") { it.joinToString(",") } }
    }

    /** Primes dividing [order]. */
    private fun primeFactors(order: Int): List<Int> {
        val out = mutableListOf<Int>(); var m = order; var d = 2
        while (d * d <= m) { if (m % d == 0) { out.add(d); while (m % d == 0) m /= d }; d++ }
        if (m > 1) out.add(m); return out
    }

    /**
     * General-prime normal series: cycle through [primeCycle]; each step divides out the verbal subgroup
     * N^q[N,N] (elementary-abelian q-quotient, possibly trivial). One full cycle removes the whole
     * abelianisation, so a SOLVABLE T reaches 1; if a full cycle makes no progress while |N| > 1, N is
     * perfect and T is NOT solvable. Returns the series over the flattened prime sequence, or a reason.
     */
    private fun buildSeriesGeneral(t: Set<List<Int>>, n: Int, primeCycle: List<Int>, maxCycles: Int): Pair<Series?, String> {
        val id = Perm.id(n)
        if (!Perm.isGroup(t, n)) return null to "candidate set T_C (|T|=${t.size}) is NOT a group"
        var cur: Set<List<Int>> = t
        for (cycle in 0 until maxCycles) {
            val before = cur.size
            for (q in primeCycle) {
                val gens = Perm.generators(cur, n)
                val seeds = gens.map { Perm.pow(it, q) } + gens.flatMap { x -> gens.map { y -> Perm.comp(Perm.comp(x, y), Perm.comp(Perm.inv(x), Perm.inv(y))) } }
                cur = Perm.closure(n, seeds.filter { it != id }.distinct(), gens)
            }
            if (cur.size == 1) return (buildSeries(t, n, List(maxCycles) { primeCycle }.flatten()) ?: return null to "series construction failed after reaching 1 (internal)") to ""
            if (cur.size == before) return null to "T_C (|T|=${t.size}) is NOT solvable: it contains a perfect subgroup of order ${cur.size}"
        }
        return null to "T_C (|T|=${t.size}): derived length exceeds $maxCycles cycles"
    }

    /**
     * Mixed normal series with a NON-ABELIAN stage (2026-09-27). Layout: [maxCycles] x (primeCycle, then one
     * non-abelian slot, marked by prime 0). Abelian slots divide out N^q[N,N] as in [buildSeriesGeneral]. At the
     * non-abelian slot of a cycle that made no progress, N is perfect (all primes dividing |T_C| are in the cycle);
     * the slot then takes N itself as ONE factor (N -> 1), its "digit" being the element's index in a fixed list
     * of N with the identity at index 0. Every term is characteristic in its predecessor, hence normal in T_C, so
     * the coset-mode argument (liftable level-l digits = coset of L_l) carries over with the factor group in
     * place of F_q^k. This is not Luks's semisimple machinery: the whole perfect part is one factor.
     */
    private fun buildSeriesMixed(t: Set<List<Int>>, n: Int, primeCycle: List<Int>, maxCycles: Int): Pair<Series?, String> {
        val id = Perm.id(n)
        if (!Perm.isGroup(t, n)) return null to "candidate set T_C (|T|=${t.size}) is NOT a group"
        val layout = List(maxCycles) { primeCycle + 0 }.flatten()
        var cur: Set<List<Int>> = t
        val repOf = mutableListOf<Map<List<Int>, List<Int>>>(); val coordOf = mutableListOf<Map<List<Int>, IntArray>>()
        val k = IntArray(layout.size); val na = HashMap<Int, List<List<Int>>>()
        var cycleStart = cur.size
        for ((l, q) in layout.withIndex()) {
            if (q == 0) {
                if (cur.size > 1 && cur.size == cycleStart) {
                    val list = listOf(id) + cur.filter { it != id }.sortedBy { it.toString() }
                    na[l] = list; k[l] = 1
                    repOf.add(list.associateWith { it }); coordOf.add(list.withIndex().associate { (i, x) -> x to intArrayOf(i) })
                    cur = setOf(id)
                } else { repOf.add(cur.associateWith { id }); coordOf.add(mapOf(id to IntArray(0))) }
                cycleStart = cur.size
                continue
            }
            val gens = Perm.generators(cur, n)
            val seeds = gens.map { Perm.pow(it, q) } + gens.flatMap { x -> gens.map { y -> Perm.comp(Perm.comp(x, y), Perm.comp(Perm.inv(x), Perm.inv(y))) } }
            val next = Perm.closure(n, seeds.filter { it != id }.distinct(), gens)
            if (!cur.containsAll(next)) return null to "series construction failed (internal)"
            val rep = HashMap<List<Int>, List<Int>>(); val reps = mutableListOf<List<Int>>()
            for (x in cur) if (x !in rep) {
                val coset = next.map { Perm.comp(x, it) }
                val r = if (id in coset) id else coset.minWith(compareBy<List<Int>> { it.toString() })
                reps.add(r); for (y in coset) rep[y] = r
            }
            if (!reps.all { a -> reps.all { b -> rep.getValue(Perm.comp(a, b)) == rep.getValue(Perm.comp(b, a)) } && rep.getValue(Perm.pow(a, q)) == rep.getValue(id) }) return null to "abelian factor check failed (internal)"
            var qc = LinkedHashMap<List<Int>, IntArray>().apply { put(rep.getValue(id), IntArray(0)) }
            for (r in reps) if (r !in qc) {
                val nx = LinkedHashMap<List<Int>, IntArray>()
                for (e in 0 until q) { val re = Perm.pow(r, e); for ((h, v) in qc) nx[rep.getValue(Perm.comp(re, h))] = v + e }
                qc = nx
            }
            if (qc.size != reps.size) return null to "abelian coordinates failed (internal)"
            k[l] = qc.values.first().size
            repOf.add(rep); coordOf.add(qc)
            cur = next
        }
        if (cur.size != 1) return null to "T_C (|T|=${t.size}): series longer than $maxCycles cycles"
        val digits = HashMap<List<Int>, List<IntArray>>()
        for (x in t) {
            var y = x; val d = mutableListOf<IntArray>()
            for (l in layout.indices) { val r = repOf[l].getValue(y); d.add(coordOf[l].getValue(r)); y = Perm.comp(y, Perm.inv(r)) }
            if (y != id) return null to "digit decomposition failed (internal)"
            digits[x] = d
        }
        return Series(t.toList(), digits, k, na) to ""
    }

    private fun buildSeries(t: Set<List<Int>>, n: Int, primes: List<Int>): Series? {
        val id = Perm.id(n)
        if (!Perm.isGroup(t, n)) return null
        var cur: Set<List<Int>> = t
        val repOf = mutableListOf<Map<List<Int>, List<Int>>>(); val coordOf = mutableListOf<Map<List<Int>, IntArray>>()
        val k = IntArray(primes.size)
        for ((l, q) in primes.withIndex()) {
            val gens = Perm.generators(cur, n)
            val seeds = gens.map { Perm.pow(it, q) } + gens.flatMap { x -> gens.map { y -> Perm.comp(Perm.comp(x, y), Perm.comp(Perm.inv(x), Perm.inv(y))) } }
            val next = Perm.closure(n, seeds.filter { it != id }.distinct(), gens)
            if (!cur.containsAll(next)) return null
            val rep = HashMap<List<Int>, List<Int>>(); val reps = mutableListOf<List<Int>>()
            for (x in cur) if (x !in rep) {
                val coset = next.map { Perm.comp(x, it) }
                // the identity represents its own coset: then the identity's digits are 0 at EVERY level
                // (coset mode relies on that); other representatives are arbitrary but fixed.
                val r = if (id in coset) id else coset.minWith(compareBy<List<Int>> { it.toString() })
                reps.add(r); for (y in coset) rep[y] = r
            }
            // factor must be elementary abelian q (true by construction; verified)
            if (!reps.all { a -> reps.all { b -> rep.getValue(Perm.comp(a, b)) == rep.getValue(Perm.comp(b, a)) } && rep.getValue(Perm.pow(a, q)) == rep.getValue(id) }) return null
            var qc = LinkedHashMap<List<Int>, IntArray>().apply { put(rep.getValue(id), IntArray(0)) }
            for (r in reps) if (r !in qc) {
                val nx = LinkedHashMap<List<Int>, IntArray>()
                for (e in 0 until q) { val re = Perm.pow(r, e); for ((h, v) in qc) nx[rep.getValue(Perm.comp(re, h))] = v + e }
                qc = nx
            }
            if (qc.size != reps.size) return null
            k[l] = qc.values.first().size
            repOf.add(rep); coordOf.add(qc)
            cur = next
        }
        if (cur.size != 1) return null
        val digits = HashMap<List<Int>, List<IntArray>>()
        for (x in t) {
            var y = x; val d = mutableListOf<IntArray>()
            for (l in primes.indices) { val r = repOf[l].getValue(y); d.add(coordOf[l].getValue(r)); y = Perm.comp(y, Perm.inv(r)) }
            if (y != id) return null
            digits[x] = d
        }
        return Series(t.toList(), digits, k)
    }

    /**
     * General layered parity solver (Christos, 2026-09-26). Per class, [buildSeries] with global primes
     * 2,3,2,3,2,3; top-down per level l: with the digits of all levels < l fixed (a node), each pair's
     * allowed element pairs that match the fixed prefix, projected to level-l digits, must be a COSET ->
     * affine GF(q_l) equations; enumerate the level's solutions and descend; at the last level count
     * q^dim. Every automorphism is a leaf, every leaf is an edge-preserving permutation -> exact.
     */
    /** COLOUR=auto (2026-10-02): the PI colouring already computed for the class-count comparison, reused by the second
     *  solve instead of being computed again (it is the expensive step; tnn(23)_598 spent > 50 min computing it twice). */
    internal var piOverride: Array<Content>? = null

    internal fun parityEquationsSeries(path: String, aIn: Int?, bIn: Int?, quiet: Boolean = false, crossCheck: Boolean = true, maxBase: Int = 12, maxNodes: Int = 200_000, usePi: Boolean = false, computeOrbits: Boolean = false, piCanonicalCopy: Boolean = false,
                                      maxCandidates: Int = 5000, maxPairTable: Long = 3_000_000L, deadlineMs: Long = Long.MAX_VALUE,
                                      generalPrimes: Boolean = false, cosetMode: Boolean = false, irFallback: Boolean = false,
                                      solveOnOriginal: Boolean = false, nonSolvableStage: Boolean = false): ParityResult {
        val res = ParityResult()
        val say: (String) -> Unit = { if (!quiet) println(it) }
        val t0 = System.currentTimeMillis()
        val el = { "${(System.currentTimeMillis() - t0) / 1000.0}s" }
        fun stop(status: String): ParityResult { res.status = status; res.seconds = (System.currentTimeMillis() - t0) / 1000.0; say("-> $status"); return res }
        // The solver works on G itself; it does not need bipartiteness.
        val g = if (solveOnOriginal) GraphIO.loadDimacs(File(path).toPath()) else loadForTrace(path)
        // Base partition: by default our own hash-1-WL from a uniform seed (canonical BY CONSTRUCTION, so
        // Aut-invariant regardless of JVM history); PI only if [usePi] (PI was seen to depend on earlier
        // calls in the same JVM, 2026-09-26).
        val baseline: Array<Content> = if (piCanonicalCopy) initialPhaseCopy(g, dialysis.refinement.uniformSeed(g.n), canonicalKey = true)
            else if (usePi && solveOnOriginal) (piOverride ?: piProjected(g))
            else if (usePi) dispatchColouring(g).colouring else {
            val uni = LongArray(g.n) { 0x1234567L }
            val tw = hashWlStableRound(g, uni, g.n + 2); val col = hashWlRounds(g, uni, tw)
            Array(g.n) { Content.Num(col[it]) }
        }
        // Optional extra Aut-invariant vertex invariant (e.g. the dialysis slice invariant of SliceGroupTest), one Long per
        // vertex in $SLICE_COL/<name>.col: combined with PI and re-refined by the canonical hash-1-WL (still Aut-invariant).
        val sliceCol = System.getenv("SLICE_COL")?.let { File(it, File(path).name + ".col") }?.takeIf { it.exists() }
        val baselineUsed: Array<Content> = if (sliceCol == null) baseline else {
            val extra = sliceCol.readLines().map { it.trim().toLong() }
            check(extra.size == g.n) { "slice colouring size ${extra.size} != n ${g.n}" }
            val seed = LongArray(g.n) { mix64(sha64(baseline[it].serialize()) xor extra[it]) }
            val tw = hashWlStableRound(g, seed, g.n + 2); val col = hashWlRounds(g, seed, tw)
            say("   base colouring: PI + slice invariant (${sliceCol.path}), re-refined")
            Array(g.n) { Content.Num(col[it]) }
        }
        // 2026-10-01: the deadline is the SOLVER's budget; the colouring time is added to it (still counted in res.seconds).
        // Before, PI used up the budget on large non-bipartite graphs (cfi-rigid-t2-2880-01-1: PI 280 s, solve 2 s,
        // reported STOP_TIME at 300 s).
        val colourMs = System.currentTimeMillis() - t0
        val solverDeadlineMs = if (deadlineMs == Long.MAX_VALUE) Long.MAX_VALUE else deadlineMs + colourMs
        return parityEquationsSeriesBody(path, g, baselineUsed, aIn, bIn, quiet, maxBase, maxNodes, usePi, computeOrbits, maxCandidates, maxPairTable, solverDeadlineMs,
            generalPrimes, cosetMode, irFallback, nonSolvableStage, res, say, t0, el, crossCheck)
    }

    /** The series parity/coset solver on an in-memory coloured graph (no file, no Traces cross-check, no time
     *  deadline -- only the count budgets, so the outcome depends on (g, baseline) alone). Used by SliceGroupTest
     *  as the slice invariant (Christos, 2026-09-28). */
    internal fun parityAutOf(g: Graph, baseline: Array<Content>, cosetMode: Boolean = false, nodeCap: Long = 5000): ParityResult {
        val res = ParityResult(); val t0 = System.currentTimeMillis()
        candidateNodeCap = nodeCap; invariantStops = true
        try {
            return parityEquationsSeriesBody("", g, baseline, null, null, true, 12, 200_000, false, true, 5000, 3_000_000L, Long.MAX_VALUE,
                false, cosetMode, false, false, res, {}, t0, { "" }, false)
        } finally { candidateNodeCap = Long.MAX_VALUE; invariantStops = false }
    }

    /** The campaign's `seriesfull` configuration (general primes, coset mode, non-abelian stage, no fallback) on an
     *  in-memory coloured graph -- for solving small derived graphs (pieces, piece quotients), 2026-09-29. */
    internal fun parityAutFull(g: Graph, baseline: Array<Content>, deadlineMs: Long = 60_000, maxCandidates: Int = 20_000): ParityResult {
        val res = ParityResult(); val t0 = System.currentTimeMillis()
        return parityEquationsSeriesBody("", g, baseline, null, null, true, 12, 200_000, false, false, maxCandidates, 3_000_000L, deadlineMs,
            true, true, false, true, res, {}, t0, { "" }, false)
    }

    /** Invariant mode (set only inside [parityAutOf]): classes in canonical colour order, candidate sets from
     *  [candidateRestrictionsInvariant], no orbit query -- so EXACT vs STOP (and which STOP) depends only on the
     *  coloured graph up to isomorphism, never on vertex numbering. */
    private var invariantStops = false
    /** Base length of the last candidate construction (complexity bookkeeping). */
    private var lastBaseLen = 0
    private var lastBase: List<Int> = emptyList()
    /** Two-sided (coset) mode, set only inside [parityIsoCount]: the IMAGE colouring H'. The solver then counts the
     *  isomorphisms H -> H' instead of |Aut(H)| (see [crossCandidates] and the twist in the pair constraints). */
    private var twistImage: Array<Content>? = null
    /** Batch two-sided mode (2026-09-29 speed-up): H is solved ONCE, then image colourings are pulled from this supplier one
     *  at a time; it receives the previous answer (true / false / null = stopped) and witness, and returns the next image or
     *  null to finish. */
    private var twistSupplier: ((Boolean?, IntArray?) -> Array<Content>?)? = null
    private var twistOnGroup: ((ParityResult) -> Unit)? = null
    private var twistQueryBudgetMs = 3_600_000L

    /** Deterministic budget (2026-09-30): when set, the GROUP phase stops on accumulated work instead of wall-clock time,
     *  so the outcome -- e.g. which depth the stabiliser chain takes -- is the same on every machine and every run.
     *  Units: vertex + adjacency visits of the canonical refinement, plus class-size-weighted search and pair-table
     *  steps. The query phase of [parityIsoBatch] keeps its own wall-clock budget. */
    internal var workBudget = Long.MAX_VALUE
    internal var work = 0L
    /** Weight of one allowed-pair / relation step of the coset search relative to one refinement unit: those steps go through
     *  boxed hash sets and digit lookups (~50 ns) where a refinement unit is an array visit (~2.5 ns). Measured 2026-10-01 on
     *  hypercube-8 depth 2 (4.5e9 unweighted units took 215 s, i.e. ~2e7/s against the calibrated ~4e8/s). */
    private val SEARCH_W = 20L
    /** work spent in the group phase of the last [parityIsoBatch] call (before its query phase) */
    internal var groupWork = 0L
    private fun overBudget(deadline: Long) = if (workBudget != Long.MAX_VALUE) work > workBudget else System.currentTimeMillis() > deadline
    private fun adjTotal(g: Graph): Long { var e = 0L; for (a in g.adj) e += a.size; return e }

    /** Solve H = (g, [dom]) once, then answer "is there an isomorphism H -> (g, img)?" for every image [next] supplies.
     *  Result: the ParityResult of H (autOrder = |Aut(H)|); answers go back through [next]. */
    internal fun parityIsoBatch(g: Graph, dom: Array<Content>, next: (Boolean?, IntArray?) -> Array<Content>?, deadlineMs: Long = 60_000,
                                queryBudgetMs: Long = 3_600_000, onGroup: ((ParityResult) -> Unit)? = null, maxCandidates: Int = 20_000,
                                workBudget: Long = Long.MAX_VALUE): ParityResult {
        val res = ParityResult(); val t0 = System.currentTimeMillis()
        twistSupplier = next; twistOnGroup = onGroup; twistQueryBudgetMs = queryBudgetMs
        this.workBudget = workBudget; work = 0L; groupWork = -1L
        try {
            return parityEquationsSeriesBody("", g, dom, null, null, true, 12, 200_000, false, false, maxCandidates, 3_000_000L, deadlineMs,
                true, true, false, true, res, {}, t0, { "" }, false)
        } finally { twistSupplier = null; twistOnGroup = null; twistImage = null; this.workBudget = Long.MAX_VALUE; if (groupWork < 0) groupWork = work }
    }

    /** Number of colour-preserving isomorphisms (g, [dom]) -> (g, [img]) by the series solver: candidates of H = (g, dom) as
     *  usual; per class C a cross candidate x0: C -> C' (same base, image tuples on H'); if an isomorphism exists the cross
     *  set equals x0 o T_C, otherwise it cannot (so a mismatch proves "0"). The unknown map is phi|_C = x0_C o t_C, t_C in
     *  T_C; the pair constraints test edges of phi, so allowed sets become cosets and the layered DFS counts them. Result
     *  autOrder = count (0 = not isomorphic), status EXACT, or a STOP. 2026-09-29, Christos: orbits for the decomposition-
     *  guided stabiliser chain without Traces. */
    internal fun parityIsoCount(g: Graph, dom: Array<Content>, img: Array<Content>, deadlineMs: Long = 120_000, maxCandidates: Int = 20_000): ParityResult {
        val res = ParityResult(); val t0 = System.currentTimeMillis()
        if (dom.map { it.serialize() }.sorted() != img.map { it.serialize() }.sorted()) { res.status = "EXACT"; res.autOrder = 0.0; res.stopDetail = "colour multisets differ"; return res }
        twistImage = img
        try {
            return parityEquationsSeriesBody("", g, dom, null, null, true, 12, 200_000, false, false, maxCandidates, 3_000_000L, deadlineMs,
                true, true, false, true, res, {}, t0, { "" }, false)
        } finally { twistImage = null }
    }

    /** Maps C -> C' (positions) induced by [base] (members of C, H side) and image tuples in C' on the H' side. */
    private fun crossCandidates(g: Graph, c: IntArray, cImg: IntArray, seedDom: (List<Int>) -> LongArray, seedImg: (List<Int>) -> LongArray,
                                posIn: IntArray, cap: Int, base: List<Int>, maxCandidates: Int): List<List<Int>> {
        val prefT = ArrayList<Int>(); val prefCol = ArrayList<LongArray>()
        for (k in 1..base.size) { val sd = seedDom(base.subList(0, k)); val t = hashWlStableRound(g, sd, cap); val col = hashWlRounds(g, sd, t); prefT.add(t); prefCol.add(LongArray(c.size) { col[c[it]] }) }
        val depth = base.size; val sortedPref = prefCol.map { it.sorted() }
        val perms = mutableListOf<List<Int>>(); var nodes = 0L
        fun dfs(tuple: MutableList<Int>) {
            if (++nodes > 5_000_000L) throw StopReason("STOP_CANDIDATE_NODES", "cross candidates: more than 5M partial maps")
            if (perms.size > maxCandidates) throw StopReason("STOP_TOO_MANY_CANDIDATES", "cross candidates: more than $maxCandidates")
            val d = tuple.size
            if (d > 0) {
                val col = hashWlRounds(g, seedImg(tuple), prefT[d - 1]); val on = LongArray(cImg.size) { col[cImg[it]] }
                if (on.sorted() != sortedPref[d - 1]) return
                if (d == depth) { val where = HashMap<Long, Int>().apply { on.forEachIndexed { i, x -> put(x, i) } }
                    perms.add(List(c.size) { i -> where.getValue(prefCol[depth - 1][i]) }); return }
                val want = prefCol[d - 1][posIn[base[d]]]
                for (i in cImg.indices) if (on[i] == want && cImg[i] !in tuple) { tuple.add(cImg[i]); dfs(tuple); tuple.removeAt(tuple.size - 1) }
            } else for (s0 in cImg) { tuple.add(s0); dfs(tuple); tuple.removeAt(tuple.size - 1) }
        }
        dfs(mutableListOf())
        return perms.distinct()
    }

    /** Node budget for [candidateRestrictions]' DFS over partial maps; unbounded except inside [parityAutOf]. Nets (slice
     *  graphs of projective planes) give that DFS no pruning at all, so without a count budget it never returns. */
    private var candidateNodeCap = Long.MAX_VALUE

    private fun parityEquationsSeriesBody(path: String, g: Graph, baseline: Array<Content>, aIn: Int?, bIn: Int?, quiet: Boolean, maxBase: Int, maxNodes: Int, usePi: Boolean,
                                          computeOrbits: Boolean, maxCandidates: Int, maxPairTable: Long, deadlineMs: Long, generalPrimes: Boolean, cosetMode: Boolean,
                                          irFallback: Boolean, nonSolvableStage: Boolean, res: ParityResult, say: (String) -> Unit, t0: Long, el: () -> String,
                                          crossCheck: Boolean): ParityResult {
        fun stop(status: String): ParityResult { res.status = status; res.seconds = (System.currentTimeMillis() - t0) / 1000.0; say("-> $status"); return res }
        val classes = (0 until g.n).groupBy { baseline[it] }.values.map { it.sorted().toIntArray() }.filter { it.size > 1 }
            .let { cl -> if (invariantStops) cl.sortedBy { baseline[it[0]].serialize() } else cl }
        res.n = g.n; res.m = g.m; res.piClasses = baseline.toHashSet().size; res.nonSingleton = classes.size
        res.classSizes = classes.groupingBy { it.size }.eachCount().toSortedMap().toString()
        say("==== $path -- SERIES PARITY EQUATIONS (n=${g.n} m=${g.m}, base partition ${if (usePi) "PI" else "canonical hash-1-WL"}) ====")
        say("[${el()}] PI: ${res.piClasses} classes, non-singleton ${classes.size}, sizes ${res.classSizes}")
        var a = aIn; var b = bIn
        if (a == null && b == null) {
            val (sub0, _) = g.induced(IntArray(g.n) { it })
            val r = dialysis.decomposition.defaultRootRule(sub0, baseline)
            val mate = (0 until g.n).firstOrNull { it != r && baseline[it] == baseline[r] }
            if (mate != null) { a = r; b = mate } else classes.minByOrNull { it.min() }?.let { a = it[0]; b = it[1] }
        }
        if (invariantStops || twistImage != null || twistSupplier != null) { a = null; b = null }
        val classBases = ArrayList<List<Int>>()
        val seedBase = LongArray(g.n) { sha64(baseline[it].serialize()) }
        val seedFor = { tuple: List<Int> -> seedBase.copyOf().also { s0 -> tuple.forEachIndexed { i, v -> s0[v] = mix64(s0[v] xor (0x5EED0000L + i)) } } }
        val classOf = IntArray(g.n) { -1 }; classes.forEachIndexed { i, c -> for (v in c) classOf[v] = i }
        val posIn = IntArray(g.n) { -1 }; classes.forEach { c -> c.forEachIndexed { i, v -> posIn[v] = i } }
        val excl = IntArray(1)
        var primesAll = listOf(2, 3, 2, 3, 2, 3)
        val ser = ArrayList<Series>()
        var deadline = if (deadlineMs == Long.MAX_VALUE) Long.MAX_VALUE else t0 + deadlineMs   // var: batch mode resets it for the query phase
        val details = mutableListOf<String>()
        // With generalPrimes: first collect every class's candidate set, then take the primes dividing any |T_C|.
        val candidateSets = ArrayList<Set<List<Int>>>()
        for (c in classes) {
            // with the fallback enabled, candidate listing gets a third of the budget; running out hands over to the fallback
            val candDeadline = if (irFallback && deadline != Long.MAX_VALUE) t0 + deadlineMs / 3 else deadline
            val perms = try { if (invariantStops) candidateRestrictionsInvariant(g, c, seedFor, posIn, g.n + 2, excl, maxBase, maxCandidates) else candidateRestrictions(g, c, seedFor, posIn, g.n + 2, excl, maxBase, maxCandidates, candDeadline)
                                  ?: candidateRestrictions(g, c, seedFor, posIn, g.n + 2, excl, maxBase, maxCandidates, candDeadline, baseRule = 1)
                                      ?.also { say("   class of size ${c.size}: default base too long, largest-cell base used") }
                                  ?: candidateRestrictions(g, c, seedFor, posIn, g.n + 2, excl, maxBase, maxCandidates, candDeadline, baseRule = 2)
                                      ?.also { say("   class of size ${c.size}: default base too long, smallest-cell base used") } }
                        catch (e: StopReason) {
                            if (irFallback && (e.status == "STOP_TOO_MANY_CANDIDATES" || e.status == "STOP_TIME")) {
                                say("   candidate list too large (${e.detail}) -> generator-based IR fallback")
                                return try { irAutomorphisms(g, baseline, res, a, b, deadline, say = say).also { it.seconds = (System.currentTimeMillis() - t0) / 1000.0; it.stopDetail = "fallback: ${e.detail}" } }
                                       catch (e2: StopReason) { res.stopDetail = "fallback after [${e.detail}] failed: ${e2.detail}"; stop(e2.status) }
                            }
                            res.stopDetail = e.detail; return stop(e.status)
                        }
            if (perms == null) {
                if (irFallback) {
                    say("   base too long for class of size ${c.size} -> generator-based IR fallback")
                    return try { irAutomorphisms(g, baseline, res, a, b, deadline, say = say).also { it.seconds = (System.currentTimeMillis() - t0) / 1000.0; it.stopDetail = "fallback: class of size ${c.size} needs a base > $maxBase" } }
                           catch (e2: StopReason) { res.stopDetail = "fallback failed: ${e2.detail}"; stop(e2.status) }
                }
                res.stopDetail = "class of size ${c.size}: individualising $maxBase base vertices does not split it into singletons"; return stop("STOP_BASE_TOO_LONG(>$maxBase)")
            }
            candidateSets.add(perms.toSet()); classBases.add(lastBase); res.maxT = maxOf(res.maxT, perms.size); res.maxBaseLen = maxOf(res.maxBaseLen, lastBaseLen)
        }
        val maxCycles = 8
        val primeCycle = if (generalPrimes) candidateSets.flatMap { primeFactors(it.size) }.toSortedSet().toList().ifEmpty { listOf(2) } else listOf(2, 3)
        val mixed = nonSolvableStage && generalPrimes && cosetMode   // non-abelian levels exist only in coset mode
        if (generalPrimes) primesAll = if (mixed) List(maxCycles) { primeCycle + 0 }.flatten() else List(maxCycles) { primeCycle }.flatten()
        for ((ci, c) in classes.withIndex()) {
            val tset = candidateSets[ci]
            val (srG, whyG) = if (mixed) buildSeriesMixed(tset, c.size, primeCycle, maxCycles)
                else if (generalPrimes) buildSeriesGeneral(tset, c.size, primeCycle, maxCycles) else (buildSeries(tset, c.size, primesAll) to "")
            val sr = srG
            if (sr == null) {
                res.notGroup++
                val id = Perm.id(c.size)
                val isGroup = Perm.isGroup(tset, c.size)
                val why = if (generalPrimes && whyG.isNotEmpty()) whyG else if (!isGroup) "candidate set T_C (|T|=${tset.size}) is NOT a group (not closed under composition)" else {
                    fun order(x: List<Int>): Int { var r = x; var k = 1; while (r != id) { r = Perm.comp(x, r); k++ }; return k }
                    var m = tset.size; var e2 = 0; var e3 = 0; while (m % 2 == 0) { m /= 2; e2++ }; while (m % 3 == 0) { m /= 3; e3++ }
                    "T_C is a group of order ${tset.size} = 2^$e2*3^$e3*$m with element orders ${tset.groupingBy { order(it) }.eachCount().toSortedMap()}, " +
                        "but has no normal series with elementary-abelian factors along primes $primesAll" + if (m > 1) " (order has a prime factor > 3)" else ""
                }
                details.add("class of size ${c.size}: $why")
                say("   class size ${c.size}: $why")
                continue
            }
            ser.add(sr)
        }
        res.excluded = excl[0]
        if (res.notGroup > 0) {
            res.stopDetail = "${res.notGroup} class(es) failed: " + details.groupingBy { it.replace(Regex("class of size \\d+: "), "") }.eachCount().entries.joinToString(" ; ") { (k, v) -> "${v}x [$k]" }
            if (irFallback) {   // the generator-based engine needs neither solvability nor a series
                val why = res.stopDetail
                say("   no layered series (${why.take(80)}) -> generator-based IR fallback")
                return try { irAutomorphisms(g, baseline, res, a, b, deadline, say = say).also { it.seconds = (System.currentTimeMillis() - t0) / 1000.0; it.stopDetail = "fallback: $why" } }
                       catch (e2: StopReason) { res.stopDetail = "fallback after [$why] failed: ${e2.detail}"; stop(e2.status) }
            }
            return stop(when {
                details.any { it.contains("is NOT a group") } -> "STOP_NOT_A_GROUP"
                details.any { it.contains("NOT solvable") } -> "STOP_NOT_SOLVABLE"
                else -> "STOP_NO_SERIES" })
        }
        val levels = (primesAll.indices).filter { l -> ser.any { it.k[l] > 0 } }
        val primes = levels.map { primesAll[it] }
        say("[${el()}] series levels (prime:total dims) " + levels.joinToString(" ") { l -> if (primesAll[l] == 0) "NA:${ser.count { it.k[l] > 0 }}cls(max ${ser.maxOf { it.na[l]?.size ?: 1 }})" else "${primesAll[l]}:${ser.sumOf { it.k[l] }}" } +
            "; max |T| ${ser.maxOfOrNull { it.elems.size } ?: 1}")
        val off = levels.map { l -> IntArray(classes.size).also { o -> var acc = 0; for (i in classes.indices) { o[i] = acc; acc += ser[i].k[l] } } }
        val nv = levels.map { l -> ser.sumOf { it.k[l] } }
        res.nVars = nv.sum()
        // allowed pairs
        val pairEdges = HashMap<Pair<Int, Int>, MutableList<Pair<Int, Int>>>()
        for (u in 0 until g.n) for (w in g.adj[u]) if (u < w) {
            val cu = classOf[u]; val cw = classOf[w]
            if (cu < 0 && cw < 0) continue
            pairEdges.getOrPut(if (cu <= cw) cu to cw else cw to cu) { mutableListOf() }.add(u to w)
        }
        // two-sided mode: global vertex map xi (cross candidate x0 per class, counterpart per singleton)
        val xi = IntArray(g.n) { it }
        twistImage?.let { imgCol ->
            val imgKey = Array(g.n) { imgCol[it].serialize() }; val domKey = Array(g.n) { baseline[it].serialize() }
            val imgByKey = (0 until g.n).groupBy { imgKey[it] }
            val seedImgBase = LongArray(g.n) { sha64(imgKey[it]) }
            val seedImg = { tuple: List<Int> -> seedImgBase.copyOf().also { s0 -> tuple.forEachIndexed { i, v -> s0[v] = mix64(s0[v] xor (0x5EED0000L + i)) } } }
            for (v in 0 until g.n) if (classOf[v] < 0) xi[v] = imgByKey.getValue(domKey[v]).single()
            for ((ci, c) in classes.withIndex()) {
                val cImg = imgByKey.getValue(domKey[c[0]]).sorted().toIntArray()
                val xs = try { crossCandidates(g, c, cImg, seedFor, seedImg, posIn, g.n + 2, classBases[ci], maxCandidates) } catch (e: StopReason) { res.stopDetail = e.detail; return stop(e.status) }
                if (xs.isEmpty()) { res.autOrder = 0.0; res.stopDetail = "no cross candidate for a class of size ${c.size}"; res.status = "EXACT"; res.seconds = (System.currentTimeMillis() - t0) / 1000.0; return res }
                val x0 = xs[0]; val inv = IntArray(c.size); x0.forEachIndexed { i, j -> inv[j] = i }
                val back = xs.map { x -> List(c.size) { i -> inv[x[i]] } }.toSet()
                if (back != candidateSets[ci]) { res.autOrder = 0.0; res.stopDetail = "cross set is not a coset x0 o T_C for a class of size ${c.size}"; res.status = "EXACT"; res.seconds = (System.currentTimeMillis() - t0) / 1000.0; return res }
                for ((i, v) in c.withIndex()) xi[v] = cImg[x0[i]]
            }
        }
        val allEdges: HashSet<Pair<Int, Int>>? = if (twistImage == null) null else HashSet<Pair<Int, Int>>().also { h -> for (u in 0 until g.n) for (w in g.adj[u]) if (u < w) h.add(u to w) }
        if (allEdges != null) for (u in 0 until g.n) for (w in g.adj[u]) if (u < w && classOf[u] < 0 && classOf[w] < 0 && (minOf(xi[u], xi[w]) to maxOf(xi[u], xi[w])) !in allEdges) {
            res.autOrder = 0.0; res.stopDetail = "an edge between fixed vertices is not preserved"; res.status = "EXACT"; res.seconds = (System.currentTimeMillis() - t0) / 1000.0; return res }
        val constraints = mutableListOf<Triple<Int, Int, List<Pair<List<Int>, List<Int>>>>>()   // (c1, c2 or -1 for unary), allowed
        // two-sided mode builds the constraints twice: untwisted (the stabiliser group, as usual) and twisted through xi
        val constraintsTw: MutableList<Triple<Int, Int, List<Pair<List<Int>, List<Int>>>>>? = if (twistImage != null) mutableListOf() else null
        val idXi = IntArray(g.n) { it }
        val invPerm = HashMap<List<Int>, List<Int>>()
        for (twPass in (if (twistImage != null) listOf(false, true) else listOf(false))) {
        val xiCur = if (twPass) xi else idXi
        val consCur = if (twPass) constraintsTw!! else constraints
        for ((key, es) in pairEdges) {
            val (c1, c2) = key
            val edgeSet = es.map { (x, y) -> minOf(x, y) to maxOf(x, y) }.toHashSet()
            val l1 = if (c1 >= 0) ser[c1].elems else listOf(emptyList()); val l2 = if (c2 >= 0 && c2 != c1) ser[c2].elems else listOf(emptyList())
            // Large tables between two DIFFERENT classes: derive p2 from p1 via neighbourhood signatures (N(p2 w) ∩ C1 = p1(N(w) ∩ C1))
            // instead of testing all |T1| x |T2| pairs; only above the old cap, so smaller instances keep the original path.
            res.maxPairTable = maxOf(res.maxPairTable, l1.size.toLong() * l2.size)
            val fastPairs = l1.size.toLong() * l2.size > maxPairTable && c1 >= 0 && c2 >= 0 && c2 != c1
            if (!fastPairs && l1.size.toLong() * l2.size > maxPairTable) {
                if (irFallback) {
                    say("   pair table ${l1.size} x ${l2.size} too large -> generator-based IR fallback")
                    return try { irAutomorphisms(g, baseline, res, a, b, deadline, say = say).also { it.seconds = (System.currentTimeMillis() - t0) / 1000.0; it.stopDetail = "fallback: pair table ${l1.size} x ${l2.size}" } }
                           catch (e2: StopReason) { res.stopDetail = "fallback failed: ${e2.detail}"; stop(e2.status) }
                }
                res.stopDetail = "pair constraint table ${l1.size} x ${l2.size} exceeds $maxPairTable"; return stop("STOP_PAIR_TABLE_TOO_LARGE")
            }
            if (overBudget(deadline)) { res.stopDetail = "time budget exceeded while building pair constraints"; return stop("STOP_TIME") }
            work += l1.size.toLong() * (if (fastPairs) 1L else l2.size.toLong()) * (es.size + 1)
            val allowed = mutableListOf<Pair<List<Int>, List<Int>>>()
            fun edgesOk(p1: List<Int>, p2: List<Int>): Boolean {
                // two-sided pass: phi|_C = xi_C o t_C^-1, so the solution set is Aut(H) o a^-1 -- prefix classes are H_l o y,
                // matching the series digits (additive under LEFT composition) that existsFrom's L_l pruning relies on.
                // (phi = xi o t gave a o Aut(H): prefix classes are cosets of a CONJUGATE of H_l -> false "no" on lattice-6.)
                val q1 = if (twPass) invPerm.getOrPut(p1) { val r = IntArray(p1.size); p1.forEachIndexed { i2, j2 -> r[j2] = i2 }; r.toList() } else p1
                val q2 = if (twPass) invPerm.getOrPut(p2) { val r = IntArray(p2.size); p2.forEachIndexed { i2, j2 -> r[j2] = i2 }; r.toList() } else p2
                val img = { x: Int -> val cx = classOf[x]; when { cx < 0 -> x; cx == c1 -> classes[c1][q1[posIn[x]]]; else -> classes[c2][q2[posIn[x]]] } }
                return es.all { (x, y) -> val u2 = xiCur[img(x)]; val w2 = xiCur[img(y)]; (minOf(u2, w2) to maxOf(u2, w2)) in (allEdges ?: edgeSet) }
            }
            if (fastPairs) {
                val n2 = classes[c2].size
                val nb = Array(n2) { mutableListOf<Int>() }
                for ((x, y) in es) { val (u1, w2) = if (classOf[x] == c1) x to y else y to x; nb[posIn[w2]].add(posIn[u1]) }
                val sig = HashMap<List<Int>, MutableList<Int>>()
                if (!twPass) { for (j in 0 until n2) sig.getOrPut(nb[j].sorted()) { mutableListOf() }.add(j) }
                else {
                    // twisted: phi|_C = xi_C o t_C^-1. For each image vertex z = xi(C2[k]) its C1'-neighbourhood, pulled back
                    // through xi to C1 positions, keys position k; the applied map t2^-1 must send j to such a k.
                    val xiInv = IntArray(g.n); for (v in 0 until g.n) xiInv[xiCur[v]] = v
                    val c1Img = classes[c1].map { xiCur[it] }.toHashSet()
                    for (k in 0 until n2) { val z = xiCur[classes[c2][k]]
                        sig.getOrPut(g.adj[z].filter { it in c1Img }.map { posIn[xiInv[it]] }.sorted()) { mutableListOf() }.add(k) }
                }
                // content -> the element object itself: allowed pairs must hold the very lists of [Series.elems], or every later
                // Series.dig falls back to content-hashing a whole permutation (2026-10-01: hypercube-8 spent most of depth 2 there)
                val t2 = HashMap<List<Int>, List<Int>>(l2.size * 2).also { m -> for (x in l2) m[x] = x }
                for (p1 in l1) {
                    work += n2
                    if (overBudget(deadline)) { res.stopDetail = "time budget exceeded while building pair constraints"; return stop("STOP_TIME") }
                    val q1 = if (twPass) invPerm.getOrPut(p1) { val r = IntArray(p1.size); p1.forEachIndexed { i2, j2 -> r[j2] = i2 }; r.toList() } else p1
                    val cand = Array(n2) { j -> sig[nb[j].map { q1[it] }.sorted()] ?: emptyList<Int>() }
                    if (cand.any { it.isEmpty() }) continue
                    fun fromApplied(a: List<Int>): List<Int> = if (!twPass) a else { val r = IntArray(a.size); a.forEachIndexed { i2, j2 -> r[j2] = i2 }; r.toList() }
                    val p2s = if (cand.all { it.size == 1 }) listOfNotNull(t2[fromApplied(List(n2) { cand[it][0] })])
                              else l2.filter { p2 ->
                                  val applied = if (twPass) invPerm.getOrPut(p2) { val r = IntArray(p2.size); p2.forEachIndexed { i2, j2 -> r[j2] = i2 }; r.toList() } else p2
                                  (0 until n2).all { applied[it] in cand[it] } }
                    for (p2 in p2s) if (edgesOk(p1, p2)) allowed.add(p1 to p2)
                }
                if (allowed.size > maxPairTable) { res.stopDetail = "pair constraint ${l1.size} x ${l2.size}: ${allowed.size} allowed pairs exceed $maxPairTable"; return stop("STOP_PAIR_TABLE_TOO_LARGE") }
                say("   pair (${c1},${c2}) ${l1.size} x ${l2.size}: ${allowed.size} allowed pairs via neighbourhood signatures")
            } else for (p1 in l1) for (p2 in l2) if (edgesOk(p1, p2)) allowed.add(p1 to p2)
            if (allowed.isEmpty()) {
                if (twPass) { res.autOrder = 0.0; res.stopDetail = "a pair constraint has no allowed pair"; res.status = "EXACT"; res.seconds = (System.currentTimeMillis() - t0) / 1000.0; return res }
                return stop("STOP_EMPTY_CONSTRAINT")
            }
            consCur.add(Triple(c1, if (c2 == c1) -1 else c2, allowed))
        }
        }
        fun affineEqs(pr: Int, m: Int, vs: List<IntArray>): List<Pair<IntArray, Int>>? {
            // EXACT coset test in O(|S| m^2) instead of O(|S|^2): D = {v - x0} lies in span(D), and D is a subgroup iff
            // it IS span(D), i.e. iff |D| (distinct) == q^rank(D). Then the equations are the annihilator of a basis.
            val x0 = vs[0]; val d = vs.map { v -> IntArray(m) { ((v[it] - x0[it]) % pr + pr) % pr } }
            val distinct = d.map { it.toList() }.toHashSet().size
            val basis = rowBasis(pr, m, d)
            if (Math.pow(pr.toDouble(), basis.size.toDouble()) != distinct.toDouble()) return null
            return dualBasis(pr, m, basis).map { y -> y to ((0 until m).sumOf { y[it] * x0[it] } % pr) }
        }
        var nodes = 0; var nonCoset = 0; var aborted = false
        // Optional explicit enumeration of Aut(G) (for orbit counts): every leaf's full affine solution space.
        var enumerate = false; val enumLimit = 200_000
        val uf = IntArray(g.n) { it }
        fun find(x: Int): Int { var r = x; while (uf[r] != r) r = uf[r]; var y = x; while (uf[y] != r) { val nx = uf[y]; uf[y] = r; y = nx }; return r }
        var enumCount = 0; var enumAllOk = true
        fun sigmaOf(levelVecs: List<IntArray>): IntArray {
            val sigma = IntArray(g.n) { it }
            for ((ci, c) in classes.withIndex()) {
                val d = primesAll.indices.map { l -> val li = levels.indexOf(l); if (li < 0) IntArray(0) else IntArray(ser[ci].k[l]) { levelVecs[li][off[li][ci] + it] } }
                val perm = ser[ci].byDigits.getValue(Series.key(d))
                for ((i, v) in c.withIndex()) sigma[v] = c[perm[i]]
            }
            return sigma
        }
        /** DFS over levels. [fixed][li] = chosen level-li solution vector (global over classes). Returns count
         *  of leaves (as a Double) and, if [wantWitness], the first full solution. */
        fun dfs(li: Int, fixed: MutableList<IntArray>, cons: List<Triple<Int, Int, List<Pair<List<Int>, List<Int>>>>>, wantWitness: Boolean, witness: Array<List<IntArray>?>): Double {
            if (aborted) return 0.0
            if (++nodes > maxNodes) { aborted = true; return 0.0 }; if (nodes > res.dfsNodes) res.dfsNodes = nodes.toLong()
            val q = primes[li]; val l = levels[li]
            val sys = ModPSystem(q, maxOf(nv[li], 1))
            fun prefixOk(ci: Int, x: List<Int>): Boolean {
                val d = ser[ci].dig(x)
                for (lj in 0 until li) { val lv = levels[lj]; val kk = ser[ci].k[lv]; for (j in 0 until kk) if (d[lv][j] != fixed[lj][off[lj][ci] + j]) return false }
                return true
            }
            for ((c1, c2, allowed) in cons) {
                val k1 = if (c1 >= 0) ser[c1].k[l] else 0; val k2 = if (c2 >= 0) ser[c2].k[l] else 0
                val vs = allowed.filter { (p1, p2) -> (c1 < 0 || prefixOk(c1, p1)) && (c2 < 0 || prefixOk(c2, p2)) }
                    .map { (p1, p2) -> (if (c1 >= 0) ser[c1].dig(p1)[l] else IntArray(0)) + (if (c2 >= 0) ser[c2].dig(p2)[l] else IntArray(0)) }
                if (vs.isEmpty()) return 0.0
                if (k1 + k2 == 0) continue
                val eqs = affineEqs(q, k1 + k2, vs) ?: run { nonCoset++; aborted = true; return 0.0 }
                for ((y, rhs) in eqs) {
                    val row = IntArray(sys.nVars)
                    for (j in 0 until k1) row[off[li][c1] + j] = y[j]; for (j in 0 until k2) row[off[li][c2] + j] = y[k1 + j]
                    sys.add(row, rhs)
                }
            }
            val (rank, ok, part) = sys.solve()
            if (!ok) return 0.0
            val free = nv[li] - rank
            if (li == levels.size - 1) {
                if (wantWitness && witness[0] == null) witness[0] = fixed.map { it.copyOf() } + listOf(part!!.copyOf())
                if (enumerate) {
                    val nb0 = sys.nullBasis()
                    var sols = listOf(part!!.copyOf())
                    for (v in nb0) { val more = mutableListOf<IntArray>(); for (s0 in sols) for (e in 1 until q) more.add(IntArray(s0.size) { (s0[it] + e * v[it]) % q }); sols = sols + more; if (enumCount + sols.size > enumLimit) { aborted = true; return 0.0 } }
                    for (sol in sols) {
                        val sigma = sigmaOf(fixed + listOf(sol))
                        enumCount++
                        if (!(0 until g.n).all { u -> g.adj[u].all { x -> g.adj[sigma[u]].contains(sigma[x]) } }) enumAllOk = false
                        for (v in 0 until g.n) { val a0 = find(v); val b0 = find(sigma[v]); if (a0 != b0) uf[a0] = b0 }
                    }
                }
                return Math.pow(q.toDouble(), free.toDouble())
            }
            val nb = sys.nullBasis()
            var total = 0.0
            val sols = mutableListOf(part!!.copyOf())
            for (v in nb) { val more = mutableListOf<IntArray>(); for (s0 in sols) for (e in 1 until q) more.add(IntArray(s0.size) { (s0[it] + e * v[it]) % q }); sols.addAll(more); if (sols.size > maxNodes) { aborted = true; return 0.0 } }
            for (sol in sols) {
                fixed.add(sol); total += dfs(li + 1, fixed, cons, wantWitness, witness); fixed.removeAt(fixed.size - 1)
                if (aborted) return 0.0
                if (wantWitness && witness[0] != null) return total
            }
            return total
        }
        if (cosetMode) {
            // ── COSET MODE: no enumeration. H_l = automorphisms trivial on levels < l; L_l = their level-l digits
            // (a subspace); |Aut| = prod q_l^dim(L_l). For ANY prefix P the liftable level-l digits form a coset
            // of L_l (digits(h' y0) = digits(h') + digits(y0), h' in H_l normal in Aut), so existence checks
            // only walk cosets of L_l. Generators: one witness per basis vector of every L_l. ──
            val last = levels.size - 1
            fun zeroPrefix(li: Int) = List(li) { IntArray(maxOf(nv[it], 1)) }
            var calls = 0
            /** digits a prefix check on class [ci] compares below level [li] (work units per allowed pair and side) */
            fun prefixLen(ci: Int, li: Int): Long { if (ci < 0) return 0L; var s = 0L; for (lj in 0 until li) s += ser[ci].k[levels[lj]]; return s }
            fun filterWork(li: Int, cons: List<Triple<Int, Int, List<Pair<List<Int>, List<Int>>>>>) =
                SEARCH_W * cons.sumOf { (c1, c2, a) -> a.size.toLong() * (2 + prefixLen(c1, li) + prefixLen(c2, li)) }
            fun systemAt(li: Int, fixed: List<IntArray>, cons: List<Triple<Int, Int, List<Pair<List<Int>, List<Int>>>>>): ModPSystem? {
                val q = primes[li]; val l = levels[li]
                val sys = ModPSystem(q, maxOf(nv[li], 1))
                fun prefixOk(ci: Int, x: List<Int>): Boolean {
                    val d = ser[ci].dig(x)
                    for (lj in 0 until li) { val lv = levels[lj]; val kk = ser[ci].k[lv]; for (j in 0 until kk) if (d[lv][j] != fixed[lj][off[lj][ci] + j]) return false }
                    return true
                }
                for ((c1, c2, allowed) in cons) {
                    val k1 = if (c1 >= 0) ser[c1].k[l] else 0; val k2 = if (c2 >= 0) ser[c2].k[l] else 0
                    val vs = allowed.filter { (p1, p2) -> (c1 < 0 || prefixOk(c1, p1)) && (c2 < 0 || prefixOk(c2, p2)) }
                        .map { (p1, p2) -> (if (c1 >= 0) ser[c1].dig(p1)[l] else IntArray(0)) + (if (c2 >= 0) ser[c2].dig(p2)[l] else IntArray(0)) }
                    if (vs.isEmpty()) return null
                    if (k1 + k2 == 0) continue
                    work += SEARCH_W * vs.size * (k1 + k2) * (k1 + k2)   // affineEqs: O(|S| m^2)
                    val eqs = affineEqs(q, k1 + k2, vs) ?: throw StopReason("STOP_NOT_COSET", "a prefix-consistent allowed set is not a coset (layer structure not affine)")
                    for ((y, rhs) in eqs) {
                        val row = IntArray(sys.nVars)
                        for (j in 0 until k1) row[off[li][c1] + j] = y[j]; for (j in 0 until k2) row[off[li][c2] + j] = y[k1 + j]
                        sys.add(row, rhs)
                    }
                }
                return sys
            }
            fun rankOf(q: Int, m: Int, vs: List<IntArray>) = ModPSystem(q, m).also { sys -> vs.forEach { sys.add(it, 0) } }.solve().first
            val isNA = BooleanArray(levels.size) { primes[it] == 0 }
            val naOrder = DoubleArray(levels.size) { 1.0 }
            val naGens = arrayOfNulls<List<List<IntArray>>>(levels.size)
            val lb = arrayOfNulls<List<IntArray>>(levels.size)
            val maxCombos = 4096
            fun combos(q: Int, k: Int): Sequence<IntArray> = sequence {
                var total = 1L; repeat(k) { total *= q; if (total > maxCombos) throw StopReason("STOP_CODIM", "more than $maxCombos coset representatives to test at one level (spurious codimension too large)") }
                for (code in 0 until total.toInt()) { val c = IntArray(k); var x = code; for (i in 0 until k) { c[i] = x % q; x /= q }; yield(c) }
            }
            /** A full witness (level vectors li..last) extending [fixed], or null. */
            fun existsFrom(li: Int, fixed: List<IntArray>, cons: List<Triple<Int, Int, List<Pair<List<Int>, List<Int>>>>>, forced: Map<Int, Int>? = null): List<IntArray>? {
                if (++calls > maxNodes) throw StopReason("STOP_TOO_MANY_NODES", "more than $maxNodes existence checks"); if (calls > res.dfsNodes) res.dfsNodes = calls.toLong()
                work += cons.size + 1L
                if (overBudget(deadline)) throw StopReason("STOP_TIME", "time budget exceeded in coset search")
                if (isNA[li]) {
                    // NON-ABELIAN level: exhaustive forward-checked search over the factor elements of the classes
                    // that have one here; each pair's prefix-consistent allowed set gives a binary relation.
                    val l = levels[li]
                    val naCls = classes.indices.filter { ser[it].k[l] > 0 }
                    fun prefixOk(ci: Int, x: List<Int>): Boolean {
                        val d = ser[ci].dig(x)
                        for (lj in 0 until li) { val lv = levels[lj]; val kk = ser[ci].k[lv]; for (j in 0 until kk) if (d[lv][j] != fixed[lj][off[lj][ci] + j]) return false }
                        return true
                    }
                    val dom = HashMap<Int, Set<Int>>(); for (ci in naCls) dom[ci] = (0 until ser[ci].na.getValue(l).size).toHashSet()
                    val bin = HashMap<Int, MutableList<Pair<Int, Map<Int, Set<Int>>>>>()
                    for ((c1, c2, allowed) in cons) {
                        // 2026-10-01: the prefix filter below touches every allowed pair and compares its prefix digits on both
                        // sides; the surviving pairs then go through two digit maps and two relation tables
                        work += SEARCH_W * allowed.size * (2 + prefixLen(c1, li) + prefixLen(c2, li))
                        val k1 = if (c1 >= 0) ser[c1].k[l] else 0; val k2 = if (c2 >= 0) ser[c2].k[l] else 0
                        val vs = allowed.filter { (p1, p2) -> (c1 < 0 || prefixOk(c1, p1)) && (c2 < 0 || prefixOk(c2, p2)) }
                        if (vs.isEmpty()) return null
                        if (k1 + k2 == 0) continue
                        work += SEARCH_W * 4 * vs.size
                        val d1 = vs.map { (p1, _) -> if (k1 > 0) ser[c1].dig(p1)[l][0] else -1 }
                        val d2 = vs.map { (_, p2) -> if (k2 > 0) ser[c2].dig(p2)[l][0] else -1 }
                        if (k1 > 0) dom[c1] = dom.getValue(c1).intersect(d1.toSet())
                        if (k2 > 0) dom[c2] = dom.getValue(c2).intersect(d2.toSet())
                        if (k1 > 0 && k2 > 0) {
                            val fw = HashMap<Int, MutableSet<Int>>(); val bw = HashMap<Int, MutableSet<Int>>()
                            for (i in vs.indices) { fw.getOrPut(d1[i]) { hashSetOf() }.add(d2[i]); bw.getOrPut(d2[i]) { hashSetOf() }.add(d1[i]) }
                            bin.getOrPut(c1) { mutableListOf() }.add(c2 to fw); bin.getOrPut(c2) { mutableListOf() }.add(c1 to bw)
                        }
                    }
                    forced?.forEach { (ci, v) -> dom[ci]?.let { dom[ci] = if (v in it) setOf(v) else emptySet() } }
                    if (dom.values.any { it.isEmpty() }) return null
                    val assign = HashMap<Int, Int>()
                    fun dfsNA(domains: Map<Int, Set<Int>>): List<IntArray>? {
                        work += naCls.size + 1L
                        if (overBudget(deadline)) throw StopReason("STOP_TIME", "time budget exceeded in the non-abelian stage")
                        if (++calls > maxNodes) throw StopReason("STOP_TOO_MANY_NODES", "more than $maxNodes existence checks (non-abelian stage)"); if (calls > res.dfsNodes) res.dfsNodes = calls.toLong()
                        val open = naCls.filter { it !in assign }
                        if (open.isEmpty()) {
                            val vec = IntArray(maxOf(nv[li], 1)); for (ci in naCls) vec[off[li][ci]] = assign.getValue(ci)
                            if (li == last) return listOf(vec)
                            val w = existsFrom(li + 1, fixed + listOf(vec), cons) ?: return null
                            return listOf(vec) + w
                        }
                        val ci = open.minBy { domains.getValue(it).size }
                        for (v in domains.getValue(ci)) {
                            val nd = HashMap(domains); nd[ci] = setOf(v)
                            var ok = true
                            for ((o, rel) in bin[ci].orEmpty()) if (o !in assign && o != ci) {
                                work += SEARCH_W * nd.getValue(o).size
                                val sNew = nd.getValue(o).intersect(rel[v] ?: emptySet()); if (sNew.isEmpty()) { ok = false; break }; nd[o] = sNew
                            }
                            if (!ok) continue
                            assign[ci] = v
                            val w = dfsNA(nd); assign.remove(ci)
                            if (w != null) return w
                        }
                        return null
                    }
                    return dfsNA(dom)
                }
                work += filterWork(li, cons)   // systemAt filters every allowed set by the fixed prefix (digits on both sides)
                val sys = systemAt(li, fixed, cons) ?: return null
                work += sys.rows.size.toLong() * sys.nVars * minOf(sys.rows.size, sys.nVars).coerceAtLeast(1)   // elimination
                val (_, ok, part) = sys.solve(); if (!ok) return null
                if (li == last) return listOf(part!!)
                val q = primes[li]; val m = maxOf(nv[li], 1)
                val bas = sys.nullBasis(); val lset = lb[li]!!
                if (rankOf(q, m, bas + lset) != bas.size) return null            // L_l not inside this affine space: nothing liftable
                work += (bas.size + 1L) * (bas.size + lset.size + 1L) * m * m   // the rank tests below
                val comp = mutableListOf<IntArray>(); val cur = lset.toMutableList()
                for (bv in bas) if (rankOf(q, m, cur + listOf(bv)) > cur.size) { comp.add(bv); cur.add(bv) }
                for (c in combos(q, comp.size)) {
                    work += m.toLong() * (comp.size + 1)
                    val u = IntArray(m) { i -> var v = part!![i]; for (j in comp.indices) v += c[j] * comp[j][i]; ((v % q) + q) % q }
                    val w = existsFrom(li + 1, fixed + listOf(u), cons) ?: continue
                    return listOf(u) + w
                }
                return null
            }
            try {
                for (li in last downTo 0) {
                    if (isNA[li]) {
                        // L_l <= prod_C P_C (P_C = the perfect factor). Chain over the classes: S_i = level-l components on
                        // class i of liftable elements that are the identity on the classes before i; |L_l| = prod |S_i|.
                        // x not in S_i => the whole coset x*K (K = known part of S_i) is excluded, so only ~[P:S_i] + #gens tests.
                        val l = levels[li]
                        val forced = HashMap<Int, Int>(); var ord = 1.0; val gensW = mutableListOf<List<IntArray>>()
                        val sizes = mutableListOf<String>()
                        for (ci in classes.indices.filter { ser[it].k[l] > 0 }) {
                            val qs = ser[ci].na.getValue(l); val idx = HashMap<List<Int>, Int>(); qs.forEachIndexed { i, x -> idx[x] = i }
                            fun mul(i: Int, j: Int) = idx.getValue(Perm.comp(qs[i], qs[j]))
                            fun inv(i: Int) = idx.getValue(Perm.inv(qs[i]))
                            var kset = hashSetOf(0); val kGens = mutableListOf<Int>(); val excl = mutableListOf<Int>()
                            for (x in qs.indices) {
                                if (x in kset) continue
                                if (excl.any { e -> mul(inv(e), x) in kset }) continue
                                val w = existsFrom(li, zeroPrefix(li), constraints, forced + (ci to x))
                                if (w != null) {
                                    gensW.add(w); kGens.add(x)
                                    val cl = hashSetOf(0); val qd = ArrayDeque(listOf(0))
                                    while (qd.isNotEmpty()) { val y = qd.removeFirst(); for (gx in kGens) { val z = mul(y, gx); if (cl.add(z)) qd.add(z) } }
                                    kset = cl
                                } else excl.add(x)
                            }
                            ord *= kset.size; sizes.add("${kset.size}/${qs.size}"); forced[ci] = 0
                        }
                        naOrder[li] = ord; naGens[li] = gensW
                        say("   non-abelian level $li: |L| = $ord (per class |S_i|/|P_C|: ${sizes.joinToString(" ")})")
                        res.stopDetail = (if (res.stopDetail.isEmpty()) "" else "${res.stopDetail}; ") + "non-abelian stage: |L|=$ord (${sizes.joinToString(" ")})"
                        continue
                    }
                    val q = primes[li]; val m = maxOf(nv[li], 1)
                    val sys0 = systemAt(li, zeroPrefix(li), constraints) ?: throw StopReason("STOP_INTERNAL", "identity prefix infeasible at level $li")
                    val (_, ok0, _) = sys0.solve(); if (!ok0) throw StopReason("STOP_INTERNAL", "identity inconsistent at level $li")
                    val b0 = sys0.nullBasis()
                    if (li == last) { lb[li] = b0; continue }
                    val lbasis = mutableListOf<IntArray>(); val nonLift = mutableListOf<IntArray>()
                    for (bv in b0) {
                        var found = false
                        for (c in combos(q, nonLift.size)) {
                            val v = IntArray(m) { i -> var x = bv[i]; for (j in nonLift.indices) x += c[j] * nonLift[j][i]; ((x % q) + q) % q }
                            if (existsFrom(li + 1, zeroPrefix(li) + listOf(v), constraints) != null) { lbasis.add(v); found = true; break }
                        }
                        if (!found) nonLift.add(bv)
                    }
                    lb[li] = lbasis
                }
                val aut0 = levels.indices.fold(1.0) { acc, li -> acc * (if (isNA[li]) naOrder[li] else Math.pow(primes[li].toDouble(), lb[li]!!.size.toDouble())) }
                res.autOrder = aut0; res.autStr = aut0.toString()
                if (constraintsTw != null) {
                    // two-sided: an isomorphism H -> H' exists iff the twisted system has a witness; then there are |Aut(H)| of them
                    val w = if (levels.isEmpty()) listOf<IntArray>() else existsFrom(0, emptyList(), constraintsTw)
                    if (w != null) {
                        // phi|_C = xi_C o t_C^-1, t from the witness digits; singletons phi = xi. Verified edge by edge before use.
                        val t = if (levels.isEmpty()) IntArray(g.n) { it } else sigmaOf(w)
                        val tInv = IntArray(g.n); for (v in 0 until g.n) tInv[t[v]] = v
                        val phi = IntArray(g.n) { v -> xi[tInv[v]] }
                        val bij = phi.toSet().size == g.n
                        val edgesOk = bij && (0 until g.n).all { u -> g.adj[u].all { x -> g.adj[phi[u]].contains(phi[x]) } }
                        val colOk = bij && (0 until g.n).all { v -> twistImage!![phi[v]] == baseline[v] }
                        if (!edgesOk || !colOk) { res.stopDetail = "witness map failed verification (edges ${edgesOk}, colours ${colOk})"; return stop("STOP_WITNESS_INVALID") }
                        res.witnessMap = phi
                    }
                    res.autOrder = if (w != null) aut0 else 0.0; res.autStr = res.autOrder.toString()
                    res.status = "EXACT"; res.seconds = (System.currentTimeMillis() - t0) / 1000.0
                    return res
                }
                say("[${el()}] COSET MODE |Aut(G)| = ${res.autStr} (L dims ${levels.indices.map { if (isNA[it]) "NA:${naOrder[it]}" else "${primes[it]}^${lb[it]!!.size}" }}, existence checks $calls)")
                // generators: one witness per basis vector of every L_l
                val gens = mutableListOf<IntArray>(); var gensOk = true
                val witnesses = levels.indices.flatMap { li ->
                    if (isNA[li]) naGens[li]!!.map { w -> zeroPrefix(li) + w }
                    else lb[li]!!.map { v -> zeroPrefix(li) + listOf(v) + (if (li == last) emptyList() else existsFrom(li + 1, zeroPrefix(li) + listOf(v), constraints) ?: throw StopReason("STOP_INTERNAL", "basis vector lost its witness")) }
                }
                for (full in witnesses) {
                    val sigma = sigmaOf(full)
                    if (!(0 until g.n).all { u -> g.adj[u].all { x -> g.adj[sigma[u]].contains(sigma[x]) } }) gensOk = false
                    if (!(0 until g.n).all { u -> baseline[sigma[u]] == baseline[u] }) throw StopReason("STOP_BASE_NOT_INVARIANT", "a generator does not preserve the base colouring")
                    gens.add(sigma)
                }
                if (gensOk) res.generators = gens.toList()
                for (sigma in gens) for (v in 0 until g.n) { val a0 = find(v); val b0 = find(sigma[v]); if (a0 != b0) uf[a0] = b0 }
                res.orbits = (0 until g.n).map { find(it) }.toSet().size; res.orbitOf = IntArray(g.n) { find(it) }
                val n0 = if (path.isEmpty()) g.n else GraphIO.loadDimacs(File(path).toPath()).n
                res.orbitsOriginal = (0 until n0).map { find(it) }.toSet().size
                res.enumeratedAuts = gens.size; res.enumeratedAllVerified = gensOk
                say("[${el()}] ${gens.size} generators (all verified on G: $gensOk) -> ${res.orbits} orbits")
                twistSupplier?.let { sup ->
                    // H is solved (order, generators, orbits): report it, then give the query phase its own time budget
                    twistOnGroup?.invoke(res)
                    deadline = System.currentTimeMillis() + twistQueryBudgetMs; workBudget = Long.MAX_VALUE; groupWork = work
                    val allE = HashSet<Pair<Int, Int>>().also { h -> for (u in 0 until g.n) for (w in g.adj[u]) if (u < w) h.add(u to w) }
                    val inv = HashMap<List<Int>, List<Int>>()
                    fun invOf(p0: List<Int>) = inv.getOrPut(p0) { val r = IntArray(p0.size); p0.forEachIndexed { i2, j2 -> r[j2] = i2 }; r.toList() }
                    /** xi for image [imgCol], or null if no isomorphism is possible (cross set empty / not a coset / fixed edge). */
                    fun xiFor(imgCol: Array<Content>): IntArray? {
                        val xiQ = IntArray(g.n) { it }
                        val imgKey = Array(g.n) { imgCol[it].serialize() }; val domKey = Array(g.n) { baseline[it].serialize() }
                        if (imgKey.sorted() != domKey.sorted()) return null
                        val imgByKey = (0 until g.n).groupBy { imgKey[it] }
                        val seedImgBase = LongArray(g.n) { sha64(imgKey[it]) }
                        val seedImg = { tuple: List<Int> -> seedImgBase.copyOf().also { s0 -> tuple.forEachIndexed { i, v -> s0[v] = mix64(s0[v] xor (0x5EED0000L + i)) } } }
                        for (v in 0 until g.n) if (classOf[v] < 0) xiQ[v] = imgByKey.getValue(domKey[v]).single()
                        for ((ci, c) in classes.withIndex()) {
                            val cImg = imgByKey.getValue(domKey[c[0]]).sorted().toIntArray()
                            val xs = crossCandidates(g, c, cImg, seedFor, seedImg, posIn, g.n + 2, classBases[ci], maxCandidates)
                            if (xs.isEmpty()) return null
                            val x0 = xs[0]; val iv = IntArray(c.size); x0.forEachIndexed { i, j -> iv[j] = i }
                            if (xs.map { x -> List(c.size) { i -> iv[x[i]] } }.toSet() != candidateSets[ci]) return null
                            for ((i, v) in c.withIndex()) xiQ[v] = cImg[x0[i]]
                        }
                        for (u in 0 until g.n) for (w in g.adj[u]) if (u < w && classOf[u] < 0 && classOf[w] < 0 && (minOf(xiQ[u], xiQ[w]) to maxOf(xiQ[u], xiQ[w])) !in allE) return null
                        return xiQ
                    }
                    /** Twisted constraints for phi|_C = xi_C o t_C^-1 (see the lattice-6 note), or null if some pair has no allowed pair. */
                    fun twisted(xiQ: IntArray): List<Triple<Int, Int, List<Pair<List<Int>, List<Int>>>>>? {
                        val out = mutableListOf<Triple<Int, Int, List<Pair<List<Int>, List<Int>>>>>()
                        for ((key, es) in pairEdges) {
                            val (c1, c2) = key
                            val l1 = if (c1 >= 0) ser[c1].elems else listOf(emptyList()); val l2 = if (c2 >= 0 && c2 != c1) ser[c2].elems else listOf(emptyList())
                            fun ok(p1: List<Int>, p2: List<Int>): Boolean {
                                val q1 = if (c1 >= 0) invOf(p1) else p1; val q2 = if (c2 >= 0 && c2 != c1) invOf(p2) else p2
                                val img = { x: Int -> val cx = classOf[x]; when { cx < 0 -> x; cx == c1 -> classes[c1][q1[posIn[x]]]; else -> classes[c2][q2[posIn[x]]] } }
                                return es.all { (x, y) -> val u2 = xiQ[img(x)]; val w2 = xiQ[img(y)]; (minOf(u2, w2) to maxOf(u2, w2)) in allE }
                            }
                            val allowed = mutableListOf<Pair<List<Int>, List<Int>>>()
                            if (l1.size.toLong() * l2.size > maxPairTable && c1 >= 0 && c2 >= 0 && c2 != c1) {
                                val n2 = classes[c2].size
                                val nb = Array(n2) { mutableListOf<Int>() }
                                for ((x, y) in es) { val (u1, w2) = if (classOf[x] == c1) x to y else y to x; nb[posIn[w2]].add(posIn[u1]) }
                                val xiInv = IntArray(g.n); for (v in 0 until g.n) xiInv[xiQ[v]] = v
                                val c1Img = classes[c1].map { xiQ[it] }.toHashSet()
                                val sig = HashMap<List<Int>, MutableList<Int>>()
                                for (k in 0 until n2) { val z = xiQ[classes[c2][k]]; sig.getOrPut(g.adj[z].filter { it in c1Img }.map { posIn[xiInv[it]] }.sorted()) { mutableListOf() }.add(k) }
                                val t2 = HashMap<List<Int>, List<Int>>(l2.size * 2).also { m -> for (x in l2) m[x] = x }   // canonical objects (see above)
                                for (p1 in l1) {
                                    if (System.currentTimeMillis() > deadline) throw StopReason("STOP_TIME", "time budget exceeded building twisted constraints")
                                    val q1 = invOf(p1)
                                    val cand = Array(n2) { j -> sig[nb[j].map { q1[it] }.sorted()] ?: emptyList<Int>() }
                                    if (cand.any { it.isEmpty() }) continue
                                    val p2s = if (cand.all { it.size == 1 }) listOfNotNull(t2[invOf(List(n2) { cand[it][0] })])
                                              else l2.filter { p2 -> val q2 = invOf(p2); (0 until n2).all { q2[it] in cand[it] } }
                                    for (p2 in p2s) if (ok(p1, p2)) allowed.add(p1 to p2)
                                }
                            } else {
                                if (l1.size.toLong() * l2.size > maxPairTable) throw StopReason("STOP_PAIR_TABLE_TOO_LARGE", "twisted pair table ${l1.size} x ${l2.size}")
                                for (p1 in l1) for (p2 in l2) if (ok(p1, p2)) allowed.add(p1 to p2)
                            }
                            if (allowed.isEmpty()) return null
                            out.add(Triple(c1, if (c2 == c1) -1 else c2, allowed))
                        }
                        return out
                    }
                    var prevAns: Boolean? = null; var prevW: IntArray? = null
                    while (true) {
                        val img = sup(prevAns, prevW) ?: break
                        prevW = null
                        prevAns = try {
                            twistImage = img
                            val xiQ = xiFor(img)
                            val cons = xiQ?.let { twisted(it) }
                            if (xiQ == null || cons == null) false else {
                                calls = 0
                                val w = if (levels.isEmpty()) listOf<IntArray>() else existsFrom(0, emptyList(), cons)
                                if (w == null) false else {
                                    val t = if (levels.isEmpty()) IntArray(g.n) { it } else sigmaOf(w)
                                    val tInv = IntArray(g.n); for (v in 0 until g.n) tInv[t[v]] = v
                                    val phi = IntArray(g.n) { v -> xiQ[tInv[v]] }
                                    val good = phi.toSet().size == g.n && (0 until g.n).all { u -> g.adj[u].all { x -> g.adj[phi[u]].contains(phi[x]) } } &&
                                        (0 until g.n).all { v -> img[phi[v]] == baseline[v] }
                                    if (!good) null else { prevW = phi; true }
                                }
                            }
                        } catch (e: StopReason) { null } finally { twistImage = null }
                    }
                    res.status = "EXACT"; res.seconds = (System.currentTimeMillis() - t0) / 1000.0
                    return res
                }
                val qa = a; val qb = b
                if (qa != null && qb != null) {
                    val a: Int = qa; val b: Int = qb
                    res.query = "$a->$b"
                    // BFS over generators from a; compose along the path to get an explicit automorphism a -> b
                    val parent = IntArray(g.n) { -2 }; val via = IntArray(g.n) { -1 }; parent[a] = -1
                    val qd = ArrayDeque<Int>(); qd.add(a)
                    while (qd.isNotEmpty()) { val x = qd.removeFirst(); for ((gi, sg) in gens.withIndex()) { val y = sg[x]; if (parent[y] == -2) { parent[y] = x; via[y] = gi; qd.add(y) } } }
                    if (parent[b] == -2) res.queryVerdict = "NOT_ORBIT_MATES" else {
                        res.queryVerdict = "ORBIT_MATES"
                        var sigma = IntArray(g.n) { it }; var y = b
                        val path0 = mutableListOf<Int>(); while (y != a) { path0.add(via[y]); y = parent[y] }
                        for (gi in path0.reversed()) { val sg = gens[gi]; sigma = IntArray(g.n) { sg[sigma[it]] } }
                        res.explicitAutOk = sigma[a] == b && (0 until g.n).all { u -> g.adj[u].all { x -> g.adj[sigma[u]].contains(sigma[x]) } }
                    }
                    say("orbit query ${res.query}: ${res.queryVerdict}${res.explicitAutOk?.let { " (explicit automorphism verified: $it)" } ?: ""}")
                }
            } catch (e: StopReason) { res.stopDetail = e.detail; return stop(e.status) }
            res.status = "EXACT"; res.seconds = (System.currentTimeMillis() - t0) / 1000.0
            return res
        }
        val aut = if (levels.isEmpty()) 1.0 else dfs(0, mutableListOf(), constraints, false, arrayOfNulls(1))
        if (nonCoset > 0) { res.stopDetail = "a prefix-consistent allowed set is not a coset (layer structure not affine)"; return stop("STOP_NOT_COSET") }
        if (aborted) { res.stopDetail = "more than $maxNodes DFS nodes / layer solutions"; return stop("STOP_TOO_MANY_NODES(>$maxNodes)") }
        res.autOrder = aut; res.autStr = "%.6g".format(aut)
        say("[${el()}] |Aut(G)| = ${res.autStr} (DFS nodes $nodes)")
        if (computeOrbits && aut <= enumLimit) {
            enumerate = true; nodes = 0
            if (levels.isEmpty()) enumCount = 1 else dfs(0, mutableListOf(), constraints, false, arrayOfNulls(1))
            enumerate = false
            if (!aborted) {
                res.orbits = (0 until g.n).map { find(it) }.toSet().size; res.orbitOf = IntArray(g.n) { find(it) }
                val n0 = if (path.isEmpty()) g.n else GraphIO.loadDimacs(File(path).toPath()).n
                res.orbitsOriginal = (0 until n0).map { find(it) }.toSet().size
                res.enumeratedAuts = enumCount; res.enumeratedAllVerified = enumAllOk
                say("[${el()}] enumerated $enumCount automorphisms (all verified on G: $enumAllOk; equals |Aut|: ${enumCount.toDouble() == aut}) -> ${res.orbits} orbits")
            }
        }
        if (crossCheck && g.n <= 2500) say("   cross-check: Traces |Aut| = ${"%.6g".format(traces.certifyAll(g, listOf(IntArray(g.n) { it }), getcanon = false).stats.autOrder)}")
        if (a != null && b != null) {
            res.query = "$a->$b"
            val ca = classOf[a]
            if (ca < 0 || classOf[b] != ca) res.queryVerdict = "NOT_SAME_PI_CLASS" else {
                val toB = ser[ca].elems.filter { classes[ca][it[posIn[a]]] == b }
                if (toB.isEmpty()) res.queryVerdict = "NOT_ORBIT_MATES(excluded)" else {
                    val witness = arrayOfNulls<List<IntArray>>(1)
                    nodes = 0
                    val cnt = if (levels.isEmpty()) (if (toB.contains(Perm.id(classes[ca].size))) 1.0 else 0.0)
                              else dfs(0, mutableListOf(), constraints + Triple(ca, -1, toB.map { it to emptyList<Int>() }), true, witness)
                    if (aborted) return stop("STOP_TOO_MANY_NODES_QUERY")
                    res.queryVerdict = if (cnt > 0) "ORBIT_MATES" else "NOT_ORBIT_MATES"
                    val w = witness[0]
                    if (cnt > 0 && w != null) {
                        val sigma = IntArray(g.n) { it }
                        for ((ci, c) in classes.withIndex()) {
                            val d = primesAll.indices.map { l -> val li = levels.indexOf(l); if (li < 0) IntArray(0) else IntArray(ser[ci].k[l]) { w[li][off[li][ci] + it] } }
                            val perm = ser[ci].byDigits.getValue(Series.key(d))
                            for ((i, v) in c.withIndex()) sigma[v] = c[perm[i]]
                        }
                        res.explicitAutOk = sigma[a] == b && (0 until g.n).all { u -> g.adj[u].all { x -> g.adj[sigma[u]].contains(sigma[x]) } }
                    }
                }
            }
            say("orbit query ${res.query}: ${res.queryVerdict}${res.explicitAutOk?.let { " (explicit automorphism verified: $it)" } ?: ""}")
        }
        res.status = "EXACT"; res.seconds = (System.currentTimeMillis() - t0) / 1000.0
        say("[${el()}] ========================================================")
        return res
    }

    /**
     * Generator-based fallback (2026-09-27) for graphs whose local candidate groups are too large to list
     * (cmz: T_C = Aut, |T_C| ~ 2^(2k) k). Classic individualisation-refinement + stabiliser chain
     * (nauty-style; NOT the parity-equation idea): individualise a global base b_1..b_L until refinement is
     * discrete; bottom-up over d, the admissible images O_d of b_d are its colour class after individualising
     * b_1..b_(d-1); every w in O_d not yet in the orbit of the known generators is either realised by an
     * explicit, verified automorphism fixing b_1..b_(d-1) (then added as a generator) or ruled out by an
     * exhaustive search. Orbit-stabiliser: |Aut| = prod_d |orbit_d|, exact. Refinement colours are the
     * canonical hash-1-WL seeded by [baseline], so every automorphism preserves them.
     */
    private fun irAutomorphisms(g: Graph, baseline: Array<Content>, res: ParityResult, a: Int?, b: Int?, deadline: Long,
                                maxBaseLen: Int = 600, searchBudget: Int = 200_000, say: (String) -> Unit): ParityResult {
        val t0 = System.currentTimeMillis()
        val seedBase = LongArray(g.n) { sha64(baseline[it].serialize()) }
        fun seedFor(tuple: List<Int>) = seedBase.copyOf().also { s0 -> tuple.forEachIndexed { i, v -> s0[v] = mix64(s0[v] xor (0x5EED0000L + i)) } }
        // global base
        val base = mutableListOf<Int>(); val prefT = mutableListOf<Int>(); val prefCol = mutableListOf<LongArray>()
        while (true) {
            if (System.currentTimeMillis() > deadline) throw StopReason("STOP_TIME", "time budget exceeded while building the global base (length ${base.size})")
            val sd = seedFor(base); val t = hashWlStableRound(g, sd, g.n + 2); val col = hashWlRounds(g, sd, t)
            prefT.add(t); prefCol.add(col)
            val cells = (0 until g.n).groupBy { col[it] }.values.filter { it.size > 1 }
            if (cells.isEmpty()) break
            if (base.size >= maxBaseLen) throw StopReason("STOP_BASE_TOO_LONG", "global base longer than $maxBaseLen")
            base.add(cells.minWith(compareBy({ it.size }, { it.min() })).min())
        }
        val lenB = base.size
        val sortedPref = prefCol.map { it.sorted() }
        fun isAut(sg: IntArray) = (0 until g.n).all { u -> g.adj[u].all { x -> g.adj[sg[u]].contains(sg[x]) } }
        var nodes = 0
        /** Explicit automorphism with image tuple extending [tuple] (length = current depth), or null (exhaustive). */
        fun search(tuple: MutableList<Int>): IntArray? {
            if (++nodes > searchBudget) throw StopReason("STOP_SEARCH_BUDGET", "more than $searchBudget refinement nodes in the automorphism search")
            if (System.currentTimeMillis() > deadline) throw StopReason("STOP_TIME", "time budget exceeded in the automorphism search")
            val j = tuple.size
            val col = hashWlRounds(g, seedFor(tuple), prefT[j])
            if (col.sorted() != sortedPref[j]) return null
            if (j == lenB) {
                val where = HashMap<Long, Int>(g.n * 2).apply { col.forEachIndexed { v, x -> put(x, v) } }
                val sg = IntArray(g.n) { v -> where.getValue(prefCol[lenB][v]) }
                if (!isAut(sg)) return null
                if (!(0 until g.n).all { u -> baseline[sg[u]] == baseline[u] }) throw StopReason("STOP_BASE_NOT_INVARIANT", "an automorphism does not preserve the base colouring")
                return sg
            }
            val want = prefCol[j][base[j]]
            for (u in 0 until g.n) if (col[u] == want && u !in tuple) { tuple.add(u); val r = search(tuple); tuple.removeAt(tuple.size - 1); if (r != null) return r }
            return null
        }
        val gens = mutableListOf<IntArray>()
        var autOrder = 1.0
        val orbitSizes = IntArray(lenB)
        for (d in lenB - 1 downTo 0) {
            val bd = base[d]
            val admissible = (0 until g.n).filter { prefCol[d][it] == prefCol[d][bd] }
            val inOrbit = BooleanArray(g.n)
            fun closeOrbit() {
                val qd = ArrayDeque<Int>(); for (v in 0 until g.n) if (inOrbit[v]) qd.add(v)
                while (qd.isNotEmpty()) { val x = qd.removeFirst(); for (sg in gens) { val y = sg[x]; if (!inOrbit[y]) { inOrbit[y] = true; qd.add(y) } } }
            }
            inOrbit[bd] = true; closeOrbit()
            for (w in admissible) {
                if (inOrbit[w]) continue
                val sg = search((base.subList(0, d) + listOf(w)).toMutableList())
                if (sg != null) { gens.add(sg); inOrbit[w] = true; closeOrbit() }
            }
            orbitSizes[d] = inOrbit.count { it }
            autOrder *= orbitSizes[d]
        }
        res.autOrder = autOrder; res.autStr = autOrder.toString()
        val uf = IntArray(g.n) { it }
        fun find(x: Int): Int { var r = x; while (uf[r] != r) r = uf[r]; return r }
        for (sg in gens) for (v in 0 until g.n) { val a0 = find(v); val b0 = find(sg[v]); if (a0 != b0) uf[a0] = b0 }
        res.orbits = (0 until g.n).map { find(it) }.toSet().size; res.orbitOf = IntArray(g.n) { find(it) }
        res.enumeratedAuts = gens.size; res.enumeratedAllVerified = true   // every generator passed isAut() before being added
        say("   IR fallback: base length $lenB, orbit sizes ${orbitSizes.filter { it > 1 }.size} non-trivial, |Aut| = $autOrder, ${gens.size} generators, ${res.orbits} orbits, $nodes search nodes (${(System.currentTimeMillis() - t0) / 1000.0}s)")
        if (a != null && b != null) {
            res.query = "$a->$b"
            val parent = IntArray(g.n) { -2 }; val via = IntArray(g.n) { -1 }; parent[a] = -1
            val qd = ArrayDeque<Int>(); qd.add(a)
            while (qd.isNotEmpty()) { val x = qd.removeFirst(); for ((gi, sg) in gens.withIndex()) { val y = sg[x]; if (parent[y] == -2) { parent[y] = x; via[y] = gi; qd.add(y) } } }
            if (parent[b] == -2) res.queryVerdict = "NOT_ORBIT_MATES" else {
                res.queryVerdict = "ORBIT_MATES"
                var sigma = IntArray(g.n) { it }; var y: Int = b
                val path0 = mutableListOf<Int>(); while (y != a) { path0.add(via[y]); y = parent[y] }
                for (gi in path0.reversed()) { val sg = gens[gi]; sigma = IntArray(g.n) { sg[sigma[it]] } }
                res.explicitAutOk = sigma[a] == b && isAut(sigma)
            }
        }
        res.status = "EXACT_IR"
        return res
    }

    /** Is the PI colouring repeatable and invariant? Runs dispatchColouring twice on G and once on a
     *  random relabelling, compares class counts and the per-vertex class multisets under the relabelling. */
    @Test fun piDeterminismCheck() {
        for (f in listOf("graphs/cfi-rigid-d3/cfi-rigid-d3-0180-01-1", "graphs/cfi-rigid-z3/cfi-rigid-z3-0180-01-2", "graphs/cfi-rigid-r2/cfi-rigid-r2-0068-03-1")) {
            val g = loadForTrace(f)
            val c1 = dispatchColouring(g).colouring; val c2 = dispatchColouring(g).colouring
            val perm = (0 until g.n).shuffled(kotlin.random.Random(11)).toIntArray()
            val c3 = dispatchColouring(g.relabeled(perm)).colouring
            val same12 = (0 until g.n).all { c1[it] == c2[it] }
            val same13 = (0 until g.n).all { c1[it] == c3[perm[it]] }
            println("PI-CHECK $f: classes run1=${c1.toHashSet().size} run2=${c2.toHashSet().size} relabelled=${c3.toHashSet().size}; run1==run2 per vertex: $same12; invariant under relabelling (same Content per vertex): $same13")
        }
    }

    /** Does clearing the ColoredAHU intern pool before each PI make PI history-independent? */
    @Test fun piHistoryCheck() {
        val target = "graphs/cfi-rigid-z3/cfi-rigid-z3-0180-01-2"
        val warmups = listOf("graphs/cfi-rigid-d3/cfi-rigid-d3-0180-01-1", "graphs/cfi-rigid-z3/cfi-rigid-z3-0180-01-1", "graphs/cfi-rigid-r2/cfi-rigid-r2-0504-01-1", "graphs/cfi-rigid-d3/cfi-rigid-d3-0360-02-1")
        val gT = loadForTrace(target)
        val perm = (0 until gT.n).shuffled(kotlin.random.Random(5)).toIntArray()
        for (clear in listOf(false, true)) {
            val counts = mutableListOf<Int>()
            var invariant = true
            for (w in listOf(null) + warmups) {
                if (w != null) { if (clear) dialysis.ahu.ColoredAHU.clearInternPool(); dispatchColouring(loadForTrace(w)) }
                if (clear) dialysis.ahu.ColoredAHU.clearInternPool()
                val c = dispatchColouring(gT).colouring
                if (clear) dialysis.ahu.ColoredAHU.clearInternPool()
                val cr = dispatchColouring(gT.relabeled(perm)).colouring
                counts.add(c.toHashSet().size)
                if (!(0 until gT.n).all { c[it] == cr[perm[it]] }) invariant = false
            }
            println("PI-HISTORY clearPool=$clear: class counts of $target after successive warm-ups: $counts; relabel-invariant at every step: $invariant")
        }
    }

    // ─────────── PI history-dependence hunt (Christos's colleague, 2026-09-26) ───────────

    /**
     * Test-local copy of [dialysis.refinement.initialPhase] (default parameters, bipartite dispatch
     * path) that differs from the original in ONE place only: Phase 1's anchoring key. [canonicalKey]
     * = false reproduces InitialPhase.kt:139 exactly (AHU raw `rootId`, an intern-pool id whose
     * magnitude depends on pool history); true uses the AHU canonical form STRING instead. Everything
     * else -- Phase 0/1/2/3 structure, anchor() ordering, cost guard, stale-streak guard, Phase 2 cell
     * order -- is a line-by-line copy.
     */
    private fun initialPhaseCopy(g: Graph, chi: Array<Content>, canonicalKey: Boolean): Array<Content> {
        fun anchorCopy(col: Array<Content>, cls: IntArray, key: (Int) -> String): Int {
            if (cls.size <= 1) return 0
            val groups = cls.groupBy(key).entries.sortedBy { it.key }
            if (groups.size <= 1) return 0
            val originalColor = col[cls[0]]
            groups.forEachIndexed { rank, (_, members) ->
                if (rank == 0) return@forEachIndexed
                val newColor = Content.Tup(listOf(originalColor, Content.Num(rank.toLong())))
                for (v in members) col[v] = newColor
            }
            return groups.size - 1
        }
        val phase2CostGuard = 1_000_000_000L
        val p0 = colorRefine1WL(g, chi)
        if (p0.isDiscrete()) return p0.color
        val needsWork = BooleanArray(g.n)
        for (cell in p0.cells) if (cell.size > 1) for (v in cell) needsWork[v] = true
        val store = dialysis.decomposition.DecompositionStore.build(g, needsWork)
        val treeOrphanKey = arrayOfNulls<Content>(g.n)
        for (v in 0 until g.n) {
            if (!needsWork[v]) continue
            val (treeVerts, orphanCount) = store.treeAndOrphanCount(v)
            val (treeGraph, treeOldToNew) = g.induced(treeVerts)
            val ahuColors = treeVerts.associate { origId -> treeOldToNew[origId] to chi[origId].serialize() }
            val ahuResult = dialysis.ahu.ColoredAHU.compute(treeGraph, ahuColors, root = treeOldToNew[v])
            treeOrphanKey[v] = if (canonicalKey) Content.Tup(listOf(Content.Str(ahuResult.treeCanonicalForm), Content.Num(orphanCount.toLong())))
                               else Content.Tup(listOf(Content.Num(ahuResult.rootId.toLong()), Content.Num(orphanCount.toLong())))
        }
        val chi1 = p0.color.copyOf()
        for (cell in p0.cells) anchorCopy(chi1, cell) { v -> treeOrphanKey[v]!!.serialize() }
        val p1 = colorRefine1WL(g, chi1)
        if (p1.isDiscrete()) return p1.color
        val chi2 = p1.color.copyOf()
        var refined = false
        var phase2CostSoFar = 0L
        for (cell in p1.cells) {
            if (cell.size <= 1) continue
            val representativeRemainderSize = store.remainderComponents(cell[0]).sumOf { it.size }.toLong()
            val estimatedCellCost = cell.size.toLong() * representativeRemainderSize
            if (phase2CostSoFar + estimatedCellCost > phase2CostGuard) break
            phase2CostSoFar += estimatedCellCost
            fun remainderKeyOf(v: Int): String {
                val components = store.remainderComponents(v).map { comp ->
                    val compGraph = g.inducedGraphOnly(comp)
                    val compChi = Array(compGraph.n) { localId -> chi2[comp[localId]] }
                    Content.MSet(dialysis.refinement.colorRefine1WLColors(compGraph, compChi).toList())
                }
                return Content.MSet(components).serialize()
            }
            val keys = cell.associateWith { remainderKeyOf(it) }
            if (anchorCopy(chi2, cell) { v -> keys.getValue(v) } > 0) refined = true
        }
        if (!refined) return p1.color
        return colorRefine1WL(g, chi2).color
    }

    /** Partition fingerprint independent of colour NAMES: class count + sorted class sizes + a canonical
     *  hash-1-WL of G seeded by the partition's class sizes (catches different partitions with equal size profiles). */
    private fun partitionFingerprint(g: Graph, col: Array<Content>): String {
        val cls = (0 until g.n).groupBy { col[it] }.values
        val sizeOf = IntArray(g.n); for (c in cls) for (v in c) sizeOf[v] = c.size
        val seed = LongArray(g.n) { mix64(sizeOf[it].toLong()) }
        val t = hashWlStableRound(g, seed, g.n + 2); val h = hashWlRounds(g, seed, t)
        val digest = h.sorted().fold(17L) { acc, x -> mix64(acc * 31 + x) }
        return "classes=${cls.size} sizes=${cls.map { it.size }.groupingBy { it }.eachCount().toSortedMap()} h=${java.lang.Long.toHexString(digest).take(8)}"
    }

    /** One JVM = one configuration: env PI_MODE (orig | copyid | copycanon), PI_WARMUP (comma list of
     *  graph paths, run through the same mode first), PI_RELABEL (random-permutation seed applied to the
     *  targets), PI_TARGETS (comma list). */
    @Test fun piHistoryRepro() {
        val mode = System.getenv("PI_MODE") ?: return
        fun pi(g: Graph): Array<Content> = when (mode) {
            "orig" -> dispatchColouring(g).colouring
            "copyid" -> initialPhaseCopy(g, dialysis.refinement.uniformSeed(g.n), canonicalKey = false)
            else -> initialPhaseCopy(g, dialysis.refinement.uniformSeed(g.n), canonicalKey = true)
        }
        val warm = System.getenv("PI_WARMUP")?.split(",")?.filter { it.isNotBlank() } ?: emptyList()
        for (w in warm) pi(loadForTrace(w))
        val relabel = System.getenv("PI_RELABEL")?.toIntOrNull()
        for (t in System.getenv("PI_TARGETS")!!.split(",")) {
            var g = loadForTrace(t)
            if (relabel != null) g = g.relabeled((0 until g.n).shuffled(kotlin.random.Random(relabel)).toIntArray())
            println("PIREPRO mode=$mode warmup=${warm.size} relabel=${relabel ?: "-"} target=${t.substringAfterLast('/')}: ${partitionFingerprint(g, pi(g))}")
        }
    }

    /** Invariance sweep of the canonical-key PI copy (and, for comparison, the original): per family
     *  (env SWEEP_FAMILY), 10 instances spread over sizes (effective n <= 5000), each under the file
     *  numbering and two random relabellings. Reports partition equality and per-vertex colour-VALUE equality. */
    @Test fun piInvarianceSweep() {
        val fam = System.getenv("SWEEP_FAMILY") ?: return
        val files = File("graphs/cfi-rigid-$fam").listFiles()!!.filter { it.isFile }.map { f ->
            val h = f.bufferedReader().use { it.readLine() }.trim().split(Regex("\\s+")); Triple(f, h[2].toInt(), h[3].toInt()) }
            .sortedWith(compareBy({ it.second }, { it.first.name }))
            .filter { (f, _, _) -> val g0 = GraphIO.loadDimacs(f.toPath()); (if (g0.bipartition() != null) g0.n else g0.n + g0.m) <= 5000 }
        val pick = if (files.size <= 10) files else (0 until 10).map { files[it * (files.size - 1) / 9] }
        for ((f, _, _) in pick) {
            val g = loadForTrace(f.path)
            for (mode in listOf("canon", "orig")) {
                val base = if (mode == "canon") initialPhaseCopy(g, dialysis.refinement.uniformSeed(g.n), true) else dispatchColouring(g).colouring
                val fp0 = partitionFingerprint(g, base)
                val out = StringBuilder()
                var allSame = true; var allValues = true
                for (seed in listOf(1, 2)) {
                    val perm = (0 until g.n).shuffled(kotlin.random.Random(seed)).toIntArray()
                    val gr = g.relabeled(perm)
                    val c = if (mode == "canon") initialPhaseCopy(gr, dialysis.refinement.uniformSeed(gr.n), true) else dispatchColouring(gr).colouring
                    val fp = partitionFingerprint(gr, c)
                    if (fp != fp0) allSame = false
                    if (!(0 until g.n).all { base[it] == c[perm[it]] }) allValues = false
                    out.append(" r$seed:${fp.substringBefore(" sizes")}")
                }
                println("SWEEP $fam ${f.name} mode=$mode ${fp0.substringBefore(" sizes")}$out partitionInvariant=$allSame valuesInvariant=$allValues")
            }
        }
    }

    /**
     * Soundness battery for the InitialPhase.kt:139 fix (2026-09-26), production path
     * dispatchColouring on the RAW graph. Env BATTERY_DIR (a graphs/ subdirectory), BATTERY_LIMIT
     * (max instances, spread over sizes; default all), OUT (CSV, appended, resumable), CAP (effective n).
     * Per instance: canonicity (values equal under a random relabelling), fidelity (bipartite: equals the
     * validated canonical-key copy exactly), power (old raw-id-key copy class count, bipartite), and
     * Aut-invariance (n <= 1500: no Traces orbit split by new PI, nor by old PI).
     */
    @Test fun piFixBattery() {
        val dirName = System.getenv("BATTERY_DIR") ?: return
        val cap = System.getenv("CAP")?.toIntOrNull() ?: 5000
        val limit = System.getenv("BATTERY_LIMIT")?.toIntOrNull()
        val out = File(System.getenv("OUT")!!)
        val done = if (out.exists()) out.readLines().drop(1).map { it.split(",")[1] }.toHashSet() else hashSetOf()
        if (!out.exists()) out.writeText("dir,instance,n,m,bipartite,classes_new,classes_old,canonical,fidelity,aut_checked,orbits,new_splits_orbit,old_splits_orbit,seconds\n")
        val all = File("graphs/$dirName").walkTopDown().filter { it.isFile && !it.name.startsWith(".") }.mapNotNull { f ->
            try { val h = f.bufferedReader().use { it.readLine() }?.trim()?.split(Regex("\\s+")) ?: return@mapNotNull null
                  if (h.size < 4 || h[0] != "p") null else Triple(f, h[2].toInt(), h[3].toInt()) } catch (e: Exception) { null } }
            .sortedWith(compareBy({ it.second }, { it.first.path })).toList()
        val pick = if (limit == null || all.size <= limit) all else (0 until limit).map { all[it * (all.size - 1) / (limit - 1)] }.distinct()
        var tracesOk = true
        val pool = java.util.concurrent.Executors.newSingleThreadExecutor { r -> Thread(r).apply { isDaemon = true } }
        for ((f, _, _) in pick) {
            if (f.name in done) continue
            val t0 = System.currentTimeMillis()
            val g = GraphIO.loadDimacs(f.toPath())
            val bip = g.bipartition() != null
            if ((if (bip) g.n else g.n + g.m) > cap) continue
            val newPi = dispatchColouring(g).colouring
            val perm = (0 until g.n).shuffled(kotlin.random.Random(3)).toIntArray()
            val relPi = dispatchColouring(g.relabeled(perm)).colouring
            val canonical = (0 until g.n).all { newPi[it] == relPi[perm[it]] }
            var fidelity = ""; var oldCount = ""; var oldPi: Array<Content>? = null
            if (bip) {
                val copy = initialPhaseCopy(g, dialysis.refinement.uniformSeed(g.n), canonicalKey = true)
                fidelity = (0 until g.n).all { copy[it] == newPi[it] }.toString()
                oldPi = initialPhaseCopy(g, dialysis.refinement.uniformSeed(g.n), canonicalKey = false)
                oldCount = oldPi.toHashSet().size.toString()
            }
            var autChecked = false; var orbitsN = ""; var newSplit = ""; var oldSplit = ""
            if (tracesOk && g.n <= 1500) {
                val fut = pool.submit<IntArray> { traces.certifyAll(g, listOf(IntArray(g.n) { it }), getcanon = false).orbits }
                try {
                    val orb = fut.get(30, java.util.concurrent.TimeUnit.SECONDS)
                    autChecked = true
                    val byOrbit = (0 until g.n).groupBy { orb[it] }.values
                    orbitsN = byOrbit.size.toString()
                    newSplit = byOrbit.count { o -> o.map { newPi[it] }.toSet().size > 1 }.toString()
                    if (oldPi != null) oldSplit = byOrbit.count { o -> o.map { oldPi[it] }.toSet().size > 1 }.toString()
                } catch (e: java.util.concurrent.TimeoutException) { tracesOk = false }
            }
            val row = listOf(dirName, f.name, g.n, g.m, bip, newPi.toHashSet().size, oldCount, canonical, fidelity, autChecked, orbitsN, newSplit, oldSplit, (System.currentTimeMillis() - t0) / 1000.0)
            out.appendText(row.joinToString(",") + "\n")
            println("BATTERY $dirName ${f.name}: new=${newPi.toHashSet().size} old=$oldCount canonical=$canonical fidelity=$fidelity aut=$autChecked splits new/old=$newSplit/$oldSplit")
        }
    }

    /** Peak heap + time of dispatchColouring alone on env PIMEM_TARGET (sampled every 50 ms). */
    @Test fun piMemoryProbe() {
        val path = System.getenv("PIMEM_TARGET") ?: return
        val g = GraphIO.loadDimacs(File(path).toPath())
        val rt = Runtime.getRuntime(); val peak = java.util.concurrent.atomic.AtomicLong(0); val stop = java.util.concurrent.atomic.AtomicBoolean(false)
        val sampler = Thread { while (!stop.get()) { peak.accumulateAndGet(rt.totalMemory() - rt.freeMemory()) { x, y -> maxOf(x, y) }; Thread.sleep(50) } }.apply { isDaemon = true; start() }
        val t0 = System.currentTimeMillis()
        val col = dispatchColouring(g).colouring
        stop.set(true); sampler.join()
        println("PIMEM $path n=${g.n} m=${g.m}: classes=${col.toHashSet().size} time=${(System.currentTimeMillis() - t0) / 1000.0}s peakHeapMB=${peak.get() / 1_000_000}")
    }

    /** Regression: null-space dualBasis spans the same subspace as the old brute-force one (random sets, p in 2,3,5,7). */
    @Test fun dualBasisRegression() {
        val rnd = kotlin.random.Random(9)
        var checked = 0
        for (p in listOf(2, 3, 5, 7)) for (m in 1..4) repeat(30) {
            val s = List(rnd.nextInt(0, 5)) { IntArray(m) { rnd.nextInt(p) } }
            val a = dualBasis(p, m, s); val b = dualBasisBrute(p, m, s)
            fun rank(v: List<IntArray>) = ModPSystem(p, m).also { sys -> v.forEach { sys.add(it, 0) } }.solve().first
            check(a.size == b.size && rank(a + b) == a.size) { "dual mismatch p=$p m=$m" }
            check(a.all { y -> s.all { x -> (0 until m).sumOf { x[it] * y[it] } % p == 0 } })
            checked++
        }
        println("DUAL-REGRESSION ok on $checked random cases")
    }

    /** cmz diagnosis: class structure, true candidate-set size (high cap), group/abelian/orders, base length. */
    @Test fun cmzDiagnose() {
        val path = System.getenv("CMZ_TARGET") ?: return
        val g = loadForTrace(path)
        val baseline = dispatchColouring(g).colouring
        val classes = (0 until g.n).groupBy { baseline[it] }.values.map { it.sorted().toIntArray() }.filter { it.size > 1 }
        val aut = traces.certifyAll(g, listOf(IntArray(g.n) { it }), getcanon = false).stats.autOrder
        println("CMZ $path n=${g.n}: Traces |Aut|=$aut; classes ${classes.groupingBy { it.size }.eachCount().toSortedMap()}")
        val seedBase = LongArray(g.n) { sha64(baseline[it].serialize()) }
        val seedFor = { tuple: List<Int> -> seedBase.copyOf().also { s0 -> tuple.forEachIndexed { i, v -> s0[v] = mix64(s0[v] xor (0x5EED0000L + i)) } } }
        val posIn = IntArray(g.n) { -1 }; classes.forEach { c -> c.forEachIndexed { i, v -> posIn[v] = i } }
        for (c in classes.sortedByDescending { it.size }.take(4)) {
            val t0 = System.currentTimeMillis()
            val perms = try { candidateRestrictions(g, c, seedFor, posIn, g.n + 2, IntArray(1), 40, 300_000, t0 + 120_000) } catch (e: StopReason) { println("   class size ${c.size}: ${e.detail}"); continue }
            if (perms == null) { println("   class size ${c.size}: base > 40"); continue }
            val t = perms.toSet(); val id = Perm.id(c.size)
            fun order(x: List<Int>): Int { var r = x; var k = 1; while (r != id) { r = Perm.comp(x, r); k++ }; return k }
            val sample = t.take(3000)
            val closedSample = sample.all { x -> sample.take(200).all { y -> Perm.comp(x, y) in t } }
            val abelianSample = sample.take(300).all { x -> sample.take(300).all { y -> Perm.comp(x, y) == Perm.comp(y, x) } }
            println("   class size ${c.size}: |T|=${t.size} (${Math.log(t.size.toDouble()) / Math.log(2.0)} bits) closed(sample)=$closedSample abelian(sample)=$abelianSample orders ${t.groupingBy { order(it) }.eachCount().toSortedMap()} (${(System.currentTimeMillis() - t0) / 1000.0}s)")
        }
    }

    /** One instance, verbose: env ONE_PATH, ONE_ORIGINAL (default 1), ONE_DEADLINE_S (default 300). */
    @Test fun seriesOne() {
        val path = System.getenv("ONE_PATH") ?: return
        val orig = System.getenv("ONE_ORIGINAL") != "0"
        val t0 = System.currentTimeMillis()
        val r = parityEquationsSeries(path, null, null, quiet = false, crossCheck = false, usePi = true, generalPrimes = true, cosetMode = true,
            irFallback = System.getenv("IR_FALLBACK") != "0", nonSolvableStage = System.getenv("NONSOLV") != "0", maxCandidates = 20_000, solveOnOriginal = orig, deadlineMs = (System.getenv("ONE_DEADLINE_S")?.toLongOrNull() ?: 300) * 1000)
        println("ONE $path original=$orig -> ${r.status} |Aut|=${r.autStr} vars=${r.nVars} ${r.stopDetail} (${(System.currentTimeMillis() - t0) / 1000.0}s)")
    }

    @Test fun series_stops_sample() {
        for (f in listOf("graphs/cfi-rigid-d3/cfi-rigid-d3-0360-02-1", "graphs/cfi-rigid-z3/cfi-rigid-z3-0180-03-1", "graphs/cfi-rigid-r2/cfi-rigid-r2-0648-04-1",
                         "graphs/cfi-rigid-z2/cfi-rigid-z2-0088-04-1", "graphs/cfi-rigid-r2/cfi-rigid-r2-0068-03-1", "graphs/cfi-rigid-d3/cfi-rigid-d3-0180-01-1",
                         "graphs/cfi-rigid-z3/cfi-rigid-z3-0180-01-2", "graphs/cfi-rigid-t2/cfi-rigid-t2-0216-01-1"))
            parityEquationsSeries(f, null, null)
    }

    @Test fun layered_stops_sample() {
        for (f in listOf("graphs/cfi-rigid-r2/cfi-rigid-r2-0648-04-1", "graphs/cfi-rigid-z2/cfi-rigid-z2-0088-04-1", "graphs/cfi-rigid-s2/cfi-rigid-s2-0384-03-1",
                         "graphs/cfi-rigid-d3/cfi-rigid-d3-0360-02-1", "graphs/cfi-rigid-z3/cfi-rigid-z3-0180-03-1",
                         "graphs/cfi-rigid-r2/cfi-rigid-r2-0068-03-1", "graphs/cfi-rigid-d3/cfi-rigid-d3-0180-01-1", "graphs/cfi-rigid-t2/cfi-rigid-t2-0216-01-1"))
            parityEquationsLayered(f, null, null)
    }

    @Test fun diagnose_stops() {
        diagnoseStops("graphs/cfi-rigid-d3/cfi-rigid-d3-0360-02-1", 10)
        diagnoseStops("graphs/cfi-rigid-z3/cfi-rigid-z3-0180-03-1", 10)
        diagnoseStops("graphs/cfi-rigid-r2/cfi-rigid-r2-0648-04-1", 10)
        diagnoseStops("graphs/cfi-rigid-z2/cfi-rigid-z2-0088-04-1", 10)
        diagnoseStops("graphs/cfi-rigid-s2/cfi-rigid-s2-0384-03-1", 10)
    }

    @Test fun z3solver_d3_0180() { for (f in listOf("01-1", "01-2", "02-1", "02-2")) parityEquationsZ3("graphs/cfi-rigid-d3/cfi-rigid-d3-0180-$f", null, null) }
    @Test fun z3solver_z3_0180() { for (f in listOf("01-1", "01-2", "02-1", "02-2")) parityEquationsZ3("graphs/cfi-rigid-z3/cfi-rigid-z3-0180-$f", null, null) }

    @Test fun gfp_regression_r2_0068() { parityEquationsGFp("graphs/cfi-rigid-r2/cfi-rigid-r2-0068-03-1", 32, 63); parityEquationsGFp("graphs/cfi-rigid-r2/cfi-rigid-r2-0068-03-1", 32, 33) }
    @Test fun gfp_regression_t2_0216() { parityEquationsGFp("graphs/cfi-rigid-t2/cfi-rigid-t2-0216-01-1", 216, 862) }
    @Test fun gfp_d3_0180() { for (f in listOf("01-1", "01-2", "02-1", "02-2")) parityEquationsGFp("graphs/cfi-rigid-d3/cfi-rigid-d3-0180-$f", null, null) }
    @Test fun gfp_z3_0180() { for (f in listOf("01-1", "01-2", "02-1", "02-2")) parityEquationsGFp("graphs/cfi-rigid-z3/cfi-rigid-z3-0180-$f", null, null) }

    @Test fun parity_r2_0068() { parityEquations("graphs/cfi-rigid-r2/cfi-rigid-r2-0068-03-1", 32, 63); parityEquations("graphs/cfi-rigid-r2/cfi-rigid-r2-0068-03-1", 32, 33) }
    @Test fun parity_r2_0144() { parityEquations("graphs/cfi-rigid-r2/cfi-rigid-r2-0144-01-1", 20, 49) }
    @Test fun parity_t2_0216() { parityEquations("graphs/cfi-rigid-t2/cfi-rigid-t2-0216-01-1", 216, 862) }
    @Test fun parity_r2_3600() { parityEquations("graphs/cfi-rigid-r2/cfi-rigid-r2-3600-01-1", 4, 371) }
    @Test fun parity_r2_0504() { parityEquations("graphs/cfi-rigid-r2/cfi-rigid-r2-0504-01-1", 322, 472) }

    @Test fun t2_0216_individualize_40_55_175_210() { individualizeClass("graphs/cfi-rigid-t2/cfi-rigid-t2-0216-01-1", listOf(40, 55, 175, 210)) }
    @Test fun t2_0216_individualize_roots() { individualizeClass("graphs/cfi-rigid-t2/cfi-rigid-t2-0216-01-1", listOf(216, 862)) }

    @Test fun t2_0216_drawBreak_L7_L8() { drawBreakDot("graphs/cfi-rigid-t2/cfi-rigid-t2-0216-01-1", 216, 862, 8,
        listOf(15, 128, 32, 122), listOf(473 to 15, 481 to 15, 1023 to 128, 1695 to 128, 706 to 32, 717 to 32, 1022 to 122, 1650 to 122)) }

    @Test fun t2_0216_previousLevelsCut_L8() { previousLevelsMinimalCut("graphs/cfi-rigid-t2/cfi-rigid-t2-0216-01-1", 216, 862, 8, setOf(15, 128, 32, 122)) }

    @Test fun t2_0216_outgoing_L8() { outgoingLeaveOneOut("graphs/cfi-rigid-t2/cfi-rigid-t2-0216-01-1", 216, 862, 8,
        setOf(473 to 15, 481 to 15, 1023 to 128, 1695 to 128)) }

    @Test fun t2_0216_isolate_L0_L8() { isolateConnectorsInto("graphs/cfi-rigid-t2/cfi-rigid-t2-0216-01-1", 216, 862, 8, 0) }

    @Test fun t2_0016_trace() = traceInstance("graphs/cfi-rigid-t2/cfi-rigid-t2-0016-04-1")
    @Test fun t2_0048_trace() = traceInstance("graphs/cfi-rigid-t2/cfi-rigid-t2-0048-01-1")
    @Test fun t2_0096_trace() = traceInstance("graphs/cfi-rigid-t2/cfi-rigid-t2-0096-01-1")
    @Test fun t2_0216_trace() = traceInstance("graphs/cfi-rigid-t2/cfi-rigid-t2-0216-01-1")

    @Test fun r2_0068_guided_32_63() = guidedDecomposition("graphs/cfi-rigid-r2/cfi-rigid-r2-0068-03-1", 32, 63)
    @Test fun r2_0068_guided_32_33() = guidedDecomposition("graphs/cfi-rigid-r2/cfi-rigid-r2-0068-03-1", 32, 33)
    @Test fun r2_0144_guided_20_49() = guidedDecomposition("graphs/cfi-rigid-r2/cfi-rigid-r2-0144-01-1", 20, 49)
    @Test fun r2_0504_guided_322_472() = guidedDecomposition("graphs/cfi-rigid-r2/cfi-rigid-r2-0504-01-1", 322, 472)
    /** Big input, strict budget (run under a systemd memory cap + wall-clock timeout). */
    @Test fun r2_3600_guided_budget() = guidedDecomposition("graphs/cfi-rigid-r2/cfi-rigid-r2-3600-01-1", null, null,
        maxTracesCalls = 300, deadlineMs = 8 * 60_000L)

    @Test fun r2_0144_findInconsistentLevel_20_49() = findInconsistentLevel("graphs/cfi-rigid-r2/cfi-rigid-r2-0144-01-1", 20, 49, crossCheckLinear = true)
    @Test fun r2_0504_findInconsistentLevel_322_472() = findInconsistentLevel("graphs/cfi-rigid-r2/cfi-rigid-r2-0504-01-1", 322, 472, crossCheckLinear = true)
    @Test fun r2_0068_findInconsistentLevel_32_63() = findInconsistentLevel("graphs/cfi-rigid-r2/cfi-rigid-r2-0068-03-1", 32, 63)

    @Test fun r2_0504_traceRoots_322_472() = traceRoots("graphs/cfi-rigid-r2/cfi-rigid-r2-0504-01-1", 322, 472)

    @Test fun r2_0068() = run("graphs/cfi-rigid-t2/cfi-rigid-t2-0120-01-1", forcedRoot = 1019)
    @Test fun d3_0180() = run("graphs/cfi-rigid-d3/cfi-rigid-d3-0180-01-1")
}
