package dialysis.viz

import dialysis.ahu.ColoredAHU
import dialysis.content.Content
import dialysis.content.serialize
import dialysis.decomposition.Piece
import dialysis.decomposition.PieceKind
import dialysis.decomposition.buildTreeOnlyGraph
import dialysis.decomposition.defaultRootRule
import dialysis.decomposition.peel
import dialysis.decomposition.pieceKey
import dialysis.graph.Graph
import dialysis.refinement.dispatchColouring
import dialysis.util.GraphIO
import java.io.File

/**
 * Renders [g]'s recursive Dialysis decomposition ("PEEL until amenable base" -- see
 * [dialysis.decomposition.peel]'s own doc) as Graphviz DOT, for visual inspection:
 *
 *  - one `cluster` per [Piece] (QUOTIENT tree+orphans, or BASE);
 *  - every vertex labelled with its initial-phase colour, its OWN PIECE's key, and its own
 *    piece-relative AHU code -- shown SEPARATELY (the AHU itself is computed UNCOLOURED, the same
 *    convention [dialysis.decomposition.positionSignatures] already uses) so all three can be
 *    compared by eye: same AHU code + different colour means colour is doing extra work beyond
 *    structure, and vice versa. All three are shown as SHORT, per-diagram-unique ids (`c<n>` for
 *    colour, `p<n>` for [pieceKey], `#<n>` for AHU) -- not the full serialized colour / pieceKey /
 *    canonical AHU string, which for a well-refined colouring or a deep subtree can run to hundreds
 *    of characters and is what made the node circles gigantic. The ids are directly comparable at a
 *    glance ANYWHERE in the same rendered diagram (one id map per kind, one [ColoredAHU] intern
 *    pool, all scoped to the whole call): two vertices showing the same `c<n>` have the identical
 *    colour, the same `p<n>` sit in pieces with the identical [pieceKey] (size, edge count, degree
 *    sequence, boundary colours -- so, notably, a 3-star's leaves and a 4-star's leaves get
 *    DIFFERENT `p<n>` even though both get the SAME `#<n>`, since a bare AHU code is a function of
 *    the subtree BELOW a vertex alone, never of the piece's own overall shape around it -- exactly
 *    why [dialysis.decomposition.PositionSignature] bundles [pieceKey] together with the AHU code
 *    rather than using the AHU code alone as a vertex's full "position"), and the same `#<n>` have
 *    isomorphic (uncoloured) subtrees, full stop, not just similar-looking. The full colour string,
 *    full pieceKey, and full (untruncated) AHU canonical string are still there -- as each node's
 *    `tooltip`, which an SVG viewer shows on hover (`dot -Tsvg`; a plain PNG has no tooltip and only
 *    shows the short ids on the node itself);
 *  - a QUOTIENT piece's root filled red, its orphans filled green;
 *  - a BASE piece that still happens to induce a tree (peel's own termination just means nothing
 *    further could be GAINED by decomposing it, not that it lacks tree structure) is rendered the
 *    same way, rooted arbitrarily (via [rootRule]) purely for display -- that root carries no
 *    decomposition meaning, only somewhere to hang the AHU computation from, so it is filled red
 *    too but the piece is still labelled BASE;
 *  - a BASE piece that is NOT tree-shaped (already 1-WL-discrete) has no natural root/tree, so it
 *    is drawn as its own induced subgraph with plain vertices, no AHU code;
 *  - every graph edge whose two endpoints land in DIFFERENT pieces (a "bridge") is drawn in blue,
 *    dotted, outside every cluster; every edge kept INSIDE a cluster (tree edges, orphan-attachment
 *    edges, or a BASE-discrete piece's own induced edges) is drawn in black/gray;
 *  - a QUOTIENT piece's tree is built strictly from PARENT POINTERS, never from `g`'s own induced
 *    edges among the same vertices (same convention [dialysis.decomposition.positionSignatures]
 *    already uses for its own AHU) -- `dialysisPerSpec`'s admission rule only looks at the
 *    STRICTLY PREVIOUS BFS layer, so same-layer ties do not block admission, and a real cycle among
 *    tree vertices (e.g. a triangle one BFS layer deep) can end up entirely INSIDE the tree with
 *    none of its edges appearing in the parent-pointer structure. Any such edge is still a genuine
 *    edge of `g` and is drawn -- in orange, dotted (distinct from the blue-dotted BRIDGE style
 *    above, and from every other edge style) -- so nothing in `g` is silently missing from the
 *    picture.
 *
 * Render with `dot -Tsvg out.dot -o out.svg` (or `-Tpng`). `dot`'s default hierarchical layout
 * keeps each cluster visually grouped; `sfdp`/`neato` may lay out a very large or dense instance
 * more legibly.
 */
private fun dotEscape(s: String): String = s.replace("\\", "\\\\").replace("\"", "\\\"")

/** Forces [peel]'s TOP-LEVEL root to [forcedRoot] (null = [defaultRootRule] throughout, unchanged);
 *  every recursive remainder-component root below the top level still uses [defaultRootRule]
 *  regardless. Shared by this file's own CLI (`--root`) and by
 *  [dialysis.experimental.PeelPieceIdRecolouringTest]'s split-reporting experiments, so "which root
 *  did this decomposition start from" means the same thing in both places. */
fun topLevelForcedRootRule(forcedRoot: Int?, totalN: Int): (Graph, Array<Content>) -> Int {
    if (forcedRoot == null) return ::defaultRootRule
    var usedTopLevelRoot = false
    return { sub, restricted ->
        if (!usedTopLevelRoot && sub.n == totalN) { usedTopLevelRoot = true; forcedRoot } else defaultRootRule(sub, restricted)
    }
}

/** Assigns each distinct [Content] value a short, per-diagram-stable sequential id (0, 1, ...) in
 *  first-seen order -- one instance each for colour and for [pieceKey], see class doc for why the
 *  node label shows these instead of the full serialized strings. */
private class ContentIds {
    private val ids = HashMap<Content, Int>()
    fun idOf(c: Content): Int = ids.getOrPut(c) { ids.size }
}

fun decompositionToDot(
    g: Graph,
    colouring: Array<Content>,
    rootRule: (Graph, Array<Content>) -> Int = ::defaultRootRule,
): String {
    val pieces = mutableListOf<Piece>()
    peel(g, IntArray(g.n) { it }, colouring, pieces, rootRule)

    val pieceOf = IntArray(g.n) { -1 }
    for ((i, piece) in pieces.withIndex()) for (v in piece.vertices) pieceOf[v] = i
    check(pieceOf.all { it >= 0 }) { "peel() did not partition every vertex of g" }

    val colourIds = ContentIds()
    val pieceKeyIds = ContentIds()

    val sb = StringBuilder()
    sb.appendLine("graph Decomposition {")
    sb.appendLine("  compound=true;")
    sb.appendLine("  nodesep=0.5;")
    sb.appendLine("  ranksep=0.9;")
    sb.appendLine("  node [shape=circle, style=filled, fillcolor=white, fontsize=8, width=0.3, fixedsize=false];")
    sb.appendLine("  edge [color=black];")

    for ((i, piece) in pieces.withIndex()) {
        val pk = pieceKey(g, piece.vertices, colouring)
        val pieceKeyId = pieceKeyIds.idOf(pk)
        sb.appendLine("  subgraph cluster_$i {")
        sb.appendLine("    label=\"piece $i (${piece.kind}) p$pieceKeyId\";")
        sb.appendLine("    style=dashed; color=gray; margin=24;")
        when (piece.kind) {
            PieceKind.QUOTIENT -> emitQuotientPiece(g, piece, colouring, colourIds, pieceKeyId, pk, sb)
            PieceKind.BASE -> emitBasePiece(g, piece, colouring, colourIds, pieceKeyId, pk, sb, rootRule)
        }
        sb.appendLine("  }")
    }

    for (v in 0 until g.n) {
        for (w in g.adj[v]) {
            if (w <= v) continue
            if (pieceOf[v] != pieceOf[w]) {
                sb.appendLine("  v$v -- v$w [color=blue, style=dotted];")
            }
        }
    }

    sb.appendLine("}")
    return sb.toString()
}

private fun edgeKey(a: Int, b: Int): Long = if (a < b) a.toLong() shl 32 or b.toLong() else b.toLong() shl 32 or a.toLong()

private fun emitQuotientPiece(
    g: Graph,
    piece: Piece,
    colouring: Array<Content>,
    colourIds: ContentIds,
    pieceKeyId: Int,
    pk: Content,
    sb: StringBuilder,
) {
    val tree = piece.tree!!
    val parent = piece.parent!!
    val root = piece.root!!
    val orphans = piece.orphans!!
    val drawn = HashSet<Long>()

    val (treeGraph, oldToNew) = buildTreeOnlyGraph(tree, parent)
    val uniformColours = tree.associate { oldToNew.getValue(it) to "u" } // structural AHU; colour shown separately
    val ahu = ColoredAHU.compute(treeGraph, uniformColours, oldToNew.getValue(root))

    for (v in tree) {
        val localV = oldToNew.getValue(v)
        val ahuId = ahu.label(localV)
        val colourId = colourIds.idOf(colouring[v])
        val tooltip = dotEscape("color=${colouring[v].serialize()} pieceKey=${pk.serialize()} ahu=${ahu.subtreeCanonicalString(localV)}")
        val fill = if (v == root) "red" else "white"
        sb.appendLine("    v$v [label=\"v$v\\nc$colourId p$pieceKeyId #$ahuId\", tooltip=\"$tooltip\", fillcolor=$fill];")
    }
    for (v in tree) {
        val p = parent[v] ?: continue
        sb.appendLine("    v$p -- v$v;")
        drawn.add(edgeKey(p, v))
    }

    val treeSet = tree.toHashSet()
    for (o in orphans) {
        val attach = g.adj[o].filter { it in treeSet }
        val attachIds = attach.map { ahu.label(oldToNew.getValue(it)) }.sorted()
        val colourId = colourIds.idOf(colouring[o])
        val tooltip = dotEscape("color=${colouring[o].serialize()} pieceKey=${pk.serialize()} attach=$attachIds")
        sb.appendLine("    v$o [label=\"v$o\\nc$colourId p$pieceKeyId\", tooltip=\"$tooltip\", fillcolor=green];")
        for (a in attach) { sb.appendLine("    v$o -- v$a [style=dashed, color=gray];"); drawn.add(edgeKey(o, a)) }
    }

    // Extra chords: real edges of g between two vertices of THIS piece that dialysisPerSpec's
    // admission rule (same-BFS-level ties don't block admission, unlike the OLDER `dialysis()`)
    // absorbed into one tree without needing them, and that buildTreeOnlyGraph -- built strictly
    // from parent pointers, never g's own induced edges (see its own doc) -- therefore never draws.
    // Without this, an edge that genuinely exists in g (e.g. a cycle among tree vertices) would be
    // silently invisible in the picture. Drawn distinctly (orange, dotted -- not blue, which is the
    // cross-piece BRIDGE style) so it reads as "present in g but not part of the AHU tree/orphan
    // structure", never confused with a tree/attachment edge OR a bridge.
    val pieceSet = piece.vertices.toHashSet()
    for (v in piece.vertices) {
        for (w in g.adj[v]) {
            if (w <= v || w !in pieceSet) continue
            val key = edgeKey(v, w)
            if (drawn.add(key)) sb.appendLine("    v$v -- v$w [style=dotted, color=orange];")
        }
    }
}

private fun emitBasePiece(
    g: Graph,
    piece: Piece,
    colouring: Array<Content>,
    colourIds: ContentIds,
    pieceKeyId: Int,
    pk: Content,
    sb: StringBuilder,
    rootRule: (Graph, Array<Content>) -> Int,
) {
    val verts = piece.vertices
    val (sub, oldToNew) = g.induced(verts)
    val isTreeShaped = sub.n > 1 && sub.m == sub.n - 1

    if (isTreeShaped) {
        // peel() stopped here because nothing further could be GAINED, not because this piece
        // lacks tree structure -- root it purely for display (see class doc).
        val localRoot = rootRule(sub, Array(sub.n) { colouring[verts[it]] })
        val parentLocal = IntArray(sub.n) { -1 }
        val visited = BooleanArray(sub.n)
        val queue = ArrayDeque<Int>()
        queue.add(localRoot); visited[localRoot] = true
        while (queue.isNotEmpty()) {
            val cur = queue.removeFirst()
            for (w in sub.adj[cur]) if (!visited[w]) { visited[w] = true; parentLocal[w] = cur; queue.add(w) }
        }
        val uniformColours = (0 until sub.n).associateWith { "u" }
        val ahu = ColoredAHU.compute(sub, uniformColours, localRoot)
        for (localV in 0 until sub.n) {
            val v = verts[localV]
            val ahuId = ahu.label(localV)
            val colourId = colourIds.idOf(colouring[v])
            val tooltip = dotEscape("color=${colouring[v].serialize()} pieceKey=${pk.serialize()} ahu=${ahu.subtreeCanonicalString(localV)}")
            val fill = if (localV == localRoot) "red" else "white"
            sb.appendLine("    v$v [label=\"v$v\\nc$colourId p$pieceKeyId #$ahuId\", tooltip=\"$tooltip\", fillcolor=$fill];")
        }
        for (localV in 0 until sub.n) {
            val p = parentLocal[localV]
            if (p >= 0) sb.appendLine("    v${verts[p]} -- v${verts[localV]};")
        }
    } else {
        // Already 1-WL-discrete (or a single isolated vertex): no natural root/tree, just the
        // vertices and this piece's own induced edges.
        for (v in verts) {
            val colourId = colourIds.idOf(colouring[v])
            val tooltip = dotEscape("color=${colouring[v].serialize()} pieceKey=${pk.serialize()}")
            sb.appendLine("    v$v [label=\"v$v\\nc$colourId p$pieceKeyId\", tooltip=\"$tooltip\"];")
        }
        for (localV in 0 until sub.n) {
            for (localW in sub.adj[localV]) {
                if (localW <= localV) continue
                sb.appendLine("    v${verts[localV]} -- v${verts[localW]};")
            }
        }
    }
}

// ---- CLI ---------------------------------------------------------------------------------------

private fun parseArgs(args: Array<String>): Map<String, String> =
    args.associate { arg ->
        val body = arg.removePrefix("--")
        val eq = body.indexOf('=')
        if (eq < 0) body to "true" else body.substring(0, eq) to body.substring(eq + 1)
    }

/**
 * `./gradlew shadowJar` once, then:
 * `java -cp build/libs/graph-dialysis-1.0-all.jar dialysis.viz.DecompositionGraphvizKt --graph=<path> --out=<path.dot> [--root=<v>]`
 * (`./gradlew run` is wired to a fixed main class elsewhere in this build, so it can't take this
 * tool's own args -- this needs the jar, same as every other standalone CLI in this codebase.)
 *
 * `--graph`: a DIMACS graph file (same format every other tool in this codebase reads via
 * [GraphIO.loadDimacs]). `--out` (default `decomposition.dot`): where to write the DOT text. The
 * DOT is ALSO printed to stdout regardless, since a small graph is easier to eyeball directly.
 * `--root` (optional): forces the TOP-level piece's root to this vertex id; every recursive
 * remainder-component root below it still uses [defaultRootRule].
 */
fun main(args: Array<String>) {
    val flags = parseArgs(args)
    val graphPath = flags["graph"] ?: error("--graph=<path> is required")
    val outPath = flags["out"] ?: "decomposition.dot"
    val forcedRoot = flags["root"]?.toInt()

    val g = GraphIO.loadDimacs(File(graphPath).toPath())
    val colouring = dispatchColouring(g).colouring
    val rootRule = topLevelForcedRootRule(forcedRoot, g.n)

    val dot = decompositionToDot(g, colouring, rootRule)
    File(outPath).writeText(dot)
    println(dot)
    println("// wrote $outPath -- render with: dot -Tsvg $outPath -o ${outPath.removeSuffix(".dot")}.svg")
}
