package dialysis.refinement

import dialysis.ahu.ColoredAHU
import dialysis.content.Content
import dialysis.content.serialize
import dialysis.decomposition.DecompositionStore
import dialysis.decomposition.dialysis
import dialysis.graph.Graph
import dialysis.util.boundedPool

/** A single-colour initial coloring — the standard starting point for [initialPhase]/
 *  [colorRefine1WL] when no external invariant colouring is available. */
fun uniformSeed(n: Int): Array<Content> = Array(n) { Content.Str("u") }

/**
 * The initial phase: a colour refinement stronger than plain 1-WL, used everywhere a stable
 * partition is needed. It is a discriminating heuristic, not a canonical or complete procedure —
 * only isomorphism-invariance is required of it; a weaker or stronger refinement here changes
 * discriminating power and speed, never correctness of anything built on top of it.
 *
 * Three phases beyond the 1-WL baseline, each anchoring colour classes by an invariant key and
 * re-propagating:
 *  - Phase 1: tree/orphan anchoring — key(v) = (AHU(T(v)), orphan count of v).
 *  - Phase 2: remainder anchoring, incremental — key(v) = the sorted multiset, over v's
 *    remainder's own connected components, of each component's own 1-WL stable colouring (seeded
 *    by whatever colours earlier classes in this same sweep have already produced).
 *  - Phase 3: final propagation, only if Phase 2 introduced a new colour.
 *
 * [runPhases23] (default true) gates Phase 2/3 off entirely: false returns right after Phase 1's
 * own 1-WL propagation, whether or not that made the partition discrete — useful for measuring
 * how much of the initial phase's discriminating power comes from tree/orphan anchoring alone,
 * isolated from the more expensive remainder-component work.
 *
 * [precomputedStore], if given, is used INSTEAD OF building a fresh [DecompositionStore] -- valid
 * because `dialysis(g, v)` (what the store actually holds) is a pure function of the graph alone,
 * never of [chi]: a caller that invokes this repeatedly on the SAME [g] with only [chi] varying
 * (e.g. FINAL_MEASUREMENTS_SPEC.md Task 2's per-query filter, individualizing a different vertex
 * each call) can build ONE store up front (`DecompositionStore.build(g)`, no `needed` mask so every
 * vertex is covered regardless of which query's `needsWork` would have asked for it) and reuse it
 * across every call instead of repeating a graph-wide decomposition per call. Measured as the actual
 * cause of a `latin-20` (n=400) per-query run exhausting memory: up to 400 redundant whole-graph
 * decompositions (one per individualized vertex) where exactly one was needed.
 *
 * [phase2CostGuard] bounds Phase 2's own cost, which Phase 1 does NOT bound: on `sts-79`'s
 * subdivision (`n_sub=59566`, REGIME_III_SPEC.md's Regime III investigation, 2026-09-02) Phase 1
 * leaves 18,486 non-singleton cells, every one only size 9 -- individually nothing -- but EVERY one
 * of those ~166K vertices has a remainder component covering essentially the whole graph (measured:
 * 46,449 of 59,566 vertices), and Phase 2 runs a full [colorRefine1WLColors] over that near-total-graph
 * component once PER VERTEX. That is ~166K calls each costing O(component size), not one big
 * computation but an enormous COUNT of individually-plausible-looking ones -- confirmed directly to
 * run 30+ minutes with no completion, where Phase 0/1/`DecompositionStore.build` together took under
 * 9 minutes on the same input. Estimating each cell's cost from ONE representative member's remainder
 * size (`cell.size * that member's total remainder size` -- every member of an anchored cell shares
 * the same tree/orphan structure by construction, so one probe stands in for the whole cell cheaply)
 * and stopping Phase 2 early once the running total would exceed the guard is always SOUND to do --
 * this function's own top-of-doc contract is that only isomorphism-invariance is required of any
 * phase here, never completeness, so cutting Phase 2 short just means less discrimination for the
 * cells not yet reached, not an incorrect result. Default `1_000_000_000` sits with real headroom
 * above the largest CONFIRMED-affordable case measured so far (`sts-51`'s subdivision: one 12,444-
 * member cell with a near-full remainder each, ~$12444 \times 15725 \approx 196$M) and well below
 * `sts-79`'s actual total (~166,374 × 46,449 ≈ 7.7 billion) -- override only with a measured
 * justification, the same spirit as the SAT encoding's own `SKIPPED_TOO_LARGE` clause-count guard.
 *
 * [relevantVertexCount], if given, restricts what "progress" means for Phase 2's OWN early-stopping:
 * only vertices `0 until relevantVertexCount` count towards it (for a caller that only uses the colours of those
 * vertices). Phase 2 tracks the relevant-vertex class count after every cell and, once it
 * goes [phase2StaleCellStreakGuard] consecutive cells without INCREASING, stops early -- a general,
 * foreknowledge-free signal (no need to know the true orbit count in advance, unlike the diagnostic
 * that found this), complementary to [phase2CostGuard]: the cost guard bounds total work regardless
 * of payoff, this bounds continuing to pay for cells that have stopped paying off, whichever guard's
 * condition is hit first stops the loop. Same soundness argument as [phase2CostGuard]: skipping the
 * remaining cells only reduces discrimination, never introduces an incorrect colouring. `null`
 * (default) disables this check entirely -- every vertex counts as relevant, matching every caller
 * that is NOT running Phase 2 over a subdivision with an irrelevant vertex tail.
 *
 * CAVEAT shared with [phase2CostGuard]: Phase 1's own cell ORDER is not tuned for "helpful cells
 * first" -- a genuinely useful split could in principle appear after a long stretch of unhelpful
 * ones, and a large enough [phase2StaleCellStreakGuard] would still stop before reaching it. Always
 * sound regardless (see above), just a real trade of speed against a small chance of leftover
 * discriminating power, exactly as already accepted for [phase2CostGuard].
 */
fun initialPhase(
    g: Graph,
    chi: Array<Content>,
    runPhases23: Boolean = true,
    precomputedStore: DecompositionStore? = null,
    phase2CostGuard: Long = 1_000_000_000L,
    relevantVertexCount: Int? = null,
    phase2StaleCellStreakGuard: Int = 200,
): StablePartition {
    // Phase 0: baseline.
    val p0 = colorRefine1WL(g, chi)
    if (p0.isDiscrete()) return p0

    // Anchoring is a no-op on an already-singleton cell -- vertices already unique after Phase 0
    // stay that way through every later phase, so skip the per-vertex decomposition/AHU/remainder
    // work for them entirely.
    val needsWork = BooleanArray(g.n)
    for (cell in p0.cells) if (cell.size > 1) for (v in cell) needsWork[v] = true

    // One decomposition per vertex that still needs it, computed once and kept off-heap; Phase 1
    // and Phase 2 both read from it below, and a later caller that needs dialysis(g, r) for some
    // root r can fetch an already-computed decomposition through the partition's
    // [StablePartition.decompositionOf] instead of recomputing it. A [precomputedStore] must cover
    // every vertex [needsWork] could ask for -- true whenever it was itself built with no mask,
    // checked here (not just documented) so a future caller passing a partially-masked store fails
    // loudly with a clear message instead of silently reading a zero-length record later.
    if (precomputedStore != null) {
        require(precomputedStore.coversEveryVertex) {
            "precomputedStore must cover every vertex (built with a null/all-true `needed` mask) -- " +
                "this call's own needsWork mask can differ from whatever built the store"
        }
    }
    val store = precomputedStore ?: DecompositionStore.build(g, needsWork)

    // Phase 1: tree/orphan anchoring.
    //
    // CANONICAL anchoring key (fix 2026-09-26). The AHU `rootId` is an intern-pool id whose MAGNITUDE
    // depends on the order the pool first saw each subtree -- i.e. on JVM history AND on vertex
    // numbering within this very call. anchor() orders groups by key, those ranks become colours, and
    // Phase 2's (order-sensitive) cell order follows the colours, so a raw-id key made PI NOT
    // isomorphism-invariant: cfi-rigid-z3-0180-01-2 gave 36 / 34 / 30 classes depending only on the
    // vertex numbering (reproduced in fresh JVMs). Equality of ids is canonical (equal canonical
    // strings intern to equal ids), only their ORDER is not -- so the fix keeps the id for grouping
    // and replaces it in the key by its rank among this call's distinct root classes under a
    // content-only order: the order of Content.Str(canonical string).serialize() -- exactly the order a
    // Content.Str(canonical string) key would get from anchor() -- with the strings fetched on demand
    // inside the comparator and never held collectively (see ColoredAHU's intern-pool history: holding
    // them all on heap blew up rnd-3-reg).
    val rootIdOf = IntArray(g.n) { -1 }
    val orphanCountOf = IntArray(g.n)
    for (v in 0 until g.n) {
        if (!needsWork[v]) continue
        // 2026-10-04: the tree is T with its PARENT edges {x, parent(x)}, not G[T]. On a bipartite graph the two coincide
        // (no edges inside a layer); on a non-bipartite graph G[T] also has the edges inside layers, is not a tree, and
        // must not be handed to the tree canonisation.
        val dec = store.get(v)
        val treeVerts = dec.treeVerts; val orphanCount = dec.orphans.size
        val treeOldToNew = HashMap<Int, Int>(treeVerts.size * 2).also { m -> treeVerts.forEachIndexed { i, x -> m[x] = i } }
        val treeAdj = Array(treeVerts.size) { ArrayList<Int>(2) }
        for (x in treeVerts) { val px = dec.parent[x]; if (px >= 0) { val a = treeOldToNew.getValue(x); val b = treeOldToNew.getValue(px); treeAdj[a].add(b); treeAdj[b].add(a) } }
        val treeGraph = dialysis.graph.Graph(treeVerts.size, Array(treeVerts.size) { treeAdj[it].toIntArray().also { a -> a.sort() } }, Array(treeVerts.size) { "${treeVerts[it]}" })
        val ahuColors = treeVerts.associate { origId -> treeOldToNew.getValue(origId) to chi[origId].serialize() }
        val ahuResult = ColoredAHU.compute(treeGraph, ahuColors, root = treeOldToNew.getValue(v))
        rootIdOf[v] = ahuResult.rootId
        orphanCountOf[v] = orphanCount
    }
    val canonicalRankOfRootId = canonicalRanks(rootIdOf.filter { it >= 0 }.distinct())
    val treeOrphanKey = arrayOfNulls<Content>(g.n)
    for (v in 0 until g.n) {
        if (!needsWork[v]) continue
        treeOrphanKey[v] = Content.Tup(listOf(Content.Num(canonicalRankOfRootId.getValue(rootIdOf[v]).toLong()), Content.Num(orphanCountOf[v].toLong())))
    }
    val chi1 = p0.color.copyOf()
    // Safe to force-unwrap: anchor() only evaluates `key(v)` for cells of size > 1, and every such
    // vertex has needsWork[v] == true (that's exactly how needsWork was built).
    for (cell in p0.cells) anchor(chi1, cell) { v -> treeOrphanKey[v]!!.serialize() }
    val p1 = colorRefine1WL(g, chi1)
    if (p1.isDiscrete() || !runPhases23) return p1.withDecompositions(g, store)

    // Phase 2: remainder anchoring, incremental -- classes in canonical order, each reading
    // whatever chi2 has become by the time it's its turn.
    val chi2 = p1.color.copyOf()
    var refined = false
    var phase2CostSoFar = 0L
    val phase2NonSingletonCells = p1.cells.count { it.size > 1 }
    var phase2CellsProcessed = 0
    // See [relevantVertexCount]'s own doc: tracks the class count restricted to the vertices the
    // caller actually cares about, and how many cells in a row have gone by without it increasing.
    fun relevantClassCount(): Int = (0 until relevantVertexCount!!).map { chi2[it] }.toHashSet().size
    var lastRelevantClassCount = relevantVertexCount?.let { relevantClassCount() }
    var cellsSinceRelevantImprovement = 0
    for (cell in p1.cells) {
        if (cell.size <= 1) continue   // anchor() is a no-op here too; skip building keys nobody needs
        // Cheap pre-check, see [phase2CostGuard]'s own doc: every member of an anchored cell shares
        // the same tree/orphan key by construction, so one representative's remainder size stands in
        // for the whole cell without probing every member. This read is just an mmap lookup (see
        // DecompositionStore.remainderComponents), nowhere near the cost of colorRefine1WLColors
        // itself, so paying it even for a cell we go on to skip is negligible.
        val representativeRemainderSize = store.remainderComponents(cell[0]).sumOf { it.size }.toLong()
        val estimatedCellCost = cell.size.toLong() * representativeRemainderSize
        if (phase2CostSoFar + estimatedCellCost > phase2CostGuard) {
            println(
                "initialPhase Phase 2: cost guard tripped after $phase2CellsProcessed/$phase2NonSingletonCells " +
                    "non-singleton cells (cumulative estimated cost ${phase2CostSoFar + estimatedCellCost} " +
                    "> guard $phase2CostGuard) -- stopping Phase 2 early. Still sound: Phase 2 is optional " +
                    "refinement on top of Phase 1's own result, so the vertices in the remaining cells simply " +
                    "keep Phase 1's colouring instead of Phase 2's finer one.",
            )
            break
        }
        phase2CostSoFar += estimatedCellCost
        phase2CellsProcessed++
        // For each remainder component: seed 1-WL WITH chi2 (restricted to the component) and let
        // it refine from there, rather than running 1-WL unseeded first and mapping chi2 on
        // afterward -- measured more discriminating on the corpus this was tuned against.
        // Returns the SERIALIZED key, not the live Content tree -- see anchor()'s own doc for why
        // that's both correct (Content's own invariants guarantee string equality/order match
        // structural equality/order exactly) and the actual fix here: the live tree this builds is
        // transient (this function's own stack frame), collectible right after serialize() runs,
        // instead of retained for every member of the cell simultaneously via precomputedKeys below
        // -- confirmed as the fix for the 15MB->5663MB blowup this replaced (measured on sts-51).
        fun remainderKeyOf(v: Int): String {
            val components = store.remainderComponents(v).map { comp ->
                // inducedGraphOnly, not induced: this call's old->new map would be discarded
                // immediately below, and induced()'s O(n) map allocation/init was measured as the
                // dominant per-call cost here (thousands of these calls per instance).
                val compGraph = g.inducedGraphOnly(comp)
                val compChi = Array(compGraph.n) { localId -> chi2[comp[localId]] }
                Content.MSet(colorRefine1WLColors(compGraph, compChi).toList())
            }
            return Content.MSet(components).serialize()
        }
        // Every v in this cell reads the SAME (pre-anchor) chi2 snapshot -- none of these calls
        // mutate chi2 or depend on each other, only on the read-only DecompositionStore and plain
        // colorRefine1WLColors -- safe to compute concurrently. anchor() itself (the actual chi2
        // mutation) still runs afterward, sequentially; only the per-vertex key computation is
        // parallelized here, up to boundedPool's cap.
        val precomputedKeys = boundedPool.submit(java.util.concurrent.Callable {
            cell.toList().parallelStream()
                .map { v -> v to remainderKeyOf(v) }
                .collect(java.util.stream.Collectors.toMap({ it.first }, { it.second }))
        }).get()
        if (anchor(chi2, cell) { v -> precomputedKeys.getValue(v) } > 0) refined = true

        if (relevantVertexCount != null) {
            val newRelevantClassCount = relevantClassCount()
            if (newRelevantClassCount > lastRelevantClassCount!!) {
                lastRelevantClassCount = newRelevantClassCount
                cellsSinceRelevantImprovement = 0
            } else {
                cellsSinceRelevantImprovement++
                if (cellsSinceRelevantImprovement >= phase2StaleCellStreakGuard) {
                    println(
                        "initialPhase Phase 2: relevant-vertex plateau after $phase2CellsProcessed/$phase2NonSingletonCells " +
                            "non-singleton cells ($phase2StaleCellStreakGuard consecutive cells with no increase to the " +
                            "$relevantVertexCount relevant vertices' class count, currently $lastRelevantClassCount) -- " +
                            "stopping Phase 2 early. Still sound: same reasoning as the cost guard above -- the remaining " +
                            "cells simply keep Phase 1's colouring for the vertices they would have touched.",
                    )
                    break
                }
            }
        }
    }
    if (!refined) return p1.withDecompositions(g, store)
    // Phase 3: final propagation.
    return colorRefine1WL(g, chi2).withDecompositions(g, store)
}

/**
 * Ranks AHU intern-pool ids by their CANONICAL STRINGS, in the order of `Content.Str(s).serialize()`
 * -- a function of the canonical forms alone, independent of the pool's id-assignment order (equal
 * strings intern to equal ids, so ids and strings are in bijection). This is exactly the order
 * anchor() would give a `Content.Str(canonical string)` key, but the strings are fetched on demand
 * inside the comparator and never held collectively (see ColoredAHU's intern-pool history: holding
 * them all on heap blew up rnd-3-reg).
 */
private fun canonicalRanks(ids: List<Int>): Map<Int, Int> =
    ids.sortedWith(Comparator { a, b ->
        Content.Str(ColoredAHU.canonicalFormOf(a)).serialize().compareTo(Content.Str(ColoredAHU.canonicalFormOf(b)).serialize())
    }).withIndex().associate { (i, id) -> id to i }

/** Attaches [store] as the partition's decomposition lookup (see
 *  [StablePartition.decompositionOf]). Falls back to computing dialysis(g, v) fresh for a vertex
 *  the store's `needsWork` mask skipped -- an already-singleton-at-Phase-0 vertex can still end up
 *  as a chosen root later, so "not stored" must mean "compute now", never "unreachable". */
private fun StablePartition.withDecompositions(g: Graph, store: DecompositionStore): StablePartition =
    StablePartition(color, cells, decompositionOf = { v -> if (store.has(v)) store.get(v) else dialysis(g, v) })

/**
 * Anchoring: groups [cls] (all sharing one colour) by [key], orders the groups by the canonical
 * order of their keys, leaves the first group's colour unchanged, and assigns freshly derived
 * colours to the rest. Equivariant: the groups and their canonical order are determined by
 * invariant keys, so corresponding classes of isomorphic inputs split identically. Returns the
 * number of new colours created.
 *
 * New colours are `Content.Tup(originalColor, groupRank)` rather than a literal global integer
 * counter: distinctness and canonical order both fall out of [Content]'s own total order
 * (different original colours never collide; within one class, group rank breaks the tie).
 */
/**
 * [key] returns [Content.serialize]'s STRING form, not a live [Content] -- grouping/sorting only
 * ever needs a comparable, equality-preserving proxy for the key, never the emitted colour (which
 * is built below from [originalColor]/[rank] alone, independent of the key's own representation).
 * Correctness of using the string instead of the live tree follows directly from two of
 * [Content]'s own documented invariants: equal values MUST serialize identically (so string
 * equality is exactly [Content] equality here), and "total order on Content = order on
 * serializations... holds everywhere" (so [String]'s natural ordering below matches [Content]'s
 * own structural order). This matters because a caller's [key] can be expensive to keep alive as a
 * live object tree -- see [dialysis.refinement.initialPhase]'s Phase 2, whose per-vertex remainder
 * key is a `Content.MSet` potentially as large as the vertex's own remainder component, retained
 * for every member of a cell simultaneously (confirmed directly: one `sts-51` cell of 12444
 * members drove heap from 15MB to 5663MB building that map of live [Content] trees before this
 * fix) -- a flat string has far less JVM per-node overhead than the equivalent tree of `Content.Tup`
 * /`Content.MSet`/`Content.Num` wrapper objects (each carrying its own object header plus a
 * [dialysis.content.SerializeCache] instance), and the LIVE tree itself only needs to exist
 * transiently per key computation (long enough to call [Content.serialize] once), not for the
 * whole cell's duration -- unlike going through `serialize()` for [Content.MSet]'s OWN
 * canonicalization/hashing (a documented, DIFFERENT past OOM bug, see that class's doc), there is
 * no cross-call structural SHARING here to lose: each vertex's key tree is built fresh,
 * independent of every other vertex's, so flattening it costs nothing semantically.
 */
private fun anchor(chi: Array<Content>, cls: IntArray, key: (Int) -> String): Int {
    if (cls.size <= 1) return 0   // a singleton class can never be split further -- skip `key` entirely
    val groups = cls.groupBy(key).entries.sortedBy { it.key }
    if (groups.size <= 1) return 0
    val originalColor = chi[cls[0]]
    groups.forEachIndexed { rank, (_, members) ->
        if (rank == 0) return@forEachIndexed
        val newColor = Content.Tup(listOf(originalColor, Content.Num(rank.toLong())))
        for (v in members) chi[v] = newColor
    }
    return groups.size - 1
}