package dialysis.group

/**
 * Luks's string isomorphism (Luks 1982; phase L2 of the Luks integration, 2026-10-10, CLOSURE_BOUND_SPEC "Luks
 * machinery"). For a permutation group K on a domain D (GAP right action), a K-invariant window W of D and two strings
 * x, y : D -> Int, [iso] returns the set { g in K*sigma : x(w) = y(w^g) for all w in W } as a coset H*tau, or null when
 * it is empty. With x = y and sigma = id this is the string automorphism group Aut_K^W(x).
 *
 * Recursion: |W| = 1 (W fixed by K): one check. K intransitive on W: chain rule over the orbit of min W and the rest.
 * K transitive on W: a block system on which K acts PRIMITIVELY (refined by repeated minimal block systems); N = kernel
 * of the action on the blocks; K*sigma = union of N*tau_i*sigma over coset representatives tau_i of N; each part is
 * solved with N, which is intransitive on W (the blocks are N-invariant); the non-empty answers H*rho_i combine into
 * <H, rho_i rho_1^-1>*rho_1. For K with composition factors of bounded order the primitive quotients have polynomial
 * order (Babai-Cameron-Palfy), so the branching is polynomial.
 *
 * [maxCosets] guards the branching: a primitive quotient larger than that throws [TooManyCosets] (no silent cut).
 */
class TooManyCosets(val count: Long) : RuntimeException("primitive block action has $count cosets")

class Coset(val group: PermGroup, val rep: IntArray) {
    /** Set when the group was NOT built (edgeSetIso with needGroup = false): its generators and exact order, so the caller
     *  can fold them into one final Schreier-Sims instead of building a large intermediate group (memory, 2026-10-12). */
    var lazyGens: List<IntArray>? = null; var lazyOrder: java.math.BigInteger? = null
}

class LuksIso(private val maxCosets: Long = 100_000, private val kernelBranchMax: Long = System.getenv("LUKS_KERNEL_BRANCH_MAX")?.toLong() ?: 64) {
    var calls = 0L; private set
    var maxBranch = 0L; private set
    /** Ablation counters (2026-10-12, FALLBACK_SPEC "do we need Babai"): primitive quotients met in the transitive step.
     *  A quotient on nb >= 5 blocks of order >= nb!/2 is a GIANT (Alt/Sym on the blocks) -- the case Babai's local
     *  certificates are for. giantMaxDegree = largest nb of a giant; maxQuotientDegree = largest nb of any quotient. */
    var giants = 0L; private set
    var giantMaxDegree = 0; private set
    var maxQuotientDegree = 0; private set

    fun iso(k: Coset, w: IntArray, x: IntArray, y: IntArray): Coset? {
        calls++
        val n = k.group.n; val sigma = k.rep
        if (w.isEmpty()) return k
        // constant strings on W: every element of the coset maps x to y on W, or none does
        run { val c = x[w[0]]; if (w.all { x[it] == c }) return if (w.all { y[sigma[it]] == c }) k else null }
        // optimisation 1 (window restriction): solve on K^W (degree |W|) and lift, unless W is the whole domain
        if (w.size > 1 && w.size < n) return isoRestricted(k, w, x, y)
        if (w.size == 1) {
            val p = w[0]
            return if (x[p] == y[sigma[p]]) k else null
        }
        val gens = k.group.generators
        // all K-orbits on W at once (W is K-invariant)
        val orbitOf = HashMap<Int, Int>(w.size * 2); val orbits = ArrayList<IntArray>()
        for (s0 in w) if (s0 !in orbitOf) {
            val o = ArrayList<Int>(); o.add(s0); orbitOf[s0] = orbits.size; var i = 0
            while (i < o.size) { val p = o[i++]; for (g in gens) { val q = g[p]; if (q !in orbitOf) { orbitOf[q] = orbits.size; o.add(q) } } }
            orbits.add(o.toIntArray())
        }
        if (orbits.size > 1) {
            // fixed points of K: one check each, no recursion
            for (o in orbits) if (o.size == 1 && x[o[0]] != y[sigma[o[0]]]) return null
            // chain rule over the non-trivial K-orbits: each stays invariant under the shrinking coset group
            var cur: Coset = k
            for (o in orbits.filter { it.size > 1 }.sortedBy { it.size }) cur = iso(cur, o, x, y) ?: return null
            return cur
        }
        val orb = orbits[0]
        // transitive on W: block system with primitive action on the blocks
        val diag = w.size >= 1000 && System.getenv("LUKS_DIAG") != null; val t0 = System.currentTimeMillis()
        val blockOf = primitiveBlockSystem(k.group, w)
        val nb = blockOf.values.max() + 1
        if (diag) System.err.println("  [iso] |W|=${w.size} blocks=$nb (${System.currentTimeMillis() - t0} ms)")
        val (kernel, reps) = kernelAndReps(k.group, w, blockOf, nb)
        if (diag) System.err.println("  [iso] kernel |N|=${kernel.order} cosets=${reps.size} (${System.currentTimeMillis() - t0} ms)")
        if (reps.size > maxBranch) maxBranch = reps.size.toLong()
        val parts = ArrayList<Coset>()
        for (tau in reps) {
            val c = iso(Coset(kernel, Perms.mul(tau, sigma)), w, x, y) ?: continue
            parts.add(c)
        }
        if (parts.isEmpty()) return null
        val r1 = parts[0].rep; val r1inv = Perms.inv(r1)
        val newGens = ArrayList<IntArray>(parts[0].group.generators)
        for (c in parts.drop(1)) newGens.add(Perms.mul(c.rep, r1inv))
        // the parts are disjoint cosets H*rho_i of the same H = Aut_N^W, so |A| = |H| * #parts: exact randomised build
        val target = parts[0].group.order.multiply(java.math.BigInteger.valueOf(parts.size.toLong()))
        return Coset(PermGroup.ofOrder(n, newGens, target).withFewGenerators(), r1)
    }

    /**
     * The same answer computed on the restriction K^W: with y'(u) = y(u^sigma) the condition for g = k sigma is
     * x(w) = y'(w^k), which depends only on k|W. Solve on K^W (local indices 0..|W|-1), then lift: K is rebuilt once
     * (known order |K|) with a base starting at a base of K^W, an element of K^W lifts by sifting along those levels,
     * and the kernel of K -> K^W is the stabiliser of those base points. Exact group sizes throughout (ofOrder).
     */
    private fun isoRestricted(k: Coset, w: IntArray, x: IntArray, y: IntArray): Coset? {
        val m = w.size; val sigma = k.rep
        val wc = WindowChain(k.group, w)
        val xW = IntArray(m) { x[w[it]] }; val yW = IntArray(m) { y[sigma[w[it]]] }
        val rw = iso(Coset(wc.kw, Perms.id(m)), IntArray(m) { it }, xW, yW) ?: return null
        val c = wc.liftCoset(rw.group, rw.rep)
        return Coset(c.group, Perms.mul(c.rep, sigma))
    }

    /** Block id per point of the transitive window [w] (= the domain of [g] here), with K acting primitively on the
     *  blocks (singletons if K is primitive on [w]). Repeated minimal coarsenings, computed on W directly: the smallest
     *  block containing B(alpha) u {beta} (union-find closure under the generators) over beta outside B(alpha); one beta
     *  per orbit of the point stabiliser K_alpha suffices (h in K_alpha maps that block to the one for beta^h). */
    private fun primitiveBlockSystem(g: PermGroup, w: IntArray): Map<Int, Int> {
        val n = g.n
        val pos = IntArray(n) { -1 }; for (i in w.indices) pos[w[i]] = i
        val alphaPt = if (g.levels.isNotEmpty() && pos[g.levels[0].point] >= 0) g.levels[0].point else w[0]
        val stabGens = if (alphaPt == g.levels.firstOrNull()?.point) g.stabiliserGens(1) else g.generators.filter { it[alphaPt] == alphaPt }
        val sOrb = Perms.orbits(n, stabGens)
        val reps = ArrayList<Int>(); run { val seen = HashSet<Int>(); for (x in w) if (x != alphaPt && seen.add(sOrb[x])) reps.add(x) }
        val gens = g.generators; val m = w.size; val a = pos[alphaPt]
        var block = IntArray(m) { it }   // block id per local point
        if (m >= 1000 && System.getenv("LUKS_DIAG") != null) System.err.println("  [blocks] m=$m gens=${gens.size} stabGens=${stabGens.size} reps=${reps.size} |K|=${g.order}")
        while (true) {
            val inB = (0 until m).filter { block[it] == block[a] }
            var best: IntArray? = null; var bestSize = Int.MAX_VALUE
            for (bp in reps) {
                val b0 = pos[bp]; if (block[b0] == block[a]) continue
                val par = IntArray(m) { it }
                fun find(x: Int): Int { var y = x; while (par[y] != y) { par[y] = par[par[y]]; y = par[y] }; return y }
                val queue = ArrayDeque<Long>()   // pairs packed as x * m + y
                fun union(x: Int, y: Int) { val rx = find(x); val ry = find(y); if (rx != ry) { par[maxOf(rx, ry)] = minOf(rx, ry); queue.add(rx.toLong() * m + ry) } }
                for (i in inB) union(a, i)   // B(alpha); closure makes the result a union of current blocks
                union(a, b0)
                while (queue.isNotEmpty()) {
                    val pr = queue.removeFirst(); val x = (pr / m).toInt(); val y = (pr % m).toInt()
                    for (h in gens) union(pos[h[w[x]]], pos[h[w[y]]])
                }
                val ra = find(a); val size = (0 until m).count { find(it) == ra }
                if (size < m && size < bestSize) { bestSize = size; best = IntArray(m) { find(it) } }
            }
            if (m >= 1000 && System.getenv("LUKS_DIAG") != null) System.err.println("  [blocks] iter: |B(alpha)|=${inB.size} -> best=$bestSize")
            val nb = best ?: return w.withIndex().associate { (i, p) -> p to block[i] }
            val ids = HashMap<Int, Int>(); block = IntArray(m) { ids.getOrPut(nb[it]) { ids.size } }
        }
    }

    /** Kernel of the action of [g] on the blocks of [w] and its coset representatives (Luks); when the quotient has more
     *  than max([kernelBranchMax], #blocks) elements, instead the stabiliser of one block and its coset representatives. */
    private fun kernelAndReps(g: PermGroup, w: IntArray, blockOf: Map<Int, Int>, nb: Int): Pair<PermGroup, List<IntArray>> {
        val n = g.n
        // extended domain: D followed by one point per block
        val rep = IntArray(nb) { -1 }; for ((p, b) in blockOf) if (rep[b] < 0) rep[b] = p
        val ext = g.generators.map { h -> IntArray(n + nb) { i -> if (i < n) h[i] else n + blockOf.getValue(h[rep[i - n]]) } }
        val blockPts = IntArray(nb) { n + it }
        // same group in a faithful extended action: its order is known -> randomised Schreier-Sims with target (exact)
        val eg = PermGroup.ofOrder(n + nb, ext, g.order, blockPts)
        // number of levels at the start of the base that are block points
        val lv = eg.levels.takeWhile { it.point >= n }
        run {
            val qOrder = lv.fold(java.math.BigInteger.ONE) { acc, l -> acc.multiply(java.math.BigInteger.valueOf(l.orbit.size.toLong())) }
            if (nb > maxQuotientDegree) maxQuotientDegree = nb
            if (nb >= 5) {
                var half = java.math.BigInteger.ONE; for (i in 3..nb) half = half.multiply(java.math.BigInteger.valueOf(i.toLong()))   // nb!/2
                if (qOrder >= half) { giants++; if (nb > giantMaxDegree) giantMaxDegree = nb }
            }
        }
        var count = 1L; for (l in lv) { count = if (count > Long.MAX_VALUE / maxOf(1, l.orbit.size)) Long.MAX_VALUE else count * l.orbit.size }
        // large primitive quotient: branch over the stabiliser of one block (index = #blocks) instead of the kernel;
        // that subgroup leaves the block invariant, so the chain rule checks the string on it first (early rejection)
        if (count > maxOf(kernelBranchMax, nb.toLong()) && lv.isNotEmpty()) {
            val l0 = lv[0]
            val sub = PermGroup.ofOrder(n, eg.stabiliserGens(1).map { it.copyOf(n) }, g.order.divide(java.math.BigInteger.valueOf(l0.orbit.size.toLong())))
            return sub to l0.orbit.map { l0.rep(it).copyOf(n) }
        }
        if (count > maxCosets) throw TooManyCosets(count)
        val kernelGens = eg.stabiliserGens(lv.size).map { it.copyOf(n) }
        val kernel = PermGroup.ofOrder(n, kernelGens, g.order.divide(java.math.BigInteger.valueOf(count))).withFewGenerators()
        // coset representatives: products u_{L-1} ... u_0 over the block levels (each coset of the kernel once)
        var reps = listOf(Perms.id(n + nb))
        for (i in lv.indices.reversed()) {
            val l = lv[i]
            val next = ArrayList<IntArray>(reps.size * l.orbit.size)
            for (r in reps) for (pt in l.orbit) next.add(Perms.mul(r, l.rep(pt)))
            reps = next
        }
        return kernel to reps.map { it.copyOf(n) }
    }

    companion object {
        /**
         * Stab_P(E) for a set [edges] of unordered pairs of points (the L1 cut), without the pair action on all of V:
         * (1) restrict P to U = P-closure of the endpoints (the kernel of P -> P^U fixes E pointwise);
         * (2) refine: colour a in U by (K-orbit of a, multiset of K-orbits of its E-neighbours) -- Stab_P(E)-invariant --
         *     and replace K by its string stabiliser (Luks on U only) until the colouring no longer splits a K-orbit;
         * (3) Luks on U u Omega with Omega = K-orbits of the E-pairs (much smaller than the P-orbits after (2));
         * (4) lift to P. Exact: Stab_P(E) <= K at every step, so Stab_K(E) = Stab_P(E).
         */
        fun edgeSetStabiliser(p: PermGroup, edges: List<IntArray>, maxCosets: Long = 100_000, log: (String) -> Unit = {}): Pair<PermGroup, LuksIso> {
            val (c, l) = edgeSetIso(p, edges, edges, maxCosets, log = log)
            return c!!.group to l
        }

        /**
         * Two-sided version: { g in P : E1^g = E2 } as a coset of Stab_P(E1), or null. Same driver as above with
         * x from E1 and y from E2. Invariant: the answer is { k sigma : k in K, E1^k = E2s } with E2s = E2^(sigma^-1)
         * (g = k sigma maps E1 to E2 iff k maps E1 to E2^(sigma^-1)); each Luks step returns H rho inside K, and the new
         * state is K := H, sigma := rho sigma.
         */
        fun edgeSetIso(p: PermGroup, e1: List<IntArray>, e2: List<IntArray>, maxCosets: Long = 100_000,
                       windowCache: MutableMap<List<Int>, WindowChain>? = null, needGroup: Boolean = true,
                       log: (String) -> Unit = {}): Pair<Coset?, LuksIso> {
            val n = p.n; val l = LuksIso(maxCosets)
            if (e1.size != e2.size) return null to l
            val inU = BooleanArray(n); val uList = ArrayList<Int>()
            for (e in e1 + e2) for (a in e) if (!inU[a]) { inU[a] = true; uList.add(a) }
            var i0 = 0
            while (i0 < uList.size) { val a = uList[i0++]; for (g in p.generators) if (!inU[g[a]]) { inU[g[a]] = true; uList.add(g[a]) } }
            val u = uList.sorted().toIntArray(); val nu = u.size   // sorted: local indices = positions, same for every call with this U
            val loc = IntArray(n) { -1 }; for (j in u.indices) loc[u[j]] = j
            // memory (2026-10-12, A5 coset loops): P restricted to U is the same for every call with the same P and U --
            // the caller may pass a cache; the restriction is a Schreier-Sims on all of P's points with full transversals
            val uc = windowCache?.getOrPut(u.toList()) { WindowChain(p, u) } ?: WindowChain(p, u)
            log("U = ${nu} points, |P^U| = ${uc.kw.order}")
            val all = IntArray(nu) { it }
            fun key(a: Int, b: Int) = minOf(a, b).toLong() * nu + maxOf(a, b)
            val e1Keys = HashSet<Long>(); for (e in e1) e1Keys.add(key(loc[e[0]], loc[e[1]]))
            val e2l = e2.map { intArrayOf(loc[it[0]], loc[it[1]]) }
            var k = uc.kw; var sigma = Perms.id(nu)
            fun e2sKeys(): HashSet<Long> { val si = Perms.inv(sigma); return e2l.map { key(si[it[0]], si[it[1]]) }.toHashSet() }
            fun adjOf(keys: Set<Long>): Array<ArrayList<Int>> {
                val adj = Array(nu) { ArrayList<Int>() }
                for (kk in keys) { val a = (kk / nu).toInt(); val b = (kk % nu).toInt(); adj[a].add(b); adj[b].add(a) }
                return adj
            }
            /** refine by string isomorphisms on U; false = no element maps E1 to E2s */
            fun refine(): Boolean {
                while (true) {
                    val e2s = e2sKeys(); if (e2s.size != e1Keys.size) return false
                    val adj1 = adjOf(e1Keys); val adj2 = adjOf(e2s)
                    val orb = k.orbits()
                    val keyOf = HashMap<List<Int>, Int>()
                    val x = IntArray(nu) { a -> keyOf.getOrPut(listOf(orb[a]) + adj1[a].map { orb[it] }.sorted()) { keyOf.size } }
                    val y = IntArray(nu) { a -> keyOf.getOrPut(listOf(orb[a]) + adj2[a].map { orb[it] }.sorted()) { keyOf.size } }
                    val nOrb = orb.distinct().size
                    if (keyOf.size == nOrb) return true   // one colour per K-orbit on both sides: every k qualifies
                    val c = l.iso(Coset(k, Perms.id(nu)), all, x, y) ?: return false
                    k = c.group; sigma = Perms.mul(c.rep, sigma)
                    log("refine: $nOrb -> ${keyOf.size} colours, |K| = ${k.order}")
                }
            }
            if (!refine()) return null to l
            // per-Omega-orbit driver: a K-orbit O of pairs meeting E1 or E2s and not inside both; K sigma := the part
            // mapping E1 n O onto E2s n O, by Luks on U u O (degree |U| + |O|); refine again
            while (true) {
                val e2s = e2sKeys()
                val idOf = HashSet<Long>(); var target: ArrayList<IntArray>? = null
                for (pk in e1Keys + e2s) {
                    if (pk in idOf) continue
                    val o = ArrayList<IntArray>(); o.add(intArrayOf((pk / nu).toInt(), (pk % nu).toInt())); idOf.add(pk); var i = 0
                    while (i < o.size) {
                        val pe = o[i++]
                        for (g in k.generators) { val kk = key(g[pe[0]], g[pe[1]]); if (idOf.add(kk)) o.add(intArrayOf(g[pe[0]], g[pe[1]])) }
                    }
                    val in1 = o.count { key(it[0], it[1]) in e1Keys }; val in2 = o.count { key(it[0], it[1]) in e2s }
                    if (in1 != in2) return null to l
                    if (in1 < o.size && (target == null || o.size < target.size)) target = o
                }
                val o = target ?: break
                val m = o.size; val dn = nu + m
                val oid = HashMap<Long, Int>(m * 2); for ((j, pe) in o.withIndex()) oid[key(pe[0], pe[1])] = j
                val ke = k.extendedAction(dn) { g -> IntArray(dn) { i -> if (i < nu) g[i] else nu + oid.getValue(key(g[o[i - nu][0]], g[o[i - nu][1]])) } }
                val x = IntArray(dn); val y = IntArray(dn)
                for ((j, pe) in o.withIndex()) { val kk = key(pe[0], pe[1]); if (kk in e1Keys) x[nu + j] = 1; if (kk in e2s) y[nu + j] = 1 }
                val c = l.iso(Coset(ke, Perms.id(dn)), IntArray(m) { nu + it }, x, y) ?: return null to l
                k = PermGroup.ofOrder(nu, c.group.generators.map { it.copyOf(nu) }, c.group.order); sigma = Perms.mul(c.rep.copyOf(nu), sigma)
                log("orbit of ${m} pairs (${x.count { it == 1 }} in E1): |K| = ${k.order}")
                if (!refine()) return null to l
            }
            log("|K| = ${k.order} on U; lifting")
            // needGroup = false: only the coset representative is wanted (the caller already has the stabiliser) -- skips a
            // Schreier-Sims of the lifted group on all of P's points
            if (needGroup) return uc.liftCoset(k, sigma) to l
            val (lg, lo) = uc.liftGens(k)
            return Coset(PermGroup.of(n, emptyList()), uc.lift(sigma)).also { it.lazyGens = lg; it.lazyOrder = lo } to l
        }

        /** Aut_P(x) on the window W: the elements of P preserving x on W. */
        fun stringAut(p: PermGroup, w: IntArray, x: IntArray, maxCosets: Long = 100_000): Pair<PermGroup, LuksIso> {
            val l = LuksIso(maxCosets)
            val c = l.iso(Coset(p, Perms.id(p.n)), w, x, x) ?: error("the identity always preserves x")
            return c.group to l
        }
    }
}

/**
 * K restricted to a K-invariant window [w], without a blind Schreier-Sims on K^W: K is rebuilt once with KNOWN order
 * (exact randomised ofOrder) on a base that starts with every point of W. The leading levels then have their points in
 * W, the product of their orbit sizes is |K^W|, and the stabiliser after them is the kernel K_(W). K^W itself is built
 * with that known order; elements of K^W lift to K by sifting along the leading levels.
 */
class WindowChain(val k: PermGroup, val w: IntArray) {
    private val n = k.n; private val m = w.size
    private val loc = IntArray(n) { -1 }.also { for (i in w.indices) it[w[i]] = i }
    private val kb = PermGroup.ofOrder(n, k.generators, k.order, w, dropTrivial = true)
    private val nl = kb.levels.takeWhile { loc[it.point] >= 0 }.size
    val orderW: java.math.BigInteger = kb.levels.take(nl).fold(java.math.BigInteger.ONE) { a, l -> a.multiply(java.math.BigInteger.valueOf(l.orbit.size.toLong())) }
    val kw: PermGroup = PermGroup.ofOrder(m, k.generators.map { g -> IntArray(m) { i -> loc[g[w[i]]] } }, orderW,
        IntArray(nl) { loc[kb.levels[it].point] })

    fun lift(gw: IntArray): IntArray {
        var r = gw; val us = ArrayList<IntArray>(nl)
        for (i in 0 until nl) {
            val l = kb.levels[i]; val beta = w[r[loc[l.point]]]
            if (beta == l.point) continue
            val u = l.repCached(beta); us.add(u)
            val uw = IntArray(m) { j -> loc[u[w[j]]] }
            r = Perms.mul(r, Perms.inv(uw))
        }
        var h = Perms.id(n); for (i in us.indices.reversed()) h = Perms.mul(h, us[i]); return h
    }

    /** Generators and exact order of the lift of [hw] <= K^W to K (= <lifts, kernel>), without building the group. */
    fun liftGens(hw: PermGroup): Pair<List<IntArray>, java.math.BigInteger> =
        (hw.generators.map { lift(it) } + kb.stabiliserGens(nl)) to hw.order.multiply(k.order.divide(orderW))

    /** The coset [hw]*[rw] of K^W lifted to K: <lifts, kernel> * lift(rw), exact order |hw| * |K_(W)|. */
    fun liftCoset(hw: PermGroup, rw: IntArray): Coset {
        val aGens = hw.generators.map { lift(it) } + kb.stabiliserGens(nl)
        val a = PermGroup.ofOrder(n, aGens, hw.order.multiply(k.order.divide(orderW)))
        return Coset(a.withFewGenerators(), lift(rw))
    }
}
