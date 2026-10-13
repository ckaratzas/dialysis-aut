package dialysis.group

import java.math.BigInteger

/**
 * Permutation groups given by generators (Luks integration, phase L0, 2026-10-10; CLOSURE_BOUND_SPEC "Luks
 * machinery"). Permutations are IntArrays of images on {0..n-1} with GAP's RIGHT action convention:
 * x^(gh) = (x^g)^h, i.e. [mul] (g, h) = "g then h". This keeps every result directly comparable with GAP.
 *
 * Core: deterministic Schreier-Sims (Holt, Eick, O'Brien, Handbook of CGT, Alg. SCHREIERSIMS) producing a base and
 * strong generating set with Schreier vectors (no explicit transversals: memory O(n) per level). On top: order,
 * membership, sifting, coset representatives, pointwise stabiliser chains with a prescribed base prefix, orbits,
 * minimal block systems (Atkinson's union-find method) and induced actions on orbits and block systems.
 * Orders are exact: [of] is deterministic Schreier-Sims; [ofOrder] is randomised Schreier-Sims that is only called with
 * a KNOWN target order and stops exactly when the chain reaches it (an overshoot is an error), so an order is never a
 * lower bound. (Comment corrected 2026-10-12: it used to say "no randomisation".)
 */
object Perms {
    fun id(n: Int) = IntArray(n) { it }
    /** g then h. */
    fun mul(g: IntArray, h: IntArray) = IntArray(g.size) { h[g[it]] }
    fun inv(g: IntArray): IntArray { val r = IntArray(g.size); for (i in g.indices) r[g[i]] = i; return r }
    fun isId(g: IntArray): Boolean { for (i in g.indices) if (g[i] != i) return false; return true }
    fun movedPoint(g: IntArray): Int { for (i in g.indices) if (g[i] != i) return i; return -1 }

    /** Orbits of <gens> on {0..n-1}: orbit id per point (smallest point of the orbit). */
    fun orbits(n: Int, gens: List<IntArray>): IntArray {
        val id = IntArray(n) { -1 }
        for (s in 0 until n) {
            if (id[s] >= 0) continue
            id[s] = s; val q = ArrayDeque<Int>(); q.add(s)
            while (q.isNotEmpty()) { val x = q.removeFirst(); for (g in gens) { val y = g[x]; if (id[y] < 0) { id[y] = s; q.add(y) } } }
        }
        return id
    }

    fun orbit(n: Int, gens: List<IntArray>, start: Int): IntArray {
        val seen = BooleanArray(n); seen[start] = true; val out = ArrayList<Int>(); out.add(start); var i = 0
        while (i < out.size) { val x = out[i++]; for (g in gens) { val y = g[x]; if (!seen[y]) { seen[y] = true; out.add(y) } } }
        return out.toIntArray()
    }

    // blocks need only generators (no stabiliser chain): static so callers need no Schreier-Sims
    fun minimalBlocks(generators: List<IntArray>, orbit: IntArray, alpha: Int, beta: Int): Map<Int, Int> {
        val pos = HashMap<Int, Int>(orbit.size * 2); orbit.forEachIndexed { i, x -> pos[x] = i }
        val par = IntArray(orbit.size) { it }
        fun find(x: Int): Int { var y = x; while (par[y] != y) { par[y] = par[par[y]]; y = par[y] }; return y }
        val queue = ArrayDeque<Pair<Int, Int>>()
        fun union(a: Int, b: Int) { val ra = find(a); val rb = find(b); if (ra != rb) { par[maxOf(ra, rb)] = minOf(ra, rb); queue.add(ra to rb) } }
        union(pos.getValue(alpha), pos.getValue(beta))
        while (queue.isNotEmpty()) {
            val (a, b) = queue.removeFirst()
            for (g in generators) union(pos.getValue(g[orbit[a]]), pos.getValue(g[orbit[b]]))
        }
        val out = HashMap<Int, Int>(); for (i in orbit.indices) out[orbit[i]] = find(i); return out
    }

    /** Primitive on the (transitive) orbit [orbit]: every minimal block through orbit[0] is trivial or everything. */
    fun isPrimitive(generators: List<IntArray>, orbit: IntArray): Boolean {
        if (orbit.size <= 2) return true
        val a = orbit[0]
        for (b in orbit) if (b != a) { val blk = minimalBlocks(generators, orbit, a, b); if (blk.values.toSet().size != 1) return false }
        return true
    }

    /** A nontrivial block system on [orbit] (block id per point, ids 0..k-1), or null if primitive. Smallest blocks first
     *  over the choices beta, i.e. a minimal block system. */
    fun minimalBlockSystem(generators: List<IntArray>, orbit: IntArray): Map<Int, Int>? {
        if (orbit.size <= 2) return null
        val a = orbit[0]; var best: Map<Int, Int>? = null; var bestSize = Int.MAX_VALUE
        for (b in orbit) if (b != a) {
            val blk = minimalBlocks(generators, orbit, a, b); val k = blk.values.toSet().size
            if (k == 1) continue
            val size = orbit.size / k
            if (size < bestSize) { bestSize = size; best = blk }
        }
        val b = best ?: return null
        val ids = b.values.toSortedSet().withIndex().associate { (i, v) -> v to i }
        return b.mapValues { ids.getValue(it.value) }
    }
}

/**
 * A level of the stabiliser chain: base point [point], strong generators [gens] (all fixing the earlier base points),
 * and a Schreier vector over the orbit of [point] under [gens]: for an orbit point x != point, [label] x = index of the
 * generator g with y^g = x for the parent y = x^(g^-1) (stored via [invGens]).
 */
class ChainLevel(val n: Int, val point: Int) {
    companion object {
        /** ints per representative cache (per level, per direction): default 4M ints = 16 MB. The bound is PER LEVEL, so a
         *  chain with many levels at large degree multiplies it (A5-K33, 22,680 points: ~1.8 GB over the levels,
         *  2026-10-12) -- GROUP_CACHE_INTS overrides it. */
        val CACHE_INTS: Long = System.getenv("GROUP_CACHE_INTS")?.toLongOrNull() ?: 4_000_000L
    }
    val gens = ArrayList<IntArray>()
    val invGens = ArrayList<IntArray>()
    /** -1 outside the orbit, -2 at the base point, else generator index. */
    var label = IntArray(n) { -1 }
    var orbit = IntArray(0)

    fun addGen(g: IntArray, gInv: IntArray = Perms.inv(g)) { gens.add(g); invGens.add(gInv); extendOrbit() }

    /** Extend the Schreier tree after new generators: existing labels (hence existing coset representatives) are kept,
     *  only new orbit points get labels. Needed for the incremental Schreier-Sims: a Schreier generator tested once
     *  stays valid because its representatives never change. */
    fun extendOrbit() {
        if (orbit.isEmpty()) { recomputeOrbit(); return }
        val out = ArrayList<Int>(orbit.size + 16); orbit.forEach { out.add(it) }; var i = 0
        while (i < out.size) {
            val x = out[i++]
            for ((gi, g) in gens.withIndex()) { val y = g[x]; if (label[y] == -1) { label[y] = gi; out.add(y) } }
        }
        orbit = out.toIntArray()
    }

    fun recomputeOrbit() {
        repCache.clear(); invRepCache.clear()
        label = IntArray(n) { -1 }; label[point] = -2
        val out = ArrayList<Int>(); out.add(point); var i = 0
        while (i < out.size) {
            val x = out[i++]
            for ((gi, g) in gens.withIndex()) { val y = g[x]; if (label[y] == -1) { label[y] = gi; out.add(y) } }
        }
        orbit = out.toIntArray()
    }

    fun inOrbit(x: Int) = label[x] != -1

    // representatives never change once computed (incremental Schreier trees keep labels), so they can be cached
    // bounded (LRU): at most CACHE_INTS ints per cache, i.e. CACHE_INTS / n entries -- an unbounded cache cost 435 MB
    // per level on A5-K4 (orbit 3,600 at degree 15,120); small groups still keep every representative
    private val maxEntries = maxOf(16, (CACHE_INTS / maxOf(1, n)).toInt())
    private val repCache = object : LinkedHashMap<Int, IntArray>(64, 0.75f, true) { override fun removeEldestEntry(e: MutableMap.MutableEntry<Int, IntArray>?) = size > maxEntries }
    private val invRepCache = object : LinkedHashMap<Int, IntArray>(64, 0.75f, true) { override fun removeEldestEntry(e: MutableMap.MutableEntry<Int, IntArray>?) = size > maxEntries }
    /** Cached coset representative and its inverse (sifting multiplies by the inverse). */
    fun repCached(x: Int): IntArray = repCache.getOrPut(x) { rep(x) }
    fun invRep(x: Int): IntArray = invRepCache.getOrPut(x) { Perms.inv(repCached(x)) }

    /** Coset representative u with point^u = x (x must be in the orbit). */
    fun rep(x: Int): IntArray {
        // walk back to the base point: x = y^g  =>  y = x^(g^-1); u_x = u_y * g
        val word = ArrayList<Int>(); var y = x
        while (label[y] != -2) { val gi = label[y]; word.add(gi); y = invGens[gi][y] }
        var u = Perms.id(n)
        for (k in word.indices.reversed()) u = Perms.mul(u, gens[word[k]])
        return u
    }
}

class PermGroup private constructor(val n: Int, val levels: List<ChainLevel>, val generators: List<IntArray>) {

    val base: IntArray get() = IntArray(levels.size) { levels[it].point }
    val order: BigInteger get() = levels.fold(BigInteger.ONE) { acc, l -> acc.multiply(BigInteger.valueOf(l.orbit.size.toLong())) }
    val isTrivial: Boolean get() = levels.isEmpty()

    /** Residue of g after sifting, and the level where sifting stopped (levels.size = through every level). */
    fun sift(g0: IntArray): Pair<IntArray, Int> {
        var g = g0
        for ((i, l) in levels.withIndex()) {
            val beta = g[l.point]
            if (!l.inOrbit(beta)) return g to i
            if (beta != l.point) g = Perms.mul(g, l.invRep(beta))
        }
        return g to levels.size
    }

    operator fun contains(g: IntArray): Boolean { val (r, lv) = sift(g); return lv == levels.size && Perms.isId(r) }

    /** The pointwise stabiliser of base points 0..k-1 (strong generators of level k). */
    fun stabiliserGens(k: Int): List<IntArray> = if (k >= levels.size) emptyList() else levels[k].gens.toList()

    /** Pointwise stabiliser of [points] (any order): a new BSGS whose base starts with [points]. */
    fun pointwiseStabiliser(points: IntArray): PermGroup {
        val g = schreierSims(n, generators, points)
        val k = points.size
        return PermGroup(n, g.levels.drop(k).map { l -> ChainLevel(n, l.point).also { nl -> l.gens.forEach { nl.gens.add(it); nl.invGens.add(Perms.inv(it)) }; nl.recomputeOrbit() } },
            g.stabiliserGens(k).ifEmpty { emptyList() })
    }

    fun orbits(): IntArray = Perms.orbits(n, generators)

    /** A uniformly random element: one random coset representative per level, multiplied up the chain. */
    fun randomElement(rnd: java.util.Random): IntArray {
        var g = Perms.id(n)
        for (i in levels.indices.reversed()) { val l = levels[i]; g = Perms.mul(g, l.repCached(l.orbit[rnd.nextInt(l.orbit.size)])) }
        return g
    }

    /**
     * The same group (same BSGS) with a short generating list: a few uniformly random elements, verified to generate by
     * the exact known-order build (ofOrder reaches |G| only if they generate G); falls back to the old list. Strong
     * generators of lifted kernels otherwise accumulate through the Luks recursion (orbit closures, block quotients).
     */
    fun withFewGenerators(seed: Long = 7L): PermGroup {
        if (fewGensThreshold <= 0 || generators.size <= fewGensThreshold || levels.isEmpty()) return this
        val rnd = java.util.Random(seed); val cand = ArrayList<IntArray>()
        repeat(2) { cand.add(randomElement(rnd)) }
        while (cand.size < minOf(generators.size, 12)) {
            val ok = try { ofOrder(n, cand, order, base, maxRounds = 50 * levels.size + 200); true } catch (e: IllegalStateException) { false }
            if (ok) return PermGroup(n, levels, cand.toList())
            cand.add(randomElement(rnd))
        }
        return this
    }

    /**
     * The same group in an extended action on {0..dn-1} ([ext] maps a permutation of {0..n-1} to one of {0..dn-1}
     * whose action on the extra points is induced, e.g. on pairs). The base lies in {0..n-1} and the action there is
     * unchanged, so this BSGS -- same base, same Schreier trees -- is a complete BSGS of the extended action: no new
     * Schreier-Sims. Shared strong generators stay shared (one extended copy and one inverse each).
     */
    fun extendedAction(dn: Int, ext: (IntArray) -> IntArray): PermGroup {
        val done = java.util.IdentityHashMap<IntArray, Pair<IntArray, IntArray>>()
        fun e(g: IntArray) = done.getOrPut(g) { val x = ext(g); x to Perms.inv(x) }
        val nl = levels.map { l -> ChainLevel(dn, l.point).also { c -> for (g in l.gens) { val (x, xi) = e(g); c.gens.add(x); c.invGens.add(xi) }; c.recomputeOrbit() } }
        return PermGroup(dn, nl, generators.map { e(it).first })
    }

    fun isTransitive(on: IntArray): Boolean = on.isEmpty() || Perms.orbit(n, generators, on[0]).size == on.size

    /**
     * Minimal block containing alpha and beta for the action on the orbit [orbit] (Atkinson: union-find closure of the
     * relation {alpha ~ beta} under the generators). Returns block id per point of [orbit] (index into [orbit] -> class).
     */
    fun minimalBlocks(orbit: IntArray, alpha: Int, beta: Int): Map<Int, Int> = Perms.minimalBlocks(generators, orbit, alpha, beta)
    fun isPrimitive(orbit: IntArray): Boolean = Perms.isPrimitive(generators, orbit)
    fun minimalBlockSystem(orbit: IntArray): Map<Int, Int>? = Perms.minimalBlockSystem(generators, orbit)

    /** Action on a union-closed set of points (an orbit or union of orbits): generators as permutations of 0..|on|-1. */
    fun actionOn(on: IntArray): List<IntArray> {
        val pos = HashMap<Int, Int>(on.size * 2); on.forEachIndexed { i, x -> pos[x] = i }
        return generators.map { g -> IntArray(on.size) { i -> pos.getValue(g[on[i]]) } }
    }

    /** Action on a block system (block id per point, ids 0..k-1): generators as permutations of the k blocks. */
    fun actionOnBlocks(blockOf: Map<Int, Int>): List<IntArray> {
        val k = blockOf.values.max() + 1
        val rep = IntArray(k) { -1 }; for ((x, b) in blockOf) if (rep[b] < 0) rep[b] = x
        return generators.map { g -> IntArray(k) { b -> blockOf.getValue(g[rep[b]]) } }
    }

    companion object {
        /** LUKS_FEWGENS: generator lists longer than this are shortened by [withFewGenerators] (default 0 = off: the
         *  verification costs more than it saves on S3 group CFI, 28.8 s vs 5.1 s on rc20). */
        val fewGensThreshold: Int = System.getenv("LUKS_FEWGENS")?.toInt() ?: 0

        /** A generating set of <gens> with at most log2|G| elements: keep a generator only if it is not already in the
         *  group generated by the kept ones (membership by sifting). For redundant generator lists (e.g. the 472 leaf
         *  automorphisms of one A5 gadget). */
        fun reduceGenerators(n: Int, gens: List<IntArray>): List<IntArray> {
            val kept = ArrayList<IntArray>(); var G: PermGroup? = null
            for (g in gens) {
                if (Perms.isId(g)) continue
                val cur = G
                if (cur != null && g in cur) continue
                kept.add(g); G = schreierSims(n, kept, IntArray(0))
            }
            return kept
        }

        /**
         * Group generated by [gens] when its order [target] is KNOWN (e.g. a kernel of order |K|/|K^B|, or the same group
         * in a faithful extended action). Randomised Schreier-Sims: sift random elements (product replacement) and add the
         * residues as strong generators until the order equals [target]. Exact on return: the chain's order equals the
         * true order, so the BSGS is complete. Throws if [maxRounds] random elements do not reach the target (then the
         * target was wrong).
         */
        fun ofOrder(n: Int, gens: List<IntArray>, target: java.math.BigInteger, initialBase: IntArray = IntArray(0), seed: Long = 1L,
                    maxRounds: Int = 1_000_000, dropTrivial: Boolean = false): PermGroup {
            val g0 = gens.filter { !Perms.isId(it) }
            val levels = ArrayList<ChainLevel>()
            val basePts = ArrayList<Int>(); initialBase.forEach { if (it !in basePts) basePts.add(it) }
            for (p in basePts) levels.add(ChainLevel(n, p).also { it.recomputeOrbit() })
            fun orderNow() = levels.fold(java.math.BigInteger.ONE) { a, l -> a.multiply(java.math.BigInteger.valueOf(l.orbit.size.toLong())) }
            fun addResidue(g: IntArray) {
                var h = g
                for (j in 0 until levels.size) {
                    val l = levels[j]; val beta = h[l.point]
                    if (!l.inOrbit(beta)) { val hi = Perms.inv(h); for (k in 0..j) levels[k].addGen(h, hi); return }
                    if (beta != l.point) h = Perms.mul(h, l.invRep(beta))
                }
                if (!Perms.isId(h)) { val l = ChainLevel(n, Perms.movedPoint(h)); l.recomputeOrbit(); levels.add(l); val hi = Perms.inv(h); for (k in 0 until levels.size) levels[k].addGen(h, hi) }
            }
            if (target == java.math.BigInteger.ONE || g0.isEmpty()) return PermGroup(n, if (dropTrivial) levels.filter { it.orbit.size > 1 } else { val ib = initialBase.toHashSet(); levels.filter { it.orbit.size > 1 || it.point in ib } }, g0)
            for (g in g0) addResidue(g)
            val rnd = java.util.Random(seed)
            val pool = ArrayList<IntArray>(); repeat(maxOf(10, g0.size)) { pool.add(g0[it % g0.size]) }
            var acc = Perms.id(n)
            var rounds = 0
            while (orderNow() < target) {
                if (++rounds > maxRounds) error("ofOrder: target $target not reached (order ${orderNow()}) -- wrong target?")
                val i = rnd.nextInt(pool.size); var j = rnd.nextInt(pool.size - 1); if (j >= i) j++
                pool[i] = if (rnd.nextBoolean()) Perms.mul(pool[i], pool[j]) else Perms.mul(pool[i], Perms.inv(pool[j]))
                acc = Perms.mul(acc, pool[i])
                addResidue(acc)
            }
            check(orderNow() == target) { "ofOrder overshoot: ${orderNow()} > $target" }
            return PermGroup(n, if (dropTrivial) levels.filter { it.orbit.size > 1 } else { val ib = initialBase.toHashSet(); levels.filter { it.orbit.size > 1 || it.point in ib } }, g0)
        }

        /** Group generated by [gens] on {0..n-1}; the base starts with [initialBase] (prescribed prefix). */
        fun of(n: Int, gens: List<IntArray>, initialBase: IntArray = IntArray(0)): PermGroup = schreierSims(n, gens, initialBase)

        /**
         * Deterministic Schreier-Sims. Invariant on exit: for every level i, every Schreier generator of level i sifts
         * to the identity through levels i+1.. -- so the strong generators generate each stabiliser and the order is
         * exact.
         */
        internal fun schreierSims(n: Int, gens0: List<IntArray>, initialBase: IntArray): PermGroup {
            val gens = gens0.filter { !Perms.isId(it) }.map { it.copyOf() }
            val levels = ArrayList<ChainLevel>()
            val basePts = ArrayList<Int>(); initialBase.forEach { if (it !in basePts) basePts.add(it) }
            // make sure every generator moves some base point
            for (g in gens) if (basePts.all { g[it] == it }) basePts.add(Perms.movedPoint(g))
            for (p in basePts) levels.add(ChainLevel(n, p))
            // S_i = generators fixing base points 0..i-1
            for ((i, l) in levels.withIndex()) {
                for (g in gens) if ((0 until i).all { g[levels[it].point] == levels[it].point }) { l.gens.add(g); l.invGens.add(Perms.inv(g)) }
                l.recomputeOrbit()
            }
            fun siftFrom(start: Int, g0: IntArray): Pair<IntArray, Int> {
                var g = g0
                for (j in start until levels.size) {
                    val l = levels[j]; val beta = g[l.point]
                    if (!l.inOrbit(beta)) return g to j
                    g = Perms.mul(g, l.invRep(beta))
                }
                return g to levels.size
            }
            // tested[i] = Schreier generators (orbit index of beta, generator index) of level i already shown to lie in the
            // stabiliser chain below; valid forever because orbits only grow and representatives never change
            val tested = ArrayList<HashSet<Long>>(); repeat(levels.size) { tested.add(HashSet()) }
            var i = levels.size - 1
            while (i >= 0) {
                val l = levels[i]
                var restart = false
                loop@ for ((bi, beta) in l.orbit.withIndex()) {
                    var uBeta: IntArray? = null
                    for (si in 0 until l.gens.size) {
                        val key = bi.toLong() * 1_000_003L + si
                        if (key in tested[i]) continue
                        val s = l.gens[si]; val gamma = s[beta]
                        val u = uBeta ?: l.repCached(beta).also { uBeta = it }
                        // Schreier generator u_beta * s * u_gamma^-1 (fixes the base point of level i)
                        val h = Perms.mul(Perms.mul(u, s), l.invRep(gamma))
                        val (res, j) = siftFrom(i + 1, h)
                        if (j < levels.size || !Perms.isId(res)) {
                            if (j == levels.size) { levels.add(ChainLevel(n, Perms.movedPoint(res))); tested.add(HashSet()) }
                            val ri = Perms.inv(res); for (k in i + 1..j) { levels[k].gens.add(res); levels[k].invGens.add(ri); levels[k].extendOrbit() }
                            i = j; restart = true; break@loop
                        }
                        tested[i].add(key)
                    }
                }
                if (!restart) i--
            }
            // drop trailing levels with trivial orbit (base points fixed by the whole remaining stabiliser)
            val kept = levels.filter { it.orbit.size > 1 || initialBase.contains(it.point) }
            return PermGroup(n, kept, gens)
        }
    }
}
