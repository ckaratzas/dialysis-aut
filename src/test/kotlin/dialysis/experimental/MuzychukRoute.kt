package dialysis.experimental

import dialysis.graph.Graph
import dialysis.group.PermGroup
import dialysis.util.GraphIO
import org.junit.jupiter.api.Test
import java.io.File
import java.math.BigInteger

/**
 * Affine-fibre route (paper 4, Theorem M; 2026-10-24): Aut(G) of a Muzychuk-CFI graph G(sigma), detected from the graph
 * alone and solved by linear algebra over Z_q. Prototype: scripts/closure_bound/muz_route.py.
 *
 * G(sigma) (m >= 4 fibres, q >= 2): fibre F_i = sum-zero vectors of Z_q^{[m] \ {i}}; (x,i) ~ (y,j) iff sigma_ij(x_j) = y_i,
 * sigma_ji = sigma_ij^-1, no edges inside a fibre. The route
 *  1. finds the fibres: the pairs with the most common neighbours are same-fibre pairs differing in two coordinates
 *     (Lemma M1, needs m >= 5, or m = 4 and q >= 3); the fibres are the components of that pair graph;
 *  2. finds the coordinates: the traces N(w) ∩ F_i, w in F_j, are the q classes of coordinate j of F_i;
 *  3. labels the classes by Z_q so that F_i becomes the set of sum-zero vectors (origin x0, addition read off the Latin
 *     square of three coordinates, a generator of Z_q); by Lemma M2 any such labelling differs from the true one by an
 *     affine map with a common unit, which step 5 enumerates;
 *  4. reads sigma^ off the edges and CHECKS that every edge obeys it and that there are exactly C(m,2) q^{2m-5} edges,
 *     so G is exactly G(sigma^) and Theorem M applies; any failed check returns "not applicable", never a group;
 *  5. enumerates rho in S_m and units u per fibre (backtracking, pruned by pairwise feasibility); for each the edge
 *     conditions give pairs (c_ij, c_ji) and every fibre needs sum_j c_ij = 0; a DP over the edges counts the solutions
 *     and gives one; |Aut| is the total count (exact by Lemmas M1, M2);
 *  6. generators: one automorphism per (rho, u) with solutions, plus generators of the translation group T (rho = id,
 *     u = 1; random solutions until their group has the DP count); every generator is verified on G and the group is
 *     built by Schreier-Sims with |Aut| as target (an overshoot would be an error).
 * The route is family-specific (it recognises one structure); it is exact when it answers.
 */
object MuzychukRoute {
    class NotApplicable(msg: String) : Exception(msg)

    private class Structure(val m: Int, val q: Int, val fibres: List<IntArray>, val fibreOf: IntArray,
                            val cls: Array<Array<IntArray?>>, val lab: Array<Array<IntArray?>>, val sig: Array<Array<IntArray?>>)

    /** Aut(G) with verified generators, or null and the reason. */
    fun autOf(g: Graph, deadlineMs: Long = Long.MAX_VALUE, log: (String) -> Unit = {}): Pair<PermGroup?, String> {
        val t0 = System.currentTimeMillis()
        val st = try { structure(g) } catch (e: NotApplicable) { return null to "not applicable: ${e.message}" }
        log("structure: m=${st.m} q=${st.q} n=${g.n} (${System.currentTimeMillis() - t0} ms)")
        val deadline = if (deadlineMs >= Long.MAX_VALUE - t0) Long.MAX_VALUE else t0 + deadlineMs
        val (total, gens) = solve(g, st, deadline) ?: return null to "deadline"
        for (h in gens) check((0 until g.n).all { u -> g.adj[u].all { x -> java.util.Arrays.binarySearch(g.adj[h[u]], h[x]) >= 0 } }) {
            "muzychuk route: a generator is not an automorphism" }
        val grp = PermGroup.ofOrder(g.n, gens, total)
        return grp to "muzychuk route: m=${st.m} q=${st.q}, |Aut| = $total, ${gens.size} generators, ${System.currentTimeMillis() - t0} ms"
    }

    // ---------------------------------------------------------------------------------------------------------------
    private fun structure(g: Graph): Structure {
        val n = g.n; val words = (n + 63) / 64
        val bits = Array(n) { LongArray(words) }
        for (v in 0 until n) for (w in g.adj[v]) bits[v][w ushr 6] = bits[v][w ushr 6] or (1L shl (w and 63))
        // pairs with the largest number of common neighbours (two passes: the maximum, then its pairs)
        fun common(u: Int, v: Int): Int { val bu = bits[u]; val bv = bits[v]; var c = 0
            for (k in 0 until words) c += java.lang.Long.bitCount(bu[k] and bv[k]); return c }
        var cmax = -1
        for (u in 0 until n) for (v in u + 1 until n) { val c = common(u, v); if (c > cmax) cmax = c }
        val nb = Array(n) { ArrayList<Int>() }
        for (u in 0 until n) for (v in u + 1 until n) if (common(u, v) == cmax) { nb[u].add(v); nb[v].add(u) }
        val fibreOf = IntArray(n) { -1 }; val fibres = ArrayList<IntArray>()
        for (s in 0 until n) { if (fibreOf[s] >= 0) continue
            val comp = arrayListOf(s); fibreOf[s] = fibres.size; var k = 0
            while (k < comp.size) { val u = comp[k++]; for (w in nb[u]) if (fibreOf[w] < 0) { fibreOf[w] = fibres.size; comp.add(w) } }
            fibres.add(comp.sorted().toIntArray()) }
        val m = fibres.size
        if (m < 4) throw NotApplicable("$m fibres")
        val sz = fibres[0].size
        if (fibres.any { it.size != sz }) throw NotApplicable("fibres of unequal size")
        for (v in 0 until n) if (g.adj[v].any { fibreOf[it] == fibreOf[v] }) throw NotApplicable("edge inside a fibre")
        var q = 2; while (pow(q, m - 2) < sz) q++
        if (pow(q, m - 2) != sz) throw NotApplicable("fibre size $sz is not q^(m-2), m=$m")
        if ((m - 3) * q <= m - 2) throw NotApplicable("Lemma M1 needs m >= 5 or m = 4, q >= 3 (m=$m, q=$q)")
        // coordinates: cls[i][j][v] = class (0..q-1) of coordinate j of v in F_i, -1 outside F_i
        val cls = Array(m) { arrayOfNulls<IntArray>(m) }
        val members = Array(m) { arrayOfNulls<List<IntArray>>(m) }
        for (i in 0 until m) for (j in 0 until m) { if (i == j) continue
            val traces = LinkedHashMap<String, IntArray>()
            for (w in fibres[j]) { val t = g.adj[w].filter { fibreOf[it] == i }.sorted().toIntArray(); traces.putIfAbsent(t.joinToString(","), t) }
            val ts = traces.values.toList()
            if (ts.size != q || ts.sumOf { it.size } != sz) throw NotApplicable("traces of F$j on F$i are not a partition into q classes")
            val c = IntArray(n) { -1 }; for ((k, t) in ts.withIndex()) for (x in t) c[x] = k
            if (fibres[i].any { c[it] < 0 }) throw NotApplicable("traces do not cover F$i")
            cls[i][j] = c; members[i][j] = ts }
        val lab = labels(m, q, fibres, cls)
        // sigma^ and the full edge check
        val sig = Array(m) { arrayOfNulls<IntArray>(m) }
        for (i in 0 until m) for (j in 0 until m) { if (i == j) continue
            val s = IntArray(q) { -1 }
            for ((k, t) in members[i][j]!!.withIndex()) {
                val a = lab[i][j]!![k]; val x = t[0]
                val bs = g.adj[x].filter { fibreOf[it] == j }.map { lab[j][i]!![cls[j][i]!![it]] }.toSet()
                if (bs.size != 1) throw NotApplicable("neighbours of a class are not one class")
                s[a] = bs.first() }
            if (s.sorted() != (0 until q).toList()) throw NotApplicable("sigma is not a bijection")
            sig[i][j] = s }
        var edges = 0L
        for (a in 0 until n) for (b in g.adj[a]) { if (a > b) continue; edges++
            val i = fibreOf[a]; val j = fibreOf[b]
            if (sig[i][j]!![lab[i][j]!![cls[i][j]!![a]]] != lab[j][i]!![cls[j][i]!![b]]) throw NotApplicable("an edge breaks the sigma rule") }
        val expected = m.toLong() * (m - 1) / 2 * pow(q, m - 2) * pow(q, m - 3)
        if (edges != expected) throw NotApplicable("edge count $edges != $expected")
        return Structure(m, q, fibres, fibreOf, cls, Array(m) { i -> Array(m) { j -> lab[i][j]?.let { l -> IntArray(n) { v -> if (cls[i][j]!![v] < 0) -1 else l[cls[i][j]!![v]] } } } }, sig)
    }

    /** lab[i][j][class] in Z_q such that every vertex of F_i has label sum 0. */
    private fun labels(m: Int, q: Int, fibres: List<IntArray>, cls: Array<Array<IntArray?>>): Array<Array<IntArray?>> {
        val lab = Array(m) { arrayOfNulls<IntArray>(m) }
        for (i in 0 until m) {
            val others = (0 until m).filter { it != i }
            fun key(x: Int) = others.map { cls[i][it]!![x] }
            val index = HashMap<List<Int>, Int>(); for (x in fibres[i]) index[key(x)] = x
            if (index.size != fibres[i].size) throw NotApplicable("coordinates do not determine the vertex")
            val k0 = key(fibres[i][0])
            fun exists(changes: Map<Int, Int>): Boolean { val kk = k0.toMutableList(); for ((p, c) in changes) kk[p] = c; return kk in index }
            val f = IntArray(q) { -1 }; val gg = IntArray(q) { -1 }
            for (a in 0 until q) for (b in 0 until q) {
                if (exists(mapOf(0 to a, 1 to b))) f[a] = b
                if (exists(mapOf(0 to a, 2 to b))) gg[a] = b }
            if (f.any { it < 0 } || gg.any { it < 0 }) throw NotApplicable("Latin structure missing")
            val h = Array(q) { IntArray(q) { -1 } }
            for (b in 0 until q) for (c in 0 until q) for (a in 0 until q) if (exists(mapOf(0 to a, 1 to b, 2 to c))) h[b][c] = a
            fun add(a1: Int, a2: Int) = h[f[a1]][gg[a2]].also { if (it < 0) throw NotApplicable("Latin structure incomplete") }
            val zero = k0[0]
            var gen = -1
            for (cand in 0 until q) { var s = cand; var k = 1; while (s != zero && k <= q) { s = add(s, cand); k++ }; if (k == q && s == zero) { gen = cand; break } }
            if (gen < 0) throw NotApplicable("coordinate group is not cyclic of order q")
            val l1 = IntArray(q) { -1 }; l1[zero] = 0; var s = gen
            for (t in 1 until q) { l1[s] = t; s = add(s, gen) }
            if (l1.any { it < 0 }) throw NotApplicable("labelling failed")
            lab[i][others[0]] = l1
            lab[i][others[1]] = IntArray(q).also { l -> for (a in 0 until q) l[f[a]] = (q - l1[a]) % q }
            for ((pos, j) in others.withIndex()) { if (pos < 2) continue
                val lj = IntArray(q) { -1 }
                for (a in 0 until q) for (c in 0 until q) if (exists(mapOf(0 to a, pos to c))) lj[c] = (q - l1[a]) % q
                if (lj.any { it < 0 }) throw NotApplicable("labelling of a coordinate failed")
                lab[i][j] = lj }
            for (x in fibres[i]) if (others.sumOf { lab[i][it]!![cls[i][it]!![x]] } % q != 0) throw NotApplicable("labelled fibre is not the sum-zero set")
        }
        return lab
    }

    // ---------------------------------------------------------------------------------------------------------------
    /** Total |Aut| and verified-to-be-checked generators, or null on the deadline. */
    private fun solve(g: Graph, st: Structure, deadline: Long): Pair<BigInteger, List<IntArray>>? {
        val m = st.m; val q = st.q
        val units = (1 until q).filter { gcd(it, q) == 1 }
        val edges = ArrayList<IntArray>(); for (i in 0 until m) for (j in i + 1 until m) edges.add(intArrayOf(i, j))
        // allowed[i][j][ti][tj][ui] : map uj -> list of (cij, cji)
        val allowed = HashMap<Long, Map<Int, List<IntArray>>>()
        fun key(i: Int, j: Int, ti: Int, tj: Int, ui: Int) = ((((i.toLong() * m + j) * m + ti) * m + tj) * q + ui)
        for (e in edges) { val i = e[0]; val j = e[1]; val sinv = st.sig[j][i]!!
            for (ti in 0 until m) for (tj in 0 until m) { if (ti == tj) continue; val s2 = st.sig[ti][tj]!!
                for (ui in units) { val d = HashMap<Int, MutableList<IntArray>>()
                    for (cij in 0 until q) {
                        val pji = IntArray(q) { y -> s2[(ui * sinv[y] + cij) % q] }
                        val c = pji[0]; val u = ((pji[1] - c) % q + q) % q
                        if (u in units && (0 until q).all { t -> pji[t] == (u * t + c) % q }) d.getOrPut(u) { ArrayList() }.add(intArrayOf(cij, c)) }
                    allowed[key(i, j, ti, tj, ui)] = d } } }
        val zeroState = 0L   // fibre partial sums encoded base q
        fun addTo(state: Long, i: Int, v: Int): Long { var p = 1L; repeat(i) { p *= q }; val digit = ((state / p) % q).toInt(); return state + (((digit + v) % q) - digit) * p }
        class Sol(val rho: IntArray, val u: IntArray, val count: BigInteger, val c: Array<IntArray>)
        val sols = ArrayList<Sol>()
        fun countAndOne(rho: IntArray, u: IntArray): Pair<BigInteger, Array<IntArray>?> {
            var cnt = HashMap<Long, BigInteger>(); cnt[zeroState] = BigInteger.ONE
            var wit = HashMap<Long, List<IntArray>>(); wit[zeroState] = emptyList()
            for (e in edges) { val i = e[0]; val j = e[1]
                val opts = allowed[key(i, j, rho[i], rho[j], u[i])]?.get(u[j]) ?: return BigInteger.ZERO to null
                val nc = HashMap<Long, BigInteger>(); val nw = HashMap<Long, List<IntArray>>()
                for ((s, c0) in cnt) for (o in opts) { val s2 = addTo(addTo(s, i, o[0]), j, o[1])
                    nc[s2] = (nc[s2] ?: BigInteger.ZERO).add(c0)
                    if (s2 !in nw) nw[s2] = wit.getValue(s) + intArrayOf(i, j, o[0], o[1]) }
                cnt = nc; wit = nw }
            val c = cnt[zeroState] ?: BigInteger.ZERO
            if (c.signum() == 0) return c to null
            val cm = Array(m) { IntArray(m) }; for (w in wit.getValue(zeroState)) { cm[w[0]][w[1]] = w[2]; cm[w[1]][w[0]] = w[3] }
            return c to cm }
        val rho = IntArray(m) { -1 }; val uu = IntArray(m) { -1 }; val used = BooleanArray(m)
        var timedOut = false
        fun extend(i: Int) {
            if (timedOut) return
            if (System.currentTimeMillis() > deadline) { timedOut = true; return }
            if (i == m) { val (c, w) = countAndOne(rho, uu); if (w != null) sols.add(Sol(rho.copyOf(), uu.copyOf(), c, w)); return }
            for (t in 0 until m) { if (used[t]) continue
                for (ui in units) { rho[i] = t; uu[i] = ui
                    if ((0 until i).all { k -> allowed[key(k, i, rho[k], t, uu[k])]?.get(ui)?.isNotEmpty() == true }) {
                        used[t] = true; extend(i + 1); used[t] = false } } }
            rho[i] = -1; uu[i] = -1 }
        extend(0)
        if (timedOut) return null
        val total = sols.fold(BigInteger.ZERO) { a, s -> a.add(s.count) }
        val gens = ArrayList<IntArray>()
        for (s in sols) gens.add(perm(g, st, s.rho, s.u, s.c))
        // translation group T at rho = id, u = 1: random solutions until their group reaches the DP count
        val id = IntArray(m) { it }; val one = IntArray(m) { 1 }
        val tCount = sols.firstOrNull { it.rho.contentEquals(id) && it.u.contentEquals(one) }?.count ?: BigInteger.ONE
        if (tCount > BigInteger.ONE) {
            val opts = edges.map { e -> allowed[key(e[0], e[1], e[0], e[1], 1)]?.get(1) ?: emptyList() }
            val rnd = java.util.Random(1); val tg = ArrayList<IntArray>(); var tries = 0
            while ((tg.isEmpty() || PermGroup.of(g.n, tg).order < tCount) && tries++ < 400) {
                if (System.currentTimeMillis() > deadline) return null
                val cm = Array(m) { IntArray(m) }; val sums = IntArray(m)
                fun rb(k: Int): Boolean {
                    if (k == edges.size) return sums.all { it == 0 }
                    val i = edges[k][0]; val j = edges[k][1]
                    for (o in opts[k].shuffled(rnd)) { sums[i] = (sums[i] + o[0]) % q; sums[j] = (sums[j] + o[1]) % q
                        cm[i][j] = o[0]; cm[j][i] = o[1]
                        if (rb(k + 1)) return true
                        sums[i] = (sums[i] - o[0] + q) % q; sums[j] = (sums[j] - o[1] + q) % q }
                    return false }
                if (!rb(0)) break
                val p = perm(g, st, id, one, cm); tg.add(p); gens.add(p) }
            check(PermGroup.of(g.n, tg).order == tCount) { "muzychuk route: translation group not generated" }
        }
        return total to gens
    }

    /** (x,i) -> ((u_i x_j + c_ij)_{rho j}, rho i), as a vertex permutation. */
    private fun perm(g: Graph, st: Structure, rho: IntArray, u: IntArray, c: Array<IntArray>): IntArray {
        val m = st.m; val q = st.q
        val index = HashMap<Long, Int>()
        fun code(i: Int, vals: IntArray): Long { var x = i.toLong(); for (v in vals) x = x * q + v; return x }
        for (i in 0 until m) { val others = (0 until m).filter { it != i }
            for (x in st.fibres[i]) index[code(i, IntArray(others.size) { st.lab[i][others[it]]!![x] })] = x }
        val p = IntArray(g.n)
        for (i in 0 until m) { val others = (0 until m).filter { it != i }; val ti = rho[i]; val tOthers = (0 until m).filter { it != ti }
            for (x in st.fibres[i]) { val y = IntArray(m)
                for (j in others) y[rho[j]] = (u[i] * st.lab[i][j]!![x] + c[i][j]) % q
                p[x] = index.getValue(code(ti, IntArray(tOthers.size) { y[tOthers[it]] })) } }
        return p
    }

    private fun pow(a: Int, e: Int): Int { var r = 1; repeat(e) { r *= a }; return r }
    private fun gcd(a: Int, b: Int): Int = if (b == 0) a else gcd(b, a % b)
}

/** Driver: MuzychukRoute on every file of INSTANCES_FILE (MUZ_DEADLINE_S, default 1800; MUZ_TRACES=1 adds the Traces oracle). */
class MuzychukRouteTest {
    @Test fun muzFullAut() {
        val files = System.getenv("INSTANCES_FILE")?.let { f -> File(f).readLines().filter { it.isNotBlank() } } ?: return
        val deadline = (System.getenv("MUZ_DEADLINE_S")?.toLongOrNull() ?: 1800) * 1000
        for (path in files) {
            val g = GraphIO.loadDimacs(File(path).toPath()); val name = File(path).name
            val (aut, detail) = try { MuzychukRoute.autOf(g, deadline) { println("MUZ $name $it") } }
                catch (e: Exception) { null to "exception: ${e.javaClass.simpleName} ${e.message}" }
            val tr = if (System.getenv("MUZ_TRACES") == "1") " | Traces ${"%.6g".format(dialysis.cl.TracesJni().stats(g, listOf(IntArray(g.n) { it })).autOrder)}" else ""
            println("MUZ $name ${if (aut == null) "FAILED: $detail" else "|Aut(G)| = ${aut.order} (generators verified) | $detail"}$tr")
        }
    }
}
