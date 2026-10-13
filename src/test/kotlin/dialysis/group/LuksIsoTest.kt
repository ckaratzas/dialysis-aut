package dialysis.group

import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import java.io.File
import java.math.BigInteger

/** Phase L2 (2026-10-10): Luks's string isomorphism on small known cases and on the L1 ambients (driver). */
class LuksIsoTest {
    private fun cycle(n: Int, pts: IntArray): IntArray { val g = Perms.id(n); for (i in pts.indices) g[pts[i]] = pts[(i + 1) % pts.size]; return g }

    /** Set stabiliser of a 2-subset in S_6 acting on 6 points: S_2 x S_4 = 48. */
    @Test fun setStabiliserInSymmetricGroup() {
        val n = 6; val p = PermGroup.of(n, listOf(cycle(n, intArrayOf(0, 1)), cycle(n, IntArray(n) { it })))
        val x = IntArray(n).also { it[0] = 1; it[3] = 1 }
        val (a, _) = LuksIso.stringAut(p, IntArray(n) { it }, x)
        assertEquals(BigInteger.valueOf(48), a.order)
    }

    /** Z2 wr S_4 on 8 points preserving a string that marks one point of two blocks: <swap other blocks> etc. */
    @Test fun wreathProductStringAut() {
        val k = 4; val n = 2 * k
        val swap = cycle(n, intArrayOf(0, 1)); val t = Perms.id(n).also { g -> g[0] = 2; g[1] = 3; g[2] = 0; g[3] = 1 }
        val c = IntArray(n) { (it + 2) % n }
        val p = PermGroup.of(n, listOf(swap, t, c))
        val x = IntArray(n).also { it[0] = 1; it[2] = 1 }   // marks 0 (block 0) and 2 (block 1)
        // stabiliser: blocks {0,1},{2,3} may be swapped with each other (2), blocks 2,3 arbitrary (2^2 * 2) -> 2 * 8 = 16
        val (a, _) = LuksIso.stringAut(p, IntArray(n) { it }, x)
        val brute = enumerate(p).count { g -> (0 until n).all { x[it] == x[g[it]] } }
        assertEquals(BigInteger.valueOf(brute.toLong()), a.order)
    }

    private fun enumerate(p: PermGroup): List<IntArray> {
        val seen = HashSet<List<Int>>(); val out = ArrayList<IntArray>(); val q = ArrayDeque<IntArray>()
        val id = Perms.id(p.n); seen.add(id.toList()); out.add(id); q.add(id)
        while (q.isNotEmpty()) { val g = q.removeFirst(); for (s in p.generators) { val h = Perms.mul(g, s); if (seen.add(h.toList())) { out.add(h); q.add(h) } } }
        return out
    }

    /** Driver (default: LuksIso.edgeSetStabiliser on the ports; LUKS_MODE=direct = pair action on V u Omega): for every $LUKS_AMB_DIR/<name>.amb.g (luksAmbient output: N, GENS on V, EDGES = cut edges) compute
     *  Stab_P(cut edges) by Luks on V u Omega, Omega = P-orbits of the cut-edge pairs. Prints LUKSSTAB lines. */
    @Test fun ambientStabilisers() {
        val dir = File(System.getenv("LUKS_AMB_DIR") ?: return)
        val only = System.getenv("LUKS_ONLY")?.split(",")?.toSet()
        for (f in dir.listFiles()!!.filter { it.name.endsWith(".amb.g") }.sortedBy { it.name }) {
            val name = f.name.removeSuffix(".amb.g"); if (only != null && name !in only) continue
            val txt = f.readText()
            val n = Regex("""N := (\d+)""").find(txt)!!.groupValues[1].toInt()
            val gensPart = txt.substringAfter("GENS := [").substringBefore("];;")
            val gens = Regex("""PermList\(\[([0-9,\s]*)\]\)""").findAll(gensPart).map { m -> m.groupValues[1].split(",").map { it.trim().toInt() - 1 }.toIntArray() }.toList()
            val edges = Regex("""\[(\d+),(\d+)\]""").findAll(txt.substringAfter("EDGES := [")).map { intArrayOf(it.groupValues[1].toInt() - 1, it.groupValues[2].toInt() - 1) }.toList()
            val t0 = System.currentTimeMillis()
            if (System.getenv("LUKS_MODE") != "direct") {
                val pv = PermGroup.of(n, gens)
                val (a, l) = LuksIso.edgeSetStabiliser(pv, edges) { msg -> println("  [$name ${(System.currentTimeMillis() - t0) / 1000.0}s] $msg") }
                println("LUKSSTAB $name n=$n |P|=${pv.order.toString().length}digits |Stab_P(E)| = ${a.order} calls=${l.calls} maxBranch=${l.maxBranch} (${(System.currentTimeMillis() - t0) / 1000.0}s) [ports]")
                continue
            }
            // Omega: closure of the cut-edge pairs under the generators
            fun key(a: Int, b: Int) = minOf(a, b).toLong() * n + maxOf(a, b)
            val idOf = HashMap<Long, Int>(); val pairs = ArrayList<IntArray>(); val q = ArrayDeque<IntArray>()
            for (e in edges) { val kk = key(e[0], e[1]); if (idOf.putIfAbsent(kk, pairs.size) == null) { pairs.add(e); q.add(e) } }
            while (q.isNotEmpty()) { val e = q.removeFirst(); for (g in gens) { val a = g[e[0]]; val b = g[e[1]]; val kk = key(a, b); if (idOf.putIfAbsent(kk, pairs.size) == null) { val ne = intArrayOf(a, b); pairs.add(ne); q.add(ne) } } }
            val m = pairs.size; val dn = n + m
            val ext = gens.map { g -> IntArray(dn) { i -> if (i < n) g[i] else n + idOf.getValue(key(g[pairs[i - n][0]], g[pairs[i - n][1]])) } }
            val x = IntArray(dn); for (e in edges) x[n + idOf.getValue(key(e[0], e[1]))] = 1
            // |P| from the faithful action on V (small degree), then the extended group by the exact known-order build
            val pOrder = PermGroup.of(n, gens).order
            val p = PermGroup.ofOrder(dn, ext, pOrder)
            val w = IntArray(m) { n + it }
            val (a, l) = LuksIso.stringAut(p, w, x)
            println("LUKSSTAB $name n=$n |Omega|=$m |P|=${p.order.toString().length}digits |Stab_P(E)| = ${a.order} calls=${l.calls} maxBranch=${l.maxBranch} (${(System.currentTimeMillis() - t0) / 1000.0}s)")
        }
    }
}
