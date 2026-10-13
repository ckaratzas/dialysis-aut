package dialysis.group

import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import java.io.File
import java.math.BigInteger

/** Phase L0 (2026-10-10): exact orders and structure of known groups; GAP cross-check driver [gapDumpOrders]. */
class PermGroupTest {
    private fun cycle(n: Int, pts: IntArray): IntArray { val g = Perms.id(n); for (i in pts.indices) g[pts[i]] = pts[(i + 1) % pts.size]; return g }
    private fun fact(k: Int): BigInteger = (1..k).fold(BigInteger.ONE) { a, i -> a.multiply(BigInteger.valueOf(i.toLong())) }

    private fun sym(n: Int) = listOf(cycle(n, intArrayOf(0, 1)), cycle(n, IntArray(n) { it }))
    private fun alt(n: Int) = (2 until n).map { k -> cycle(n, intArrayOf(0, 1, k)) }

    @Test fun symmetricAndAlternating() {
        for (n in 2..12) assertEquals(fact(n), PermGroup.of(n, sym(n)).order, "S_$n")
        for (n in 3..12) assertEquals(fact(n).divide(BigInteger.TWO), PermGroup.of(n, alt(n)).order, "A_$n")
    }

    @Test fun wreathProductZ2WrSk() {
        for (k in 2..8) {
            val n = 2 * k
            // blocks {2i, 2i+1}; swap inside block 0; permute blocks by S_k
            val swap = cycle(n, intArrayOf(0, 1))
            val t = Perms.id(n).also { g -> g[0] = 2; g[1] = 3; g[2] = 0; g[3] = 1 }
            val c = IntArray(n) { (it + 2) % n }
            val G = PermGroup.of(n, listOf(swap, t, c))
            assertEquals(BigInteger.TWO.pow(k).multiply(fact(k)), G.order, "Z2 wr S_$k")
            val orb = IntArray(n) { it }
            assertTrue(G.isTransitive(orb)); assertFalse(G.isPrimitive(orb))
            val blocks = G.minimalBlockSystem(orb)!!
            assertEquals(k, blocks.values.toSet().size, "k blocks of size 2")
            assertEquals(fact(k), PermGroup.of(k, G.actionOnBlocks(blocks)).order, "action on blocks = S_k")
        }
    }

    @Test fun intransitiveProductAndStabilisers() {
        val n = 7   // S3 on {0,1,2} x S4 on {3,4,5,6}
        val gens = listOf(cycle(n, intArrayOf(0, 1)), cycle(n, intArrayOf(0, 1, 2)), cycle(n, intArrayOf(3, 4)), cycle(n, intArrayOf(3, 4, 5, 6)))
        val G = PermGroup.of(n, gens)
        assertEquals(BigInteger.valueOf(144), G.order)
        assertEquals(2, G.orbits().toSet().size)
        assertEquals(BigInteger.valueOf(12), G.pointwiseStabiliser(intArrayOf(0, 3)).order)
        assertEquals(BigInteger.valueOf(1), G.pointwiseStabiliser(intArrayOf(0, 1, 3, 4, 5)).order)
    }

    @Test fun affineGroupAndMembership() {
        for (p in listOf(5, 7, 11, 13, 31)) {
            val prim = (2 until p).first { a -> (1 until p - 1).all { e -> powMod(a, e, p) != 1 } }
            val mulA = IntArray(p) { (it * prim) % p }; val add = IntArray(p) { (it + 1) % p }
            val G = PermGroup.of(p, listOf(mulA, add))
            assertEquals(BigInteger.valueOf((p * (p - 1)).toLong()), G.order, "AGL(1,$p)")
            assertTrue(G.isPrimitive(IntArray(p) { it }))
            assertTrue(IntArray(p) { (3 * it + 2) % p } in G)
            assertFalse(cycle(p, intArrayOf(0, 1)) in G, "a transposition is not affine for p > 3")
            assertEquals(BigInteger.valueOf((p - 1).toLong()), G.pointwiseStabiliser(intArrayOf(0)).order)
        }
    }

    private fun powMod(a: Int, e: Int, m: Int): Int { var r = 1L; var b = a.toLong(); var k = e; while (k > 0) { if (k and 1 == 1) r = r * b % m; b = b * b % m; k = k shr 1 }; return r.toInt() }

    /** GAP cross-check driver: for every TC_INST dump (*.g, tcCompositionDump format) in $PG_DUMP_DIR, print
     *  "PGORDER <file> <class index> <size> <order>" for every class with generators. Compare with GAP's Size. */
    @Test fun gapDumpOrders() {
        val dir = File(System.getenv("PG_DUMP_DIR") ?: return)
        val out = File(System.getenv("PG_OUT") ?: return)
        out.writeText("")
        for (f in dir.walkTopDown().filter { it.isFile && it.name.endsWith(".g") }.sortedBy { it.path }) {
            val txt = f.readText()
            // one record per class: split at "rec(size := ", then every PermList inside the record's gens list
            val recs = txt.split("rec(size := ").drop(1)
            for ((ci, r) in recs.withIndex()) {
                val size = r.substringBefore(",").trim().toInt()
                val gensPart = r.substringAfter("gens := [", "")
                val gens = Regex("""PermList\(\[([0-9,\s]*)\]\)""").findAll(gensPart).map { p -> p.groupValues[1].split(",").map { it.trim().toInt() - 1 }.toIntArray() }.toList()
                if (gens.isEmpty()) continue
                val t0 = System.nanoTime(); val G = PermGroup.of(size, gens); val ms = (System.nanoTime() - t0) / 1e6
                out.appendText("PGORDER ${f.relativeTo(dir).path} $ci $size ${G.order} ${"%.1f".format(ms)}ms\n")
            }
        }
    }
}
