package dialysis.experimental

import dialysis.graph.Graph
import dialysis.util.GraphIO
import org.junit.jupiter.api.Test
import java.io.File

/**
 * Diagnostic (2026-10-17, 2-CLASS_SPEC option (c), "stronger pair invariants"). On c2stress-rnd-p2-d4-e3-s2 the chain's
 * level-1 refutations that go deep are the diagonal cells (k,k) of the Latin square; 1-WL with r0 and s individualised
 * does not separate them from r1 = (1,1) until tuple depth 4-5. Candidate invariant: a one-step LOOKAHEAD on a canonical
 * cell C of the partition P(r0, s): the multiset over t in C of the refined colouring of (r0, s, t). Aut-invariant (C is
 * chosen by its canonical colour name), so a mismatch with (r0, r1) refutes s. Reports, per candidate, which cells (by
 * size, smallest first) separate it from r1 and what that costs (refinements).
 *
 * Env PI_FILE (DIMACS), PI_R0, PI_R1, PI_CANDS (comma list), PI_MAXCELL (largest cell tried, default 4096).
 * Same numeric refinement as PieceProfileTest's SC_FASTNODE (uniform start, marks by position).
 */
class PairInvariantDiag {
    private fun mix64(x: Long): Long { var z = x + -0x61c8864680b583ebL; z = (z xor (z ushr 30)) * -0x40a7b892e31b1a47L; z = (z xor (z ushr 27)) * -0x6b2fb644ecceee15L; return z xor (z ushr 31) }
    private fun h64(s: String): Long { var h = -0x3c5a2d1e7b9f4c11L; for (ch in s) { h = (h xor ch.code.toLong()) * 0x100000001b3L; h = h xor (h ushr 29) }; return h }
    private fun distinct(c: LongArray): Int { val a = c.copyOf(); a.sort(); var k = if (a.isEmpty()) 0 else 1; for (i in 1 until a.size) if (a[i] != a[i - 1]) k++; return k }
    private fun refine(g: Graph, c0: LongArray): LongArray {
        var c = c0; var k = distinct(c)
        while (true) {
            val nx = LongArray(g.n) { v -> var s = 0L; for (u in g.adj[v]) s += mix64(c[u]); mix64(c[v] * -0x61c8864680b583ebL xor s) }
            val k2 = distinct(nx); c = nx; if (k2 == k) return c; k = k2
        }
    }
    private fun mark(g: Graph, c: LongArray, v: Int, pos: Int): LongArray { val c0 = c.copyOf(); c0[v] = h64("node-mark$pos"); return refine(g, c0) }
    private fun msHash(c: LongArray): Long { val a = c.copyOf(); a.sort(); var h = 0x2545F4914F6CDD1DL; for (x in a) h = h * 1000003L xor x; return h }

    @Test fun pairLookahead() {
        val path = System.getenv("PI_FILE") ?: return
        val g = GraphIO.loadDimacs(File(path).toPath())
        val r0 = System.getenv("PI_R0")!!.toInt(); val r1 = System.getenv("PI_R1")!!.toInt()
        val cands = System.getenv("PI_CANDS")!!.split(",").map { it.trim().toInt() }
        val maxCell = (System.getenv("PI_MAXCELL") ?: "4096").toInt()
        val c0 = refine(g, LongArray(g.n) { 1L })
        val cr0 = mark(g, c0, r0, 0)
        /** cell colour -> (size, lookahead multiset hash) for the pair (r0, s); only cells of size <= maxCell */
        fun profile(s: Int): Pair<Long, Map<Long, Pair<Int, Long>>> {
            val p = mark(g, cr0, s, 1)
            val cells = p.indices.groupBy { p[it] }
            val out = HashMap<Long, Pair<Int, Long>>()
            for ((col, mem) in cells) {
                if (mem.size < 2 || mem.size > maxCell) continue
                val hs = LongArray(mem.size) { i -> msHash(mark(g, p, mem[i], 2)) }; hs.sort()
                var h = 0x9E3779B97F4A7C15uL.toLong(); for (x in hs) h = h * 1000003L xor x
                out[col] = mem.size to h
            }
            return msHash(p) to out
        }
        val t0 = System.currentTimeMillis()
        val (base, ref) = profile(r1)
        println("PAIRINV r1=$r1: node invariant ${base}; cells tried (size <= $maxCell): ${ref.values.map { it.first }.sorted()} (${(System.currentTimeMillis() - t0) / 1000.0}s)")
        for (s in cands) {
            val t1 = System.currentTimeMillis()
            val (b, pr) = profile(s)
            if (b != base) { println("PAIRINV s=$s: separated by the NODE invariant (no lookahead needed)"); continue }
            val sep = ref.filter { (col, v) -> pr[col] != v }.values.map { it.first }.sorted()
            println("PAIRINV s=$s: separating cells by size ${sep.ifEmpty { listOf("NONE") }}; cheapest = ${sep.firstOrNull() ?: "-"} refinements (${(System.currentTimeMillis() - t1) / 1000.0}s)")
        }
    }
}
