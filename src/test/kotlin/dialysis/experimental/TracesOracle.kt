package dialysis.experimental

import dialysis.content.serialize
import dialysis.util.GraphIO
import org.junit.jupiter.api.Test
import java.io.File

/**
 * The oracle / baseline of paper3, kept SEPARATE from our method (2026-10-01): Traces on ONE instance per process
 * (the script scripts/xeon/run_traces.sh loops, with an outer time limit per process).
 *
 * Env TR_FILE (one DIMACS file), TR_COLOUR = none (default: uncoloured, the independent oracle) | pi (Traces gets
 * exactly our starting colouring, the PI colouring of dispatchColouring -- to show the referees what the architecture
 * contributes beyond the colouring), OUT (CSV, one row appended). PI time and Traces time are separate columns.
 */
class TracesOracle {
    @Test fun tracesOne() {
        val path = System.getenv("TR_FILE") ?: return
        val colour = System.getenv("TR_COLOUR") ?: "none"
        val out = File(System.getenv("OUT") ?: "traces.csv")
        val g = GraphIO.loadDimacs(File(path).toPath())
        val t0 = System.currentTimeMillis()
        val cells = if (colour == "pi") {
            val col = dialysis.refinement.dispatchColouring(g).colouring
            (0 until g.n).groupBy { col[it].serialize() }.toSortedMap().values.map { it.toIntArray() }
        } else listOf(IntArray(g.n) { it })
        val piMs = System.currentTimeMillis() - t0
        val t1 = System.currentTimeMillis()
        val r = dialysis.cl.TracesJni().certifyAll(g, cells, getcanon = false)
        val trMs = System.currentTimeMillis() - t1
        if (!out.exists()) out.writeText("family,instance,n,m,colour,colour_classes,colour_ms,traces_order,traces_orbits,traces_ms,outcome\n")
        val fam = File(path).parentFile?.name ?: ""
        out.appendText("$fam,${File(path).name},${g.n},${g.m},$colour,${cells.size},$piMs,${r.stats.autOrder},${r.stats.numOrbits},$trMs,OK\n")
        println("TRACES ${File(path).name} colour=$colour classes=${cells.size} colour_ms=$piMs |Aut|=${r.stats.autOrder} traces_ms=$trMs")
    }
}
