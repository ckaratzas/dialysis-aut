package dialysis.util

import dialysis.graph.Graph
import org.jgrapht.graph.DefaultEdge
import java.nio.file.Files
import java.nio.file.Path
import java.util.HashSet

object GraphIO {

    /** Reads a plain edge-list file: one "u v" per line, blank lines and # comments ignored. */
    fun loadEdgeList(path: Path): Graph {
        val edges = mutableListOf<Pair<Int, Int>>()
        var maxVertex = -1
        Files.readAllLines(path).forEach { raw ->
            val line = raw.trim()
            if (line.isBlank() || line.startsWith("#")) return@forEach
            val parts = line.split("\\s+".toRegex())
            require(parts.size >= 2) { "Expected 'u v' on line: $line" }
            val u = parts[0].toInt()
            val v = parts[1].toInt()
            edges.add(u to v)
            maxVertex = maxOf(maxVertex, u, v)
        }
        return buildFromEdges(maxVertex + 1, edges)
    }

    /** Reads a DIMACS edge file (1-indexed vertices, converted to 0-indexed). */
    fun loadDimacs(path: Path): Graph {
        var n = 0
        val edges = mutableListOf<Pair<Int, Int>>()
        Files.readAllLines(path).forEach { raw ->
            val parts = raw.trim().split("\\s+".toRegex())
            when (parts.firstOrNull()) {
                "p" -> n = parts[2].toInt()
                "e" -> edges.add(parts[1].toInt() - 1 to parts[2].toInt() - 1)
            }
        }
        return buildFromEdges(n, edges)
    }

    /** Reads a graph6 (.g6) file: a single graph6-encoded line (header N + bit-packed upper
     *  triangle of the adjacency matrix, 6 bits per character, offset by 63). Supports the
     *  standard 1-byte (N<=62) and extended 3-byte (N<=262143) header forms. */
    fun loadGraph6(path: Path): Graph {
        val line = Files.readAllLines(path).first { it.isNotBlank() }.trim()
        val vals = IntArray(line.length) { line[it].code - 63 }

        var pos = 0
        val n: Int
        if (vals[0] == 63) {
            n = (vals[1] shl 12) or (vals[2] shl 6) or vals[3]
            pos = 4
        } else {
            n = vals[0]
            pos = 1
        }

        fun bitAt(bitIndex: Int): Int {
            val byteIdx = pos + bitIndex / 6
            val bitInByte = bitIndex % 6
            return (vals[byteIdx] shr (5 - bitInByte)) and 1
        }

        val edges = mutableListOf<Pair<Int, Int>>()
        var bitIndex = 0
        for (j in 1 until n) for (i in 0 until j) {
            if (bitAt(bitIndex) == 1) edges.add(i to j)
            bitIndex++
        }
        return buildFromEdges(n, edges)
    }

    /** Writes edges sorted canonically (smaller endpoint first), one per line. */
    fun save(graph: Graph, path: Path) {
        val lines = mutableListOf<String>()
        for (u in 0 until graph.n) for (v in graph.adj[u]) if (u <= v) lines.add("$u $v")
        Files.writeString(path, lines.sorted().joinToString("\n", postfix = "\n"))
    }

    private fun buildFromEdges(n: Int, edges: List<Pair<Int, Int>>): Graph {
        val bucket = Array(n) { mutableListOf<Int>() }
        for ((u, v) in edges) {
            bucket[u].add(v); bucket[v].add(u)
        }
        val adj = Array(n) { bucket[it].distinct().sorted().toIntArray() }
        return Graph(n, adj, Array(n) { it.toString() })
    }
}