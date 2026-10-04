package dialysis.refinement

import dialysis.content.Content
import dialysis.graph.Graph

/** The starting colouring handed to the solver and the chain; [colouring] is indexed by the vertices of the graph. */
class ColouringDispatch(val colouring: Array<Content>)

/**
 * The structural colouring PI of [g]: [initialPhase] (dialysis from every root, canonical AHU forms, refined), computed
 * on [g] itself for every graph, bipartite or not. It is Aut(g)-invariant, so it can start the algebraic solver and the
 * stabiliser chain.
 */
fun dispatchColouring(g: Graph): ColouringDispatch = ColouringDispatch(initialPhase(g, uniformSeed(g.n)).color)
