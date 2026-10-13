#!/usr/bin/env python3
"""Deeper stars (CLOSURE_BOUND_SPEC Lemma G, 2026-10-12, diagnostic): for a class C at level k of the greedy root path,
S_r(C) = Aut(G[ball_r(C)], level colouring) acting on C -- a valid ambient group (every colour-preserving automorphism of G
maps ball_r(C) onto itself) that shrinks to the true action as r grows. Writes a GAP file printing per r: ball size,
log10 |S_r(C)| on C, transitivity, and the action on the block system of C with d blocks (giant? natural Alt/Sym),
plus the true group's orbits on C. Usage: deep_star.py GRAPH LEVEL CLASS_ID D RADII(e.g. 1,2) OUT.g"""
import sys, os
sys.path.insert(0, os.path.dirname(__file__)); os.environ.setdefault('GREEDY', '8')
import split_classify as sc
f, lv, cid, d, radii, out = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), [int(x) for x in sys.argv[5].split(',')], sys.argv[6]
nb = sc.load(f); sc.TRACE = []; sc.ROOTS = []; sc.path(nb, cap=200); col = sc.TRACE[lv]; roots = sc.ROOTS[:lv]
C = [v for v in range(len(nb)) if col[v] == cid]
def ball(r):
    seen = set(C); fr = list(C)
    for _ in range(r):
        nx = [w for v in fr for w in nb[v] if w not in seen]; seen.update(nx); fr = list(dict.fromkeys(nx))
    return sorted(seen)
with open(out, 'w') as g:
    g.write('LoadPackage("grape");;\n')
    g.write('rep := function(r, N, edges, cells, pts, d) local A, B, sys, orb, Q;\n'
            '  A := AutGroupGraph(EdgeOrbitsGraph(Group(()), edges, N), cells);; B := Action(A, pts);;\n'
            '  Print("r=", r, " ball=", N, " log10|S_r| = ", LogInt(Size(B), 10), " transitive ", IsTransitive(B, [1..Length(pts)]));\n'
            '  if not IsTransitive(B, [1..Length(pts)]) then Print(" | orbits ", Collected(List(Orbits(B, [1..Length(pts)]), Length)), " giant on an orbit (deg >= 5, order >= deg!/2): ", List(Filtered(Orbits(B, [1..Length(pts)]), o -> Length(o) >= 5), o -> Size(Action(B, o)) * 2 >= Factorial(Length(o))), "\\n"); return; fi;\n'
            '  if Length(pts) = d then Q := B; else\n'
            '    sys := Filtered(AllBlocks(B), b -> Length(b) * d = Length(pts));;\n'
            '    if sys = [] then Print(" no block system with ", d, " blocks\\n"); return; fi;\n'
            '    orb := Orbit(B, Set(sys[1]), OnSets);; Q := Action(B, orb, OnSets);; fi;\n'
            '  Print(" | on ", d, " blocks: log10 order ", LogInt(Size(Q), 10), " natAlt ", IsNaturalAlternatingGroup(Q), " natSym ", IsNaturalSymmetricGroup(Q), "\\n"); end;;\n')
    for r in radii:
        B = ball(r); idx = {v: i + 1 for i, v in enumerate(B)}
        e = ",".join(f"[{idx[v]},{idx[w]}],[{idx[w]},{idx[v]}]" for v in B for w in nb[v] if w in idx and v < w)
        cells = {}
        for v in B: cells.setdefault(col[v], []).append(idx[v])
        cl = ",".join("[" + ",".join(map(str, c)) + "]" for c in cells.values())
        g.write(f'rep({r}, {len(B)}, [{e}], [{cl}], [{",".join(str(idx[v]) for v in C)}], {d});\n')
    n = len(nb); e = ",".join(f"[{v+1},{w+1}],[{w+1},{v+1}]" for v in range(n) for w in nb[v] if v < w)
    cells = {}
    for v in range(n): cells.setdefault(col[v], []).append(v + 1)
    cl = ",".join("[" + ",".join(map(str, c)) + "]" for c in cells.values())
    g.write(f'T := Action(AutGroupGraph(EdgeOrbitsGraph(Group(()), [{e}], {n}), [{cl}]), [{",".join(str(v+1) for v in C)}]);;\n')
    g.write(f'Print("TRUE log10 = ", LogInt(Size(T), 10), " orbits on C: ", Collected(List(Orbits(T, [1..{len(C)}]), Length)), "\\n");\nQUIT;\n')
print(f, 'level', lv, 'class', cid, '|C| =', len(C), 'roots', roots, 'balls', [len(ball(r)) for r in radii])
