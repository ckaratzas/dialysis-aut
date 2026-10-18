#!/usr/bin/env python3
"""CFI-type graphs over a group Gamma (diagnostic family, CLOSURE_BOUND_SPEC.md: "find something we cannot break").

Base: a 3-regular graph H with an ordering of the 3 edges at every vertex. Vertices of the output graph:
  end vertices   (v, e, g)       for every vertex v, incident edge e, g in Gamma        (|Gamma| per edge end)
  inner vertices (v; g1, g2, g3) with g1 g2 g3 = t_v (ordered product), e1, e2, e3 the edges at v in their order
Edges: inner (v; g1, g2, g3) -- end (v, e_i, g_i) for i = 1..3;  wire  end (v, e, x) -- end (u, e, x^-1)  for e = uv.
t_v = 1 everywhere (untwisted) or t_v = a fixed non-identity element at one vertex (twisted, suffix -tw).

Each gadget's constraint is preserved by (g1, g2, g3) -> (a g1 b^-1, b g2 c^-1, c g3 a^-1), so the local symmetry is built
from copies of Gamma: for Gamma = A5 non-solvable, the case the series solver (elementary-abelian normal series) cannot
handle. Gamma = Z2 is the classical CFI construction (control), S3 is non-abelian but solvable.

Not a benchmark family. Usage:  gen_group_cfi.py OUTDIR GROUP:BASE[:tw][:bip] ...   (bip = subdivided wires, bipartite)   (GROUP in Z2 Z3 S3 A4 A5; BASE below, or rcN-S = random cubic, N vertices, seed S)
"""
import itertools
import os
import sys


def perm_group(m, even):
    els = [p for p in itertools.permutations(range(m))
           if not even or sum(1 for i in range(m) for j in range(i + 1, m) if p[i] > p[j]) % 2 == 0]
    return els, (lambda a, b: tuple(a[b[i]] for i in range(m))), tuple(range(m))


def cyclic(n):
    return list(range(n)), (lambda a, b: (a + b) % n), 0


def elem_abelian(p, k):   # F_p^k (2026-10-17, ATTACK_G2_SPEC: the abelian form of projective-geometry gadgets)
    els = list(itertools.product(range(p), repeat=k))
    return els, (lambda a, b: tuple((x + y) % p for x, y in zip(a, b))), tuple([0] * k)


GROUPS = {'Z2': lambda: cyclic(2), 'Z3': lambda: cyclic(3), 'S3': lambda: perm_group(3, False),
          'A4': lambda: perm_group(4, True), 'A5': lambda: perm_group(5, True),
          'F2_3': lambda: elem_abelian(2, 3), 'F3_2': lambda: elem_abelian(3, 2), 'F5_2': lambda: elem_abelian(5, 2)}


def lcf(n, shifts, rep):   # cubic graph from LCF notation [shifts]^rep on a Hamiltonian cycle of n vertices
    E = {tuple(sorted((i, (i + 1) % n))) for i in range(n)}
    for i in range(n):
        E.add(tuple(sorted((i, (i + shifts[i % len(shifts)]) % n))))
    return sorted(E)

# 3-regular base graphs (edge lists)
BASES = {
    'K4': [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)],
    'K33': [(0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5)],
    'prism': [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3), (0, 3), (1, 4), (2, 5)],
    'cube': [(0, 1), (1, 3), (3, 2), (2, 0), (4, 5), (5, 7), (7, 6), (6, 4), (0, 4), (1, 5), (2, 6), (3, 7)],
    'petersen': [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
                 (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)],
    'mobius8': [(i, (i + 1) % 8) for i in range(8)] + [(i, i + 4) for i in range(4)],
    'ladder10': [(i, (i + 1) % 5) for i in range(5)] + [(5 + i, 5 + (i + 1) % 5) for i in range(5)] + [(i, i + 5) for i in range(5)],
}
# high-girth cubic bases (ATTACK_G2_SPEC: expander-like, every neighbourhood looks alike): Heawood (girth 6, 14 vertices),
# McGee (girth 7, 24), Tutte-Coxeter / Tutte 8-cage (girth 8, 30)
BASES['heawood'] = lcf(14, [5, -5], 7)
BASES['mcgee'] = lcf(24, [12, 7, -7], 8)
BASES['tutte8'] = lcf(30, [-13, -9, 7, -7, 9, 13], 5)


def prism_n(n):   # n-gonal prism (circular ladder), 2n vertices
    return [(i, (i + 1) % n) for i in range(n)] + [(n + i, n + (i + 1) % n) for i in range(n)] + [(i, n + i) for i in range(n)]


def random_cubic(bname):   # 'rcN-S': connected random 3-regular graph on N vertices, seed S (treewidth grows with N)
    import networkx as nx
    nb, seed = (int(x) for x in bname[2:].split('-'))
    while True:
        h = nx.random_regular_graph(3, nb, seed=seed)
        if nx.is_connected(h):
            return sorted(tuple(sorted(e)) for e in h.edges())
        seed += 1000


def build(gname, bname, twisted, bip=False):
    els, mul, e = GROUPS[gname]()
    idx = {g: i for i, g in enumerate(els)}; G = len(els)
    inv = [idx[next(h for h in els if mul(g, h) == e)] for g in els]
    M = [[idx[mul(a, b)] for b in els] for a in els]
    E = BASES[bname] if bname in BASES else random_cubic(bname) if bname.startswith('rc') else prism_n(int(bname[5:]))   # 'prismN' = N-gonal prism
    nv = 1 + max(max(u, v) for u, v in E)
    inc = [[] for _ in range(nv)]                          # ordered incident edges per vertex
    for k, (u, v) in enumerate(E):
        inc[u].append(k); inc[v].append(k)
    assert all(len(x) == 3 for x in inc), "base graph is not 3-regular"
    t = [idx[e]] * nv
    if twisted:
        t[0] = next(i for i, g in enumerate(els) if g != e)   # first non-identity element
    end = {}; n = 0
    for v in range(nv):
        for k in inc[v]:
            for g in range(G):
                end[(v, k, g)] = n; n += 1
    edges = []
    wires = [(end[(v, k, x)], end[(u, k, inv[x])]) for k, (u, v) in enumerate(E) for x in range(G)]
    for v in range(nv):                                     # gadgets
        e1, e2, e3 = inc[v]
        for g1 in range(G):
            for g2 in range(G):
                g3 = M[inv[M[g1][g2]]][t[v]]                # g1 g2 g3 = t_v  =>  g3 = (g1 g2)^-1 t_v
                assert M[M[g1][g2]][g3] == t[v]
                w = n; n += 1
                edges += [(w, end[(v, e1, g1)]), (w, end[(v, e2, g2)]), (w, end[(v, e3, g3)])]
    for a, b in wires:   # bip: subdivide every wire (bipartite: inner + midpoints | ends; Aut unchanged, degrees 3/61 vs 2)
        if bip:
            edges += [(a, n), (n, b)]; n += 1
        else:
            edges.append((a, b))
    return n, edges


def main():
    out = sys.argv[1]; os.makedirs(out, exist_ok=True)
    for spec in sys.argv[2:]:
        parts = spec.split(':'); gname, bname = parts[0], parts[1]; tw = 'tw' in parts[2:]; bip = 'bip' in parts[2:]
        name = f"gcfi-{gname}-{bname}{'-tw' if tw else ''}{'-bip' if bip else ''}"
        path = os.path.join(out, name)
        if os.path.exists(path):
            print(f"{name}: exists, skipped"); continue
        n, edges = build(gname, bname, tw, bip)
        with open(path, 'w') as f:
            f.write(f"p edge {n} {len(edges)}\n"); f.writelines(f"e {a + 1} {b + 1}\n" for a, b in edges)
        print(f"{name}: n = {n}, m = {len(edges)}", flush=True)


if __name__ == '__main__':
    main()
