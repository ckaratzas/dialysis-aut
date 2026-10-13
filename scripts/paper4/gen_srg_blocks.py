#!/usr/bin/env python3
"""chh wiring with 2-WL-blind blocks (diagnostic, Lemma G counterexample attempt, 2026-10-12; NOT a benchmark family).
Block = one of the two srg(16,6,2,2) (type 0: 4x4 rook's graph, type 1: Shrikhande graph, non-isomorphic, 2-WL equivalent)
plus 4 port vertices (3 group ports, 1 cross port), each port adjacent to all 16 SRG vertices (identical for both types,
so the block types stay 2-WL equivalent). Wiring as chh: b groups of a blocks; K33 between the group ports of two blocks
of the same group; one edge between the cross ports of any two blocks in different groups.
Usage: gen_srg_blocks.py OUT a b "t,t,...;..." (block types per group, a per group, b groups)."""
import sys
def rook():
    V = [(i, j) for i in range(4) for j in range(4)]
    return [(x, y) for x in range(16) for y in range(x + 1, 16) if (V[x][0] == V[y][0]) != (V[x][1] == V[y][1])]
def shrikhande():
    V = [(i, j) for i in range(4) for j in range(4)]; S = {(0, 1), (0, 3), (1, 0), (3, 0), (1, 1), (3, 3)}
    return [(x, y) for x in range(16) for y in range(x + 1, 16) if ((V[x][0] - V[y][0]) % 4, (V[x][1] - V[y][1]) % 4) in S]
T = [rook(), shrikhande()]
for e in T: assert len(e) == 48
out, a, b = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
types = [list(map(int, g.split(','))) for g in sys.argv[4].split(';')]
assert len(types) == b and all(len(g) == a for g in types)
edges = []; blocks = []; nv = 0
for gi, g in enumerate(types):
    for t in g:
        base = nv; nv += 20
        edges += [(base + x, base + y) for x, y in T[t]]
        ports = [base + 16 + k for k in range(4)]
        edges += [(p, base + x) for p in ports for x in range(16)]
        blocks.append((gi, ports[:3], ports[3]))
for i in range(len(blocks)):
    for j in range(i + 1, len(blocks)):
        (g1, p1, c1), (g2, p2, c2) = blocks[i], blocks[j]
        if g1 == g2: edges += [(x, y) for x in p1 for y in p2]
        else: edges.append((c1, c2))
with open(out, 'w') as f:
    f.write(f"p edge {nv} {len(edges)}\n"); f.writelines(f"e {x + 1} {y + 1}\n" for x, y in edges)
print(out, nv, len(edges))
