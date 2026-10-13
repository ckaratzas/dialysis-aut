#!/usr/bin/env python3
"""chh-type graphs of any size (diagnostic, Lemma G counterexample attempt 2026-10-12; NOT a benchmark family).
Structure read off CHH_cc(a-b) (chh_blocks.py): b groups of a blocks; each block = one of two 22-vertex templates
(extracted from CHH_cc(7-7)_1078-2; bundled as scripts/paper4/data/chh_templates.json) with 3 group ports and 1 cross port; the group ports of two
blocks of the same group form a K33; the cross port of a block is adjacent to the cross port of every block outside its
group. Usage: gen_chh_like.py TEMPLATES OUT a b   (TEMPLATES = scripts/paper4/data/chh_templates.json) "n1,n2;n1,n2;..." (type counts per group, b entries)."""
import sys, json
T = json.load(open(sys.argv[1])); out = sys.argv[2]; a, b = int(sys.argv[3]), int(sys.argv[4])
comp = [tuple(map(int, g.split(','))) for g in sys.argv[5].split(';')]
assert len(comp) == b and all(sum(c) == a for c in comp)
edges = []; blocks = []   # per block: (group, gports, cport)
nv = 0
for gi, (n1, n2) in enumerate(comp):
    for t in [0] * n1 + [1] * n2:
        tp = T[t]; base = nv; nv += len(tp['role'])
        edges += [(base + x, base + y) for x, y in tp['edges']]
        gp = [base + k for k, r in enumerate(tp['role']) if r == 'g']; cp = [base + k for k, r in enumerate(tp['role']) if r == 'c']
        assert len(gp) == 3 and len(cp) == 1
        blocks.append((gi, gp, cp[0]))
for i in range(len(blocks)):
    for j in range(i + 1, len(blocks)):
        (g1, p1, c1), (g2, p2, c2) = blocks[i], blocks[j]
        if g1 == g2: edges += [(x, y) for x in p1 for y in p2]
        else: edges.append((c1, c2))
with open(out, 'w') as f:
    f.write(f"p edge {nv} {len(edges)}\n"); f.writelines(f"e {x + 1} {y + 1}\n" for x, y in edges)
print(out, nv, len(edges))
