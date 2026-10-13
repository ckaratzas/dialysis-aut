#!/usr/bin/env python3
"""Voltage covers (graph lifts) of the Johnson graph J(m,2) (diagnostic, Lemma G / G2 counterexample attempt, 2026-10-12;
NOT a benchmark family). Base B = J(m,2) (pairs of [m], adjacent iff they share a point): one 1-WL class, no invariant cut,
Sym(m) symmetry, not a closure structure. Group Gamma acting regularly on itself; each base vertex becomes a fibre
{v} x Gamma; each base edge {u, w} (u < w in a fixed order) gets a voltage g_uw in Gamma; (u, x) ~ (w, x g_uw).
Size |V(B)| |Gamma| = C(m,2) |Gamma| -- polynomial in m, so Sym(m)-type local symmetry with m >> log n is possible
(CFI-type gadgets would be exponential in the base degree).
Voltages: 'random' (seed), or 'twistK' = identity everywhere except K random edges (a few non-trivial holonomies).
Usage: gen_voltage_cover.py OUT m GROUP(S3|A4|A5|Z2|Z3) MODE SEED"""
import sys, itertools, random
out, m, gname, mode, seed = sys.argv[1], int(sys.argv[2]), sys.argv[3], sys.argv[4], int(sys.argv[5])
def perms(k, even):
    return [p for p in itertools.permutations(range(k)) if not even or sum(1 for i in range(k) for j in range(i + 1, k) if p[i] > p[j]) % 2 == 0]
G = {'S3': perms(3, False), 'A4': perms(4, True), 'A5': perms(5, True), 'Z2': [(0, 1), (1, 0)], 'Z3': [(0, 1, 2), (1, 2, 0), (2, 0, 1)]}[gname]
idx = {g: i for i, g in enumerate(G)}
def mul(a, b): return tuple(b[a[i]] for i in range(len(a)))   # x * y as composition (apply a then b)
rng = random.Random(seed)
V = list(itertools.combinations(range(m), 2)); vid = {v: i for i, v in enumerate(V)}
E = [(u, w) for u, w in itertools.combinations(V, 2) if len(set(u) & set(w)) == 1]
ident = tuple(range(len(G[0])))
if mode == 'random': volt = {e: rng.choice(G) for e in E}
elif mode.startswith('twist'):
    K = int(mode[5:]); volt = {e: ident for e in E}
    for e in rng.sample(E, K): volt[e] = rng.choice([g for g in G if g != ident])
elif mode == 'sts13':   # hidden cyclic STS(13) (base blocks {0,1,4}, {0,2,8} mod 13): voltage g on {a,b}-{a,c} iff {a,b,c} is a block
    assert m == 13
    T = {frozenset((x + i) % 13 for x in blk) for blk in ((0, 1, 4), (0, 2, 8)) for i in range(13)}; assert len(T) == 26
    g0 = [g for g in G if g != ident][seed % (len(G) - 1)]
    volt = {e: (g0 if frozenset(set(e[0]) | set(e[1])) in T else ident) for e in E}
elif mode == 'stsrand':   # random STS(m) by Stinson's hill-climbing (m = 1, 3 mod 6); voltage g on {a,b}-{a,c} iff {a,b,c} is a block
    def stinson(v, r):
        live = {x: set(range(v)) - {x} for x in range(v)}; other = {}; blocks = set(); need = v * (v - 1) // 6
        while len(blocks) < need:
            x = r.choice([p for p in range(v) if live[p]]); y, z = r.sample(sorted(live[x]), 2)
            if z in live[y]:
                blocks.add(frozenset((x, y, z)))
                for a_, b_ in ((x, y), (x, z), (y, z)): live[a_].discard(b_); live[b_].discard(a_); other[(min(a_, b_), max(a_, b_))] = ({x, y, z} - {a_, b_}).pop()
            else:
                w = other[(min(y, z), max(y, z))]; blocks.discard(frozenset((w, y, z)))
                blocks.add(frozenset((x, y, z)))
                for a_, b_ in ((x, y), (x, z)): live[a_].discard(b_); live[b_].discard(a_)
                live[w].add(y); live[y].add(w); live[w].add(z); live[z].add(w)
                del other[(min(w, y), max(w, y))]; del other[(min(w, z), max(w, z))]
                for a_, b_ in ((x, y), (x, z), (y, z)): other[(min(a_, b_), max(a_, b_))] = ({x, y, z} - {a_, b_}).pop()
        return blocks
    T = stinson(m, rng); g0 = [g for g in G if g != ident][0]
    volt = {e: (g0 if frozenset(set(e[0]) | set(e[1])) in T else ident) for e in E}
else: raise SystemExit("mode")
h = len(G); edges = []
for (u, w) in E:
    g = volt[(u, w)]
    for x in G: edges.append((vid[u] * h + idx[x], vid[w] * h + idx[mul(x, g)]))
with open(out, 'w') as f:
    f.write(f"p edge {len(V) * h} {len(edges)}\n"); f.writelines(f"e {a + 1} {b + 1}\n" for a, b in edges)
print(out, len(V) * h, len(edges))
