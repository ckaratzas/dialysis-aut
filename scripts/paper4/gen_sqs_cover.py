#!/usr/bin/env python3
"""t = 3 analogue of the hidden-STS covers (G2 attempt 4, lead 2, 2026-10-12; diagnostic, NOT a benchmark family).
Base J(16,3) (triples of 16 points, adjacent iff they share 2 points). Hidden SQS(16) by doubling SQS(8) = AG(3,2):
blocks B x {0}, B x {1} (B in SQS(8)) and {(x,0),(y,0),(z,1),(w,1)} with {x,y} in F_i, {z,w} in F'_{pi(i)} for two
independently relabelled 1-factorizations F, F' of K_8 and a random pi. Every triple lies in exactly one block (uniform up
to size 3). Voltage in Gamma on the edge {a,b,c} - {a,b,d}: g if {a,b,c,d} is a block, else identity.
Usage: gen_sqs_cover.py OUT GROUP(S3|A5|Z2) SEED"""
import sys, itertools, random
out, gname, seed = sys.argv[1], sys.argv[2], int(sys.argv[3]); rng = random.Random(seed)
def perms(k, even): return [p for p in itertools.permutations(range(k)) if not even or sum(1 for i in range(k) for j in range(i + 1, k) if p[i] > p[j]) % 2 == 0]
G = {'S3': perms(3, False), 'A5': perms(5, True), 'Z2': [(0, 1), (1, 0)]}[gname]; idx = {g: i for i, g in enumerate(G)}
def mul(a, b): return tuple(b[a[i]] for i in range(len(a)))
ident = tuple(range(len(G[0]))); g0 = [g for g in G if g != ident][0]
sqs8 = [frozenset(q) for q in itertools.combinations(range(8), 4) if q[0] ^ q[1] ^ q[2] ^ q[3] == 0]; assert len(sqs8) == 14
def onefact(perm):   # round-robin 1-factorization of K_8, relabelled
    F = []
    for r in range(7):
        pairs = [(7, r)] + [((r + k) % 7, (r - k) % 7) for k in range(1, 4)]
        F.append([frozenset((perm[a], perm[b])) for a, b in pairs])
    return F
p0 = list(range(8)); rng.shuffle(p0); p1 = list(range(8)); rng.shuffle(p1)
F, F2 = onefact(p0), onefact(p1); pi = list(range(7)); rng.shuffle(pi)
blocks = set()
for B in sqs8: blocks.add(frozenset(x for x in B)); blocks.add(frozenset(x + 8 for x in B))
for i in range(7):
    for e in F[i]:
        for f in F2[pi[i]]: blocks.add(frozenset(set(e) | {z + 8 for z in f}))
assert len(blocks) == 140
for T in itertools.combinations(range(16), 3): assert sum(1 for B in blocks if set(T) <= B) == 1
V = list(itertools.combinations(range(16), 3)); vid = {v: i for i, v in enumerate(V)}
E = [(u, w) for u, w in itertools.combinations(V, 2) if len(set(u) & set(w)) == 2]
h = len(G); edges = []
for (u, w) in E:
    g = g0 if frozenset(set(u) | set(w)) in blocks else ident
    for x in G: edges.append((vid[u] * h + idx[x], vid[w] * h + idx[mul(x, g)]))
with open(out, 'w') as f:
    f.write(f"p edge {len(V) * h} {len(edges)}\n"); f.writelines(f"e {a + 1} {b + 1}\n" for a, b in edges)
print(out, len(V) * h, len(edges))
