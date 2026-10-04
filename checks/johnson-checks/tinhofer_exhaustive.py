# Exhaustive Tinhofer check on small Johnson graphs J(n,k) (independent of the proofs):
# for EVERY tuple of vertices up to automorphism, extended until its pointwise stabiliser is trivial, compare colour
# refinement with the tuple individualised against the orbits of the pointwise stabiliser in Aut(J(n,k)), computed by
# brute force over S_n (times complementation when n = 2k).
import itertools, sys
import numpy as np
n, k = int(sys.argv[1]), int(sys.argv[2])
V = [frozenset(c) for c in itertools.combinations(range(n), k)]; idx = {v: i for i, v in enumerate(V)}; N = len(V)
adj = [[idx[w] for w in V if len(v & w) == k-1] for v in V]
rows = []
for p in itertools.permutations(range(n)):
    img = [idx[frozenset(p[x] for x in v)] for v in V]
    rows.append(img)
    if n == 2*k: rows.append([idx[frozenset(range(n)) - V[i]] for i in img])
G = np.array(rows, dtype=np.int32)                       # every automorphism as a row (image of each vertex)
def refine(ind):
    c = [0]*N
    for j, r in enumerate(ind): c[r] = j+1
    while True:
        sig = [(c[v], tuple(sorted(c[u] for u in adj[v]))) for v in range(N)]
        names = {s: i for i, s in enumerate(sorted(set(sig)))}; nc = [names[s] for s in sig]
        if len(set(nc)) == len(set(c)): return nc
        c = nc
tuples = checked = bad = 0; stack = [((), G)]
while stack:
    tup, H = stack.pop()
    if tup:
        R = refine(tup); checked += 1
        orb = [frozenset(H[:, v].tolist()) for v in range(N)]   # H is the pointwise stabiliser (a group)
        cls = {}
        for v in range(N): cls.setdefault(R[v], set()).add(v)
        if any(frozenset(cls[R[v]]) != orb[v] for v in range(N)):
            bad += 1; print('MISMATCH', [sorted(V[r]) for r in tup])
    if len(H) == 1: continue
    seen = set()
    for v in range(N):                                    # one extension per orbit of the stabiliser
        if v in seen: continue
        o = set(H[:, v].tolist()); seen |= o
        if len(o) == 1: continue                           # fixed vertex: individualising it changes nothing
        stack.append((tup + (v,), H[H[:, v] == v]))
print(f'J({n},{k}): |Aut| = {len(G)}, tuples checked (up to Aut) = {checked}, mismatches = {bad}')
