#!/usr/bin/env python3
"""Classify every step of the root path (1-WL, root = lowest vertex of the smallest non-singleton class, until discrete)
on benchmark instances: S1 = split (mu ratio <= ALPHA), CLO = closure (singleton ratio >= BETA), PRIM = neither (candidate
S2-prim step: where an explicit split constant would need Babai's argument). Prints per family the counts and examples."""
import sys, glob, os, random
from collections import Counter, defaultdict
ALPHA, BETA = 0.8, 1.3
MU0 = int(__import__('os').environ.get('MU0', '16'))
def load(f):
    nb = None
    for l in open(f):
        p = l.split()
        if p and p[0] == 'p': n = int(p[2]); nb = [[] for _ in range(n)]
        elif p and p[0] == 'e': a, b = int(p[1]) - 1, int(p[2]) - 1; nb[a].append(b); nb[b].append(a)
    return nb
def refine(nb, col):
    k = len(set(col)); n = len(nb)
    while True:
        keys = [(col[v], tuple(sorted(col[w] for w in nb[v]))) for v in range(n)]
        ids = {kk: i for i, kk in enumerate(sorted(set(keys)))}
        col = [ids[kk] for kk in keys]
        if len(ids) == k: return col
        k = len(ids)
GREEDY = int(os.environ.get('GREEDY', '0'))
ROOTS = None   # set to [] to record the chosen roots
TRACE = None   # set to [] to record the colouring of every state on the path
def imp_split(nb, col):
    """(D)'s trigger: delete singleton vertices; True if >= 2 components meet a largest class (the class is split across
    pieces, so the level goes to (D)/(G), whose costs add instead of multiply)."""
    c = Counter(col); mu = max(c.values()); big = {cl for cl, z in c.items() if z == mu}
    keep = [c[col[v]] > 1 for v in range(len(nb))]; comp = [-1] * len(nb); k = 0; hit = 0
    for v0 in range(len(nb)):
        if not keep[v0] or comp[v0] >= 0: continue
        st = [v0]; comp[v0] = k; meets = False
        while st:
            v = st.pop(); meets |= col[v] in big
            for w in nb[v]:
                if keep[w] and comp[w] < 0: comp[w] = k; st.append(w)
        hit += meets; k += 1
        if hit >= 2: return True
    return False
KEY = os.environ.get('GREEDY_KEY', 'mu')   # 'sg' = closure-greedy: maximise singletons first (the rule the plane lemma is proved for)
def stats(col):
    c = Counter(col); return max(c.values()), sum(1 for v in c.values() if v == 1), c
def ind(nb, col, r):
    col = list(col); col[r] = max(col) + 1; return refine(nb, col)
def path(nb, cap=80, init=None):
    """Root rule: naive (lowest vertex of smallest non-singleton class), or GREEDY=k: try one vertex from each of up to
    k non-singleton classes (smallest first) and keep the root with the best (mu, -singletons). Any root is legal for
    Aut (the refutation handles orbits); for iso the choice is made on one side, so greedy costs only refinement work."""
    n = len(nb); col = refine(nb, list(init) if init is not None else [0] * n); out = []
    for d in range(cap):
        mu, sg, c = stats(col); out.append((mu, sg))
        if TRACE is not None: TRACE.append(list(col))
        ns = sorted((cl for cl, sz in c.items() if sz > 1), key=lambda cl: (c[cl], cl))
        if not ns: break
        cands = [min(v for v in range(n) if col[v] == cl) for cl in ns[:max(1, GREEDY)]]
        if GREEDY:
            rng = random.Random(d); pool = [v for v in range(n) if c[col[v]] > 1]
            cands += rng.sample(pool, min(GREEDY, len(pool)))
        best = None
        for r in cands:
            nc = ind(nb, col, r); m1, s1, _ = stats(nc)
            key = (-s1, m1) if KEY == 'sg' else (m1, -s1)
            if best is None or key < best[0]: best = (key, nc, r)
        col = best[1]
        if ROOTS is not None: ROOTS.append(best[2])
    return out
if __name__ == '__main__':
    fams = sys.argv[1:]; per = 4
    tot = Counter(); ex = defaultdict(list)
    for fam in fams:
        files = sorted(glob.glob(f'graphs/{fam}/*'), key=lambda p: os.path.getsize(p))
        files = [f for f in files if os.path.getsize(f) < 400_000]
        pick = [files[i * (len(files) - 1) // max(1, per - 1)] for i in range(min(per, len(files)))] if files else []
        cnt = Counter()
        for f in dict.fromkeys(pick):
            p = path(load(f))
            for (m0, s0), (m1, s1) in zip(p, p[1:]):
                if m0 <= MU0: cnt['BCM'] += 1
                elif m1 <= ALPHA * m0: cnt['S1'] += 1
                elif s0 > 0 and s1 >= BETA * s0 and s1 - s0 >= 2: cnt['CLO'] += 1   # >= 2: growth beyond the root itself
                elif s0 == 0 and s1 >= 2: cnt['CLO'] += 1    # first root: closure beyond the root
                else:
                    cnt['PRIM'] += 1
                    if len(ex[fam]) < 3: ex[fam].append((os.path.basename(f), (m0, s0), (m1, s1)))
        tot.update(cnt)
        print(f"{fam:14s} {dict(cnt)} examples PRIM: {ex[fam]}", flush=True)
    print("TOTAL", dict(tot))
