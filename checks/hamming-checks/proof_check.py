# Checks the statements used in the Hamming proof (paper, section "Hamming graphs"):
#  (1) Lemma hamming-orbits: profile classes = orbits of the pointwise stabiliser (brute force in S_q wr S_d);
#  (2) Theorem hamming-lemmaA: refinement with the roots individualised = profile classes;
#  (3) Lemma hamming-depth: along a chain whose roots come from non-singleton refined classes, Psi strictly
#      increases, and the chain reaches a discrete colouring within d(q+1)-1 roots.
import random, sys
sys.path.insert(0, '.')
from lemmaA import refine, ham, stab_orbits, same_partition
def patterns(roots, d):
    E = []
    for i in range(d):
        blocks = {}
        for r, x in enumerate(roots): blocks.setdefault(x[i], []).append(r)
        E.append(frozenset(frozenset(b) for b in blocks.values()))
    return E
def profile(T, roots, E, d):
    prof = {}
    for i in range(d):
        lab = frozenset(r for r, x in enumerate(roots) if x[i] == T[i])
        prof[(E[i], lab)] = prof.get((E[i], lab), 0) + 1
    return frozenset(prof.items())
def psi(E): return len(set(E)) + sum(len(e) for e in E)
d, q, chains = map(int, sys.argv[1:4])
V, idx, adj = ham(d, q); n = len(V); rnd = random.Random(7); bad = 0; steps = 0; maxdepth = 0
for c in range(chains):
    roots = []
    while True:
        col = [0]*n
        for j, r in enumerate(roots): col[r] = j+1
        R = refine(n, adj, col)
        rv = [V[r] for r in roots]; E = patterns(rv, d)
        P = [profile(V[t], rv, E, d) for t in range(n)]
        if roots and not same_partition(R, P): bad += 1; print('refinement != profile', rv)
        if roots and len(roots) <= 3 and not same_partition(P, stab_orbits(V, idx, d, q, rv)):
            bad += 1; print('profile != orbits', rv)
        cls = {}
        for t in range(n): cls.setdefault(R[t], []).append(t)
        big = [v for v in cls.values() if len(v) > 1]
        if not big: break
        t = rnd.choice(rnd.choice(big)); old = psi(E) if roots else 1
        roots.append(t); new = psi(patterns([V[r] for r in roots], d)); steps += 1
        if new <= old: bad += 1; print('Psi did not grow', old, new)
    maxdepth = max(maxdepth, len(roots))
    if len(roots) > d*(q+1) - 1: bad += 1; print('depth bound violated', len(roots))
print(f'H({d},{q}) chains {chains} roots {steps} max depth {maxdepth} bound {d*(q+1)-1} failures {bad}')
