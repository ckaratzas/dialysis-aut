# Route A check. Claim: for R^I(G) (gadget degree r, any I), starting colouring chi* = stable colouring of the input
# colouring, C a chi*-class inside M(v), base b = m_{B0} in C and ANY round limit t >= 2, the candidate s = m_{B1} in C
# is admissible at round t  <=>  A = B0+B1 passes the flip-labelling DP below (a homogeneous GF(2) system restricted to
# one A). Hence Adm_t is a subspace and T_C (translations by Adm_t) is a group.
# DP over node types of the depth-t unfolding tree:
#   pair node (w, depth k, status f): infeasible if w in K and f=1, or w in N(v), k<=t-1 and f != A(w); feasible if k=t;
#     else every gadget u containing w: gadget node (u, k+1, entry w, f) feasible.
#   gadget node (u, k, entry w, f): feasible if k=t; else exists even g on N(u), g(w)=f, with every
#     pair node (w', k+1, g(w')) feasible (w' in N(u)).   Root: gadget v, g = A.
import random, itertools, sys, collections
from functools import lru_cache
from mp_lib import build, graph, rounds
def adm_dp(N, v, K, A, t, pairs_of):
    @lru_cache(None)
    def pair(w, k, f):
        if w in K and f: return False
        if w in Nv and k <= t-1 and f != (w in A): return False
        if k == t: return True
        return all(gad(u, k+1, w, f) for u in pairs_of[w])
    @lru_cache(None)
    def gad(u, k, w, f):
        if k == t: return True
        others = [x for x in N[u] if x != w]
        for bits in itertools.product((0,1), repeat=len(others)):
            if (f + sum(bits)) % 2: continue
            if all(pair(x, k+1, b) for x, b in zip(others, bits)) and pair(w, k+1, f): return True
        return False
    Nv = set(N[v])
    return all(pair(w, 1, int(w in A)) for w in N[v])
RS = [int(x) for x in sys.argv[3].split(',')] if len(sys.argv) > 3 else [3,3,4]
TWIST = len(sys.argv) > 4 and sys.argv[4] == 'twist'
rng = random.Random(int(sys.argv[1])); st = collections.Counter(); bad = []
for trial in range(int(sys.argv[2])):
    r = rng.choice(RS); nW = rng.randint(5,10 if r<5 else 8); nV = rng.randint(nW, nW+4 if r<5 else nW+1)
    par = [rng.randint(0,1) for _ in range(nV)] if TWIST else None
    N = build(nV, nW, r, rng); vid, adj, col = graph(N, nW, par); inv = {i:k for k,i in vid.items()}
    I = set(rng.sample(range(nW), rng.randint(0,2)))
    col = [(('Fa',k[1]) if k[0]=='a' else ('Fb',k[1])) if k[0] in 'ab' and k[1] in I else col[i]
           for i,k in ((i,inv[i]) for i in range(len(adj)))]
    base, _ = rounds(adj, col, []); stab = base[-1]
    K = {w for w in range(nW) if stab[vid[('a',w)]] != stab[vid[('b',w)]]}
    pairs_of = collections.defaultdict(list)
    for u, Nu in enumerate(N):
        for w in Nu: pairs_of[w].append(u)
    cls = collections.defaultdict(list)
    for i, c in enumerate(stab): cls[c].append(i)
    for C in cls.values():
        if len(C) < 2 or inv[C[0]][0] != 'm': continue
        st['odd_gadget'] += len(inv[C[0]][2]) % 2
        v = inv[C[0]][1]
        # chi* structure check: gadget class = fixed pattern on K
        pats = {frozenset(inv[x][2] & K) for x in C}; st['class_is_Kpattern'] += len(pats) == 1
        b = C[0]; B0 = inv[b][2]
        _, tstab = rounds(adj, stab, [b])
        for t in sorted({2, 3, tstab, tstab+1, tstab+3}):
            ref, _ = rounds(adj, stab, [b], t); nameR = sorted(ref[t][x] for x in C)
            adm = set()
            for s in C:
                h, _ = rounds(adj, stab, [s], t)
                if sorted(h[t][x] for x in C) == nameR: adm.add(B0 ^ inv[s][2])
            dp = {B0 ^ inv[s][2] for s in C if adm_dp(N, v, frozenset(K), frozenset(B0 ^ inv[s][2]), t, pairs_of)}
            st['cases'] += 1; st['dp_equals_refinement'] += adm == dp
            st['group'] += all((a ^ c) in adm for a in adm for c in adm)
            st['proper_subset'] += len(adm) < len(C)
            if adm != dp: bad.append((trial, v, t, tstab, len(adm), len(dp), sorted(I)))
print(dict(st)); print('mismatches', len(bad), bad[:6])
