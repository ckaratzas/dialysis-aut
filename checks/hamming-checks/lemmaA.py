# Lemma A test on Hamming graphs H(d,q): refinement with roots individualised vs orbits of their pointwise stabiliser.
import itertools, random, sys
def refine(n, adj, colour):
    c = list(colour)
    while True:
        sig = [(c[v], tuple(sorted(c[u] for u in adj[v]))) for v in range(n)]
        names = {s:i for i,s in enumerate(sorted(set(sig)))}
        nc = [names[s] for s in sig]
        if len(set(nc)) == len(set(c)): return nc
        c = nc
def ham(d, q):
    V = list(itertools.product(range(q), repeat=d)); idx = {v:i for i,v in enumerate(V)}
    adj = [[idx[v[:i]+(a,)+v[i+1:]] for i in range(d) for a in range(q) if a != v[i]] for v in V]
    return V, idx, adj
def stab_orbits(V, idx, d, q, roots):
    # Aut = S_q wr S_d: g = (pi, sigma_0..sigma_{d-1}); (g x)[pi(i)] = sigma_i(x[i])
    perms = list(itertools.permutations(range(q)))
    parent = list(range(len(V)))
    def find(a):
        while parent[a] != a: parent[a] = parent[parent[a]]; a = parent[a]
        return a
    for pi in itertools.permutations(range(d)):
        # sigma_i must send root symbols in coord i to root symbols in coord pi(i): constraints per coord
        choices = []
        ok = True
        for i in range(d):
            cs = [s for s in perms if all(s[r[i]] == r[pi[i]] for r in roots)]
            if not cs: ok = False; break
            choices.append(cs)
        if not ok: continue
        # generators suffice: orbits of the group = orbits of generating set; but we take all products lazily
        # (group is small: enumerate)
        for sig in itertools.product(*choices):
            for v in V:
                w = [0]*d
                for i in range(d): w[pi[i]] = sig[i][v[i]]
                a, b = find(idx[v]), find(idx[tuple(w)])
                if a != b: parent[a] = b
    return [find(i) for i in range(len(V))]
def same_partition(a, b):
    m = {}
    for x, y in zip(a, b):
        if m.setdefault(x, y) != y: return False
    return len(set(a)) == len(set(b))
if __name__ == '__main__':
    d, q, trials, maxk = map(int, sys.argv[1:5])
    V, idx, adj = ham(d, q); n = len(V); rnd = random.Random(1); bad = 0; tot = 0
    for t in range(trials):
        k = rnd.randint(1, maxk); roots = rnd.sample(range(n), k)
        col = [0]*n
        for j, r in enumerate(roots): col[r] = j+1
        R = refine(n, adj, col); O = stab_orbits(V, idx, d, q, [V[r] for r in roots])
        tot += 1
        if not same_partition(R, O):
            bad += 1
            if bad <= 3: print('FAIL', [V[r] for r in roots], 'refine classes', len(set(R)), 'orbits', len(set(O)))
    print(f'H({d},{q}) trials {tot} mismatches {bad}')
