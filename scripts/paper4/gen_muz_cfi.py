#!/usr/bin/env python3
"""Hard-core candidate, interior of the Muzychuk family (CLOSURE_BOUND_SPEC), diagnostic only, NOT a benchmark family.
Base K_m; fibre i = gadget points {x in Z_q^{N(i)} : sum x = 0} (q^{m-2} points, the affine design whose parallel classes
are the coordinate hyperplanes, "a = dimension" end = CFI); for every base edge {i,j} a bijection sigma_ij of Z_q
(sigma_ji = inverse); (x,i) ~ (y,j) iff sigma_ij(x_j) = y_i.
  aff:q:m:seed   sigma_ij(t) = t + c_ij (translations): CFI over Z_q (twisted iff sum of c over a cycle basis != 0 ...)
  nonaff:q:m:seed random permutations of Z_q (non-affine for q >= 4 w.h.p.): non-linear twists
Usage: gen_muz_cfi.py OUTDIR spec..."""
import sys, os, random, itertools
def build(q, m, mode, rng):
    nbrs = {i: [j for j in range(m) if j != i] for i in range(m)}
    fib = {}
    for i in range(m):
        pts = [x + ((-sum(x)) % q,) for x in itertools.product(range(q), repeat=m - 2)]
        fib[i] = pts
    off = {i: i * q ** (m - 2) for i in range(m)}
    E = []
    for i, j in itertools.combinations(range(m), 2):
        if mode == 'aff': c = rng.randrange(q); sig = [(t + c) % q for t in range(q)]
        else: sig = list(range(q)); rng.shuffle(sig)
        pj = nbrs[i].index(j); pi = nbrs[j].index(i)
        byval = {}
        for b, y in enumerate(fib[j]): byval.setdefault(y[pi], []).append(b)
        for a, x in enumerate(fib[i]):
            for b in byval.get(sig[x[pj]], []): E.append((off[i] + a, off[j] + b))
    return m * q ** (m - 2), E
if __name__ == '__main__':
    out = sys.argv[1]; os.makedirs(out, exist_ok=True)
    for spec in sys.argv[2:]:
        mode, q, m, seed = spec.split(':'); q, m = int(q), int(m)
        n, E = build(q, m, mode, random.Random(int(seed)))
        name = f"muz-{mode}-q{q}-m{m}-s{seed}"
        with open(os.path.join(out, name), 'w') as f:
            f.write(f"p edge {n} {len(E)}\n"); f.writelines(f"e {a+1} {b+1}\n" for a, b in E)
        print(name, n, len(E))
