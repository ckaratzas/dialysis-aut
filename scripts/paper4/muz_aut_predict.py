#!/usr/bin/env python3
"""Muzychuk-CFI (gen_muz_cfi.py) automorphism count predicted by the COORDINATE LEMMA (CLOSURE_BOUND_SPEC, 2026-10-11),
diagnostic only. Assumes: every automorphism maps fibres to fibres (some rho in S_m) and acts on fibre i coordinatewise,
coordinate j -> rho(j) by a value map pi_ij; the lemma says pi_ij(t) = u_i t + c_ij with u_i a unit of Z_q (common to
the fibre) and sum_j c_ij = 0. Edge {i,j} forces pi_ji = sigma_{rho i, rho j} pi_ij sigma_ij^{-1}, which must again be
affine with unit u_j. |Aut| = sum over rho, u of #(translation vectors), counted by a DP over the edges (state = partial
sums at the m fibres). Equality with Traces' |Aut| checks the lemma's hypotheses on the instance.
Usage: muz_aut_predict.py spec...   (spec as in gen_muz_cfi.py: aff:q:m:seed | nonaff:q:m:seed)"""
import sys, random, itertools, math
import numpy as np

def sigmas(q, m, mode, rng):   # replays gen_muz_cfi.build's rng use: sig[(i,j)] maps x_j (fibre i) to y_i (fibre j)
    sig = {}
    for i, j in itertools.combinations(range(m), 2):
        if mode == 'aff': c = rng.randrange(q); s = [(t + c) % q for t in range(q)]
        else: s = list(range(q)); rng.shuffle(s)
        sig[(i, j)] = s; sig[(j, i)] = [s.index(t) for t in range(q)]
    return sig

def affine_of(f, q, units):    # f as a list on Z_q -> (u, c) if f(t) = u t + c, else None
    c = f[0]; u = (f[1] - c) % q
    if u not in units: return None
    return (u, c) if all(f[t] == (u * t + c) % q for t in range(q)) else None

def count(q, m, sig):
    units = [u for u in range(1, q) if math.gcd(u, q) == 1]
    edges = list(itertools.combinations(range(m), 2)); total = 0
    for rho in itertools.permutations(range(m)):
        # per edge and unit pair: allowed (c_ij, c_ji)
        allowed = {}
        for (i, j) in edges:
            s, s2 = sig[(i, j)], sig[(rho[i], rho[j])]
            for ui in units:
                for cij in range(q):
                    pij = [(ui * t + cij) % q for t in range(q)]
                    # pi_ji(y) = s2(pi_ij(s^{-1}(y)))
                    sinv = sig[(j, i)]
                    pji = [s2[pij[sinv[y]]] for y in range(q)]
                    a = affine_of(pji, q, units)
                    if a: allowed.setdefault((i, j, ui, a[0]), []).append((cij, a[1]))
        for u in itertools.product(units, repeat=m):
            lists = [allowed.get((i, j, u[i], u[j]), []) for (i, j) in edges]
            if any(not l for l in lists): continue
            dp = np.zeros((q,) * m, dtype=np.float64); dp[(0,) * m] = 1.0
            for (i, j), l in zip(edges, lists):
                nd = np.zeros_like(dp)
                for a, b in l: nd += np.roll(np.roll(dp, a, axis=i), b, axis=j)
                dp = nd
            total += dp[(0,) * m]
    return total

if __name__ == '__main__':
    for spec in sys.argv[1:]:
        mode, q, m, seed = spec.split(':'); q, m = int(q), int(m)
        print(spec, "predicted |Aut| =", count(q, m, sigmas(q, m, mode, random.Random(int(seed)))), flush=True)
