#!/usr/bin/env python3
"""Stress instances for the stabiliser chain: Latin square graphs of class-2 p-groups with FEW automorphisms.

Not a benchmark family (CLOSURE_BOUND_SPEC.md, "find something we cannot break"). Group construction (Baer): a random
bilinear map beta: F_p^d x F_p^d -> F_p^e, elements (v, w) in F_p^d x F_p^e, product
    (v, w)(v', w') = (v + v', w + w' + beta(v, v')).
beta is bilinear, so this is a group; it has class <= 2, exponent p for odd p and exponent <= 4 for p = 2. Its
isomorphism type depends on the commutator map beta(v,v') - beta(v',v). A random beta with e >= 2 gives class-2 groups
with small automorphism groups -- the hard case for group isomorphism (best known n^{O(log n)}), unlike the
extraspecial / Heisenberg groups (huge Aut) tested so far. Controls: a symmetric extraspecial group of the same order.

Every group is self-checked (associativity on samples, identity, |Z(G)|, |[G,G]|, class 2) before its graph is written.
The Latin square graph has N = n^2 vertices (cells of the Cayley table), cells adjacent iff they share a row, a column
or a symbol; degree 3(n-1).

Usage:  python3 gen_class2_stress.py OUTDIR [SPEC ...]      (pure Python, no numpy; existing files are skipped)
        SPEC = p,d,e,seed   (e.g. 3,3,2,1)   or   'default' for the planned Xeon set (see DEFAULT below).
"""
import os
import random
import sys

# order 243 (N = 59,049) and 256 (N = 65,536) for the Xeon; 128 (N = 16,384) as the laptop check
DEFAULT = [(3, 3, 2, s) for s in (1, 2, 3)] + [(2, 5, 3, s) for s in (1, 2, 3)] + [(2, 4, 3, s) for s in (1, 2)]

# Pure Python (no numpy): the Xeon has none. Same random draws as the first (numpy) version, so the same groups.


def rank_mod_p(M, p):
    M = [[x % p for x in row] for row in M]; r = 0; rows = len(M); cols = len(M[0]) if M else 0
    for c in range(cols):
        piv = next((i for i in range(r, rows) if M[i][c] % p), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = pow(M[r][c], p - 2, p) if p > 2 else 1
        M[r] = [(x * inv) % p for x in M[r]]
        for i in range(rows):
            if i != r and M[i][c]:
                f = M[i][c]; M[i] = [(x - f * y) % p for x, y in zip(M[i], M[r])]
        r += 1
        if r == rows:
            break
    return r


def random_beta(p, d, e, seed, tries=200):
    """Random bilinear beta (e x d x d) whose commutator map has trivial radical and full image F_p^e, so that
    Z(G) = [G,G] = F_p^e (no abelian direct factor)."""
    rng = random.Random(seed * 1_000_003 + 31 * p + 7 * d + e)
    for _ in range(tries):
        B = [[[rng.randrange(p) for _ in range(d)] for _ in range(d)] for _ in range(e)]
        A = [[[(B[k][i][j] - B[k][j][i]) % p for j in range(d)] for i in range(d)] for k in range(e)]
        # radical: v with A_k v = 0 for all k  <=>  kernel of the stacked (e*d) x d matrix
        if rank_mod_p([A[k][j] for k in range(e) for j in range(d)], p) < d:
            continue
        # the e alternating forms are linearly independent: image spans F_p^e
        if rank_mod_p([[A[k][i][j] for i in range(d) for j in range(d)] for k in range(e)], p) < e:
            continue
        return B
    raise RuntimeError(f"no suitable beta for p={p} d={d} e={e}")


def extraspecial_beta(p, d, e):
    """Control: symplectic standard form on coordinate pairs into the first centre coordinate (extraspecial when
    e = 1; for e > 1 an abelian direct factor remains). Highly symmetric."""
    B = [[[0] * d for _ in range(d)] for _ in range(e)]
    for i in range(0, d - 1, 2):
        B[0][i][i + 1] = 1
    return B


def table(p, d, e, B):
    n = p ** (d + e)
    pw = [p ** i for i in range(d + e)]
    dig = [[(x // pw[i]) % p for i in range(d + e)] for x in range(n)]   # little-endian digits
    V = [dg[:d] for dg in dig]; W = [dg[d:] for dg in dig]
    # beta(v, .) as e linear forms per element a: row[k][j] = sum_i v_i B[k][i][j]
    lin = [[[sum(V[a][i] * B[k][i][j] for i in range(d)) % p for j in range(d)] for k in range(e)] for a in range(n)]
    L = [None] * n
    for a in range(n):
        va, wa, la = V[a], W[a], lin[a]; row = [0] * n
        for b in range(n):
            vb, wb = V[b], W[b]; idx = 0
            for i in range(d):
                idx += ((va[i] + vb[i]) % p) * pw[i]
            for k in range(e):
                bet = sum(la[k][j] * vb[j] for j in range(d))
                idx += ((wa[k] + wb[k] + bet) % p) * pw[d + k]
            row[b] = idx
        L[a] = row
    return L


def check(L):
    n = len(L)
    rng = random.Random(1)
    for _ in range(20000):
        a, b, c = rng.randrange(n), rng.randrange(n), rng.randrange(n)
        assert L[L[a][b]][c] == L[a][L[b][c]], "not associative"
    assert L[0] == list(range(n)) and [L[x][0] for x in range(n)] == list(range(n)), "0 is not the identity"
    assert all(len(set(row)) == n for row in L), "not a Latin square"
    centre = [z for z in range(n) if all(L[z][x] == L[x][z] for x in range(n))]
    inv = [row.index(0) for row in L]
    step = max(1, n // 64)
    comm = {L[L[inv[x]][inv[y]]][L[x][y]] for x in range(n) for y in range(0, n, step)}
    cs = set(centre)
    return len(centre), len(comm), all(z in cs for z in comm)


def write_latin_graph(L, path):
    n = len(L); N = n * n; m = N * 3 * (n - 1) // 2
    col_of = [[0] * n for _ in range(n)]   # col_of[s][r] = c with L[r][c] = s
    for r in range(n):
        for c, s in enumerate(L[r]):
            col_of[s][r] = c
    tmp = path + '.part'
    with open(tmp, 'w') as f:
        f.write(f'p edge {N} {m}\n')
        for r in range(n):
            buf = []
            for c in range(n):
                u = r * n + c + 1
                # same row (c' > c), same column (r' > r), same symbol (r' > r); vertex ids 1-based
                buf.extend(f'e {u} {r * n + c2 + 1}\n' for c2 in range(c + 1, n))
                buf.extend(f'e {u} {r2 * n + c + 1}\n' for r2 in range(r + 1, n))
                cs = col_of[L[r][c]]
                buf.extend(f'e {u} {r2 * n + cs[r2] + 1}\n' for r2 in range(r + 1, n))
            f.write(''.join(buf))
    os.replace(tmp, path)
    return N, m


def main():
    out = sys.argv[1]; os.makedirs(out, exist_ok=True)
    specs = sys.argv[2:] or ['default']
    todo = []
    for sp in specs:
        if sp == 'default':
            todo += [('rnd', *t) for t in DEFAULT] + [('ctl', 3, 4, 1, 0), ('ctl', 2, 6, 2, 0)]
        else:
            kind = 'ctl' if sp.startswith('ctl:') else 'rnd'
            p, d, e, s = map(int, sp.split(':')[-1].split(','))
            todo.append((kind, p, d, e, s))
    for kind, p, d, e, seed in todo:
        name = f"c2stress-{kind}-p{p}-d{d}-e{e}-s{seed}"
        path = os.path.join(out, name)
        if os.path.exists(path):
            print(f"{name}: exists, skipped", flush=True)
            continue
        B = extraspecial_beta(p, d, e) if kind == 'ctl' else random_beta(p, d, e, seed)
        L = table(p, d, e, B)
        z, cm, cls2 = check(L)
        print(f"{name}: order {len(L)}, |Z| = {z}, |[G,G]| (sampled) = {cm}, [G,G] <= Z: {cls2}", flush=True)
        if not cls2:
            raise SystemExit(f"{name}: not class 2")
        N, m = write_latin_graph(L, path)
        print(f"   wrote {name}: N = {N}, m = {m}", flush=True)


if __name__ == '__main__':
    main()
