"""Computer-algebra checks for the n = 2k part of the Johnson section (paper3, Section 8).

J(n,k) with n = 2k. A vertex T is described by its atom counts a_m = |T cap atom(m)|; the atom sizes s_m are SYMBOLIC.
The adjacency operator acts as (Af)(a) = sum_{m,m'} a_m (s_{m'} - a_{m'}) f(a - e_m + e_{m'})  (T - x + y, x in atom m,
y in atom m'). Each identity below is checked as a polynomial identity in the a_m, the s_m and k.

 (1) Majority lemma (lem:majority): X, Y, Z of size k each; 8 atoms, sizes symbolic subject to |X|=|Y|=|Z|=k and
     sum s_m = 2k:  A(psi_X psi_Y psi_Z) = k psi_Maj + P3(psi_X, psi_Y, psi_Z).
 (2) Remark rem:n2k, first identity: arbitrary X, Y (sizes sx, sy, |X cap Y| = x symbolic):
     A(psi_X psi_Y^2) = 2(|Y| - k) u + P1(psi_X, psi_Y),  u = psi_{X cap Y}.
 (3) Remark rem:n2k, second identity: A(psi_X^2 psi_Y^2) = -4 u^2 + beta(psi_X, psi_Y) u + P2(psi_X, psi_Y).
 (4) Proposition prop:n2k-two: two roots S, R of size k, |S cap R| = x symbolic:
     A(psi_S^2 psi_R^2) = 4 u (C - u) + G(psi_S, psi_R),  C = x - k + psi_S + psi_R,
     and A of every monomial of degree <= 3 in psi_S, psi_R is a polynomial in psi_S, psi_R alone.
Run: python3 check_identities.py   (sympy; a few minutes).
"""
import itertools, sympy as sp
k = sp.Symbol('k')
def A_of(f, atoms, coords):
    """atoms: list of (size, count, vec), vec = how the coordinates change when T gains a point of that atom;
    moving a point of T from atom i to atom j changes the coordinates by vec_j - vec_i."""
    tot = 0
    for (si, ai, vi) in atoms:
        for (sj, aj, vj) in atoms:
            sh = {c: c - di + dj for c, di, dj in zip(coords, vi, vj)}
            tot += ai * (sj - aj) * (f.subs(sh, simultaneous=True) - f)
    return sp.expand(tot)
ok = True
def report(name, cond):
    global ok; ok &= bool(cond); print(f"{'PASS' if cond else 'FAIL'}  {name}")

# ---- (2), (3): two arbitrary sets, coordinates u = psi_{X cap Y}, p = psi_X, q = psi_Y
x, sx, sy, u, p, q = sp.symbols('x sx sy u p q')
V = {'11': (1, 1, 1), '10': (0, 1, 0), '01': (0, 0, 1), '00': (0, 0, 0)}   # (u, p, q) membership
two = [(x, u, V['11']), (sx - x, p - u, V['10']), (sy - x, q - u, V['01']), (2*k - sx - sy + x, k - p - q + u, V['00'])]
e2 = A_of(p*q**2, two, [u, p, q]); P = sp.Poly(e2, u)
report("(2) A(psiX psiY^2): u-degree 1, coefficient 2(|Y|-k)", P.degree() == 1 and sp.simplify(P.coeff_monomial(u) - 2*(sy - k)) == 0)
e3 = A_of(p**2*q**2, two, [u, p, q]); P = sp.Poly(e3, u)
report("(3) A(psiX^2 psiY^2): u-degree 2, u^2 coefficient -4", P.degree() == 2 and sp.simplify(P.coeff_monomial(u**2) + 4) == 0)

# ---- (4): |X| = |Y| = k
two_k = [(x, u, V['11']), (k - x, p - u, V['10']), (k - x, q - u, V['01']), (x, k - p - q + u, V['00'])]
C = x - k + p + q
e4 = A_of(p**2*q**2, two_k, [u, p, q])
report("(4) A(psiS^2 psiR^2) - 4u(C-u) is free of u", sp.Poly(sp.expand(e4 - 4*u*(C - u)), u).degree() <= 0)
low = all(sp.Poly(A_of(p**i*q**j, two_k, [u, p, q]), u).degree() <= 0 for i in range(4) for j in range(4) if 0 < i + j <= 3)
report("(4) A(psiS^i psiR^j), i+j <= 3, free of u", low)

# ---- (1): three sets of size k, eight atoms
M = list(itertools.product((0, 1), repeat=3))
s = {m: sp.Symbol('s' + ''.join(map(str, m))) for m in M}
a = {m: sp.Symbol('a' + ''.join(map(str, m))) for m in M}
cons = [sum(s.values()) - 2*k] + [sum(s[m] for m in M if m[i]) - k for i in range(3)]
ssol = sp.solve(cons, [s[(0,0,0)], s[(1,0,0)], s[(0,1,0)], s[(0,0,1)]], dict=True)[0]
free = [a[m] for m in M if m != (0,0,0)]
a000 = k - sum(free)
vec = lambda m: tuple(int(mm == m) for mm in M if mm != (0,0,0))   # free coordinates = a_m, m != 000
atoms3 = [(sp.expand(s[m].subs(ssol)), a000 if m == (0,0,0) else a[m], vec(m)) for m in M]
psi = lambda pred: sum((a000 if m == (0,0,0) else a[m]) for m in M if pred(m))
pX, pY, pZ = psi(lambda m: m[0]), psi(lambda m: m[1]), psi(lambda m: m[2]); pMaj = psi(lambda m: sum(m) >= 2)
lhs = A_of(sp.expand(pX*pY*pZ), atoms3, free)
X, Y, Z = sp.symbols('X Y Z')
mons = [X**i*Y**j*Z**l for i in range(4) for j in range(4) for l in range(4) if i + j + l <= 3]
cs = sp.symbols('b0:%d' % len(mons))
resid = sp.expand(lhs - k*pMaj - sum(c*mo.subs({X: pX, Y: pY, Z: pZ}) for c, mo in zip(cs, mons)))
sol = sp.solve(sp.Poly(resid, *free).coeffs(), cs, dict=True)
report("(1) A(psiX psiY psiZ) - k psi_Maj is a polynomial in psiX, psiY, psiZ (8 symbolic atom sizes)", len(sol) == 1)
print("ALL PASS" if ok else "SOME CHECK FAILED")
