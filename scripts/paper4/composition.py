#!/usr/bin/env python3
"""Explicit coset-count (bits) of nested Split-or-Johnson calls (CLOSURE_BOUND_SPEC, 2026-10-12), numeric check of the
closed forms. One call on a domain of size m (alpha = 2/3, Design-Lemma parameter a = 2, our accounting of HBD Thm 5.3):
  f(m) = log2 m + 6 log2 m * R(m) + log2(v*(m)!),   R(m) = ceil(log_{3/2}(m / v*(m)))  (costing rounds)
  v*(m) = min{ v : a ln m / ln v + 1 <= v^{1-1/a}  and  4 ceil(a ln m / ln v) <= v }      (Lemma RChW*)
Branch shapes (Lemma N): (a) nu0 calls at size n; (b) polynomial shrink m -> m^gamma; (c) constant-factor shrink
m -> (2/3) m down to c0 = 8. Prints bits and bits / L^k for the leading-term comparison.
Usage: composition.py [a] [alpha]"""
import sys, math
A = float(sys.argv[1]) if len(sys.argv) > 1 else 2.0
ALPHA = float(sys.argv[2]) if len(sys.argv) > 2 else 2 / 3
C0 = 8
def vstar(m):
    v = 2
    while True:
        l = A * math.log(m) / math.log(v)
        if l + 1 <= v ** (1 - 1 / A) and 4 * math.ceil(l) <= v: return v
        v += 1
def f(m):
    if m <= C0: return math.lgamma(m + 1) / math.log(2)
    v = min(vstar(m), m); L = math.log2(m)
    R = max(0, math.ceil(math.log(m / v) / math.log(1 / ALPHA)))
    return L + (2 * A + 2) * L * R + math.lgamma(v + 1) / math.log(2)
def shrink_c(n):
    s, m = 0.0, float(n)
    while m > C0: s += f(m); m *= ALPHA
    return s + f(C0)
def shrink_b(n, gamma):
    s, m = 0.0, float(n)
    while m > C0: s += f(m); m = m ** gamma
    return s
lead1 = (2 * A + 2) / math.log2(1 / ALPHA)          # per call: lead1 * L^2
lead3 = lead1 / (3 * math.log2(1 / ALPHA))           # case (c): lead3 * L^3
print(f"a = {A}, alpha = {ALPHA:.4f}: per call ~ {lead1:.2f} L^2, case (c) ~ {lead3:.2f} L^3, "
      f"case (b) gamma=1/2 ~ {lead1 / (1 - 0.25):.2f} L^2")
print(f"{'n':>8} {'L':>6} {'v*':>4} {'f(n) bits':>10} {'f/L^2':>6} {'(b) bits':>9} {'(b)/L^2':>7} {'(c) bits':>10} {'(c)/L^3':>7}")
for e in (3, 4, 6, 9, 12, 18, 30, 60):
    n = 10 ** e; L = math.log2(n)
    fb, bb, cb = f(n), shrink_b(n, 0.5), shrink_c(n)
    print(f"{'1e' + str(e):>8} {L:6.1f} {vstar(n):4d} {fb:10.0f} {fb / L**2:6.2f} {bb:9.0f} {bb / L**2:7.2f} {cb:10.0f} {cb / L**3:7.2f}")

# --- Giant case (2026-10-12), HBD App. A eq. (13), our bit accounting. One giant reduction on a quotient Alt(m),
# x = log2 m, string length n (L_n = log2 n), test-set size k = floor(L_n) + 3 (Babai Thm 10.1.3 threshold):
#   c(x, L_n) = k * x  [aggregation branching log2 m + Design Lemma (k-1) log2 m]  +  f(2^x)  [Split-or-Johnson]
# CRUDE (eq. 13 as HBD use it: m <= n, rho <= 2L): 2L reductions at full price c(L, L), then halvings c(L-j, L-j).
# REFINED (HBD A.1: after a reduction the next quotient has <= m/2 blocks (wreath case) or ~sqrt(2m) (Johnson), or the
# group becomes intransitive without large orbits (n halves); a fully reduced quotient of x bits sends the recursion into
# blocks of size n/m, i.e. n shrinks by x bits). Along a path x is non-increasing (r_i never grow, HBD p. 41), every
# QUOTIENT step lowers x by >= 1 and every SHRINK step (halving / certificate call) lowers L_n by >= 1, x <= L_n. So
# quotient steps visit distinct x <= L at k <= L + 3, shrink steps distinct L_n <= L:
#   REFINED (rigorous) = sum_{x=1}^{L} c(x, L) + sum_{u=1}^{L} c(u, u).
if __name__ == '__main__':
    def c(x, Ln): k = math.floor(Ln) + 3; return k * x + f(2.0 ** x)
    print()
    print("giant case (a = %.1f, alpha = %.4f): bits / L^3" % (A, ALPHA))
    print(f"{'n':>8} {'L':>6} {'crude':>12} {'/L^3':>6} {'refined':>12} {'/L^3':>6} {'comb (c)':>10} {'total crude':>12} {'total ref':>10}")
    for e in (3, 6, 9, 12, 18, 30, 60):
        n = 10 ** e; L = math.log2(n); Li = int(round(L))
        crude = 2 * L * c(L, L) + sum(c(L - j, L - j) for j in range(Li))
        ref = sum(c(x, L) for x in range(1, Li + 1)) + sum(c(u, u) for u in range(1, Li + 1))
        comb = shrink_c(n)
        print(f"{'1e' + str(e):>8} {L:6.1f} {crude:12.0f} {crude / L**3:6.2f} {ref:12.0f} {ref / L**3:6.2f} "
              f"{comb / L**3:10.2f} {(crude + comb) / L**3:12.2f} {(ref + comb) / L**3:10.2f}")
    print("closed forms (a=2, alpha=2/3): crude 2*11.26 + 11.26/3 = 26.3; refined (1/2 + 10.26/3) + 11.26/3 = 3.92 + 3.75 = 7.67; comb 5.84")

# --- Giant case with BABAI's ratios (2026-10-12, check of H1-H3). Step types along a branch (x = log2 m, u = log2 n):
#  Q_soj : Split-or-Johnson -> equipartition / Johnson on the dominant class: x drops >= 1 (Babai eq. 43, m' < m/2)
#          cost k x + f(2^x)          [Design Lemma on k-ary structure + Split-or-Johnson]
#  Q_agg : AggregateCertificates colored 4/5-partition, dominant class kept as the new Gamma: x drops >= log2(5/4)
#          cost k x                   [individualise the test set: m^k, Thm 10.2.1 case 1]
#  S_soj : no dominant class after Split-or-Johnson: all windows <= 2n/3 (Lemma 5.2.1, eq. 42): u drops >= log2(3/2)
#          cost k u + f(2^u) (+ log2 m from the factor m in eq. 42)
#  S_agg : 4/5-partition without dominant class: u drops >= log2(5/4), cost k u
# x is non-increasing between chain ends (HBD H2, tower inherited), so quotient steps visit x-values spaced by their drop;
# shrink steps visit u-values spaced by their drop. Upper bound = sum of the four worst-case sums.
if __name__ == '__main__':
    def spaced(top, step):   # values top, top - step, ... > 0
        v = top
        while v > 0: yield v; v -= step
    def kx(x, u): return (math.floor(u) + 3) * x
    print()
    print("giant case, Babai ratios: bits / L^3")
    print(f"{'n':>8} {'Q_soj':>6} {'Q_agg':>6} {'S_soj':>6} {'S_agg':>6} {'giant':>6} {'comb':>6} {'TOTAL':>6}")
    for e in (6, 12, 30, 60, 200):
        n = 10 ** e; L = math.log2(n)
        q1 = sum(kx(x, L) + f(2.0 ** x) for x in spaced(L, 1.0))
        q2 = sum(kx(x, L) for x in spaced(L, math.log2(5 / 4)))
        s1 = sum(kx(u, u) + f(2.0 ** u) + u for u in spaced(L, math.log2(3 / 2)))
        s2 = sum(kx(u, u) for u in spaced(L, math.log2(5 / 4)))
        comb = shrink_c(n); g = q1 + q2 + s1 + s2
        print(f"{'1e' + str(e):>8} " + " ".join(f"{v / L**3:6.2f}" for v in (q1, q2, s1, s2, g, comb, g + comb)))
    l23, l54 = math.log2(3 / 2), math.log2(5 / 4)
    print(f"closed forms: Q_soj 1/2 + 10.26/3 = 3.92, Q_agg 1/(2*{l54:.3f}) = {1/(2*l54):.2f}, "
          f"S_soj 11.26/(3*{l23:.3f}) = {11.26/(3*l23):.2f}, S_agg 1/(3*{l54:.3f}) = {1/(3*l54):.2f}; comb 5.84")

# --- Units (2026-10-12). For GRAPHS on v vertices the string domain is Omega = pairs (|Omega| ~ v^2, Babai sec. 1):
# window u starts at 2 L_v, the giant degree x <= L_v (giants act on vertices / blocks of vertices), k = floor(u) + 3
# (Unaffected Stabiliser Theorem: n0 = largest orbit ON OMEGA). Cost of every step k x + f(2^x) with x <= min(L_v, u).
if __name__ == '__main__':
    print()
    print("graphs: bits / L_v^3 (Omega = pairs, u0 = 2 L_v, x <= L_v)")
    print(f"{'v':>8} {'Q_soj':>6} {'Q_agg':>6} {'S_soj':>6} {'S_agg':>6} {'giant':>6} {'chain':>6} {'TOTAL':>6} {'/L_Om^3':>8}")
    for e in (6, 12, 30, 60, 200):
        v = 10 ** e; L = math.log2(v); U = 2 * L
        q1 = sum(kx(x, U) + f(2.0 ** x) for x in spaced(L, 1.0))
        q2 = sum(kx(x, U) for x in spaced(L, math.log2(5 / 4)))
        s1 = sum(kx(min(L, u), u) + f(2.0 ** min(L, u)) + min(L, u) for u in spaced(U, math.log2(3 / 2)))
        s2 = sum(kx(min(L, u), u) for u in spaced(U, math.log2(5 / 4)))
        comb = shrink_c(v); g = q1 + q2 + s1 + s2
        print(f"{'1e' + str(e):>8} " + " ".join(f"{t / L**3:6.2f}" for t in (q1, q2, s1, s2, g, comb, g + comb))
              + f" {(g + comb) / U**3:8.2f}")
