# Brute-force check of the closed forms used in the hand proofs of Appendix D (Johnson graphs):
#   S1 = sum_{x in T, y notin T} alpha_X                 = k|X| - n psi_X
#   S2 = sum alpha_X alpha_Y                            = k|XnY| + (n-2k) psi_{XnY} - |X| psi_Y - |Y| psi_X + 2 psi_X psi_Y
#   S3 = sum alpha_X alpha_Y alpha_Z                    = k|XYZ| - n psi_XYZ - sum_cyc |XnY| psi_Z + sum_cyc |X| psi_{YnZ}
#   A(psi_X psi_Y psi_Z) = k(n-k) psi_X psi_Y psi_Z + sum_cyc psi_X psi_Y S1(Z) + sum_cyc psi_X S2(Y,Z) + S3
# and, at n = 2k with |X|=|Y|=|Z|=k:  A(psi_X psi_Y psi_Z) - k psi_Maj is the stated polynomial P3; and the u-coefficients
# 2(|Y|-k) in A(psi_X psi_Y^2) and -4 (of u^2) in A(psi_X^2 psi_Y^2), u = psi_{XnY}.
import itertools, random
rnd = random.Random(1)
def A(f, T, n):
    s = 0
    for x in T:
        for y in range(n):
            if y in T: continue
            s += f((T - {x}) | {y})
    return s
bad = 0; checks = 0
for trial in range(400):
    n = rnd.randint(4, 9); k = rnd.randint(1, n-1)
    X, Y, Z = (set(rnd.sample(range(n), rnd.randint(0, n))) for _ in range(3))
    T = set(rnd.sample(range(n), k)); psi = lambda S, U=None: len((U if U is not None else T) & S)
    pX, pY, pZ = psi(X), psi(Y), psi(Z)
    S1 = lambda W: k*len(W) - n*psi(W)
    S2 = lambda V, W: k*len(V & W) + (n-2*k)*psi(V & W) - len(V)*psi(W) - len(W)*psi(V) + 2*psi(V)*psi(W)
    XYZ = X & Y & Z
    S3 = (k*len(XYZ) - n*psi(XYZ) - (len(X&Y)*pZ + len(Y&Z)*pX + len(X&Z)*pY)
          + (len(X)*psi(Y&Z) + len(Y)*psi(X&Z) + len(Z)*psi(X&Y)))
    lhs = A(lambda U: psi(X,U)*psi(Y,U)*psi(Z,U), T, n)
    rhs = k*(n-k)*pX*pY*pZ + pX*pY*S1(Z) + pY*pZ*S1(X) + pX*pZ*S1(Y) + pX*S2(Y,Z) + pY*S2(X,Z) + pZ*S2(X,Y) + S3
    checks += 1; bad += lhs != rhs
    # n = 2k, size-k sets: majority form
    n2 = 2*k
    if n2 >= 2:
        X2, Y2, Z2 = (set(rnd.sample(range(n2), k)) for _ in range(3)); T2 = set(rnd.sample(range(n2), k))
        p = lambda S: len(T2 & S)
        maj = {v for v in range(n2) if (v in X2) + (v in Y2) + (v in Z2) >= 2}
        P3 = (k*k*p(X2)*p(Y2)*p(Z2)
              + sum(p(a)*p(b)*(k*k - 2*k*p(c)) for a, b, c in ((X2,Y2,Z2),(Y2,Z2,X2),(X2,Z2,Y2)))
              + sum(p(a)*(k*len(b & c) - k*p(b) - k*p(c) + 2*p(b)*p(c)) for a, b, c in ((X2,Y2,Z2),(Y2,X2,Z2),(Z2,X2,Y2)))
              + k*len(X2 & Y2 & Z2) - (len(X2&Y2)*p(Z2) + len(Y2&Z2)*p(X2) + len(X2&Z2)*p(Y2)))
        checks += 1; bad += A(lambda U: len(U&X2)*len(U&Y2)*len(U&Z2), T2, n2) != k*p(maj) + P3
print(f'{checks} checks, {bad} failures')
