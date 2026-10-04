# J(2k,k), two roots S,R with |S cap R| = x. Profile of T: u = |T cap S cap R|, p = |T cap S|, r = |T cap R|.
# Atoms (n = 2k): 11 (size x, count u), 10 (k-x, p-u), 01 (k-x, r-u), 00 (x, k-p-r+u).
# A acts on functions of (u,p,r): (Af) = sum_{m,m'} a_m (s_m' - a_m') f(profile - v_m + v_m').
# Goal: find beta_ij, lambda with  sum beta_ij A(p^i r^j) = lambda*u*(C-u) + q(p,r),  C = x - k + p + r.
import sympy as sp, itertools
k,x,u,p,r=sp.symbols('k x u p r')
atoms={'11':(x,u,(1,1,1)),'10':(k-x,p-u,(0,1,0)),'01':(k-x,r-u,(0,0,1)),'00':(x,k-p-r+u,(0,0,0))}
def A(f):
    tot=0
    for m,(sm,am,vm) in atoms.items():
        for m2,(s2,a2,v2) in atoms.items():
            sh={u:u-vm[0]+v2[0], p:p-vm[1]+v2[1], r:r-vm[2]+v2[2]}
            tot+=am*(s2-a2)*f.subs(sh,simultaneous=True)
    return sp.expand(tot)
D=4
mons=[p**i*r**j for i in range(D+1) for j in range(D+1-i)]
imgs=[A(m) for m in mons]
C=x-k+p+r
betas=sp.symbols('b0:%d'%len(mons)); lam=sp.Symbol('lam')
qdeg=D+2
qmons=[p**i*r**j for i in range(qdeg+1) for j in range(qdeg+1-i)]
qs=sp.symbols('q0:%d'%len(qmons))
expr=sp.expand(sum(b*im for b,im in zip(betas,imgs)) - lam*u*(C-u) - sum(q*m for q,m in zip(qs,qmons)))
eqs=sp.Poly(expr,u,p,r).coeffs()
sol=sp.solve(eqs+[lam-1], list(betas)+list(qs)+[lam], dict=True)
print("solutions:",len(sol))
if sol:
    s0=sol[0]; used={str(m):sp.factor(s0.get(b,b)) for b,m in zip(betas,mons) if s0.get(b,b)!=0}
    print("lambda = 1 achieved with A-image coefficients:"); [print("  ",m,"->",c) for m,c in used.items()]
