# General X, Y subsets of [n] (sizes sx, sy, |X cap Y| = x), n = 2k. Profile: u = psi_{X cap Y}, p = psi_X, q = psi_Y.
import sympy as sp
k,x,sx,sy,u,p,q=sp.symbols('k x sx sy u p q')
n=2*k
atoms={'11':(x,u,(1,1,1)),'10':(sx-x,p-u,(0,1,0)),'01':(sy-x,q-u,(0,0,1)),'00':(n-sx-sy+x,k-p-q+u,(0,0,0))}
def A(f):
    tot=0
    for m,(sm,am,vm) in atoms.items():
        for m2,(s2,a2,v2) in atoms.items():
            sh={u:u-vm[0]+v2[0], p:p-vm[1]+v2[1], q:q-vm[2]+v2[2]}
            tot+=am*(s2-a2)*f.subs(sh,simultaneous=True)
    return sp.expand(tot)
for name,f in [("A(psiX psiY)",p*q),("A(psiX psiY^2)",p*q**2),("A(psiX^2 psiY)",p**2*q),("A(psiX^2 psiY^2)",p**2*q**2)]:
    P=sp.Poly(A(f),u)
    print(name, " u-degree", P.degree(), "; coefficients of u^d:")
    for d in range(P.degree(),0,-1): print("   u^%d:"%d, sp.factor(P.coeff_monomial(u**d)))
