# n = 2k, three sets X,Y,Z of size k with ARBITRARY atom sizes s_m (8 atoms, constraints |X|=|Y|=|Z|=k, total 2k).
# T in J(2k,k), a_m = |T cap atom m|. Question: is A(psiX psiY psiZ) = c * psi_Maj + poly(psiX,psiY,psiZ), c != 0 ?
import sympy as sp, itertools
k=sp.Symbol('k')
M=list(itertools.product((0,1),repeat=3))
s={m:sp.Symbol('s'+''.join(map(str,m))) for m in M}
a={m:sp.Symbol('a'+''.join(map(str,m))) for m in M}
# eliminate: s000,s100,s010,s001 via constraints; a000 via sum a = k
free=[s[(1,1,1)],s[(1,1,0)],s[(1,0,1)],s[(0,1,1)]]
eqs=[sum(s.values())-2*k]+[sum(s[m] for m in M if m[i])-k for i in range(3)]
ssol=sp.solve(eqs,[s[(0,0,0)],s[(1,0,0)],s[(0,1,0)],s[(0,0,1)]],dict=True)[0]
S={m:sp.expand(s[m].subs(ssol)) for m in M}
asub={a[(0,0,0)]:k-sum(a[m] for m in M if m!=(0,0,0))}
def A(f):
    tot=0
    for m in M:
        for m2 in M:
            if m==m2: continue
            sh={a[x]:a[x]-int(x==m)+int(x==m2) for x in M}
            tot+=a[m]*(S[m2]-a[m2])*(f.subs(sh,simultaneous=True)-f)
    return sp.expand(tot.subs(asub,simultaneous=True))
psi=lambda pred: sum(a[m] for m in M if pred(m))
p,q,r=psi(lambda m:m[0]),psi(lambda m:m[1]),psi(lambda m:m[2])
maj=psi(lambda m:sum(m)>=2)
P,Q,R,c=sp.symbols('P Q R c')
monos=[P**i*Q**j*R**l for i in range(4) for j in range(4) for l in range(4) if i+j+l<=3]
cs=sp.symbols('b0:%d'%len(monos))
target=A(p*q*r)
expr=sp.expand(target-c*maj.subs(asub)-sum(ci*mo.subs({P:p,Q:q,R:r}) for ci,mo in zip(cs,monos)).subs(asub))
vars_=[a[m] for m in M if m!=(0,0,0)]
eqs=sp.Poly(expr,*vars_).coeffs()
sol=sp.solve(eqs,[c]+list(cs),dict=True)
print("solutions:",len(sol))
for so in sol: print(" c =",sp.factor(so.get(c,c)))
# sanity: is A(pqr) even affected by maj? also check without maj (c=0 forced?)
