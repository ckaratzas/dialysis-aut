# J(2k,k): which polynomial identities suffice? Functions: monomials in psi_S, psi_R, psi_Q of degree <= d and their images
# under A (and A applied to products with the degree-<=d monomials, one more level). Compare their joint level sets with
# the true orbit partition (intersection vectors, merged under sigma o complementation when that fixes the roots).
import itertools, random, collections
def setup(k):
    n=2*k; V=[frozenset(c) for c in itertools.combinations(range(n),k)]; idx={v:i for i,v in enumerate(V)}
    nb=[[idx[(v-{x})|{y}] for x in v for y in range(n) if y not in v] for v in V]
    return n,V,nb
def orbits(n,k,V,roots):
    lab={}
    for x in range(n): lab.setdefault(tuple(x in S for S in roots),[]).append(x)
    keys=sorted(lab); A=[frozenset(lab[m]) for m in keys]; vec=lambda v: tuple(len(v&a) for a in A)
    flip={m:tuple(not b for b in m) for m in keys}
    sym=all(flip[m] in lab and len(lab[flip[m]])==len(lab[m]) for m in keys)
    pos={m:i for i,m in enumerate(keys)}
    out=[]
    for v in V:
        a=vec(v)
        if sym: b=tuple(len(lab[flip[m]])-a[pos[flip[m]]] for m in keys); a=min(a,b)
        out.append(a)
    return out,sym
def partition_of(funcs,N): return [tuple(f[i] for f in funcs) for i in range(N)]
def same(p,q):
    m={}; r={}
    return all(m.setdefault(a,b)==b and r.setdefault(b,a)==a for a,b in zip(p,q))
def Aop(f,nb): return [sum(f[u] for u in nb[t]) for t in range(len(nb))]
if __name__=="__main__":
    random.seed(5)
    for k in [4,5,6]:
        n,V,nb=setup(k); N=len(V)
        trials=[]
        for _ in range(4): trials.append(random.sample(V,3))
        # a symmetric triple: |SR|+|SQ|+|RQ|-k = 2|SRQ|
        for _ in range(4000):
            S,R,Q=random.sample(V,3)
            if len(S&R)+len(S&Q)+len(R&Q)-k==2*len(S&R&Q): trials.append([S,R,Q]); break
        for roots in trials:
            orb,sym=orbits(n,k,V,roots)
            psi=[[len(v&S) for v in V] for S in roots]
            res=[]
            for d in [1,2,3,4]:
                mons=[]
                for e in itertools.product(range(d+1),repeat=3):
                    if 0<sum(e)<=d: mons.append([psi[0][i]**e[0]*psi[1][i]**e[1]*psi[2][i]**e[2] for i in range(N)])
                funcs=mons+[Aop(f,nb) for f in mons]
                res.append(same(partition_of(funcs,N),orb))
            print(f"J({n},{k}) roots pairwise {[len(roots[a]&roots[b]) for a,b in [(0,1),(0,2),(1,2)]]} triple {len(roots[0]&roots[1]&roots[2])}"
                  f" symmetric={sym}: orbits {len(set(orb))}; separated with degree<=1..4 (+A): {res}", flush=True)
