# Lemma A on J(2k,k): stable 1-WL classes after individualising the roots vs the true orbits of the root stabiliser
# (profile classes, merged under a -> a* when the system is symmetric).
import itertools, random, sys
from n2k import setup, orbits, same
def refine(V,nb,roots):
    col=[0]*len(V); 
    for i,R in enumerate(roots): col[V.index(R)]=i+1
    k_=len(set(col))
    while True:
        sig=[(col[t],tuple(sorted(col[u] for u in nb[t]))) for t in range(len(V))]
        m={}; new=[m.setdefault(s,len(m)) for s in sig]
        if len(m)==k_: return new
        col,k_=new,len(m)
def run(k,roots,tag):
    n,V,nb=setup(k); orb,sym=orbits(n,k,V,roots)
    st=refine(V,nb,roots)
    print(f"J({n},{k}) {tag:28s} roots {len(roots)} symmetric={sym!s:5} orbits {len(set(orb)):5d} stable {len(set(st)):5d} equal={same(st,orb)}",flush=True)
