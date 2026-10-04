import random, itertools
from refine_check import refine
from n2k import setup
from sym_run import symmetric_build
random.seed(7)
for k,r in [(5,3),(6,4),(6,5),(7,4)]:
    n,V,nb=setup(k); R=symmetric_build(n,k,r); st=refine(V,nb,R)
    pat=lambda x: tuple(x in S for S in R)
    pairs={}; 
    for x in range(n):
        m=pat(x); key=min(m,tuple(not b for b in m)); pairs.setdefault(key,[set(),set()])[0 if m==key else 1].add(x)
    P=list(pairs.values())
    w=lambda T,p: len(T&p[0])+len(T&p[1])-len(p[0]); dl=lambda T,p: len(T&p[0])-len(T&p[1])
    ok_d=ok_w=True; nonconst_w=0; cls={}
    for i,T in enumerate(V): cls.setdefault(st[i],[]).append(T)
    for c,Ts in cls.items():
        f=lambda T:(tuple(dl(T,p) for p in P), tuple(w(T,p)*w(T,q) for p in P for q in P))
        vals={f(T) for T in Ts}; ok_d&=len({v[0] for v in vals})==1; ok_w&=len({v[1] for v in vals})==1
        nonconst_w+=len({tuple(w(T,p) for p in P) for T in Ts})>1
    print(f"J({n},{k}) {r} roots, {len(P)} pairs: delta const on classes {ok_d}, w_p*w_q const {ok_w}; classes where w itself varies (sign flip): {nonconst_w}/{len(cls)}")
