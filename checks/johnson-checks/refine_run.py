import random, itertools
from refine_check import run
from n2k import setup
random.seed(11)
for k in [4,5,6]:
    n,V,nb=setup(k)
    for r in [3,4]:
        for t in range(3): run(k,random.sample(V,r),"random")
        for _ in range(20000):
            R=random.sample(V,r); lab={}
            for x in range(n): m=tuple(x in S for S in R); lab[m]=lab.get(m,0)+1
            if all(lab.get(tuple(not b for b in m),0)==c for m,c in lab.items()): run(k,R,"symmetric (searched)"); break
k=8; pts=[m for m in itertools.product((0,1),repeat=5) if sum(m)%2==0]
roots=[frozenset(j for j,m in enumerate(pts) if m[i]) for i in range(5)]
run(k,roots,"5 roots, triples symmetric")
