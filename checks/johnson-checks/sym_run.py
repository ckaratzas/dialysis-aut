import random
from refine_check import run
from n2k import setup
random.seed(23)
def symmetric_search(n,V,r,tries=200000):
    for _ in range(tries):
        R=random.sample(V,r); lab={}
        for x in range(n): m=tuple(x in S for S in R); lab[m]=lab.get(m,0)+1
        if all(lab.get(tuple(not b for b in m),0)==c for m,c in lab.items()): return R
def symmetric_build(n,k,r):
    # build directly: random self-dual atom structure. pick k "half" points, pair x<->x+k, root i = for each pair choose side
    for _ in range(1000):
        R=[]
        for i in range(r):
            S=frozenset(x if random.random()<.5 else x+k for x in range(k)); R.append(S)
        if len(set(R))==r: return R
for k,rs in [(6,[5]),(7,[3,4,5])]:
    n,V,nb=setup(k)
    for r in rs:
        R=symmetric_search(n,V,r,40000)
        if R: run(k,R,"symmetric (searched)")
        for t in range(2): run(k,symmetric_build(n,k,r),"symmetric (paired build)")
