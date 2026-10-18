#!/usr/bin/env python3
"""Independent |Aut P| of a gen_class2_stress group by backtracking over generator images (pure Python).
Usage: aut_group_check.py p,d,e,seed   Prints |Aut P| and |P|^2*6*|Aut P| (= |Aut| of the Latin square graph).
2,4,3,3: 24,576 (= Traces); 2,5,3,1: 32,768 in 13 min."""
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen_class2_stress import random_beta, table
p,d,e,seed = map(int, sys.argv[1].split(','))
L = table(p,d,e,random_beta(p,d,e,seed)); n=len(L)
def gen(S):
    H={0}; fr=[0]
    while fr:
        nf=[]
        for h in fr:
            for s in S:
                y=L[h][s]
                if y not in H: H.add(y); nf.append(y)
        fr=nf
    return H
gens=[]; H={0}
for x in range(n):
    if x not in H: gens.append(x); H=gen(gens)
    if len(H)==n: break
def order(x):
    k=1;y=x
    while y: y=L[y][x]; k+=1
    return k
ords=[order(x) for x in range(n)]
count=0
def extend(phi, k):
    global count
    if k==len(gens):
        count+=1; return
    g=gens[k]
    for x in range(n):
        if ords[x]!=ords[g]: continue
        ph=dict(phi); imgs=[phi.get(gg) for gg in gens[:k]]+[x]
        S=gens[:k+1]; fr=list(ph.keys()) if ph else [0]
        if not ph: ph={0:0}; fr=[0]
        ok=True; fr=list(ph.keys())
        while fr and ok:
            nf=[]
            for h in fr:
                for s,t in zip(S,imgs):
                    y=L[h][s]; z=L[ph[h]][t]
                    if y in ph:
                        if ph[y]!=z: ok=False; break
                    else: ph[y]=z; nf.append(y)
                if not ok: break
            fr=nf
        if ok and len(set(ph.values()))==len(ph): extend(ph,k+1)
extend({0:0},0)
print(f"|P|={n} gens={len(gens)} |Aut P|={count} |P|^2*6*|Aut P|={n*n*6*count:.6g}")
