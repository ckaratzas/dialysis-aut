# Multipede construction and colour refinement rounds (shared by the checks).
# Coloured multipedes R(G) (Neuen-Schweitzer): pairs F(w), gadgets M(v) = {m_B : B subset N(v), |B| even},
# m_B ~ a(w) if w in B else b(w). Input colouring: every F(w), M(v) its own class (base discrete).
# Test: candidate sets T_C of the solver for C = M(v), base b = m_{emptyset}: (1) translations, (2) a group,
# (3) equal to the predicted subspace {D : orientation propagation of D from N(v) through cl^1 is consistent}.
import random, itertools, hashlib, sys
def build(nV,nW,r,rng):
    while True:
        N=[sorted(rng.sample(range(nW),r)) for _ in range(nV)]
        if all(any(w in N[v] for v in range(nV)) for w in range(nW)): return N
def graph(N,nW,par=None):
    # par[v] in {0,1}: parity of the gadget sets (twisted multipede); default all even
    vid={}; adj=[]; col=[]
    def add(key,c): vid[key]=len(adj); adj.append([]); col.append(c)
    for w in range(nW): add(('a',w),('F',w)); add(('b',w),('F',w))
    for v,Nv in enumerate(N):
        for k in range(par[v] if par else 0,len(Nv)+1,2):
            for B in itertools.combinations(Nv,k): add(('m',v,frozenset(B)),('M',v))
    for key,i in list(vid.items()):
        if key[0]=='m':
            _,v,B=key
            for w in N[v]: j=vid[('a',w)] if w in B else vid[('b',w)]; adj[i].append(j); adj[j].append(i)
    return vid,adj,col
H=lambda s: hashlib.blake2b(repr(s).encode(),digest_size=8).hexdigest()
def rounds(adj,col,ind,T=None):
    c=[H(('init',col[i])) for i in range(len(adj))]
    for k,i in enumerate(ind): c[i]=H(('ind',k))
    hist=[c]; k=len(set(c)); t=0
    while True:
        c=[H((c[i],tuple(sorted(c[j] for j in adj[i])))) for i in range(len(adj))]; t+=1; hist.append(c)
        kk=len(set(c))
        if T is None and kk==k: return hist, t-1   # stable round = last round that changed the partition
        if T is not None and t>=T: return hist, T
        k=kk
def closure(N,start):
    K=set(start); ch=True
    while ch:
        ch=False
        for Nv in N:
            if len(set(Nv)-K)==1: K|=set(Nv); ch=True
    return K
