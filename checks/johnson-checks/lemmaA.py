# Lemma A for J(n,k): colour refinement with individualised k-sets S_1..S_j  ==  partition by intersection vectors with
# the atoms of S_1..S_j (= orbits of the pointwise stabiliser in S_n).  Checked for random and adversarial root sequences.
import itertools, random, sys
def johnson(n,k):
    V=[frozenset(c) for c in itertools.combinations(range(n),k)]
    idx={v:i for i,v in enumerate(V)}
    adj=[[] for _ in V]
    for i,v in enumerate(V):
        for x in v:
            for y in range(n):
                if y not in v:
                    w=(v-{x})|{y}; adj[i].append(idx[w])
    return V,adj
def refine(adj,col):
    k=len(set(col))
    while True:
        sig={}; new=[0]*len(col)
        for v in range(len(col)):
            key=(col[v],tuple(sorted(col[w] for w in adj[v])))
            new[v]=sig.setdefault(key,len(sig))
        if len(sig)==k: return new
        col,k=new,len(sig)
def atoms(n,roots):
    lab={}
    for x in range(n): lab.setdefault(tuple(x in S for S in roots),[]).append(x)
    return [frozenset(a) for a in lab.values()]
def ivec_partition(V,n,roots):
    # orbits of the pointwise stabiliser of the roots in Aut(J(n,k)): S_n preserving every atom; for n = 2k also
    # sigma o complement when sigma can map every atom (membership pattern m) onto the atom of pattern not-m
    k=len(next(iter(V)))
    lab={}
    for x in range(n): lab.setdefault(tuple(x in S for S in roots),[]).append(x)
    keys=sorted(lab); A=[frozenset(lab[m]) for m in keys]
    vec=lambda v: tuple(len(v & a) for a in A)
    if n!=2*k or not roots: return [vec(v) for v in V]
    flip={m:tuple(not b for b in m) for m in keys}
    if any(flip[m] not in lab or len(lab[flip[m]])!=len(lab[m]) for m in keys): return [vec(v) for v in V]
    pos={m:i for i,m in enumerate(keys)}
    def g(vv):   # intersection vector of sigma(complement(T)): |T' cap atom(m)| = |atom(not m)| - |T cap atom(not m)|
        return tuple(len(lab[flip[m]])-vv[pos[flip[m]]] for m in keys)
    out=[]
    for v in V:
        a=vec(v); b=g(a); out.append(min(a,b))
    return out
def same_partition(p,q):
    m={}; r={}
    for a,b in zip(p,q):
        if m.setdefault(a,b)!=b or r.setdefault(b,a)!=a: return False
    return True
random.seed(1)
cases=[(8,2),(10,2),(12,2),(16,2),(9,3),(10,3),(12,3),(14,3),(10,4),(11,4),(12,4),(13,4),(8,4),(10,5),(11,5),(12,6)]
total=0; bad=0
for n,k in cases:
    V,adj=johnson(n,k); N=len(V)
    seqs=[]
    for _ in range(6): seqs.append(random.sample(range(N),min(8,N)))
    # adversarial: nested-overlap chains (each root shares k-1 points with the previous), and disjoint roots
    s=[V.index(frozenset(range(k)))]
    for t in range(1,min(8,n-k+1)): s.append(V.index(frozenset(list(range(k-1))+[k-1+t])))
    seqs.append(s)
    seqs.append([V.index(frozenset(range(i*k,(i+1)*k))) for i in range(n//k)][:8])
    for sq in seqs:
        for j in range(len(sq)+1):
            roots=[V[i] for i in sq[:j]]
            col=[0]*N
            for t,i in enumerate(sq[:j]): col[i]=t+1
            r=refine(adj,col); iv=ivec_partition(V,n,roots)
            total+=1
            if not same_partition(r,iv):
                bad+=1; print(f"MISMATCH J({n},{k}) prefix {j}: refinement {len(set(r))} classes vs orbits {len(set(iv))}")
    print(f"J({n},{k}) N={N}: {len(seqs)} sequences checked", flush=True)
print(f"TOTAL prefixes checked {total}, mismatches {bad}")
