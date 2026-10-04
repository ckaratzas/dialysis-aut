# Lemma B for J(n,k): simulate the chain's root rule (smallest refined class in the current part, lowest vertex;
# peel from the root; continue in the largest remainder; largest class when no remainder) and track, per depth,
# the atoms, the largest class and the greedy base length of every class (by Lemma A: classes = intersection vectors).
import itertools, random, sys, collections
def johnson(n,k,perm):
    V=[frozenset(c) for c in itertools.combinations(range(n),k)]
    V=[V[i] for i in perm]                        # random vertex numbering (ties are broken by the lowest number)
    idx={v:i for i,v in enumerate(V)}
    adj=[[] for _ in V]
    for i,v in enumerate(V):
        for x in v:
            for y in range(n):
                if y not in v: adj[i].append(idx[(v-{x})|{y}])
    return V,adj
def classes(V,n,roots):
    lab={}
    for x in range(n): lab.setdefault(tuple(x in S for S in roots),[]).append(x)
    A=[frozenset(a) for a in lab.values()]
    return [tuple(len(v & a) for a in A) for v in V], sorted(len(a) for a in A)
def peel(adj,part,r):
    P=set(part); dist={r:0}; q=collections.deque([r]); layers=[[r]]
    while q:
        x=q.popleft()
        for y in adj[x]:
            if y in P and y not in dist:
                dist[y]=dist[x]+1; q.append(y)
                if len(layers)<=dist[y]: layers.append([])
                layers[dist[y]].append(y)
    T={r}
    for i in range(1,len(layers)):
        prev={v for v in layers[i-1] if v in T}
        for v in layers[i]:
            if sum(1 for w in adj[v] if w in prev)==1: T.add(v)
    O={v for v in P-T if all(w in T for w in adj[v] if w in P)}
    rest=P-T-O; comps=[]; seen=set()
    for s in sorted(rest):
        if s in seen: continue
        c=[]; st=[s]; seen.add(s)
        while st:
            x=st.pop(); c.append(x)
            for y in adj[x]:
                if y in rest and y not in seen: seen.add(y); st.append(y)
        comps.append(c)
    return comps
def base_len(V,n,roots,members):
    # greedy: individualise class members (lowest first) until all members have distinct intersection vectors
    b=0; extra=[]
    while True:
        iv,_=classes([V[i] for i in members],n,roots+extra)
        if len(set(iv))==len(members): return b
        # pick the member whose individualisation splits the class most
        best=None
        for i in members[:60]:
            iv2,_=classes([V[j] for j in members],n,roots+extra+[V[i]])
            sc=len(set(iv2))
            if best is None or sc>best[0]: best=(sc,i)
        extra.append(V[best[1]]); b+=1
        if b>40: return b
def run(n,k,seed,maxdepth=40):
    N=len(list(itertools.combinations(range(n),k))); perm=list(range(N)); random.Random(seed).shuffle(perm)
    V,adj=johnson(n,k,perm)
    roots=[]; part=list(range(N)); gen=False; first=None; rows=[]
    for d in range(maxdepth+1):
        iv,atomsz=classes(V,n,roots)
        cl=collections.defaultdict(list)
        for v in range(N): cl[iv[v]].append(v)
        nonsing=[c for c in cl.values() if len(c)>1]
        mb=max((base_len(V,n,roots,c) for c in nonsing),default=0)
        rows.append((d,len(cl),max(len(c) for c in cl.values()),mb,atomsz))
        if mb<=6 and first is None: first=d
        if not nonsing: break
        # next root (chain rule)
        inpart=collections.defaultdict(list)
        for v in part: inpart[iv[v]].append(v)
        cands=[c for c in inpart.values() if len(c)>1] or nonsing
        c=max(cands,key=lambda c:(len(c),-min(c))) if gen else min(cands,key=lambda c:(len(c),min(c)))
        r=min(c); roots.append(V[r])
        comps=peel(adj,part,r)
        gen=not comps
        if comps: part=max(comps,key=len)
    return first,rows
cases=[(14,2),(22,2),(30,2),(12,3),(16,3),(20,3),(11,4),(13,4),(14,4),(11,5)]
for n,k in cases:
    outs=[run(n,k,s) for s in range(3)]
    firsts=[o[0] for o in outs]
    d,ncl,maxc,mb,at=outs[0][1][min(outs[0][0],len(outs[0][1])-1)]
    print(f"J({n},{k}) N={len(list(itertools.combinations(range(n),k))):5}  first depth with base<=12 (3 numberings): {firsts}  at that depth: classes {ncl}, largest {maxc}, max base {mb}, atoms {at}", flush=True)
print("---- depth-by-depth (numbering 0): depth, classes, largest class, max base, atom sizes")
for n,k in [(30,2),(20,3),(14,4)]:
    first,rows=run(n,k,0)
    print(f"J({n},{k}) first depth with base<=6: {first}")
    for d,ncl,maxc,mb,at in rows[:(first or 0)+2]: print(f"   depth {d:2}: classes {ncl:4} largest {maxc:5} max base {mb:2} atoms {at}")
