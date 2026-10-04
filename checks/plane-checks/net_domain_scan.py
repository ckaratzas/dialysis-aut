# For every vertex of every instance the chain ran on (bipartite graphs only: the net filters are off otherwise),
# compare the implementation's old net check (isNet / relPlaneInv: no remainder, one slice, >= 3 branches of equal size
# q >= 2, q^2 orphans, every orphan meets every branch exactly once) with the full net condition (additionally: for
# every two branches, distinct orphans have distinct attachment pairs, i.e. two attachments in different branches share
# exactly one orphan), which is what makes every R_x a bijection. Projective planes are skipped: their slices are full
# nets (Proposition net). Prints instances where the old check passes on a vertex whose slice is not a full net.
import sys, os, collections
def load(path):
    E = []; n = 0
    for line in open(path):
        if line.startswith('e '):
            _, a, b = line.split(); E.append((int(a), int(b)))
        elif line.startswith('p '): n = int(line.split()[2])
    lo = min(min(e) for e in E); hi = max(max(e) for e in E)
    if lo == 1 and hi == n: E = [(a-1, b-1) for a, b in E]
    adj = [[] for _ in range(n)]
    for a, b in E: adj[a].append(b); adj[b].append(a)
    return n, adj
def bipartite(n, adj):
    col = [-1]*n
    for s in range(n):
        if col[s] >= 0: continue
        col[s] = 0; st = [s]
        while st:
            x = st.pop()
            for y in adj[x]:
                if col[y] < 0: col[y] = 1 - col[x]; st.append(y)
                elif col[y] == col[x]: return False
    return True
def is_plane(n, adj):
    deg = {len(a) for a in adj}
    if len(deg) != 1: return False
    q = deg.pop() - 1
    return q >= 2 and n == 2*(q*q+q+1)
def check(n, adj, s):
    depth = {s: 0}; parent = {}; T = {s}; layer = [s]; nonadm = []; d = 0; orph = []
    while layer:
        nxt = []
        for x in layer:
            for y in adj[x]:
                if y not in depth: depth[y] = d+1; nxt.append(y)
        d += 1
        newnon = []
        for y in nxt:
            ps = [p for p in adj[y] if depth.get(p) == d-1 and p in T]
            if len(ps) == 1: T.add(y); parent[y] = ps[0]
            else: newnon.append(y)
        for u in nonadm:                          # all neighbours of u now classified
            if any(w not in T for w in adj[u]): return (False, False)   # remainder
            orph.append(u)
        nonadm = newnon; layer = nxt
    for u in nonadm:
        if any(w not in T for w in adj[u]): return (False, False)
        orph.append(u)
    # slices: components of orphans-of-one-layer + attachments
    bylayer = collections.defaultdict(list)
    for o in orph: bylayer[depth[o]].append(o)
    nslices = 0
    for L, os_ in bylayer.items():
        seen = set(); oset = set(os_)
        for o in os_:
            if o in seen: continue
            nslices += 1; st = [o]; seen.add(o)
            while st:
                x = st.pop()
                nb = adj[x] if x in oset else [w for w in adj[x] if w in oset]
                for y in nb:
                    if (y in oset or x in oset) and y not in seen: seen.add(y); st.append(y)
    if nslices != 1: return (False, False)
    children = sorted(v for v in T if depth[v] == 1); k = len(children)
    if k < 3: return (False, False)
    br = {c: i for i, c in enumerate(children)}
    for v in sorted(T, key=lambda v: depth[v]):
        if depth[v] >= 2: br[v] = br[parent[v]]
    sizes = [0]*k
    for v in T:
        if depth[v] >= 2: sizes[br[v]] += 1
    q = sizes[0]
    if q < 2 or any(x != q for x in sizes) or len(orph) != q*q: return (False, False)
    att = []
    for o in orph:
        hit = [None]*k
        for w in adj[o]:
            if w not in br or depth[w] < 2 or hit[br[w]] is not None: return (False, False)
            hit[br[w]] = w
        if any(h is None for h in hit): return (False, False)
        att.append(hit)
    full = all(len({(a[X], a[Y]) for a in att}) == len(att) for X in range(k) for Y in range(X+1, k))
    return (True, full)
G = sys.argv[1]; R = sys.argv[2]; fams = sys.argv[3:]
tot = collections.Counter(); bad = []
for fam in fams:
    p = os.path.join(R, fam, 'chain_done.txt')
    if not os.path.exists(p): continue
    for line in open(p):
        name = line.split()[0]; path = os.path.join(G, fam, name)
        if not os.path.exists(path): tot['missing'] += 1; continue
        n, adj = load(path); tot['instances'] += 1
        if not bipartite(n, adj): tot['nonbipartite'] += 1; continue
        if is_plane(n, adj): tot['plane_skipped'] += 1; continue
        tot['scanned'] += 1; old = full = 0
        for s in range(n):
            o, f = check(n, adj, s); old += o; full += o and f
        tot['old_pass'] += old; tot['full_pass'] += full
        if old != full: bad.append((fam, name, old, full))
        if old: print(fam, name, 'old net check passes on', old, 'vertices; full nets', full, flush=True)
print(dict(tot)); print('instances where the old check passes on a non-net:', bad)
