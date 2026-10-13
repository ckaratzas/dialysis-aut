#!/usr/bin/env python3
"""d_k of Lemma L3 (CLOSURE_BOUND_SPEC, 2026-10-11), diagnostic only. Along the greedy root path (split_classify, GREEDY
env) at every level with mu > MU0, for every 1-WL class C (|C| >= 5) the STAR group S(C) = Aut(G[C] + the sets N(y) cap C,
y in each other class D, as hyperedges coloured by D) acting on C -- GAP/GRAPE (nauty) -- and its non-abelian
composition factors. d_k = the largest Alt(t) factor over the classes of the level (0 = all solvable / no Alt).
(The first version measured L(C) and E(C,D) separately; both are inflated by free coordinates / perfect matchings.)
Usage: local_groups.py WORKDIR GRAPH...   (orders printed as log10)"""
import sys, os, subprocess
sys.path.insert(0, os.path.dirname(__file__))
os.environ.setdefault('GREEDY', '8')
import split_classify as sc
from collections import Counter, defaultdict
W = sys.argv[1]; os.makedirs(W, exist_ok=True)
MU0 = int(os.environ.get('MU0', '16')); CAP_E = int(os.environ.get('PER_LEVEL_EDGES', '400'))
GAP_HDR = '''LoadPackage("grape");; SetPrintFormattingStatus("*stdout*", false);;
nab := function(G) local cs, i, r, info, out; out := [];
  if IsSolvableGroup(G) then return out; fi;
  cs := CompositionSeries(G);
  for i in [1..Length(cs)-1] do r := Size(cs[i]) / Size(cs[i+1]);
    if not IsPrimeInt(r) then info := IsomorphismTypeInfoFiniteSimpleGroup(r);
      if info = fail then Add(out, Concatenation("order ", String(r))); else Add(out, info.name); fi; fi; od;
  return out; end;;
orbrun := function(lv, gam, n, fix) local A, col, o, id, i;
  col := Concatenation(List(fix, x -> [x]), [Difference([1..n], fix)]); col := Filtered(col, c -> Length(c) > 0);
  A := AutGroupGraph(gam, col); id := ListWithIdenticalEntries(n, 0);
  for o in Orbits(A, [1..n]) do for i in o do id[i] := o[1]; od; od;
  AppendTo(OUTF, "ORB ", lv, " | ", id, "\\n"); return A; end;;
truerun := function(lv, cid, A, pts)   # composition factors of the TRUE group Aut(G)_(roots) acting on class pts
  AppendTo(OUTF, "TRU ", lv, " ", cid, " | ", nab(Action(A, pts)), "\\n"); end;;
run := function(tag, N, edges, colouring, pts) local gam, A, B;
  gam := EdgeOrbitsGraph(Group(()), edges, N);
  A := AutGroupGraph(gam, colouring); B := Action(A, pts);
  AppendTo(OUTF, "RES ", tag, " | ", LogInt(Size(B), 10), " | ", nab(B), "\\n"); end;;
'''
def gap_struct(tag, n_nodes, edges, colouring, pts):
    e = ",".join(f"[{a+1},{b+1}],[{b+1},{a+1}]" for a, b in edges)
    c = ",".join("[" + ",".join(str(v + 1) for v in cl) + "]" for cl in colouring)
    return f'run("{tag}", {n_nodes}, [{e}], [{c}], [{",".join(str(v + 1) for v in pts)}]);\n'
def level_structs(nb, col, lv):
    """One structure per class C (|C| >= 5): the STAR of C = G[C] plus, for every other class D, the distinct sets
    N(y) cap C (y in D; empty and all-of-C dropped) as hyperedge nodes coloured by D. Its automorphism group acting on
    C is the ambient group S(C) of Lemma L3 (every isomorphism respects the star)."""
    cls = defaultdict(list)
    for v, c in enumerate(col): cls[c].append(v)
    out = []
    for C, cv in cls.items():
        if len(cv) < 5: continue
        idx = {x: i for i, x in enumerate(cv)}; N = len(cv); colouring = [list(range(N))]
        edges = [(idx[x], idx[y]) for x in cv for y in nb[x] if y in idx and x < y]
        for D, dv in cls.items():
            if D == C: continue
            hs = {frozenset(idx[w] for w in nb[y] if w in idx) for y in dv}
            hs = [h for h in hs if 0 < len(h) < len(cv)]
            if not hs: continue
            ids = list(range(N, N + len(hs))); colouring.append(ids)
            for b, h in zip(ids, hs): edges.extend((x, b) for x in h)
            N += len(hs)
        out.append(gap_struct(f"S {lv} {len(cv)} {C}", N, edges, colouring, range(len(cv))))
    return out, 0, False
def alt_deg(name):   # GAP: "A(t)" alternating; "A(n,q)" etc. Lie type (returned as None, reported by name)
    s = name.strip().strip('"'); head = s.split('~')[0].strip()
    if head.startswith('A(') and head.endswith(')') and head[2:-1].isdigit(): return int(head[2:-1])
    return None
def orbits(f, fix, tag):   # Traces orbits of Aut(G)_(fix) -- ORACLE ONLY (as orbit_levels.py), memory-capped JVM
    out = os.path.join(W, f'orb-{tag}.txt'); log = os.path.join(W, f'orb-{tag}.log')
    env = dict(os.environ, TR_FILE=f, TR_FIX=",".join(map(str, fix)), OUT=out, FLOOR_MB='1000')
    rc = subprocess.run(['scripts/safe_java_test.sh', f'orb{os.getpid()}', '700', 'dialysis.experimental.TracesOracle',
                         'tracesOrbits', log], env=env, stdout=subprocess.DEVNULL).returncode
    if rc != 0 or not os.path.exists(out): return None
    lines = open(out).read().split('\n'); os.remove(out)
    return [int(x) for x in lines[1].split()]
ORB = os.environ.get('ORBITS') == '1'
for f in sys.argv[2:]:
    nb = sc.load(f); sc.TRACE = []; sc.ROOTS = []; p = sc.path(nb, cap=200); cols, roots = sc.TRACE, sc.ROOTS
    name = os.path.basename(f); gfile = os.path.join(W, f"lg-{name}.g"); levels = []
    resf = os.path.join(W, f"lg-{name}.res"); open(resf, 'w').close()
    with open(gfile, 'w') as g:
        g.write(f'OUTF := "{resf}";;\n' + GAP_HDR)
        for i in range(1, len(p) - 1):
            if p[i][0] <= MU0: continue   # level 0 skipped: the star is G itself (Aut(G)), not informative
            g.writelines(level_structs(nb, cols[i], i)[0]); levels.append(i)
        if ORB:   # orbits of Aut(G)_(roots) per level, nauty via GRAPE -- ORACLE ONLY
            e = ",".join(f"[{a+1},{b+1}],[{b+1},{a+1}]" for a in range(len(nb)) for b in nb[a] if a < b)
            g.write(f"GAM := EdgeOrbitsGraph(Group(()), [{e}], {len(nb)});;\n")
            for i in levels:
                g.write(f"AL := orbrun({i}, GAM, {len(nb)}, [{','.join(str(r + 1) for r in roots[:i])}]);;\n")
                cl = defaultdict(list)
                for v, c in enumerate(cols[i]): cl[c].append(v + 1)
                for c, pts in cl.items():
                    if len(pts) >= 5: g.write(f"truerun({i}, {c}, AL, [{','.join(map(str, pts))}]);\n")
        g.write("QUIT;\n")
    r = subprocess.run(['timeout', os.environ.get('GAP_TIMEOUT', '1800'), 'gap', '-q', '-o', '2g', gfile],
                       stdin=subprocess.DEVNULL, capture_output=True, text=True)
    res = defaultdict(list)   # level -> [(class id, size, Alt degrees, other non-abelian names)]
    orbs = {}; merged = []   # AppendTo wraps long lines: glue continuation lines back on
    for line in open(resf).read().splitlines():
        if line.startswith(('RES ', 'ORB ', 'TRU ')) or not merged: merged.append(line)
        else: merged[-1] = merged[-1].rstrip('\\') + line
    tru = {}   # (level, class id) -> max Alt degree of the true action
    for line in merged:
        if line.startswith('TRU '):
            hd, fac = line[4:].split('|', 1); lv, cid = map(int, hd.split())
            names = [x.strip().strip('"') for x in fac.strip(' []').split('",') if x.strip()]
            tru[(lv, cid)] = max([t for t in map(alt_deg, names) if t], default=0); continue
        if line.startswith('ORB '):
            lv, ids = line[4:].split('|'); orbs[int(lv)] = [int(x) for x in ids.strip(' []').replace(' ', '').split(',')]
            continue
        if not line.startswith('RES '): continue
        tag, order, fac = [x.strip() for x in line[4:].split('|')]
        _, lv, size, cid = tag.split()
        names = [x.strip().strip('"') for x in fac.strip('[] ').split('",') if x.strip()]
        alts = [t for t in map(alt_deg, names) if t]; other = [nm for nm in names if not alt_deg(nm)]
        res[int(lv)].append((int(cid), int(size), alts, other))
    print(f"{name}: n={len(nb)} depth={len(p)-1} gap_rc={r.returncode}", flush=True)
    for i in levels:
        items = res[i]; dk = max([max(a) for _, _, a, _ in items if a], default=0)
        oth = Counter(nm for _, _, _, o in items for nm in o)
        line = f"  level {i:2d} mu {p[i][0]:5d} | {len(items)} classes, d_k = {dk:3d}"
        if oth: line += f" other simple: {dict(oth.most_common(3))}"
        if ORB and dk >= 5:
            orb = orbs.get(i)
            if orb is None: line += " | orbits: oracle failed"
            else:
                def is_orbit(cid): return len({orb[v] for v in range(len(nb)) if cols[i][v] == cid}) == 1
                ref = [max(a) for cid, _, a, _ in items if a and not is_orbit(cid)]
                orbd = [max(a) for cid, _, a, _ in items if a and is_orbit(cid)]
                tref = [tru.get((i, cid), -1) for cid, _, a, _ in items if a and not is_orbit(cid)]
                line += (f" | at orbit classes: {max(orbd, default=0)}, at NON-orbit classes: d_ref = {max(ref, default=0)}"
                         f" (true action there: {max(tref, default=0)})")
        print(line, flush=True)
    if r.returncode != 0: print("  GAP rc", r.returncode, r.stderr[-300:], flush=True)
