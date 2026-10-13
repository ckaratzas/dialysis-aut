#!/usr/bin/env python3
"""Certificate size t* (CLOSURE_BOUND_SPEC, 2026-10-12), diagnostic only. Input: local_groups.py's .res files (star
groups S(C) + nauty orbits, ORBITS=1). At every level k with a NON-orbit class C whose star group has a large Alt
factor (the 'star looseness' classes), take test sets T subset C, |T| = t, and compute the LOCAL CERTIFICATE
  X_{T,r} = G[ball of radius r around T], vertices coloured by the level-k colouring, T split off as its own cell,
  full(T, r) <=> Aut(X_{T,r}) induces Alt(T) or Sym(T) on T (|action| >= t!/2).
Only structure within distance r of T is used (no global group). t*(r) = the least t with every sampled T non-full.
GAP/GRAPE (nauty). Usage: tstar.py WORKDIR(lg dir) GRAPH...   env: TS_MAXT (6), TS_NS (samples, 8), TS_LEVELS (3),
TS_MINALT (10), TS_MINLV (0), TS_R ("1,2").
TS_PAIRS=1 (2026-10-12): test sets are t BLOCKS of the star group's maximal block system on C (the giant's domain when
S(C) is imprimitive, e.g. chh: Z_2 wr S_d on d pairs); full <=> Alt/Sym induced on the t blocks.
TS_COL=local: the certificate's colouring is strictly local -- T one cell, the roots that fall inside the ball as
singletons, everything else one cell (nauty's refinement then does 1-WL on the ball itself). Default TS_COL=level."""
import sys, os, subprocess, random, math
sys.path.insert(0, os.path.dirname(__file__))
os.environ.setdefault('GREEDY', '8')
import split_classify as sc
from collections import defaultdict
W = sys.argv[1]
MAXT = int(os.environ.get('TS_MAXT', '6')); NS = int(os.environ.get('TS_NS', '8'))
NLEV = int(os.environ.get('TS_LEVELS', '3')); MINALT = int(os.environ.get('TS_MINALT', '10'))
RADII = [int(x) for x in os.environ.get('TS_R', '1,2').split(',')]
HDR = '''LoadPackage("grape");;
cert := function(tag, N, edges, col, T) local A;
  A := AutGroupGraph(EdgeOrbitsGraph(Group(()), edges, N), col);
  AppendTo(OUTF, "CERT ", tag, " | ", Size(Action(A, T, OnSets)), "\\n"); end;;
blk := function(tag, N, edges, colouring, pts, d) local A, B, sys;   # block system of S(C) on C with d blocks (the giant's domain)
  A := AutGroupGraph(EdgeOrbitsGraph(Group(()), edges, N), colouring); B := Action(A, pts);
  if not IsTransitive(B, [1..Length(pts)]) then AppendTo(OUTF, "BLK ", tag, " | intransitive\\n"); return; fi;
  if Length(pts) = d then AppendTo(OUTF, "BLK ", tag, " | points\\n"); return; fi;
  sys := Filtered(AllBlocks(B), b -> Length(b) * d = Length(pts));
  if sys = [] then AppendTo(OUTF, "BLK ", tag, " | none\\n"); return; fi;
  AppendTo(OUTF, "BLK ", tag, " | ", List(Orbit(B, Set(sys[1]), OnSets), x -> List(x)), "\\n"); end;;
'''
PAIRS = os.environ.get('TS_PAIRS') == '1'; CONTROL = os.environ.get('TS_CONTROL') == '1';  # CONTROL: ORBIT classes instead (real giant -> must be full)
LOCAL = os.environ.get('TS_COL') == 'local'
def star_struct(nb, col, c):   # as local_groups.level_structs, one class; returns (N, edges, colouring) 0-based
    cls = defaultdict(list)
    for v, x in enumerate(col): cls[x].append(v)
    cv = cls[c]; idx = {x: i for i, x in enumerate(cv)}; N = len(cv); colouring = [list(range(N))]
    edges = [(idx[x], idx[y]) for x in cv for y in nb[x] if y in idx and x < y]
    for D, dv in cls.items():
        if D == c: continue
        hs = {frozenset(idx[w] for w in nb[y] if w in idx) for y in dv}
        hs = [h for h in hs if 0 < len(h) < len(cv)]
        if not hs: continue
        ids = list(range(N, N + len(hs))); colouring.append(ids)
        for b, h in zip(ids, hs): edges.extend((x, b) for x in h)
        N += len(hs)
    return N, edges, colouring, cv
def blocks_of(name, nb, cols, picks):   # {(lv, c): list of blocks (lists of vertices)}
    gfile = os.path.join(W, f"tsb-{name}.g"); outf = os.path.join(W, f"tsb-{name}.res"); open(outf, 'w').close()
    with open(gfile, 'w') as g:
        g.write(f'OUTF := "{outf}";;\n' + HDR); cvs = {}
        for lv, c, d in picks:
            N, edges, colouring, cv = star_struct(nb, cols[lv], c); cvs[(lv, c)] = cv
            e = ",".join(f"[{a+1},{b+1}],[{b+1},{a+1}]" for a, b in edges)
            cl = ",".join("[" + ",".join(str(v + 1) for v in x) + "]" for x in colouring)
            g.write(f'blk("{lv} {c}", {N}, [{e}], [{cl}], [{",".join(str(i + 1) for i in range(len(cv)))}], {d});\n')
        g.write("QUIT;\n")
    subprocess.run(['timeout', '3600', 'gap', '-q', '-o', '4g', gfile], stdin=subprocess.DEVNULL, capture_output=True)
    merged = []
    for line in open(outf).read().splitlines():
        if line.startswith('BLK ') or not merged: merged.append(line)
        else: merged[-1] = merged[-1].rstrip('\\') + line
    out = {}
    for line in merged:
        hd, body = line[4:].split('|', 1); lv, c = map(int, hd.split())
        if 'intransitive' in body or 'none' in body: continue
        if 'points' in body: out[(lv, c)] = [[x] for x in cvs[(lv, c)]]; continue
        bl = eval(body.strip().replace(' ', ''))
        out[(lv, c)] = [[cvs[(lv, c)][i - 1] for i in b] for b in bl]
    return out
def alt_deg(name):
    s = name.strip().strip('"'); head = s.split('~')[0].strip()
    return int(head[2:-1]) if head.startswith('A(') and head.endswith(')') and head[2:-1].isdigit() else None
def parse_res(resf):
    merged = []
    for line in open(resf).read().splitlines():
        if line.startswith(('RES ', 'ORB ', 'TRU ')) or not merged: merged.append(line)
        else: merged[-1] = merged[-1].rstrip('\\') + line
    star, orbs = defaultdict(dict), {}
    for line in merged:
        if line.startswith('ORB '):
            lv, ids = line[4:].split('|'); orbs[int(lv)] = [int(x) for x in ids.strip(' []').replace(' ', '').split(',')]
        elif line.startswith('RES '):
            tag, _, fac = [x.strip() for x in line[4:].split('|')]; _, lv, _, cid = tag.split()
            names = [x.strip().strip('"') for x in fac.strip('[] ').split('",') if x.strip()]
            star[int(lv)][int(cid)] = max([t for t in map(alt_deg, names) if t], default=0)
    return star, orbs
def ball(nb, T, r):
    seen = set(T); front = list(T)
    for _ in range(r):
        nxt = [y for x in front for y in nb[x] if y not in seen]; seen.update(nxt); front = list(dict.fromkeys(nxt))
    return sorted(seen)
for f in sys.argv[2:]:
    name = os.path.basename(f); resf = os.path.join(W, f"lg-{name}.res")
    star, orbs = parse_res(resf)
    nb = sc.load(f); sc.TRACE = []; sc.ROOTS = []; p = sc.path(nb, cap=200); cols = sc.TRACE
    picks = []   # (level, class, star alt degree)
    for lv in sorted(star):
        if lv not in orbs or lv < int(os.environ.get('TS_MINLV', '0')): continue
        cand = [(d, c) for c, d in star[lv].items() if d >= MINALT
                and (len({orbs[lv][v] for v in range(len(nb)) if cols[lv][v] == c}) > 1) != CONTROL]
        if cand: d, c = max(cand); picks.append((lv, c, d))
    picks = picks[:NLEV]
    gfile = os.path.join(W, f"ts-{name}.g"); outf = os.path.join(W, f"ts-{name}.res"); open(outf, 'w').close()
    rng = random.Random(1); roots = sc.ROOTS
    blocks = blocks_of(name, nb, cols, picks) if PAIRS else {}
    with open(gfile, 'w') as g:
        g.write(f'OUTF := "{outf}";;\n' + HDR)
        for lv, c, d in picks:
            C = [v for v in range(len(nb)) if cols[lv][v] == c]
            dom = blocks.get((lv, c)) if PAIRS else None
            if PAIRS and dom is None: print(f"  level {lv} class {c}: no block system (intransitive star)"); continue
            if dom is None: dom = [[x] for x in C]
            rts = set(roots[:lv])
            for t in range(2, min(MAXT, len(dom) - 1) + 1):
                for s in range(NS):
                    TB = rng.sample(dom, t); T = [x for b in TB for x in b]
                    for r in RADII:
                        B = ball(nb, T, r); idx = {x: i + 1 for i, x in enumerate(B)}; Ts = set(T)
                        e = ",".join(f"[{idx[x]},{idx[y]}],[{idx[y]},{idx[x]}]" for x in B for y in nb[x] if y in idx and x < y)
                        cells = defaultdict(list)
                        for x in B: cells[('T',) if x in Ts else ('R', x) if LOCAL and x in rts
                                          else 'rest' if LOCAL else cols[lv][x]].append(idx[x])
                        col = ",".join("[" + ",".join(map(str, v)) + "]" for v in cells.values())
                        g.write(f'cert("{lv} {c} {d} {t} {r} {s} {len(B)}", {len(B)}, [{e}], [{col}], '
                                f'[{",".join("[" + ",".join(str(idx[x]) for x in b) + "]" for b in TB)}]);\n')
        g.write("QUIT;\n")
    rc = subprocess.run(['timeout', os.environ.get('GAP_TIMEOUT', '3600'), 'gap', '-q', '-o', '4g', gfile],
                        stdin=subprocess.DEVNULL, capture_output=True, text=True).returncode
    full = defaultdict(lambda: [0, 0]); bsz = defaultdict(list)
    for line in open(outf):
        if not line.startswith('CERT '): continue
        tag, size = line[5:].split('|'); lv, c, d, t, r, s, nB = map(int, tag.split())
        k = (lv, c, d, r, t); full[k][1] += 1; full[k][0] += int(size) * 2 >= math.factorial(t); bsz[(lv, r)].append(nB)
    print(f"{name}: n={len(nb)} gap_rc={rc} picks={picks}", flush=True)
    for lv, c, d in picks:
        for r in RADII:
            row = [full[(lv, c, d, r, t)] for t in range(2, MAXT + 1)]
            ts = next((t for t, (a, b) in zip(range(2, MAXT + 1), row) if b and a == 0), None)
            bs = bsz[(lv, r)]
            nd = len(blocks[(lv, c)]) if (lv, c) in blocks else sum(1 for v in cols[lv] if v == c)
            print(f"  level {lv:2d} class {c} star Alt({d}) |C|={sum(1 for v in cols[lv] if v == c)} domain={nd} r={r} "
                  f"ball~{sum(bs)//max(1,len(bs))}: full/sampled by t=2..{MAXT}: "
                  + " ".join(f"{a}/{b}" for a, b in row) + f"  -> t*(r={r}) = {ts if ts else '>' + str(MAXT)}", flush=True)
