#!/usr/bin/env python3
"""G2 dichotomy test (CLOSURE_BOUND_SPEC Lemma G, 2026-10-12, diagnostic). For every refutation-level star giant from the
d_k sweep (local_groups.py .res files: class not an orbit of Aut(G)_(roots), star Alt degree >= 5) on the greedy root path:
for r in RADII: ball_r(C) size, condition (R) (C individualised pointwise -> 1-WL on the ball discrete?), and -- via GAP,
in a memory-capped scope -- whether S_r(C) = Aut(G[ball_r(C)], level colouring) on C still has a giant (an orbit of size
>= 5 on which it acts with order >= deg!/2). Branch (i) = some r with (R) and no giant. Usage: dichotomy.py LGDIR OUT GRAPH...
env: RADII (default 1,2), MAXLEV (3 per graph), MAXBALL (skip GAP above this ball size, default 1300)."""
import sys, os, subprocess, re
sys.path.insert(0, os.path.dirname(__file__)); os.environ.setdefault('GREEDY', '8')
import split_classify as sc
from collections import defaultdict
def alt_deg(name):
    s = name.strip().strip('"'); head = s.split('~')[0].strip()
    return int(head[2:-1]) if head.startswith('A(') and head.endswith(')') and head[2:-1].isdigit() else None
def parse_res(resf):   # as tstar.parse_res (tstar runs its main loop on import)
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
from collections import Counter
W, OUT = sys.argv[1], sys.argv[2]
RADII = [int(x) for x in os.environ.get('RADII', '1,2').split(',')]; MAXLEV = int(os.environ.get('MAXLEV', '3')); MAXBALL = int(os.environ.get('MAXBALL', '1300'))
out = open(OUT, 'a')
def ball(nb, C, r):
    seen = set(C); fr = list(C)
    for _ in range(r):
        nx = [w for v in fr for w in nb[v] if w not in seen]; seen.update(nx); fr = list(dict.fromkeys(nx))
    return sorted(seen)
def cond_R(nb, col, C, B):
    idx = {v: i for i, v in enumerate(B)}; sub = [[idx[w] for w in nb[v] if w in idx] for v in B]; inC = set(C)
    keys = [('C', v) if v in inC else ('o', col[v]) for v in B]; ids = {k: i for i, k in enumerate(sorted(set(keys), key=str))}
    c = sc.refine(sub, [ids[k] for k in keys]); cnt = Counter(c)
    return sum(s for s in cnt.values() if s > 1)
def gap_giant(nb, col, C, B):
    idx = {v: i + 1 for i, v in enumerate(B)}
    e = ",".join(f"[{idx[v]},{idx[w]}],[{idx[w]},{idx[v]}]" for v in B for w in nb[v] if w in idx and v < w)
    cells = {}
    for v in B: cells.setdefault(col[v], []).append(idx[v])
    cl = ",".join("[" + ",".join(map(str, x)) + "]" for x in cells.values())
    g = os.path.join(W, 'dich.g')
    with open(g, 'w') as f:
        f.write('LoadPackage("grape");;\n')
        f.write(f'A := AutGroupGraph(EdgeOrbitsGraph(Group(()), [{e}], {len(B)}), [{cl}]);; B := Action(A, [{",".join(str(idx[v]) for v in C)}]);;\n')
        f.write(f'os := Filtered(Orbits(B, [1..{len(C)}]), o -> Length(o) >= 5);;\n')
        f.write('Print("RESULT ", LogInt(Size(B), 10), " ", Length(Orbits(B, [1..' + str(len(C)) + '])), " ", ForAny(os, o -> 2 * Size(Action(B, o)) >= Factorial(Length(o))), "\\n");\nQUIT;\n')
    r = subprocess.run(['systemd-run', '--user', '--scope', '-q', f'--unit=dich{os.getpid()}', '-p', 'MemoryMax=2200M', '-p', 'MemorySwapMax=0',
                        'timeout', '1800', 'gap', '-q', '-o', '1900m', g], stdin=subprocess.DEVNULL, capture_output=True, text=True)
    m = re.search(r'RESULT (\d+) (\d+) (true|false)', r.stdout.replace('\n', ''))
    return (int(m.group(1)), int(m.group(2)), m.group(3) == 'true') if m else None
for f in sys.argv[3:]:
    name = os.path.basename(f); resf = os.path.join(W, f"lg-{name}.res")
    if not os.path.exists(resf): print(name, 'no .res', flush=True); continue
    star, orbs = parse_res(resf)
    nb = sc.load(f); sc.TRACE = []; sc.ROOTS = []; sc.path(nb, cap=200); cols = sc.TRACE
    items = []
    for lv in sorted(star):
        if lv not in orbs: continue
        for c, d in star[lv].items():
            if d >= 5 and len({orbs[lv][v] for v in range(len(nb)) if cols[lv][v] == c}) > 1: items.append((lv, c, d))
    lvs = sorted({lv for lv, _, _ in items})[:MAXLEV]
    for lv, c, d in items:
        if lv not in lvs: continue
        C = [v for v in range(len(nb)) if cols[lv][v] == c]; parts = []
        branch_i = False
        for r in RADII:
            B = ball(nb, C, r); nR = cond_R(nb, cols[lv], C, B)
            gg = gap_giant(nb, cols[lv], C, B) if len(B) <= MAXBALL else None
            parts.append(f"r={r}: ball {len(B)}/{len(nb)} (R):{'yes' if nR == 0 else f'no({nR} undetermined)'} S_r: " +
                         (f"log10 {gg[0]}, {gg[1]} orbits, giant={'YES' if gg[2] else 'no'}" if gg else "skipped"))
            if gg and nR == 0 and not gg[2]: branch_i = True
        line = f"{name} level {lv} class {c} |C|={len(C)} star Alt({d}) | " + " ; ".join(parts) + f" | branch (i): {'YES' if branch_i else 'no'}"
        print(line, flush=True); out.write(line + "\n"); out.flush()
