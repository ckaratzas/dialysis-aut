#!/usr/bin/env python3
"""Per-family comparison with Traces (paper, Section "Comparison with Traces"): joins our Xeon times
(results/xeon-2026-10: series.csv and chain logs) with the uncoloured Traces runs on the same Xeon (traces.csv there, or
results/traces-paper1/gt-*.csv for cfi-rigid and sat_cfi_dim). Run from the repository root: python3 scripts/paper4/traces_compare.py"""
import csv, os, re, statistics, sys
R2 = 'results/xeon-2026-10'; R1 = 'results/traces-paper1'
V1 = {'cfi-rigid-r2': 'r2', 'cfi-rigid-s2': 's2', 'cfi-rigid-t2': 't2', 'cfi-rigid-z2': 'z2', 'cfi-rigid-z3': 'z3',
      'cfi-rigid-d3': 'd3', 'sat_cfi_dim': 'sat_cfi_dim'}
def num(x):
    try: return float(x)
    except: return None
def ours(fam):
    d = os.path.join(R2, fam); o = {}
    p = os.path.join(d, 'series.csv')
    if os.path.exists(p):
        for r in csv.DictReader(open(p)):
            if r['status'] == 'EXACT': o[r['instance']] = (num(r['seconds']), int(r['n_orig'] or 0))
    cd = os.path.join(d, 'chain')
    if os.path.isdir(cd):
        for f in sorted(os.listdir(cd)):
            if not f.endswith('.txt'): continue
            name = f[:-4].rsplit('.', 1)[0]; n = None
            for line in open(os.path.join(cd, f)):
                m = re.match(r'== (\S+) n=(\d+)', line)
                if m: n = int(m.group(2))
                m = re.search(r'\|Aut\| = (\S+)( \(incomplete\))?\s+ours ([\d.]+)s', line)
                if m and not m.group(2) and name not in o: o[name] = (num(m.group(3)), n or 0)
    return o
def traces(fam):
    t = {}
    if fam in V1:
        for r in csv.DictReader(open(os.path.join(R1, f'gt-{V1[fam]}.csv'))):
            ok = r['gt_outcome'] == 'OK'
            t[os.path.basename(r['instance'])] = (num(r['gt_ms']) / 1000, ok, r['gt_outcome'], int(r['n']))
    else:
        p = os.path.join(R2, fam, 'traces.csv')
        if os.path.exists(p):
            for r in csv.DictReader(open(p)):
                ok = r['outcome'] == 'OK'
                s = ((num(r['traces_ms']) or 0) + (num(r['colour_ms']) or 0)) / 1000
                t[os.path.basename(r['instance'])] = (s, ok, r['outcome'], int(r['n']))
    return t
rows = []
for fam in sorted(os.listdir(R2)):
    if not os.path.isdir(os.path.join(R2, fam)): continue
    o = ours(fam); t = traces(fam)
    both = [(o[k][1] or t[k][3], o[k][0], t[k][0]) for k in o if k in t and t[k][1] and o[k][0]]
    fail = [(o[k][1] or t[k][3], o[k][0], t[k][2]) for k in o if k in t and not t[k][1]]
    notrun = [k for k in o if k not in t]
    both.sort()
    nmax = max([b[0] for b in both] + [0])
    # ratio ours/traces, overall and on the largest quarter of the commonly solved instances
    rat = [b[1] / max(b[2], 1e-3) for b in both]
    top = both[len(both) * 3 // 4:]
    rtop = [b[1] / max(b[2], 1e-3) for b in top]
    wins = [b for b in both if b[1] < b[2]]
    print(f"{fam:20s} ours={len(o):5d} both={len(both):5d} trFail={len(fail):3d} notrun={len(notrun):4d} "
          f"n=[{min([b[0] for b in both]+[0])},{nmax}] medR={statistics.median(rat) if rat else 0:8.1f} "
          f"topQ medR={statistics.median(rtop) if rtop else 0:8.1f} trMax={max([b[2] for b in both]+[0]):8.1f} "
          f"ourMax={max([v[0] for v in o.values()]+[0]):8.1f} wins={len(wins)} "
          f"failN={sorted(set(f[0] for f in fail))[:6]} failOursMax={max([f[1] for f in fail]+[0]):.1f} "
          f"outc={sorted(set(f[2] for f in fail))}")

print("\n=== detail by size")
for fam in sorted(os.listdir(R2)):
    if not os.path.isdir(os.path.join(R2, fam)): continue
    o = ours(fam); t = traces(fam)
    recs = []
    for k in o:
        if k not in t: continue
        n = t[k][3]
        recs.append((n, o[k][0], t[k][0] if t[k][1] else None, t[k][2]))
    recs.sort(key=lambda r: (r[0], r[1]))
    # n0: smallest n such that every instance with size >= n0 has ours faster or Traces failing
    n0 = None
    for i in range(len(recs)):
        if all(r[2] is None or r[1] < r[2] for r in recs[i:]): n0 = recs[i][0]; break
    # largest n where Traces is faster
    tf = [r[0] for r in recs if r[2] is not None and r[2] <= r[1]]
    fails = [r for r in recs if r[2] is None]
    sizes = sorted(set(r[0] for r in recs))
    # median ratio ours/traces per size tercile
    def med(rs): 
        x = [r[1] / max(r[2], 1e-3) for r in rs if r[2] is not None]
        return f"{statistics.median(x):.3g}" if x else '-'
    k3 = len(recs) // 3
    tr_big = max([r[2] for r in recs if r[2] is not None] + [0])
    first_fail = min([r[0] for r in fails] + [10**9])
    tr_slow = [r for r in recs if r[2] is not None and r[2] > 60]
    print(f"{fam:18s} N={len(recs):4d} n {sizes[0] if sizes else 0}-{sizes[-1] if sizes else 0} "
          f"medR small/mid/large {med(recs[:k3])}/{med(recs[k3:2*k3])}/{med(recs[2*k3:])} "
          f"TracesFaster up to n={max(tf) if tf else '-'} oursAlways from n={n0} firstTrFail n={first_fail if fails else '-'} "
          f"#fail={len(fails)} trMax={tr_big:.0f}s #tr>60s={len(tr_slow)} oursMaxOnThose={max([r[1] for r in fails+tr_slow]+[0]):.1f}")

print("\n=== table numbers")
for fam in sorted(os.listdir(R2)):
    if not os.path.isdir(os.path.join(R2, fam)): continue
    o = ours(fam); t = traces(fam)
    recs = sorted(((t[k][3], o[k][0], t[k][0] if t[k][1] else None, t[k][2]) for k in o if k in t), key=lambda r: (r[0], r[1]))
    allns = sorted(v[1] for v in o.values())
    nmin_o, nmax_o = (min(allns), max(allns)) if allns else (0, 0)
    # our n from summary if 0
    ok = [r for r in recs if r[2] is not None]
    fails = [r for r in recs if r[2] is None]
    rat = [r[1] / max(r[2], 1e-3) for r in ok]
    k3 = len(ok) * 2 // 3
    rbig = [r[1] / max(r[2], 1e-3) for r in ok[k3:]]
    below = [r for r in ok if not fails or r[0] < min(f[0] for f in fails)]
    rbelow = [r[1] / max(r[2], 1e-3) for r in below]
    from collections import Counter
    print(f"{fam:18s} inst={len(o)} trRun={len(recs)} trN={recs[0][0] if recs else 0}-{recs[-1][0] if recs else 0} "
          f"med={statistics.median(rat) if rat else 0:.0f} medBig={statistics.median(rbig) if rbig else 0:.0f} "
          f"medBelowFail={statistics.median(rbelow) if rbelow else 0:.1f} "
          f"trSlow={max([r[2] for r in ok]+[0]):.1f} ourSlow={max(v[0] for v in o.values()):.1f} "
          f"fails={dict(Counter(f[3] for f in fails))} firstFail={min([f[0] for f in fails]+[0])} oursOnFails={max([f[1] for f in fails]+[0]):.2f} "
          f"failMinS={min([f[1] for f in fails]+[0]):.2f}")

print("\n=== hard families: below / above crossover")
for fam in ['cfi-rigid-r2','cfi-rigid-s2','cfi-rigid-t2','cfi-rigid-z2','cfi-rigid-z3','cfi-rigid-d3','sat_cfi_dim','chh','tnn']:
    o = ours(fam); t = traces(fam)
    recs = sorted(((t[k][3], o[k][0], t[k][0] if t[k][1] else None, t[k][2]) for k in o if k in t), key=lambda r: (r[0], r[1]))
    fails = [r for r in recs if r[2] is None]; ff = min(f[0] for f in fails)
    lo = [r for r in recs if r[0] < ff and r[2] is not None]
    hi = [r for r in recs if r[0] >= ff]
    hi_ok = [r for r in hi if r[2] is not None]
    print(f"{fam}: below n={ff}: {len(lo)} inst, Traces faster on {sum(1 for r in lo if r[2] < r[1])}, med ours/Tr={statistics.median([r[1]/max(r[2],1e-3) for r in lo]):.2f}, "
          f"Tr max {max(r[2] for r in lo):.1f}s ours max {max(r[1] for r in lo):.2f}s | from n={ff}: {len(hi)} inst, Traces failed {len(hi)-len(hi_ok)}, "
          f"answered {len(hi_ok)} (Tr faster on {sum(1 for r in hi_ok if r[2] < r[1])}; Tr med {statistics.median([r[2] for r in hi_ok]) if hi_ok else 0:.0f}s), ours max {max(r[1] for r in hi):.2f}s; "
          f"Traces ran up to n={recs[-1][0]}; ours to n={max(v[1] for v in o.values())}")
