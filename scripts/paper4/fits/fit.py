import json, math, sys
import numpy as np
from collections import defaultdict

A = json.load(open('scripts/paper4/fits/all.json'))


def linfit(x, y):
    X = np.vstack([np.ones_like(x), x]).T
    coef, res, *_ = np.linalg.lstsq(X, y, rcond=None)
    yhat = X @ coef
    ss_res = float(((y - yhat) ** 2).sum()); ss_tot = float(((y - y.mean()) ** 2).sum())
    r2 = 1 - ss_res / ss_tot if ss_tot > 0 else float('nan')
    rmse = math.sqrt(ss_res / len(y))
    return coef, r2, rmse


def fits(ns, cs):
    ns = np.array(ns, float); cs = np.array(cs, float)
    L = np.log2(ns); Y = np.log2(cs)
    (a1, b), r2p, ep = linfit(L, Y)
    (a2, c), r2q, eq = linfit(L ** 2, Y)
    # 3-parameter: Y = a + b L + c L^2  (curvature sign)
    X = np.vstack([np.ones_like(L), L, L ** 2]).T
    co3, *_ = np.linalg.lstsq(X, Y, rcond=None)
    return dict(b=b, r2p=r2p, rmse_p=ep, c=c, r2q=r2q, rmse_q=eq, curv=co3[2], b3=co3[1])


def worst_per_n(ns, cs):
    d = defaultdict(float)
    for n, c in zip(ns, cs):
        d[n] = max(d[n], c)
    k = sorted(d)
    return k, [d[x] for x in k]


def run(fam, subset, measure, label, minval=None):
    rs = [r for r in A[fam] if r['solved'] and (subset is None or r['solver'] == subset)]
    pts = []
    for r in rs:
        v = measure(r)
        if v is None: continue
        if v <= 0: continue
        pts.append((r['n'], v))
    nd = len(set(p[0] for p in pts))
    out = dict(family=fam, subset=subset or 'all', measure=label, N=len(pts), distinct=nd,
               nmin=min(p[0] for p in pts) if pts else None, nmax=max(p[0] for p in pts) if pts else None,
               zero_dropped=len(rs) - len(pts))
    if nd >= 4:
        out.update(fits([p[0] for p in pts], [p[1] for p in pts]))
        wn, wc = worst_per_n([p[0] for p in pts], [p[1] for p in pts])
        w = fits(wn, wc)
        out['b_worst'] = w['b']; out['r2p_worst'] = w['r2p']; out['c_worst'] = w['c']; out['r2q_worst'] = w['r2q']
    return out


def depthinfo(fam):
    rs = [r for r in A[fam] if r['solved']]
    ch = [r for r in rs if r['solver'] == 'chain' and r.get('chain_depth') is not None]
    se = [r for r in rs if r['solver'] == 'series']
    s = {}
    if ch:
        mx = max(ch, key=lambda r: (r['chain_depth'], r['n']))
        big = max(ch, key=lambda r: r['n'])
        sm = min(ch, key=lambda r: r['n'])
        s['chain_depth'] = (min(r['chain_depth'] for r in ch), mx['chain_depth'], mx['n'], sm['n'], sm['chain_depth'], big['n'], big['chain_depth'])
        s['chain_maxbase'] = max(r.get('max_base_chain', 0) for r in ch)
        s['capped'] = sum(1 for r in ch if r.get('capped_levels', 0) > 0)
        s['capped_levels_max'] = max(r.get('capped_levels', 0) for r in ch)
    if se:
        mx = max(se, key=lambda r: (r['max_base'], r['n']))
        s['series_maxbase'] = (mx['max_base'], mx['n'])
        s['series_dfs_max'] = max(r['dfs_nodes'] for r in se)
    return s

if __name__ == '__main__':
    work = lambda r: r.get('work')
    secs = lambda r: r.get('total_secs')
    dfs = lambda r: r.get('dfs_nodes')
    queries = lambda r: r.get('queries')
    res = []
    for fam in sorted(A):
        for sub, meas, lab in [('chain', work, 'chain groupWork'), ('chain', secs, 'seconds'),
                               ('series', secs, 'seconds'), ('series', dfs, 'dfs_nodes'), (None, secs, 'seconds')]:
            o = run(fam, sub, meas, lab)
            if o['N'] == 0: continue
            res.append(o)
        res.append(dict(family=fam, depth=depthinfo(fam)))
    json.dump(res, open('scripts/paper4/fits/fits.json', 'w'), default=float, indent=0)
    for o in res:
        if 'depth' in o:
            print('   depth', o['depth']); continue
        if 'b' in o:
            print(f"{o['family']:18s} {o['subset']:6s} {o['measure']:16s} N={o['N']:5d} d={o['distinct']:4d} n={o['nmin']}-{o['nmax']} drop0={o['zero_dropped']} "
                  f"b={o['b']:.2f}(R2 {o['r2p']:.3f}) c={o['c']:.3f}(R2 {o['r2q']:.3f}) curv={o['curv']:+.3f} | worst b={o['b_worst']:.2f}({o['r2p_worst']:.3f}) c={o['c_worst']:.3f}({o['r2q_worst']:.3f})")
        else:
            print(f"{o['family']:18s} {o['subset']:6s} {o['measure']:16s} N={o['N']:5d} d={o['distinct']} n={o['nmin']}-{o['nmax']} (too few sizes)")
