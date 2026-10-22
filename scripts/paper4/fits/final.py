import json, numpy as np, csv
from fit import fits, A
def pts(fam, sub, key, extra=None):
    out=[]
    for r in A[fam]:
        if not r['solved']: continue
        if sub and r['solver']!=sub: continue
        v=r.get(key)
        if v is None or v<=0: continue
        out.append((r['n'],v))
    return out
def halves(p):
    ns=sorted(set(x[0] for x in p)); med=ns[len(ns)//2]
    lo=[x for x in p if x[0]<=med]; hi=[x for x in p if x[0]>=med]
    def b(q):
        if len(set(x[0] for x in q))<3: return None
        return fits([x[0] for x in q],[x[1] for x in q])['b']
    return b(lo), b(hi)
def depth(fam, sub):
    rs=[r for r in A[fam] if r['solved'] and r['solver']==sub]
    if sub=='chain':
        rs=[r for r in rs if r.get('chain_depth') is not None]
        if not rs: return '-'
        big=max(rs,key=lambda r:(r['n'],r['chain_depth'])); sm=min(rs,key=lambda r:r['n'])
        mx=max(rs,key=lambda r:r['chain_depth'])
        return f"k* {sm['chain_depth']}@{sm['n']} -> {big['chain_depth']}@{big['n']} (max {mx['chain_depth']}@{mx['n']}); maxBase {max(r.get('max_base_chain',0) for r in rs)}"
    else:
        mx=max(rs,key=lambda r:(r['max_base'],r['n']))
        big=[r for r in rs if r['n']==max(x['n'] for x in rs)]
        return f"base {mx['max_base']}@{mx['n']}, {max(r['max_base'] for r in big)}@{big[0]['n']}; dfs<={max(r['dfs_nodes'] for r in rs)}"
rows=[]
spec=[('latin','series','total_secs','seconds (series)'),
('sts','series','total_secs','seconds (series)'),
('had','chain','work','groupWork (chain)'),('had','chain','work_uncapped','uncapped groupWork'),('had',None,'total_secs','seconds (all)'),
('pg','chain','work','groupWork (chain)'),('pg','chain','work_uncapped','uncapped groupWork'),('pg','chain','total_secs','seconds (chain)'),
('pp','chain','work','groupWork (chain)'),('pp','chain','work_uncapped','uncapped groupWork'),('pp','chain','total_secs','seconds (chain)'),
('ag','chain','work','groupWork (chain)'),('ag','chain','work_uncapped','uncapped groupWork'),('ag','chain','total_secs','seconds (chain)'),
('cmz','chain','work','groupWork (chain)'),('cmz','chain','total_secs','seconds (chain)'),
('chh','chain','work','groupWork (chain)'),('chh','chain','work_uncapped','uncapped groupWork'),('chh','chain','total_secs','seconds (chain)'),
('quartic-at','chain','work','groupWork (chain)'),('quartic-at','chain','total_secs','seconds (chain)'),('quartic-at','series','total_secs','seconds (series)'),
('johnson','chain','work','groupWork (chain)'),('johnson','chain','work_uncapped','uncapped groupWork'),('johnson','chain','total_secs','seconds (chain)'),
('hypercube','chain','work','groupWork (chain)'),('hypercube','chain','work_uncapped','uncapped groupWork'),('hypercube','chain','total_secs','seconds (chain)'),
('paley','chain','work','groupWork (chain)'),('paley','chain','total_secs','seconds (chain)'),('paley','series','total_secs','seconds (series)'),
]+[(f,'series','total_secs','seconds (series)') for f in ['cfi-rigid-r2','cfi-rigid-s2','cfi-rigid-t2','cfi-rigid-z2','cfi-rigid-z3','cfi-rigid-d3']] + [
('lattice','chain','work','groupWork (chain)'),('lattice','chain','work_uncapped','uncapped groupWork'),('triang','chain','work','groupWork (chain)'),('triang','chain','work_uncapped','uncapped groupWork'),
('grid-w','chain','work','groupWork (chain)'),('grid-w',None,'total_secs','seconds (all)'),('tnn','chain','total_secs','seconds (chain)'),
('grid','series','total_secs','seconds (series)'),('cfi','series','total_secs','seconds (series)'),('sat_cfi_dim','series','total_secs','seconds (series)'),
('rnd-3-reg','series','total_secs','seconds (series)'),('quartic-hat','series','total_secs','seconds (series)'),('quartic-hog','series','total_secs','seconds (series)'),
('mz','series','total_secs','seconds (series)'),('mz','series','dfs_nodes','dfs_nodes (series)'),('mz-aug2','series','dfs_nodes','dfs_nodes (series)'),
('latin-sw','series','total_secs','seconds (series)'),('sts-sw','series','total_secs','seconds (series)'),('had-sw','series','total_secs','seconds (series)')]
for fam,sub,key,lab in spec:
    p=pts(fam,sub,key)
    nd=len(set(x[0] for x in p))
    tot=sum(1 for r in A[fam] if r['solved'] and (sub is None or r['solver']==sub))
    capped=sum(1 for r in A[fam] if r['solver']=='chain' and r.get('capped_levels',0)>0) if sub=='chain' else 0
    row=dict(fam=fam,lab=lab,N=len(p),tot=tot,nd=nd,nmin=min(x[0] for x in p) if p else 0,nmax=max(x[0] for x in p) if p else 0,capped=capped,
             depth=depth(fam, sub or 'series') if (sub or 'series') in ('chain','series') else '')
    if nd>=4:
        f=fits([x[0] for x in p],[x[1] for x in p]); row.update(f)
        row['lo'],row['hi']=halves(p)
    rows.append(row)
json.dump(rows,open('rows.json','w'),default=float)
for r in rows:
    if 'b' in r:
        better = 'tie' if abs(r['r2p']-r['r2q'])<0.01 else ('quasi' if r['r2q']>r['r2p'] else 'power')
        print(f"{r['fam']:12s}|{r['lab']:20s}|{r['N']}/{r['tot']}|{r['nmin']}-{r['nmax']} ({r['nd']})|b={r['b']:.2f} ({r['r2p']:.3f})|c={r['c']:.3f} ({r['r2q']:.3f})|{better}|curv {r['curv']:+.2f}|lo/hi {r['lo'] and round(r['lo'],2)}/{r['hi'] and round(r['hi'],2)}|capped {r['capped']}|{r['depth']}")
    else:
        print(r['fam'],r['lab'],r['N'],r['nd'],'TOO THIN')
