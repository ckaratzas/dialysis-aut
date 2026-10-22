import json, os
from fit import fits, A
from final import halves
R='results/xeon-2026-10'
out={}
for fam in ['latin','sts','paley','quartic-at','cfi-rigid-r2','cfi-rigid-s2','cfi-rigid-t2','cfi-rigid-z2','cfi-rigid-z3','cfi-rigid-d3','grid','cfi','sat_cfi_dim','quartic-hat','latin-sw','sts-sw','had-sw','mz','rnd-3-reg','had']:
    small=set(open(os.path.join(R,fam,'stage1_small.txt')).read().split())
    p=[(r['n'],r['total_secs']) for r in A[fam] if r['solver']=='series' and r['instance'] in small and r['total_secs']>0]
    nd=len(set(x[0] for x in p))
    nl=sum(1 for r in A[fam] if r['solver']=='series' and r['instance'] not in small)
    if nd>=4:
        f=fits([x[0] for x in p],[x[1] for x in p]); lo,hi=halves(p)
        out[fam]=dict(N=len(p),nd=nd,nmin=min(x[0] for x in p),nmax=max(x[0] for x in p),excl=nl,lo=lo,hi=hi,**f)
        print(f"{fam:12s} N={len(p)} excl_large={nl} n={out[fam]['nmin']}-{out[fam]['nmax']} b={f['b']:.2f}({f['r2p']:.3f}) c={f['c']:.3f}({f['r2q']:.3f}) curv={f['curv']:+.2f} lo/hi={lo and round(lo,2)}/{hi and round(hi,2)}")
    else: print(fam,'thin',nd,nl)
json.dump(out,open('warm.json','w'),default=float)
