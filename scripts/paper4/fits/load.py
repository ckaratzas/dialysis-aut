import csv, glob, os, re, json, sys
ROOT = 'results/xeon-2026-10'

dep_re = re.compile(r'depth (\d+): roots=\[([^\]]*)\] refinedClasses=(\d+) .*?ours=(\S+) .*?maxT=(\d+) maxBase=(\d+) groupWork=(\d+)')
hdr_re = re.compile(r'^== (\S+) n=(\d+)')
fin_re = re.compile(r'\|Aut\| = (\S+)\s+ours ([\d.]+)s')
q_re = re.compile(r'two-sided queries in total: (\d+)')
orb_re = re.compile(r'orbit of r\d+=\d+: (\d+) of (\d+) candidates, (\d+) two-sided')


def parse_chain(path):
    d = dict(path=path, depths=[], n=None, final=None, secs=None, queries=0, cands=0, component=False)
    for line in open(path, errors='replace'):
        m = hdr_re.match(line.strip())
        if m:
            d['n'] = int(m.group(2)); continue
        m = dep_re.search(line)
        if m:
            roots = [x for x in m.group(2).split(',') if x.strip()]
            d['depths'].append(dict(depth=int(m.group(1)), nroots=len(roots), status=m.group(4),
                                    maxT=int(m.group(5)), maxBase=int(m.group(6)), work=int(m.group(7))))
            continue
        m = fin_re.search(line)
        if m:
            d['final'] = m.group(1); d['secs'] = float(m.group(2)); continue
        m = q_re.search(line)
        if m:
            d['queries'] += int(m.group(1)); continue
        m = orb_re.search(line)
        if m:
            d['cands'] += int(m.group(2))
        if 'component type' in line or 'combination:' in line:
            d['component'] = True
    return d


def load_family(fam):
    rows = list(csv.DictReader(open(os.path.join(ROOT, fam, 'series.csv'))))
    out = []
    chains = {}
    for p in glob.glob(os.path.join(ROOT, fam, 'chain', '*.txt')):
        c = parse_chain(p)
        name = os.path.basename(p)
        inst = re.sub(r'\.(wl1|pi|wl2|auto)\.txt$', '', name)
        chains.setdefault(inst, []).append(c)
    for r in rows:
        inst = r['instance']
        rec = dict(family=fam, instance=inst, n=int(r['n_orig']), m=int(r['m_orig']),
                   series_status=r['status'], series_secs=float(r['seconds'] or 0),
                   dfs_nodes=int(r['dfs_nodes'] or 0), max_base=int(r['max_base'] or 0),
                   max_T=int(float(r['max_T'] or 0)))
        if r['status'] == 'EXACT':
            rec['solver'] = 'series'; rec['solved'] = True
            rec['total_secs'] = rec['series_secs']
        else:
            cs = chains.get(inst, [])
            cs = [c for c in cs if c['final'] is not None]
            if cs:
                c = cs[0]
                rec['solver'] = 'chain'; rec['solved'] = True
                rec['chain'] = c
                rec['total_secs'] = rec['series_secs'] + c['secs']
                if c['depths']:
                    rec['work'] = sum(x['work'] for x in c['depths'])
                    ex = [x for x in c['depths'] if x['status'] == 'EXACT']
                    rec['chain_depth'] = ex[-1]['nroots'] if ex else None
                    rec['capped_levels'] = sum(1 for x in c['depths'] if x['status'].startswith('STOP_TIME'))
                    rec['max_base_chain'] = max(x['maxBase'] for x in c['depths'])
                    rec['work_uncapped'] = sum(x['work'] for x in c['depths'] if not x['status'].startswith('STOP_TIME'))
                rec['queries'] = c['queries']
                rec['component'] = c['component']
            else:
                rec['solver'] = None; rec['solved'] = False
        out.append(rec)
    seen = set(r['instance'] for r in rows)
    for inst, cs in chains.items():
        if inst in seen: continue
        cs = [c for c in cs if c['final'] is not None]
        if not cs: 
            out.append(dict(family=fam, instance=inst, n=None, solved=False, solver=None)); continue
        c = cs[0]
        rec = dict(family=fam, instance=inst, n=c['n'], m=None, series_status='NONE', series_secs=0.0,
                   dfs_nodes=0, max_base=0, max_T=0, solver='chain', solved=True, chain=c, total_secs=c['secs'])
        if c['depths']:
            rec['work'] = sum(x['work'] for x in c['depths'])
            ex = [x for x in c['depths'] if x['status'] == 'EXACT']
            rec['chain_depth'] = ex[-1]['nroots'] if ex else None
            rec['capped_levels'] = sum(1 for x in c['depths'] if x['status'].startswith('STOP_TIME'))
            rec['max_base_chain'] = max(x['maxBase'] for x in c['depths'])
            rec['work_uncapped'] = sum(x['work'] for x in c['depths'] if not x['status'].startswith('STOP_TIME'))
        rec['queries'] = c['queries']; rec['component'] = c['component']
        out.append(rec)
    return out

if __name__ == '__main__':
    fams = sorted(os.listdir(ROOT))
    allr = {}
    for f in fams:
        if os.path.exists(os.path.join(ROOT, f, 'series.csv')):
            allr[f] = load_family(f)
    json.dump(allr, open(os.path.join(os.path.dirname(__file__), 'all.json'), 'w'), default=str)
    for f, rs in allr.items():
        ns = sorted(set(r['n'] for r in rs if r['n'])) or [0]
        print(f, len(rs), 'solved', sum(r['solved'] for r in rs), 'series', sum(r['solver'] == 'series' for r in rs),
              'chain', sum(r['solver'] == 'chain' for r in rs), 'distinct n', len(ns), ns[0], ns[-1])
