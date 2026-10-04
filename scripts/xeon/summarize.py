#!/usr/bin/env python3
"""Per-family summary of run_family.sh (our method) and run_traces.sh (the separate Traces oracle/baseline).

usage: summarize.py OUT_DIR GRAPHS_DIR [FAMILY]
writes OUT_DIR/<family>/summary.txt (with FAMILY) and always OUT_DIR/summary.md + OUT_DIR/summary.csv

Per instance: our |Aut| and time come from stage 1 (series.csv, status EXACT) or stage 2 (chain/<name>.<mode>.txt);
the Traces order and time from traces.csv (uncoloured Traces, separate processes). "agree" compares the two orders.
"""
import csv, os, re, statistics, sys

out_dir, graphs = sys.argv[1], sys.argv[2]


def num(x):
    try: return float(x)
    except (TypeError, ValueError): return None


def same(a, b):
    return a is not None and b is not None and abs(a - b) <= 1e-9 * max(1.0, abs(b))


def family_row(fam):
    d = os.path.join(out_dir, fam)
    files = sorted(f for f in os.listdir(os.path.join(graphs, fam))
                   if os.path.isfile(os.path.join(graphs, fam, f)) and not f.startswith('.'))
    ours = {}            # name -> (order, seconds, n, how)
    p = os.path.join(d, 'series.csv')
    if os.path.exists(p):
        for r in csv.DictReader(open(p)):
            if r['status'] == 'EXACT':
                ours[r['instance']] = (num(r['aut_log2']), num(r['seconds']), int(r['n_orig'] or 0), 'series')
    status = {}
    p = os.path.join(d, 'chain_done.txt')
    if os.path.exists(p):
        for line in open(p):
            a = line.split()
            if len(a) >= 2: status[a[0]] = a[1]
    formula_bad = 0
    cd = os.path.join(d, 'chain')
    if os.path.isdir(cd):
        for f in sorted(os.listdir(cd)):
            if not f.endswith('.txt'): continue
            name, mode = f[:-4].rsplit('.', 1)
            n = None
            for line in open(os.path.join(cd, f)):
                m = re.match(r'== (\S+) n=(\d+)', line)
                if m: n = int(m.group(2))
                m = re.search(r'\|Aut\| = (\S+)( \(incomplete\))?\s+ours ([\d.]+)s(.*)', line)
                if m and not m.group(2) and name not in ours:
                    ours[name] = (num(m.group(1)), num(m.group(3)), n or 0, 'chain-' + mode)
                    if 'formula' in m.group(4) and 'agree=false' in m.group(4).split('Traces')[0]: formula_bad += 1
    def load_traces(fname):   # name -> (order or None, seconds incl. the colouring, outcome)
        t = {}
        p = os.path.join(d, fname)
        if os.path.exists(p):
            for r in csv.DictReader(open(p)):
                name = os.path.basename(r['instance'])
                ok = r['outcome'] == 'OK'
                secs = ((num(r.get('traces_ms')) or 0) + (num(r.get('colour_ms')) or 0)) / 1000.0
                t[name] = (num(r['traces_order']) if ok else None, secs, r['outcome'])
        return t
    traces = load_traces('traces.csv')          # uncoloured: the independent oracle and baseline
    traces_pi = load_traces('traces_pi.csv')    # Traces given our PI colouring (time = PI + Traces)
    solved = [f for f in files if f in ours]
    agree = [f for f in solved if f in traces and same(ours[f][0], traces[f][0])]
    disagree = [f for f in solved if f in traces and traces[f][0] is not None and not same(ours[f][0], traces[f][0])]
    tr_fail = [f for f in solved if f in traces and traces[f][0] is None]
    both = [f for f in agree]
    ratios = [traces[f][1] / ours[f][1] for f in both if ours[f][1] and ours[f][1] > 0]
    pi_agree = [f for f in solved if f in traces_pi and same(ours[f][0], traces_pi[f][0])]
    pi_dis = [f for f in solved if f in traces_pi and traces_pi[f][0] is not None and not same(ours[f][0], traces_pi[f][0])]
    pi_fail = [f for f in solved if f in traces_pi and traces_pi[f][0] is None]
    pi_ratios = [traces_pi[f][1] / ours[f][1] for f in pi_agree if ours[f][1] and ours[f][1] > 0]
    cp = os.path.join(d, 'colour.txt')   # starting colouring of the run (run_family.sh COLOUR); older runs: PI
    colour = open(cp).read().strip() if os.path.exists(cp) else 'pi'
    return dict(
        family=fam, colour=colour, instances=len(files), solved=len(solved),
        by_series=sum(1 for f in solved if ours[f][3] == 'series'),
        by_chain=sum(1 for f in solved if ours[f][3].startswith('chain')),
        from_1wl=sum(1 for f in solved if ours[f][3] == 'chain-wl1'),
        traces_run=sum(1 for f in files if f in traces), traces_agree=len(agree), disagree=len(disagree) + len(pi_dis) + formula_bad,
        traces_fail_we_solve=len(tr_fail),
        largest_n=max((ours[f][2] for f in solved), default=0),
        largest_aut=max((ours[f][0] or 0 for f in solved), default=0),
        ours_max_s=max((ours[f][1] or 0 for f in solved), default=0),
        ours_total_s=sum(ours[f][1] or 0 for f in solved),
        traces_total_s=sum(traces[f][1] for f in files if f in traces),
        median_ratio=statistics.median(ratios) if ratios else 0, max_ratio=max(ratios, default=0),
        pi_traces_run=sum(1 for f in files if f in traces_pi), pi_traces_fail_we_solve=len(pi_fail),
        pi_median_ratio=statistics.median(pi_ratios) if pi_ratios else 0, pi_max_ratio=max(pi_ratios, default=0),
        open=';'.join(f"{f}:{status.get(f, 'not solved')}" for f in files if f not in ours))


rows = []
for fam in sorted(os.listdir(out_dir)):
    if os.path.isdir(os.path.join(out_dir, fam)) and os.path.isdir(os.path.join(graphs, fam)):
        rows.append(family_row(fam))
if len(sys.argv) > 3:
    for r in rows:
        if r['family'] == sys.argv[3]:
            txt = '\n'.join(f'{k}: {v}' for k, v in r.items())
            open(os.path.join(out_dir, r['family'], 'summary.txt'), 'w').write(txt + '\n')
            print(txt)
if rows:
    with open(os.path.join(out_dir, 'summary.csv'), 'w', newline='') as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys())); w.writeheader(); w.writerows(rows)
    with open(os.path.join(out_dir, 'summary.md'), 'w') as f:
        f.write('| family | start colouring | instances | solved | by algebraic solver | by chain | (from 1-WL) | Traces run | agree | disagree '
                '| Traces fails, we solve | largest n | largest Aut order | our slowest s | median / max Traces÷ours '
                '| Traces+PI run | Traces+PI fails, we solve | median / max (PI+Traces)÷ours |\n')
        f.write('|' + '---|' * 18 + '\n')
        for r in rows:
            f.write(f"| {r['family']} | { {'wl1': '1-WL', 'auto': 'auto'}.get(r['colour'], 'PI') } | {r['instances']} | {r['solved']} | {r['by_series']} | {r['by_chain']} | {r['from_1wl']} | "
                    f"{r['traces_run']} | {r['traces_agree']} | {r['disagree']} | {r['traces_fail_we_solve']} | {r['largest_n']} | "
                    f"{r['largest_aut']:.3g} | {r['ours_max_s']:.1f} | {r['median_ratio']:.3g} / {r['max_ratio']:.3g} | "
                    f"{r['pi_traces_run']} | {r['pi_traces_fail_we_solve']} | {r['pi_median_ratio']:.3g} / {r['pi_max_ratio']:.3g} |\n")
print(f"summary over {len(rows)} families: {os.path.join(out_dir, 'summary.md')}")
