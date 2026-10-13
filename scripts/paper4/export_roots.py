#!/usr/bin/env python3
"""Greedy root path (split_classify, GREEDY env, default 8) per instance, for the Luks ablation (FALLBACK_SPEC,
2026-10-12: "do we need Babai's giant case?"). Output lines: path<TAB>r1,r2,... (0-based, DIMACS ids - 1).
Usage: export_roots.py OUT GRAPH..."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
os.environ.setdefault('GREEDY', '8')
import split_classify as sc
with open(sys.argv[1], 'w') as out:
    for f in sys.argv[2:]:
        nb = sc.load(f); sc.TRACE = []; sc.ROOTS = []; sc.path(nb, cap=200)
        out.write(f + "\t" + ",".join(map(str, sc.ROOTS)) + "\n"); out.flush()
        print(os.path.basename(f), len(nb), "roots:", len(sc.ROOTS), flush=True)
