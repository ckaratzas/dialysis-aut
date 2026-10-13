#!/usr/bin/env python3
"""Disjoint union G + H for the isomorphism-by-automorphisms reduction (paper 4, Lemma iso-aut; 2026-10-12). Optionally
relabels H by a random permutation (seed) to make an isomorphic copy. Usage: disjoint_union.py G H OUT [relabel_seed]"""
import sys, random
def load(f):
    n = 0; E = []
    for l in open(f):
        p = l.split()
        if p and p[0] == 'p': n = int(p[2])
        elif p and p[0] == 'e': E.append((int(p[1]) - 1, int(p[2]) - 1))
    return n, E
(n1, E1), (n2, E2) = load(sys.argv[1]), load(sys.argv[2])
if len(sys.argv) > 4:
    pi = list(range(n2)); random.Random(int(sys.argv[4])).shuffle(pi); E2 = [(pi[a], pi[b]) for a, b in E2]
E = E1 + [(a + n1, b + n1) for a, b in E2]
with open(sys.argv[3], 'w') as f:
    f.write(f"p edge {n1 + n2} {len(E)}\n"); f.writelines(f"e {a + 1} {b + 1}\n" for a, b in E)
print(sys.argv[3], n1 + n2, len(E))
