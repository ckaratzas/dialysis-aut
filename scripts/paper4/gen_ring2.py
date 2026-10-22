#!/usr/bin/env python3
"""Regression instances for the glue-type fix of the (D) route (2026-10-22): a ring of 2m pieces alternating a triangle and
a 4-cycle (two piece types), consecutive pieces joined by one cut edge, vertex numbers shuffled so that the piece order of
adjacent pairs is scrambled. |Aut| = 2m * 2^m (the dihedral group of the alternating ring, order 2m, times one swap per 4-cycle;
48, 128, 320 for m = 3, 4, 5, equal to Traces). Before the fix, glue
keys of pieces of different types depended on the piece numbering and could split equivalent pairs (too small |Aut|).
usage: gen_ring2.py OUT_DIR [m ...]   (default m = 3 4 5, seeds 1 2 3)"""
import os, random, sys

def ring(m, seed):
    V, E, ports = 0, [], []
    for i in range(2 * m):
        b = V
        if i % 2 == 0: E += [(b, b + 1), (b + 1, b + 2), (b, b + 2)]; ports.append((b, b + 1)); V += 3
        else: E += [(b, b + 1), (b + 1, b + 2), (b + 2, b + 3), (b + 3, b)]; ports.append((b, b + 2)); V += 4
    for i in range(2 * m): E.append((ports[i][1], ports[(i + 1) % (2 * m)][0]))
    p = list(range(V)); random.Random(seed).shuffle(p)
    return V, [(p[a], p[b]) for a, b in E]

out = sys.argv[1]; os.makedirs(out, exist_ok=True)
for m in [int(x) for x in sys.argv[2:]] or [3, 4, 5]:
    for seed in (1, 2, 3):
        n, E = ring(m, seed)
        with open(os.path.join(out, f"ring2-m{m}-s{seed}"), "w") as f:
            f.write(f"p edge {n} {len(E)}\n" + "".join(f"e {a + 1} {b + 1}\n" for a, b in E))
