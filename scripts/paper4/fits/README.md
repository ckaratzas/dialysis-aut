# Growth fits (paper 4, Table "Families")

Least-squares fits of log(cost) = a + b log n (and the quasi-polynomial form a + c log^2 n) on the benchmark campaign of
the earlier paper (`results/xeon-2026-10`, Xeon). Run from the repository root:

    python3 scripts/paper4/fits/load.py    # parses series.csv and chain/*.txt into all.json
    python3 scripts/paper4/fits/fit.py     # fits per family and cost measure (prints; writes fits.json)
    python3 scripts/paper4/fits/final.py   # the rows of the table
    python3 scripts/paper4/fits/warm.py    # warm-start check

The chain is fitted on its group-phase work ("chain groupWork", all depths) and, for families where some depths stop at the
per-depth budget, also on the uncapped depths only ("uncapped groupWork"); the series solver on wall-clock seconds.
