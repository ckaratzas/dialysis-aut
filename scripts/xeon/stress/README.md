# Class-2 stress runs (random class-2 groups)

`gen_class2_stress.py OUTDIR p,d,e,seed ...` writes the Latin square graph of the group on F_p^d x F_p^e with product
(v,w)(v',w') = (v+v', w+w'+beta(v,v')), beta a random bilinear map whose commutator map has trivial radical and full image
(few automorphisms). `ctl:p,d,e,0` gives a symmetric control. The paper uses 2,4,3,s (order 128, seeds 1 to 3),
3,3,2,1 (order 243) and 2,5,3,1 (order 256).

`run_stress.sh` generates the instances and runs the stabiliser chain (`PieceProfileTest`) in the modes of `MODES` and
the Traces oracle:

    INST=./stress_instances OUT=./stress_results JAR=build/libs/dialysis-paper3.jar MODES=look JOBS=1 HEAP=5g \
      TIMEOUT_S=28800 SPECS="2,5,3,1" SC_QUERY_MS=28800000 ./run_stress.sh

Modes: `base` (node invariants, delayed fingerprint, automorphism pruning), `reset` (base plus the adaptive reset),
`look` (base plus `SC_STABPRUNE=1 SC_LOOKAHEAD=1 SC_LOOK_FRAC=0.1`: stabiliser-orbit pruning of refuted images and the
canonical-cell lookahead). `SC_QUERY_MS` is the budget of the query phase (default one hour); set it to the timeout for
the order-256 instance. `TRACES_TIMEOUT=0` skips Traces.

`aut_group_check.py p,d,e,seed` computes |Aut G| independently (backtracking over generator images) and prints
|G|^2 * 6 * |Aut G|, the order of the automorphism group of the Latin square graph. Order 256 takes about 13 minutes.

Results of the paper's runs: `results/xeon-2026-10-class2/`.
