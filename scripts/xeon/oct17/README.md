# G2 attack runs (group-CFI graphs)

`run_g2_attack.sh` runs every instance of `INST` with every method of `METHODS`, one JVM per run, with its own timeout,
and writes one log per run plus `summary.txt` to `OUT`. Finished runs (a log ending in a `DONE` line) are skipped.

    INST=./g2_instances OUT=./g2_results JAR=build/libs/dialysis-paper3.jar \
      METHODS="tcgl tcgl0 luks traces" JOBS=1 HEAP=4g TIMEOUT_S=7200 TMP_DIR=$HOME/tmp_g2 ./run_g2_attack.sh

Instances: `scripts/paper4/gen_group_cfi.py OUTDIR GROUP:BASE[:tw] ...` with GROUP in S3, A5, F2_3, F3_2, F5_2 and BASE
in K4, K33, prism, cube, heawood, mcgee, tutte8, rc12-1 ... rc64-1 (random cubic). The paper's 30 instances:
S3 on rc12, rc20, rc24, rc32, rc48, rc64 and tutte8; A5 on K4, K33, prism, cube; F3_2 on mcgee and tutte8; F2_3 on
tutte8; F5_2 on heawood; each with and without the twist.

Methods:
- `tcgl`: the flow of the paper. Series solver with leaf-group pruning and admissibility on V
  (`SERIES_TCPRUNE=1 SERIES_ADMIT_V=1`, unconditional by the paper's Proposition on leaf maps), a quarter of `TIMEOUT_S`,
  then on a stop Luks' method from the uniform colouring (`SERIES_LUKS=1 SERIES_LUKS_PLAIN=1`).
- `tcgl0`: the same without the leaf-group pruning (the ablation of the paper).
- `tcg`, `tcgu`: the series solver alone, with the pruning conditional on Conjecture 11.1 of the first paper (`tcg`,
  answers COND_EXACT) or without it (`tcgu`).
- `luks`: the (D) route alone; the `GIANTS` lines give the degrees of the giant quotients met.
- `traces`: the uncoloured Traces oracle.

Graphs with more than `PI_MAX_N` (8000) vertices start from 1-WL instead of PI. Results of the paper's run:
`results/xeon-2026-10-g2/`.
