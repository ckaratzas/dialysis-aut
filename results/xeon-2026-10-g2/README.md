# G2 attack: group-CFI graphs on the Xeon (2026-10-17/18)

30 group-CFI instances (S3, A5, F2_3, F3_2, F5_2 gadgets; random cubic bases and the Heawood, McGee and Tutte cages;
with and without a twist), run by `scripts/xeon/oct17/run_g2_attack.sh` on the Xeon of the campaign, one JVM at a time,
heap 4 GB. One log per method and instance: `<method>_<instance>.log`, last line `DONE rc=<exit code> seconds=<wall>`.

- `luks_*`: the (D) route; `LUKSAUT` = |Aut|, `GIANTS ... maxGiantDeg` = largest giant degree met in Luks' method.
- `tcgl_*`: the paper's flow (series solver with leaf-group pruning on V-admissibility, then Luks on a stop).
  The runs of S3-rc64 (+tw) have `TIMEOUT_S=7200` (series stage 1,800 s); all other `tcgl` runs come from the first run,
  `TIMEOUT_S=1800` (series stage 450 s). S3-tutte8 (+tw) `tcgl` with the raised coset-test cap is not included.
- `tcgl0_*`: the same flow without the leaf-group pruning, `TIMEOUT_S=7200` (series stage 1,800 s); S3-rc64-tw and
  S3-tutte8 (+tw) are not included.
- `tcg_*`: the series solver with the pruning conditional on Conjecture 11.1 of the first paper (answers COND_EXACT).
- `traces_*`, `traces.csv`: the uncoloured Traces oracle (3,600 s or 7,200 s limit; missing rows = no answer).
- `campaign.log`: start and end of every run; `summary.txt`: one line per instance.

The ablation in the paper compares `tcgl` with `tcgl0` only where the budget difference does not matter.
