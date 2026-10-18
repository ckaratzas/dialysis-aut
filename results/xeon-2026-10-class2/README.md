# Random class-2 groups on the Xeon (2026-10-17/18)

Latin square graphs of random class-2 groups (`scripts/xeon/stress/gen_class2_stress.py`), stabiliser chain in mode
`look` (`scripts/xeon/stress/run_stress.sh`), Traces as oracle.

| instance | order | vertices | ours (look) | Traces |
|---|---|---|---|---|
| c2stress-rnd-p2-d4-e3-s1 | 128 | 16,384 | 256 s | 37 s |
| c2stress-rnd-p2-d4-e3-s2 | 128 | 16,384 | 196 s | 49 s |
| c2stress-rnd-p2-d4-e3-s3 | 128 | 16,384 | 168 s | 12 s |
| c2stress-rnd-p3-d3-e2-s1 | 243 | 59,049 | 1,000 s | not run |
| c2stress-rnd-p2-d5-e3-s1 | 256 | 65,536 | 6,468 s | not run |

|Aut| agrees with Traces at order 128. At orders 243 and 256 it equals |G|^2 * 6 * |Aut G| with |Aut G| computed by
`scripts/xeon/stress/aut_group_check.py` (3^6 * 864 and 2^15). The order-256 run used `SC_QUERY_MS=28800000`; with the
default one-hour query budget it stopped after 5,692 s.

Files: `chain_<instance>.look.txt` (per depth status, orbit phase, search statistics, final |Aut| and time),
`chain_<instance>.look.log` (progress), `traces.csv`, `traces.log`, `chain_campaign.log`, `summary.txt`, `generate.log`.
