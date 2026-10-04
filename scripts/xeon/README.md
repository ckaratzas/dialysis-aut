# The campaign of the paper: every family, one at a time, resumable

`run_family.sh <family>` runs the pipeline of the paper on one family:

1. **stage 1**: the algebraic (series) solver alone on every instance (paper settings: no fallback, 300 s per
   instance, candidate cap 20,000, base cap 12);
2. **stage 2**: the decomposition-guided stabiliser chain on every instance stage 1 did not solve, one JVM per
   instance, 2 in parallel, 1 hour each. It starts from the PI colouring; if PI runs out of memory it retries
   the instance from plain 1-WL (`SC_COLOUR=wl1`; sound, since the chain needs only an invariant colouring).

**Starting colouring (`COLOUR`).** On `cfi-rigid-r2`, `-s2` and `-t2` plain 1-WL gives the same partition as PI, so
both stages start from 1-WL there by default and PI is never computed. Every other family starts from PI. Override with `COLOUR=pi` or `COLOUR=wl1`; the choice is written to
`results/<family>/colour.txt`. Instances of r2/s2/t2 that already have a stage-1 row are not recomputed; delete the
rows you want redone (e.g. the STOP_TIME ones) and run again.

**Traces is not part of these runs at all**, so every time reported is ours alone. The oracle and baseline is a
separate job, `run_traces.sh <family>`: plain *uncoloured* Traces (no PI colouring, so the check is independent of
our colouring), one fresh process per instance, with its own time limit. Run it on its own, not alongside
`run_family.sh` (Traces' native memory is not bounded by `-Xmx`). `summarize.py` joins the two and refreshes
`results/summary.md`, one row per family: instances, solved, by which stage, agreement with Traces, instances
where Traces fails but we solve, our slowest time, and the Traces÷ours time ratio. That is the table for the paper.

**All families in one command:** `GRAPHS=/path/to/graphs ./run_traces_all.sh`. It runs every family folder in
`graphs/` (change the excluded folders with `EXCLUDE`), smallest instance first. It skips only the
305 instances where Traces, in an earlier campaign on the same machine, failed or needed more than 60 s
(`samples/traces_v1_skip.txt`); the other instances of that campaign are re-run because it kept orbit counts but not
group orders. A family stops after K consecutive failures (K=1 on cfi-rigid-* and sat_cfi_dim, K=2 elsewhere); the skipped
larger instances are listed in `results/<family>/traces_skipped.txt`. Resumable. Needs the `samples/` folder next to the
script.

## 1. Build the jar and copy it next to the scripts

```
./gradlew paperJar                  # or scripts/run_gradle.sh paperJar (memory-capped) -> build/libs/dialysis-paper3.jar
X=server:~/paper3run; ssh server mkdir -p paper3run
rsync -av build/libs/dialysis-paper3.jar scripts/xeon/run_family.sh scripts/xeon/run_traces.sh \
          scripts/xeon/run_traces_all.sh scripts/xeon/summarize.py $X/
rsync -av scripts/xeon/samples $X/
```

The jar contains the dependencies, the native libraries (built from source by Gradle: needs gcc/g++), the compiled
code and the experiment code, with a launcher: `java -jar dialysis-paper3.jar series | chain | oracle | traces |
run <Class> <method>` (settings are environment variables; `run_family.sh` sets them). The native libraries are
compiled with `-march=native`: build the jar on the machine that runs it (or one with the same CPU generation).

Needs on the server: Java >= 17 (`java -version`), python3, and disk space for temp files: the PI colouring writes a
memory-mapped file per instance, about 8·n² bytes (0.8 GB at n = 10,000).
**Always set `TMP_DIR`** to a folder on a disk with 10 GB or more free (relative paths are fine; it is created if
missing):

```
TMP_DIR=./tmp GRAPHS=./graphs ./paper3run/run_family.sh cfi-rigid-t2
```

Do not use `JAVA_TOOL_OPTIONS=-Ddialysis.tmpDir=...` with a relative path: the script changes directory, the folder
then does not exist, and Java cannot even unpack its native libraries (every instance fails with no row).
`run_traces.sh` takes `TMP_DIR` too.

Each JVM writes its temp files into its own subfolder of `TMP_DIR` (`p3run.*/jvm.*`), deleted as soon as that JVM
exits, also when it is killed by a timeout or crashes; the `p3run.*` folder is removed when the script exits (also
on Ctrl-C). Before this, every killed JVM left several GB behind. If you ran older versions, delete leftover
`dialysis-decomp*.bin` and `ahu-intern*.bin` files in `TMP_DIR` (and `/tmp`) while nothing is running.

## 2. Run one family

```
cd ~/paper3run
GRAPHS=/path/to/graphs ./run_family.sh cfi-rigid-r2      # our method (stages 1 + 2)
GRAPHS=/path/to/graphs ./run_traces.sh cfi-rigid-r2      # the oracle / baseline, separately (TRACES_TIMEOUT=3600 s)
```

Run it inside `tmux` or `screen` so it survives a dropped ssh session.

Options of `run_traces.sh`:

- **samples only**: `./run_traces.sh cfi-rigid-r2 cfi-rigid-r2-2880-01-1 cfi-rigid-r2-2880-02-2` runs only those files;
  or put one file name per line in a list and use `SAMPLE=list.txt ./run_traces.sh cfi-rigid-r2`.
- **`COLOUR=pi`**: Traces is given exactly our starting colouring (the PI colouring), written to `traces_pi.csv`, with
  the PI time and the Traces time in separate columns. If Traces with the
  same colouring still fails or is slow where our solver is fast (e.g. the large cfi-rigid / Dawar–Yeung instances),
  the difference is the architecture, not the colouring. `COLOUR=none` (default, `traces.csv`) is the independent
  oracle. `summarize.py` reports both, with the (PI + Traces)÷ours ratio.

  ```
  COLOUR=pi GRAPHS=/path/to/graphs ./run_traces.sh cfi-rigid-r2 cfi-rigid-r2-2880-02-2
  ```

Both are resumable and independent; the Traces job can run days later. **Resume:** stop it any time (Ctrl-C, reboot, ...) and run the same command again. Stage 1 skips every instance
that already has a row in `results/<family>/series.csv`; stage 2 skips every instance listed in
`results/<family>/chain_done.txt`. To retry one failed chain instance, delete its line from `chain_done.txt`
and rerun.

## 3. The families, in the suggested order (fast first)

| # | family | what to expect |
|---|---|---|
| 1 | `cfi-rigid-r2` | stage 1 solves it |
| 2 | `cfi-rigid-z2` | stage 1 |
| 3 | `cfi-rigid-t2` | stage 1 |
| 4 | `cfi-rigid-d3` | stage 1 |
| 5 | `cfi-rigid-z3` | stage 1 |
| 6 | `cfi-rigid-s2` | stage 1; 504 instances, most were above the laptop's size cap |
| 7 | `cfi` | stage 1 |
| 9 | `sat_cfi_dim` | stage 1 |
| 10 | `mz` | stage 1 |
| 11 | `mz-aug` | stage 1 |
| 12 | `mz-aug2` | stage 1 |
| 13 | `grid` | stage 1 |
| 14 | `rnd-3-reg` | stage 1 (PI discrete) |
| 15 | `sts-sw` | stage 1 |
| 16 | `latin-sw` | stage 1 |
| 17 | `paley` | stage 1 |
| 18 | `latin` | stage 1 |
| 19 | `had-sw` | stage 1 |
| 20 | `sts` | stage 1, the rest via the chain |
| 21 | `quartic-validation` | stage 1 |
| 22 | `quartic-hog` | stage 1, 3 via the chain |
| 23 | `quartic-hat` | stage 1; 3,229 instances |
| 24 | `cmz` | chain for 45 of 46 |
| 25 | `triang` | chain; triang-30 may need the 1-WL retry |
| 26 | `lattice` | chain |
| 27 | `johnson` | chain (copy `graphs/johnson` first) |
| 28 | `grid-w` | chain; tori up to 10,000 vertices |
| 29 | `ag` | chain |
| 30 | `pg` | chain |
| 31 | `had` | chain |
| 32 | `quartic-at` | stage 1 for 4,234, chain for 586 |
| 33 | `hypercube` | Q_3 .. Q_13 (8 to 8,192 vertices), |Aut| = 2^d d!; generated by `scripts/gen_hypercube.py` |
| 34 | `pp` | chain on 241 planes, 2 by stage 1. The campaign ran without pruning except `pp-27-6`: rerun it alone with `CHAIN_PRUNE=1` (automorphism pruning in the chain's witness search; without it the run does not finish in an hour, with it 982 s). `CHAIN_PRUNE=1` is sound for every plane and faster where the witness search backtracks (laptop: `pp-27-10` 956 s against > 5,400 s) |
| 35 | `tnn` | non-disjoint unions of tripartite graphs (conauto; 20 graphs, 26 to 1,014 vertices): `CHAIN_COMPLEMENT=1 CHAIN_MAXDEPTH=200 COLOUR=wl1` (complemented dense class pair; laptop: 1,014 vertices in 44 s) |
| 36 | `chh` | cubic hypohamiltonian graphs (conauto; 26 graphs, 22 to 1,078 vertices): `COLOUR=auto SERIES_DEADLINE=10` (`auto`: stage 1 first tries plain 1-WL, which stops at once on all but the eight smallest, and then PI, which has twice as many classes; from PI every chain candidate is in the orbit, from 1-WL the shallow levels need ~10^5 negative queries and time out), chain (laptop, from PI: 1,078 vertices in 248 s) |
| 37 | `Aff25` | one rigid affine plane of order 25 (1,275 vertices, from the Traces page): `CHAIN_JOBS=1 CHAIN_THREADS=12 COLOUR=wl1`; solved through its projective completion (`CHAIN_AFFINE=1`, the default; laptop 344 s) |

Several families back to back (still one at a time):

```
for f in cfi-rigid-r2 cfi-rigid-z2 cfi-rigid-t2; do GRAPHS=/path/to/graphs ./run_family.sh $f; done
```

## 4. Chain settings

- `CHAIN_MAXDEPTH` (default 32): most decomposition roots the chain individualises. The deepest chain in the
  benchmark is `lattice-30` (depth 27); everything else needs at most about 13.
- `CHAIN_WORK1`, `CHAIN_WORK2`: the chain's per-depth budgets for its first and second pass, in solver work units
  (defaults 4.5e9 and 2.7e10, about 10 s and 60 s on the laptop). They are counts, not seconds, so the depth the
  chain takes is the same on every machine: raise them only if you want the paper's numbers to change.
- `CHAIN_TIMEOUT` (default 3600): wall-clock limit per instance.

Example: `CHAIN_MAXDEPTH=40 CHAIN_TIMEOUT=7200 GRAPHS=/path/to/graphs ./run_family.sh lattice`

## 5. Memory (8 GB machine)

- stage 1: one JVM, `SERIES_HEAP=6g`;
- stage 2: `CHAIN_JOBS=2` JVMs with `CHAIN_HEAP=3g` each (plus reclaimable file cache from the PI colouring);
- if the kernel OOM killer ever fires (`dmesg | tail`), rerun with `CHAIN_JOBS=1 CHAIN_HEAP=5g` (resume keeps
  everything already done).

## 6. What to send back

The whole `results/` folder, or at least `results/summary.md`, `results/summary.csv`, and per family
`series.csv`, `chain_done.txt` and `chain/*.txt`. The `.log` files only if something failed.

Per family (`results/<family>/`): `series.csv` (stage 1, one row per instance), `chain/<instance>.pi.txt` or
`.wl1.txt` (stage 2: per depth the solver status, per level orbit size and queries, final |Aut| next to Traces),
`chain_done.txt` (stage 2 outcome per instance: `pi`, `wl1`, `*-noexact`, `*-timeout`, `*-fail`), `summary.txt`.

---

Older scripts, still here: `run_parity_campaign.sh` and `run_chain.sh` (they use loose class folders).
`run_family.sh` with the jar replaces both for the paper table.
