# dialysis-aut

Code, benchmark graphs, scripts and results for

> C. I. Karatzas, *Refinement-Derived Algebraic Computation of Graph Automorphism Groups* (manuscript).

The method computes the automorphism group of a graph exactly, with a verified generating set:

1. **Refinement-derived permutation groups.** Inside each class of an invariant colouring, individualisation and
   refinement give a set `T_C` of permutations containing the restriction of every automorphism; it is checked to be a
   group.
2. **Algebraic solver.** A normal series of every `T_C` with elementary abelian factors turns the edges between classes
   into affine systems over finite fields, solved level by level and counted by cosets (the classical
   bounded-colour-multiplicity tower method, applied where bounded multiplicity is not given).
3. **Decomposition-guided stabiliser chain.** Where the `T_C` are too large, roots taken from the recursive
   decomposition (dialysis) are individualised until the solver is exact on their stabiliser; root orbits are decided
   by a two-sided coset solve.
4. **Decomposition-derived invariants** for projective and affine planes (nets).
5. **Starting colouring (plug-in).** The solver and the chain start from any invariant colouring: plain colour
   refinement (1-WL) or the structural colouring `PI` derived from the dialysis of every vertex.

Every reported group order is exact; every generator is verified edge by edge on the input graph. `Traces` is used
only as a separate oracle, never inside the method.

## Requirements

Linux x86-64, JDK 17 or newer, `gcc`/`g++` (the three JNI libraries are built from source), Python 3 (scripts and
checks). Memory: 4 GB is enough for most instances; the largest (`pp` of order 27, graphs with 10,000 vertices) need
about 8 GB.

## Build

```
./gradlew paperJar                 # -> build/libs/dialysis-paper3.jar
scripts/run_gradle.sh paperJar     # the same inside a memory-capped systemd scope (recommended on a desktop)
```

The jar is self-contained (Kotlin runtime, jgrapht, native libraries, code). The native libraries are compiled with
`-march=native`: build on the machine that runs the experiments. `./gradlew test` is disabled on purpose: the
experiment classes in `src/test` are whole campaigns, run through the jar.

## Quick start

The graphs are in `graphs/<family>/` (DIMACS format). One family through the whole pipeline, results in
`results-run/<family>/`:

```
JAR=build/libs/dialysis-paper3.jar GRAPHS=graphs OUT=results-run TMP_DIR=./tmp \
    scripts/xeon/run_family.sh johnson
python3 scripts/xeon/summarize.py results-run graphs      # per-family table: results-run/summary.md
```

`run_family.sh` runs stage 1 (the algebraic solver alone) on every instance and stage 2 (the stabiliser chain) on
every instance stage 1 did not solve. It is resumable: stop it any time and run the same command again. Per instance
the outputs are a row of `series.csv` (stage 1: status, `aut_log2`, orbits, time) and, for stage 2,
`chain/<instance>.<colour>.txt`, whose last line is `|Aut| = ... ours <seconds>`.

The JVMs get bounded heaps (`SERIES_HEAP` [6g], `CHAIN_HEAP` [3g], `CHAIN_JOBS` [2] in parallel). On a desktop, run the
script inside a memory-capped scope so that a large instance cannot take the machine down:

```
systemd-run --user --scope -p MemoryMax=8G -p MemorySwapMax=0 \
    env JAR=build/libs/dialysis-paper3.jar GRAPHS=graphs OUT=results-run TMP_DIR=./tmp scripts/xeon/run_family.sh <family>
```

`scripts/xeon/README.md` lists every family with the settings used in the paper (starting colouring, budgets,
threads, options such as `CHAIN_PRUNE`, `CHAIN_COMPLEMENT`, `CHAIN_AFFINE`) and what each output file contains.

### Other entry points

```
java -jar build/libs/dialysis-paper3.jar series   # algebraic solver alone on a family    (env: FAMILY, DIR, OUT, ...)
java -jar build/libs/dialysis-paper3.jar chain    # stabiliser chain on instances          (env: SC_FILES, OUT, ...)
java -jar build/libs/dialysis-paper3.jar oracle   # Traces on one instance (separate oracle; env: TR_FILE, TR_COLOUR, OUT)
java -jar build/libs/dialysis-paper3.jar traces --family=<f> --out=<csv> --timeoutMs=<ms>   # Traces oracle on a family
java -jar build/libs/dialysis-paper3.jar run <Class> <method>                             # any experiment method
GRAPHS=graphs scripts/xeon/run_traces_all.sh                                             # Traces oracle, every family
```

Settings are environment variables; `run_family.sh` and `scripts/xeon/README.md` document them.

## Graphs

`graphs/` holds the 12,001 instances of the 36 families of the paper; `graphs/SHA256SUMS` lists every file with its
checksum (`cd graphs && sha256sum -c SHA256SUMS`). Sources: the `nauty`/`Traces` benchmark collection of McKay and
Piperno (most families, including the CFI-type families of Neuen and Schweitzer and `Aff25`), the `conauto` collection
(`tnn`, `chh`), Moorhouse's list of projective planes (`pp`), the censuses of 4-valent arc-transitive (n <= 640,
`quartic-at`) and half-arc-transitive (n <= 1000, `quartic-hat`) graphs of Potočnik, Spiga and Verret, and House of
Graphs (`quartic-hog`); `quartic-validation` is the Coxeter graph. The files are redistributed unmodified; please
cite the original collections when you use them. Two families were generated for the paper: `graphs/johnson`
(Johnson graphs J(n,k), k = 3..6) and `graphs/hypercube` (Q_3..Q_13), both with seeded random vertex numbering; their
orders have closed forms (n!, doubled when n = 2k; 2^d d!). Family folders keep the names of the downloaded archives;
the paper's `grid-sw` is the folder `grid-w` (tori with wrap-around, orders (2m)^d d!).

## Results

- `results/xeon-2026-10/<family>/`: the campaign of the paper (one Xeon server, every instance of every family):
  `series.csv` (stage 1, one row per instance), `chain/<instance>.<colour>.txt` (stage 2 logs: per depth the solver
  status, per level orbit sizes and queries, final |Aut|), `traces.csv` (the uncoloured Traces oracle), `summary.txt`.
- `results/traces-paper1/`: earlier uncoloured `Traces` runs on the same machine (orbit counts and failures), the
  oracle for the CFI-type families.
- `results/laptop/`: the smaller experiments of the appendices, with their own README.

## Numerical checks of the proofs

`checks/` holds Python checks of the complexity section (pure Python unless noted):

| folder | what |
|---|---|
| `checks/johnson-identities/` | `hand_identities.py`: brute-force check of the expansion formulas and of the identities proved by hand for J(2k,k); `check_identities.py`: the same identities with symbolic atom sizes (needs sympy; prints ALL PASS) |
| `checks/johnson-checks/` | Condition A on root prefixes, Condition B simulation, the n = 2k orbit checks, `tinhofer_exhaustive.py` (refinement against brute-force orbits for every root tuple on small Johnson graphs) |
| `checks/hamming-checks/` | `lemmaA.py d q trials maxroots`: refinement against brute-force stabiliser orbits; `proof_check.py d q chains`: profiles, refinement and the depth potential along random chains |
| `checks/multipede-checks/` | `mpA.py seed trials [r-list] [twist]`: admissible sets of refinement against the linear system of the multipede proof |
| `checks/plane-checks/` | `net_domain_scan.py GRAPHS RESULTS families...`: on every bipartite non-plane instance the chain ran on, compares the net check with the full net axioms (N1)+(N2) |

## Where things are

| paper | code |
|---|---|
| dialysis, recursive decomposition, structural colouring PI | `dialysis/decomposition/Dialysis.kt`, `Peel.kt` (`dialysisPerSpec`, `peel`), `dialysis/refinement/InitialPhase.kt` (PI), `dialysis/refinement/ColouringDispatch.kt`, `dialysis/ahu/ColoredAHU.kt` |
| refinement-derived groups `T_C` | `DecompositionCanonicalFormsTest.candidateRestrictions*`, `hashWlRounds`, `hashWlStableRound` |
| algebraic solver, coset counting | `DecompositionCanonicalFormsTest.parityEquationsSeries`, `parityCampaign` (stage 1) |
| starting colouring per family | `DecompositionCanonicalFormsTest.parityCampaign` (`SERIES_COLOUR`), `scripts/xeon/run_family.sh` (`COLOUR`) |
| stabiliser chain, two-sided coset solve, orbit closure, automorphism pruning | `PieceProfileTest.stabiliserChain`, `runChain`, `nextRoot`, `frameRoot`, `OrbitPhase` (`SC_PRUNE`); `DecompositionCanonicalFormsTest.parityIsoBatch` |
| dense class pairs (complement and combination) | `PieceProfileTest.complementDense`, `solveByComponents` |
| decomposition-derived invariants, affine planes | `PieceProfileTest.relPlaneInv*`, `isNet`, `fullNet`, `planeClosure`, `affineCompletion`; `SliceGroupTest.rootInvariant` |
| appendix: PI against 1-WL and 2-WL, starting colourings | `PartitionStrengthTest` |
| colour refinement backend | `dialysis/refinement/NativeWL1.kt` + `src/main/cpp/paige_tarjan_wl1.cpp` |
| Traces (oracle only) | `dialysis/cl/TracesJni.kt`, `src/main/cpp/nauty_traces.cpp`, vendored nauty 2.9.3 in `src/main/cpp/nauty` |

The experiment and solver code lives in the test source set (`src/test/kotlin/dialysis/experimental`) for historical
reasons; it is compiled into the jar like the main code.

## Licence

MIT (see `LICENSE`), for the code, scripts, checks and result files of this repository. Exceptions: the vendored
nauty/Traces sources keep their own licence (`src/main/cpp/nauty/COPYRIGHT`, Apache 2.0), and the benchmark graphs in
`graphs/` remain under the terms of the collections they come from (see Graphs above).
