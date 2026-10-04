# Laptop experiments (appendices)

Smaller experiments run on the author's laptop (AMD Ryzen 7 4800H, 15 GB RAM), each JVM in a memory-capped systemd
scope. The paper marks every number that comes from here as "laptop"; none of these numbers is compared with a Xeon
number.

| folder | what | paper |
|---|---|---|
| `colourings/` | `PartitionStrengthTest`: class counts and times of 1-WL, 2-WL and PI on single graphs and on pairs (`full.csv`), on the largest graphs (`big.csv`), PI against 1-WL on five samples per family (`pi1wl_<family>.csv`), and the method from three starting colourings (`startcol.csv`). `stage1-samples/`: stage 1 on the same samples from PI (`<family>_pi.csv`) and from plain refinement first (`<family>_auto.csv`, the outcome from plain refinement is in column `stop_detail`). `large/`: stage 1 on the largest `rnd-3-reg` and `sts` instances from 1-WL and from PI | Section 6 (`tab:pi1wl`), Appendix B |
| `chain/` | chain campaigns: calibration of the deterministic work budget (`cal*`), ablations (`abl*`), the projective-plane campaign (`ppall*_pp.txt`, `fast_pp.txt`), the unsound global plane invariant before the `isNet` guard (`ag_unsound_globalinv.txt`) | Appendix A (accelerators, budget), Appendix C (planes) |
| `pruning/` | automorphism pruning in the chain's witness search (`SC_PRUNE`): `pp-27-10` without pruning (`p0`, stopped after more than 5,400 s) and with it (`p1`, 956 s); `pp-27-6` with pruning; `run.sh` reproduces the comparison | Section 7, Appendix C |
| `complement/` | dense class pairs: chain on G (`.G.`) and on the complemented G' (`.C.`) for tnn and chh | Section 7 (`sec:complement`), Appendix C (`tab:tnn`) |
| `traces/` | uncoloured Traces, 20 s limit (test of `run_traces_all.sh`): every order equal to ours | Appendix C (chh) |

The numerical checks of the complexity section are in `checks/` at the top of the repository.
