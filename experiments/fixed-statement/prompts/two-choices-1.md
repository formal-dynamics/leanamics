# Task: prove `consensus_whp` in `median/Median/Binary.lean` (Lean 4 + Mathlib)

You are working in a git worktree of the Leanamycs monorepo (your current directory). The Lake
package `median/` depends on the sibling path package `dynamics/` (finite probability layer:
`Dynamics.avg`, `Dynamics.expList` and its lemmas, `Dynamics/Concentration.lean` with Hoeffding and
Bernstein bounds for sums of independent coordinates on finite product spaces, ...). Toolchain
and Mathlib are pinned and **already built**; no network access is needed and none should be
attempted.

`median/Median/Defs.lean` defines the median dynamics; with values in `Bool` it is 2-Choices: a node
keeps its value unless both of its two sampled nodes hold the other value. `median/Median/Binary.lean`
states one theorem, `consensus_whp`, proved by `sorry`: there is a constant `C` such that if the
`true` nodes outnumber the `false` ones by at least `C √(n log n)`, all nodes hold `true` after
`⌈C log n⌉` rounds with probability at least `1 - C/n` (whenever `log n ≥ C`). **Your job: replace
the `sorry` with a complete proof.** You choose the constants.

## Hard rules (checked mechanically afterwards; any violation voids the run)

1. **Do not change any statement.** `median/Median/Defs.lean` (all definitions) must stay
   byte-identical, the `import`/`namespace`/`open`/`variable` lines of `Binary.lean` must not change,
   and each theorem must keep exactly its current text up to its `:=`. You may edit only the proofs
   after `:=`. Adding `omit … in` before a theorem to drop an unused section instance is allowed.
2. You may edit only `median/Median/Binary.lean` and create new files `median/Median/Binary*.lean`, imported
   from it. **Do not import `Median.Basic`** (another agent is proving it in parallel, so its theorems are
   `sorry` here), and do not modify any other file.
3. No `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`, or options that
   weaken kernel checking. Raising `maxHeartbeats` locally is allowed if really needed.
4. Do **not** run writing git commands and do not run `lake update` or `lake exe cache get`.

## Commands

```bash
cd median
lake build Median.Binary                    # fast check of your file
lake build                              # whole package; your file must have no warnings
lake env lean Audit.lean                # the axioms of `consensus_whp` must be only
                                        # propext, Classical.choice, Quot.sound
```
(`Audit.lean` also lists the other agent's theorems, which still show `sorryAx` here: ignore those.)

Keep `median/PROGRESS.md` up to date (proved / remaining / current errors / plan).

## Mathematical plan

**The template for this regime exists in this repository**: `plurality/Plurality/*.lean` proves
`Plurality.theorem_3_8` for 3-Majority with `k` colors from a bias `22 √(λ n log n)` (a vanishing
fraction), with the same kind of phases you need: `Growth.lean` (the bias grows by a constant
factor per round w.h.p. while it is small), `Saturation.lean` (the minority shrinks once the
majority is large), `Tail.lean` (Chernoff/Markov), `Upper.lean` (assembling the phases with
`Dynamics.Kernel.nested_phases` and a union bound), and `Numerics.lean` (explicit "large n"
bounds). For two colors 3-Majority and 2-Choices have the **same expected one-round map**
`p ↦ 3p² − 2p³`. Read these files first and adapt their structure; you may copy and adapt code
into `Binary*.lean` files, but do not import `plurality/` (it is not a dependency of `median/`).
The 3-majority package (`3-majority/ThreeMajority/*.lean`) is a simpler template for the
constant-bias phases.

Differences to handle. In 2-Choices the probability that a node holds `true` after the round
depends on its own value: `1 - (1-p)²` if it holds `true`, `p²` if it holds `false` (`p` =
fraction of `true`). Given the configuration, the new values of different nodes are independent
(each node uses only its own pair `r v`), so the number of `true`s is a sum of independent,
non-identical Bernoulli variables (`Dynamics/Concentration.lean`: `avg_hoeffding`).

Suggested phases. Write the gap as `s = 2 ones - n`.
1. **Growth** (`s` small): with `p = 1/2 + s/(2n)`, the expected new gap is `s (3/2 - s²/(2n²))`,
   so it grows by a factor at least `5/4` while `s ≤ n/2`; by concentration the deviation is
   `O(√(n log n))`, which `C √(n log n) ≤ s` dominates for `C` large, so `s ≥ n/2` within
   `O(log n)` rounds w.h.p.
2. **Saturation** (minority `m ≤ n/4`): the expected new minority is at most `3m²/n ≤ (3/4) m`; keep
   `m ≤ n/4` w.h.p. and iterate until the expected minority is `O(1/n)` (Markov); once the minority
   is `0` it stays `0`.
3. Combine the phases (e.g. as in `Upper.lean`) and choose `C`.

When `consensus_whp` is proved, `lake build` succeeds with no warnings in your files, and
`Audit.lean` shows only standard axioms for `consensus_whp`, write a short final summary.
