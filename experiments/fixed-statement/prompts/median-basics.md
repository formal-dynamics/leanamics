# Task: complete the proofs in `median/Median/Basic.lean` (Lean 4 + Mathlib)

You are working in a git worktree of the Leanamycs monorepo (your current directory). The Lake
package `median/` depends on the sibling path package `dynamics/` (finite probability layer:
`Dynamics.avg`, `Dynamics.Kernel`, `Kernel.ofStep`, `Kernel.apply_ofStep`, `Kernel.iterate_ofStep`,
`Kernel.finite_absorption`, ...). Toolchain and Mathlib are pinned and **already built**; no network
access is needed and none should be attempted.

`median/Median/Defs.lean` defines the median dynamics (every node adopts the median of its own value
and the values of two sampled nodes); `median/Median/Basic.lean` states eight theorems proved by
`sorry`. **Your job: replace every `sorry` in `Basic.lean` with a complete proof.**

## Hard rules (checked mechanically afterwards; any violation voids the run)

1. **Do not change any statement.** `median/Median/Defs.lean` (all definitions) must stay
   byte-identical, the `import`/`namespace`/`open`/`variable` lines of `Basic.lean` must not change,
   and each theorem must keep exactly its current text up to its `:=`. You may edit only the proofs
   after `:=`. Adding `omit … in` before a theorem to drop an unused section instance is allowed.
2. You may edit only `median/Median/Basic.lean` and create new files `median/Median/Basic*.lean`, imported
   from it. **Do not import `Median.Binary`** (another agent is proving it in parallel, so its theorems are
   `sorry` here), and do not modify any other file.
3. No `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`, or options that
   weaken kernel checking. Raising `maxHeartbeats` locally is allowed if really needed.
4. Do **not** run writing git commands and do not run `lake update` or `lake exe cache get`.

## Commands

```bash
cd median
lake build Median.Basic                    # fast check of your file
lake build                              # whole package; your file must have no warnings
lake env lean Audit.lean                # the axioms of the eight theorems of Basic.lean must be only
                                        # propext, Classical.choice, Quot.sound
```
(`Audit.lean` also lists the other agent's theorems, which still show `sorryAx` here: ignore those.)

Keep `median/PROGRESS.md` up to date (proved / remaining / current errors / plan).

## Mathematical plan

1. **`med3_monotone`**: `med3 a b c = max (min a b) (min (max a b) c)`, and a monotone map between
   linear orders commutes with `min` and `max` (`Monotone.map_min`, `Monotone.map_max`).
2. **`threshold_step`**: `fun a => decide (θ ≤ a)` is monotone into `Bool` (`false < true`); apply 1.
   pointwise. **`threshold_run`**: induction on the list (`run` is `List.foldl step`), generalizing `x`.
3. **`step_mem`**: the median of three values is one of them (case analysis on the order).
   **`step_mem_Icc`**: `min`/`max` of values in an interval stay in it.
4. **`step_of_consensus`**: `med3 c c c = c`.
5. **`expected_ones`**: `ones y = ∑ v, [y v = true]`; by linearity it suffices to average, for each
   node `v`, the indicator that `v` holds `true` after the round. It depends only on `r v`, which is
   uniform on `Fin n × Fin n`, i.e. two independent uniform nodes. A `true` node stays `true` unless
   both samples are `false` (probability `(1-p)²`); a `false` node becomes `true` iff both samples
   are `true` (probability `p²`), with `p = ones x / n`. Summing:
   `k (1 - (1-p)²) + (n - k) p² = n (3p² - 2p³)` for `k = ones x = n p`.
6. **`absorbed`**: `Dynamics.Kernel.finite_absorption` with `f = notConsensus` (values in `{0,1}`):
   from a consensus configuration the kernel stays there (4.), and from any configuration the round
   in which every node samples node `0` twice has positive probability and gives consensus on
   `x 0` (since `med3 a c c = c`). Use `Kernel.apply_ofStep` to turn the kernel into an average over
   rounds.

When all eight theorems are proved, `lake build` succeeds with no warnings in your file and
`Audit.lean` shows only standard axioms for them, write a short final summary.
