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

## Status: one step left

`median/Median/BinaryAssembly.lean` already proves (no `sorry`, builds, standard axioms)

```lean
theorem binary_consensus {n : ℕ} [NeZero n] (hL : (128 : ℝ) ≤ Real.log n)
    (x : Config n Bool) (hx : 128 * √((n : ℝ) * Real.log n) ≤ gapR x) :
    1 - 128 / (n : ℝ) ≤ expList (Round n) ⌈128 * Real.log n⌉₊
      (fun l => if run x l = (fun _ => true) then (1 : ℝ) else 0)
```

and `median/Median/Binary.lean` already imports it. **Your only job:** replace the `sorry` of
`consensus_whp` in `Binary.lean` by a proof with `C = 128` that applies `binary_consensus`
(relate `gapR x` to `(ones x : ℝ) - (n - ones x)` by unfolding its definition). Do not change
any other file. Then run `lake build` in `median/` and `lake env lean Audit.lean`, and write a
one-paragraph final summary.
