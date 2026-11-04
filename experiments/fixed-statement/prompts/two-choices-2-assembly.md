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

## Status: only the final assembly remains

A previous session already wrote and compiled (no `sorry`, no errors) `median/Median/BinaryAux.lean`
and `median/Median/BinaryPhases.lean`: the counting layer, expectation identities, Hoeffding and
Bernstein wrappers, the numerics for `log n ≥ 128`, the kernel plumbing (probabilities,
absorbing-event monotonicity, `expList` conversion), and the three phase moves
`growth_move`, `sat_move` and `mono_move`. Its plan and notes are in `median/PROGRESS.md`.

**Your job now is only the assembly**: read `median/PROGRESS.md` and both files first, then
combine the phase moves with `Dynamics.Kernel.nested_phases` (growth sets, saturation sets,
consensus; `ℓ = 4` rounds per phase) exactly as `plurality/Plurality/Upper.lean` assembles its
phases for `Plurality.theorem_3_8`, convert the kernel statement to the `expList` form of
`consensus_whp` (padding the number of rounds by monotonicity of the absorbing event), and
prove `consensus_whp` with the constant `C = 128` (or another one if needed). Do not rewrite
the existing moves unless an interface forces a small change. Run `lake build` often.

When `consensus_whp` is proved, `lake build` succeeds with no warnings in your files, and
`Audit.lean` shows only standard axioms for `consensus_whp`, write a short final summary that
states the constant `C` you used.
