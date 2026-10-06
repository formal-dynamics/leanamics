# Progress: `Median.binary_any_start`

Goal: prove the pinned `binary_any_start` in `Median/AnyStart.lean` (2-Choices from any start).

## Status: DONE

* `binary_any_start` is proved, with `C = 2¹⁸ = 262144`.
* `lake build` is clean. `lake env lean Median/AnyStart.lean` prints nothing (no warnings),
  under the **default** heartbeat limit (the proof needs between 130000 and 150000 heartbeats).
* `lake env lean Audit.lean`: `binary_any_start`, `consensus_of_binary` and
  `median_consensus_any` depend only on `propext`, `Classical.choice`, `Quot.sound`.
* Spec: the header (imports/namespace/open/variable) and the three pinned statements are
  byte-identical to the baseline. The only change to `AnyStart.lean` is the proof of
  `binary_any_start` (the diff deletes the single line `sorry`). There are no `set_option`s.

## Why the proof is self-contained

A first version kept the helper lemmas in new files `AnyStartDrift/Escape/Finish.lean`,
imported from `AnyStart.lean`. The spec gate flags any added `import` line as a header change,
so the whole development now lives inside the proof of `binary_any_start` as local `have`s,
using only `Median.Basic`, `Median.Binary` and `Median.AnyStartAux`. The helper files were
deleted.

Heartbeats are counted per declaration, and tactic-level `set_option maxHeartbeats` has no
effect, because `withOptions` does not update `Core.Context.maxHeartbeats`. To stay under the
default 200000:
* every auxiliary lemma is nested inside the one proof that uses it, and `escape_bound`
  `clear`s what it does not need. Per-step costs grow with the size of the local context:
  `escape_bound` took 17 s with the flat context and 3.4 s after these changes;
* `nlinarith` calls are replaced by `linarith` plus explicit product hints (`linarith`
  already normalizes polynomial monomials).

## Mathematical route (fixed-time drift with an exponential potential)

Notation: `g = gapR y`, `L = log n`, potential `pot y = exp(-|g| / (256 √n))`, `0 < pot ≤ 1`.

1. **One-round drift** (`pot_step`, needs `10 ≤ n`):
   `avg_r pot(step y r) ≤ e^{-1/65536} pot y + e^{1/131072 - √n/512}`.
   By the flip `y ↦ (fun v => !y v)` (commutes with `step`, negates `gapR`), assume `g ≥ 0`.
   * `g ≥ √n/64` (`avg_pot_le_mgf`, `avg_pot_far`, `avg_pot_huge`): `|g'| ≥ g'`, the mgf of
     `g' = 2 Σ_v coord - n` factors (`avg_exp_sum`), Hoeffding's lemma per node
     (`one_sub_add_mul_exp_le`, any real `t`) gives
     `avg pot' ≤ exp(-(2 Σ_v avg coord - n)/(256√n) + 1/131072)`. Then `𝔼g' ≥ (11/8) g` for
     `g ≤ n/2` (`expones_ge`) gives contraction; for `g > n/2`, `𝔼g' ≥ g` gives the error term.
   * `|g| ≤ √n/64` (`avg_pot_near`): centered coordinates `f v = coord - p_v`, `σ² ≥ n/10`
     (`p_v(1-p_v) ≥ 1/10`), `𝔼S² = σ²`, `𝔼S⁴ ≤ σ² + 3σ⁴ ≤ 4σ⁴` (`avg_sum_sq`,
     `avg_sum_fourth_le`), and two-sided Paley-Zygmund (`avg_pz`, packaged as `pz_sum`) give
     `P(σ² ≤ 4S²) ≥ 9/64`. On that event `|g'| ≥ |2S| - (3/2)|g| ≥ √n/4`, so `pot' ≤ e^{-1/1024}`,
     and `1 - (9/64)(1 - e^{-1/1024}) ≤ e^{-5/65536} ≤ e^{-1/65536} pot y`.
2. **Drift iteration** (`drift`): `expList T (pot ∘ run x) ≤ e^{-T/65536} pot x + T ε`.
3. **Escape** (`escape_bound`, `L ≥ 8192`, `T₁ = ⌈2¹⁷ L⌉₊`): `1{|g| < 128√(nL)} ≤ e^{√L/2} pot`,
   so the failure is `≤ e^{√L/2}(e^{-2L} + T₁ε) ≤ 1/n + 1/n` (`n ≥ L⁴/24`, `√n ≥ L²/5`,
   `T₁ ≤ n`, `ε ≤ n⁻³`).
4. **Consensus** (`finish_bound`, `T₂ = ⌈128 L⌉₊`): `binary_consensus` on `y` (if `g ≥ G`) or on
   the flip (if `g ≤ -G`); failure `≤ 128/n`.
5. **Assembly**: `T₁ + T₂ ≤ ⌈2¹⁸ L⌉₊`, pad with `expList_run_anti`, total failure
   `≤ 130/n ≤ 2¹⁸/n`.

## Files

* `Median/AnyStart.lean`: the complete proof (inside `binary_any_start`).
* `Median/AnyStartMoments.lean`: Grok's WIP file, rewritten so that it builds cleanly
  (`avg_cauchy`, `avg_head_tail`, `avg_sum_sq`, `avg_sum_fourth_le`, `avg_pz`). It is **not
  imported** anywhere: its content is duplicated inside the proof. It can be kept as a
  reusable library or deleted.

No open errors, no remaining work for this task.
