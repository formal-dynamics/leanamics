# Consensus from any configuration: map of the development

Status: **done.** `binary_any_start`, `consensus_of_binary` and `median_consensus_any`
(`Median/AnyStart.lean`) are proved; `lake build Median` is warning-free; `lake env lean Audit.lean`
shows only `propext`, `Classical.choice`, `Quot.sound`. The pinned statements, imports and
`namespace`/`open`/`variable` lines are unchanged, except for added `import Median.AnyStart...`
lines. There are no `set_option`s, and every declaration fits in 50000 heartbeats (a quarter
of the default budget; checked with `lake env lean -DmaxHeartbeats=50000`).

## Proof route

With `L = log n` and `g = gapR y` (`#true - #false`):

1. **Reduction to two values** (`consensus_of_binary`). A run that has not reached consensus has
   two nodes with values `a < b`; the threshold configuration `decide (b ≤ x ·)` follows the
   same rounds (`threshold_run`) and has not reached consensus either
   (`notConsensus_run_le_sum`). A union bound over the at most `n - 1` thresholds follows.
2. **Amplification** (`median_consensus_any`). Three blocks of `⌈C₀ L⌉` rounds turn the binary
   bound `C₀/n` into `(C₀/n)³` (`expList_amplify`), and `n (C₀/n)³ ≤ (3C₀ + 3)/n` because
   `C₀³ ≤ n` (`pow_three_le_of_log`, `mul_div_pow_three_le`).
3. **2-Choices from any start** (`binary_any_start`, `C = 2¹⁸`): two phases composed by
   `expList_add_le`, padded by `expList_run_mono`.
   * **Escape** (`escape_bound`, `L ≥ 8192`, `⌈2¹⁷ L⌉` rounds, failure `2/n`). The potential
     `gapPot y = exp (-|g| / (256 √n))` satisfies the one-round drift (`avg_gapPot_step`)
     `𝔼 gapPot' ≤ e^{-1/65536} gapPot + e^{1/131072 - √n/512}`. By the flip symmetry, take
     `g ≥ 0`:
     - `√n/64 ≤ g ≤ n/2` (`avg_gapPot_step_far`): Hoeffding's lemma at every node bounds the
       exponential moment of the next gap (`avg_exp_neg_gapR_step`), and the mean gap is at
       least `11g/8` (`meanGap_ge`);
     - `g > n/2` (`avg_gapPot_step_huge`): the same bound gives the additive error;
     - `g ≤ √n/64` (`avg_gapPot_step_near`): the next gap has variance at least `n/10`
       (`one_tenth_le_variance_coord`), so Paley-Zygmund (`avg_pz_zero_one`) gives
       `|g'| ≥ √n/4`, where the potential is at most `e^{-1/1024}`, with probability at least
       `9/64`.

     The fixed-time drift lemma (`expList_le_of_drift`) iterates this over `T` rounds. Markov's
     inequality (`gapPot ≥ e^{-√L/2}` below the threshold) and `escape_error_le` bound the
     probability that `|g| < 128 √(nL)` by `2/n`.
   * **Consensus** (`finish_bound`, `⌈128 L⌉` rounds, failure `128/n`): `binary_consensus` on the
     configuration, or on its flip if `g < 0` (`expList_notConsensus_run_flip`).

## Files

Import order: `Scalar`, `Moments`, `Drift` (generic), then `Aux`, `Gap`, `Potential`, `Phases`,
`Reduction`, `AnyStart`.

| File | Lines | Content |
|---|---|---|
| `AnyStart.lean` | 103 | the three pinned theorems, each a short outline |
| `AnyStartScalar.lean` | 151 | real inequalities: round budgets, `c³ ≤ x`, constants, escape error |
| `AnyStartMoments.lean` | 292 | moments of sums of independent coordinates, Paley-Zygmund, Hoeffding mgf, `{0,1}` coordinates |
| `AnyStartDrift.lean` | 88 | fixed-time drift and two-phase composition for any finite kernel |
| `AnyStartAux.lean` | 179 | `notConsensus` facts, values stay initial, consensus absorbs, amplification |
| `AnyStartGap.lean` | 161 | flip symmetry, the gap after one round, `meanGap`, variance near balance |
| `AnyStartPotential.lean` | 219 | the potential `gapPot` and its one-round drift |
| `AnyStartPhases.lean` | 116 | `escape_bound`, `finish_bound` |
| `AnyStartReduction.lean` | 61 | threshold witness, number of distinct values |

Main lemmas by file:

* `AnyStartScalar`: `ceil_add_ceil_le`, `mul_ceil_le_ceil`, `pow_three_le_of_log`,
  `mul_div_pow_three_le`, `sq_mul_one_sub_sq_ge`, `le_abs_two_mul_add`, `near_const_le`,
  `log_pow_four_div_le`, `escape_error_le`.
* `AnyStartMoments`: `avg_cauchy`, `avg_head_tail`, `avg_tail`, `avg_sum_coords`, `avg_sum_sq`,
  `avg_sum_fourth_le`, `avg_pz`, `avg_pz_sum`, `avg_pz_zero_one`, `variance_of_zero_one`,
  `avg_exp_sum_le`.
* `AnyStartDrift`: `iterate_le_of_drift`, `iterate_add_le`, `expList_le_of_drift`,
  `expList_add_le`, `expList_one_sub`.
* `AnyStartAux`: `run_mem_image`, `run_append`, `run_consensus`, `expList_run_anti`,
  `expList_run_mono`, `expList_amplify`.
* `AnyStartGap`: `step_flip`, `run_flip`, `gapR_flip`, `notConsensus_flip`, `gapR_step`,
  `gapR_step_eq`, `meanGap` (with `meanGap_eq : meanGap y = g (3/2 - g²/(2n²))`),
  `gapR_le_meanGap`, `abs_meanGap_le`, `meanGap_ge`, `one_tenth_le_variance_coord`.
* `AnyStartPotential`: `gapPot`, `exp_neg_le_gapPot`, `gapPot_le_exp_neg`,
  `avg_exp_neg_gapR_step`, `avg_gapPot_step_far`, `avg_gapPot_step_huge`,
  `avg_gapPot_step_near`, `avg_gapPot_step`.
* `AnyStartPhases`: `escape_bound`, `expList_notConsensus_le_of_gap`, `finish_bound`.
* `AnyStartReduction`: `notConsensus_run_le_sum`, `card_image_sub_one_le`.

## Candidates for `dynamics/` (not moved yet)

These lemmas only use `Dynamics` notions (`avg`, `expList`, `variance`, `Kernel`) or plain reals.
They now live in namespace `Median`.

* To `Dynamics/Kernel.lean`: `iterate_le_of_drift` (fixed-time drift),
  `iterate_add_le` (two phases).
* To `Dynamics/Rounds.lean`: `expList_le_of_drift`, `expList_add_le`.
* To `Dynamics/Uniform.lean`: `expList_one_sub`, `avg_cauchy`, `avg_head_tail`, `avg_tail`,
  `sum_head_tail`, `avg_sum_coords`.
* To `Dynamics/Concentration.lean`: `avg_exp_sum_le` (Hoeffding's mgf bound for any real `t`;
  `Dynamics.avg_hoeffding` proves it inline and could then use it), `avg_sum_sq`,
  `avg_sum_fourth_le`, `avg_pz`, `avg_pz_sum`, `avg_pz_zero_one`, `avg_nonneg_of_zero_one`,
  `avg_le_one_of_zero_one`, `abs_sub_avg_le_one_of_zero_one`, `variance_of_zero_one`.
* Plain real inequalities (a scalar-lemma file, or Mathlib-style helpers): `ceil_add_ceil_le`,
  `mul_ceil_le_ceil`, `pow_three_le_of_log`, `log_pow_four_div_le`.
