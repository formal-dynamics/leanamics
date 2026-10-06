# Progress: `Median/ManyValues.lean` (fast consensus, odd case of Theorem 21)

## Status: done

- [x] `binary_consensus_fast` (C = 128)
- [x] `median_consensus_fast` (C = 128, from `binary_consensus_fast`)
- [x] `odd_split_consensus` (C' = 2C, from `median_consensus_fast`)

`lake build Median` is warning-free; `lake env lean Audit.lean` shows only `propext`,
`Classical.choice`, `Quot.sound`. No `set_option` anywhere. Every declaration of the development
fits in 25k heartbeats (an eighth of the default), the three pinned proofs in 12k (measured with
`lake env lean -DmaxHeartbeats=N <file>`).

## Map of the development

Imports: `ManyValues` ← `Segments`, `Threshold`, `Split`; `Segments` ← `Kernel`, `Scalar`,
`Fast`, `BinaryAssembly`; `Split` ← `Kernel`, `Threshold`; `Fast` ← `BinaryMoves`;
`Threshold` ← `Basic`; `Kernel` ← `Dynamics.Rounds`; `Scalar` ← `Mathlib`.

| File | Contents |
|---|---|
| `ManyValues.lean` | the three pinned theorems (proofs of 34, 11 and 16 lines) |
| `ManyValuesKernel.lean` | generic kernel / `expList` tools (namespace `Dynamics`, see below) |
| `ManyValuesScalar.lean` | real-number facts: round counts, quadratic thresholds, budget |
| `ManyValuesFast.lean` | `bernstein_move`, `quad_move` (the quadratic saturation move) |
| `ManyValuesSegments.lean` | the four segments of the binary proof and their round counts |
| `ManyValuesThreshold.lean` | many values → two binary threshold runs |
| `ManyValuesSplit.lean` | counting for `2k+1` equally supported values; padding |

## Proof route

### `binary_consensus_fast`
Four segments, each a chain of one-round moves with failure `n⁻²` per round
(`Dynamics.Kernel.event_chain`), composed by `Dynamics.Kernel.event_comp`; `β = 512 log n`.
1. `growth_segment`: gap thresholds `(5/4)^i Δ` (`growth_move`), until the minority is below
   `n/4`; `T₁ ≤ 5 log (n/Δ) + 2` rounds (`exists_growth_rounds` ← `exists_lt_pow_mul`).
2. `linear_sat_segment`: 6 rounds of `sat_move`, `n/4 → n/8`.
3. `quad_sat_segment`: thresholds `q_j = (n/4)(1/2)^(2^j)`, `4 q_j²/n = q_(j+1)`
   (`quad_move`, `quad_threshold_succ`, `max_sq_div_le`); `T₃ ≤ 2 log log n + 3` rounds
   (`exists_quad_rounds` ← `exists_le_two_pow_two_pow`).
4. `consensus_segment`: `nested_phases` with `mono_move`, 8 rounds, failure `10 n⁻²`.

Then padding (`event_absorb_mono`) to `⌈128 (log (n/Δ) + log log n)⌉₊ ≥ T₁ + T₃ + 14`, and the
budget `(T₁ + T₃ + 16) n⁻² ≤ 128/n` (`mul_one_div_sq_le`).

`quad_move` is a corollary of `bernstein_move` (mean of the next minority `≤ (3/4) τ` and
`τ ≥ β` ⟹ next minority `< τ` except w.p. `n⁻²`), with `τ = max (4t²/n) β` and
`𝔼[m'] ≤ 3t²/n` (`expfalses_le`); no case split, no `nlinarith`. Its former hypothesis
`t ≤ n/8` was unused and has been dropped.

### `median_consensus_fast`
The thresholds `u ↦ [v ≤ x u]` (monotone, `threshold_run`) and `u ↦ [x u ≤ v]` (antitone:
`med3_antitone`, `comp_run_of_med3`) run as binary dynamics with the same samples; their gaps are
the two margins (`gap_upper`, `gap_lower`); both all-`true` forces consensus on `v`
(`run_eq_const_of_thresholds`); union bound `expList_ge_of_and` gives `1 - 2C/n`.

### `odd_split_consensus`
`odd_split_margins`: both margins equal `n/(2k+1)` (fiber counting `cast_card_filter_comp`,
`card_filter_le_eq_succ`), so `median_consensus_fast` applies with `Δ = n/(2k+1)` and
`log (n/Δ) = log (2k+1)`. Padding from `⌈C …⌉₊` to `⌈2C …⌉₊` rounds: `expList_run_const_mono`
(← `expList_foldl_mono`) and `nat_ceil_mul_le_of_le`.

## Candidates for `dynamics/` (not moved)

Already in namespace `Dynamics` (`ManyValuesKernel.lean`), so moving them renames nothing:
- `Dynamics.Kernel.event_mono_set`: occupation probability is monotone in the target set.
- `Dynamics.Kernel.event_chain`: chain of one-step moves, failure `T ε`. Kernel analogue of
  `Dynamics.expList_escape` (`Dynamics/Rounds.lean`); the two could be unified.
- `Dynamics.Kernel.event_comp`: composition of two segments (Markov property).
- `Dynamics.expList_ge_of_and`: union bound for two events of `T` uniform rounds.
- `Dynamics.expList_foldl_mono`: an event closed under the update rule has nondecreasing
  probability. `expList` analogue of `Median.event_absorb_mono` (`BinaryMoves.lean`, stated for
  any kernel), which also belongs in `dynamics/`.

Scalar facts (namespace `Median`, `ManyValuesScalar.lean`) that are not about medians:
`exists_lt_pow_mul`, `exists_le_two_pow_two_pow`, `le_pow_ceil_real`, `mul_one_div_sq_le`,
`nat_ceil_mul_le_of_le`, `log_two_ge`, `log_two_le_one`.

Order-theoretic facts that hold for any linear order (`ManyValuesThreshold.lean`):
`med3_antitone` (the median is self-dual), `comp_run_of_med3`.

## Notes

- `linarith` treats `2 * C / n` as an atom unrelated to `C / n` (division by a non-numeral is not
  linearized), hence the `rw [show 2 * C / (n : ℝ) = C / n + C / n by ring]` in
  `median_consensus_fast`; products of atoms are fine.
- `BinaryPhases.lean` duplicates `BinaryMoves.lean` declaration by declaration, so the two cannot
  be imported together; this development uses `BinaryMoves` (via `BinaryAssembly`).
