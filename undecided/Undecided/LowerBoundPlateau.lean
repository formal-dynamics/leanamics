import Undecided.LowerBoundBasic

/-! # The `Ω(md(c))` lower bound (UND-3): the plateau (SODA 2015, Lemma 7)

[BCNPS15, Lemma 7] ("Plateau"): let `k ≤ ε (n / log n)^{1/4}`. If at some round
`|q - n/2| ≤ 2γ² n / md(c̄)` and `c_m ≤ γ n / md(c̄)`, then the plurality stays below
`2γ n / md(c̄)` for the next `Ω(md(c̄))` rounds w.h.p.

The proof shows that one round keeps the window `|q - n/2| ≤ 2γ² n / md(c̄)` and multiplies the
plurality by at most `1 + a / md(c̄)` w.h.p.; then `(1 + a / md)^T ≤ 2` for `T = O(md)`.
The one-round step (`plateau_step`) has failure probability `C / n²`, so that it can be iterated
over `T ≤ D / C ≤ n` rounds. Here the monochromatic distance `md(c̄)` of the initial
configuration is a real parameter `D ≤ k` (as `md(c̄) ≤ k`, `md_le_card`).

Corrections (see `PROGRESS-UND3.md`):
* the bound is kept for **every** colour (`maxCount`): the proof bounds `∑ⱼ cⱼ²` and uses
  `c_m ≥ (n - q)/k`, which hold for the largest colour, not for a fixed colour `m`;
* the growth factor is `1 + (4γ² + 2γ + 1)/D`, not `1 + (2γ(γ + 1) + 1)/D`: from
  `|q - n/2| ≤ 2γ² n / D` the term `2δ/n` in `µ_m = (1 + (2δ + c_m)/n) c_m` is at most `4γ²/D`;
* the lower bound `E[Q' - n/2] ≥ -(4/9) n / D` needs a minor correction (it bounds `∑ⱼ cⱼ²` from
  above by `k ((n - q)/k)²`, which is a lower bound): with `∑ⱼ cⱼ² ≤ maxⱼ cⱼ · (n - q)` one gets
  `E[Q' - n/2] ≥ -(4γ/3) n / D`, which stays inside the window for `γ ≥ 1` (not for an arbitrary
  `γ > 0`: for `γ < 1/2` the window is left in one round from configurations with many equal
  colours).
-/

namespace Undecided.Plurality
open Finset Dynamics Real

/-- **One round of the plateau** (proof of [BCNPS15, Lemma 7], corrected growth factor). Let
`γ ≥ 1`. There is `C > 0` such that, for every `n` with `log n ≥ C`, every `k` with
`C k ≤ (n / log n)^{1/4}`, every `D` with `C ≤ D ≤ k`, every configuration `y` with
`|q - n/2| ≤ 2γ² n / D` and every `B ∈ [γ n / D, 2γ n / D]` bounding all colours of `y`, after
one round, with probability at least `1 - C / n²`, all colours are at most
`(1 + (4γ² + 2γ + 1)/D) B` and still `|q - n/2| ≤ 2γ² n / D`. -/
theorem plateau_step : ∀ γ : ℝ, 1 ≤ γ → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, C ≤ Real.log n →
    ∀ k : ℕ, C * k ≤ ((n : ℝ) / Real.log n) ^ ((1 : ℝ) / 4) → ∀ D : ℝ, C ≤ D → D ≤ k →
    ∀ (y : Config n k) (B : ℝ), γ * n / D ≤ B → B ≤ 2 * γ * n / D →
      |und y - n / 2| ≤ 2 * γ ^ 2 * n / D → (maxCount y : ℝ) ≤ B →
      miss {z | (maxCount z : ℝ) ≤ (1 + (4 * γ ^ 2 + 2 * γ + 1) / D) * B ∧
        |und z - n / 2| ≤ 2 * γ ^ 2 * n / D} 1 y ≤ C / n ^ 2 := by
  sorry

/-- **Lemma 7 of [BCNPS15]** (plateau). Let `γ ≥ 1`. There is `C > 0` such that, for every `n`
with `log n ≥ C`, every `k` with `C k ≤ (n / log n)^{1/4}`, every `D` with `C ≤ D ≤ k` (the
monochromatic distance of the initial configuration), every configuration `y` with
`|q - n/2| ≤ 2γ² n / D` and all colours at most `γ n / D`, and every `T` with `C T ≤ D`: after
`T` rounds, with probability at least `1 - C / n`, all colours are at most `2γ n / D` and
`|q - n/2| ≤ 2γ² n / D`. -/
theorem plateau : ∀ γ : ℝ, 1 ≤ γ → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, C ≤ Real.log n →
    ∀ k : ℕ, C * k ≤ ((n : ℝ) / Real.log n) ^ ((1 : ℝ) / 4) → ∀ D : ℝ, C ≤ D → D ≤ k →
    ∀ y : Config n k, |und y - n / 2| ≤ 2 * γ ^ 2 * n / D → (maxCount y : ℝ) ≤ γ * n / D →
    ∀ T : ℕ, C * T ≤ D →
      miss {z | (maxCount z : ℝ) ≤ 2 * γ * n / D ∧ |und z - n / 2| ≤ 2 * γ ^ 2 * n / D} T y
        ≤ C / n := by
  sorry

end Undecided.Plurality
