import Dynamics.Concentration

/-! # Two-sided Bernstein bound for sums of independent indicators (UND-3)

For `X = ∑ᵢ Yᵢ(ωᵢ)` with independent `{0,1}`-valued coordinates and mean `μ`, Bernstein's
inequality (`Dynamics.avg_bernstein`, with variance bound `μ + 2ℓ` and `b = 1`; the core
corollaries `Dynamics.avg_bernstein_of_zero_one` and `avg_bernstein_lower_of_zero_one`) gives,
for every `ℓ > 0`,
`P(X ≥ μ + dev ℓ μ) ≤ e^{-ℓ}` and `P(X ≤ μ - dev ℓ μ) ≤ e^{-ℓ}`, where
`dev ℓ μ = √(3ℓ(μ + 2ℓ))`. The deviation is multiplicative (`≈ √(3ℓμ)`) for large means, which
the `k`-colour analysis needs for colour communities much smaller than `√(n log n)`.
-/

namespace Undecided.Plurality
open Finset Dynamics Real

/-- The deviation `√(3ℓ(μ + 2ℓ))` of a sum of indicators with mean `μ`. -/
noncomputable def dev (ℓ μ : ℝ) : ℝ := √(3 * ℓ * (μ + 2 * ℓ))

lemma dev_nonneg (ℓ μ : ℝ) : 0 ≤ dev ℓ μ := sqrt_nonneg _

/-- `dev` is monotone in the mean. -/
lemma dev_mono {ℓ μ μ' : ℝ} (hℓ : 0 ≤ ℓ) (h : μ ≤ μ') : dev ℓ μ ≤ dev ℓ μ' := by
  unfold dev
  apply sqrt_le_sqrt
  have : 0 ≤ 3 * ℓ := by positivity
  nlinarith

/-- For a mean at most `M` with `M ≥ 6ℓ`, the deviation is at most `2√(ℓM)`. -/
lemma dev_le {ℓ μ M : ℝ} (hℓ : 0 ≤ ℓ) (hμ : μ ≤ M) (hM : 6 * ℓ ≤ M) :
    dev ℓ μ ≤ 2 * √(ℓ * M) := by
  calc dev ℓ μ ≤ dev ℓ M := dev_mono hℓ hμ
    _ ≤ √((2 : ℝ) ^ 2 * (ℓ * M)) := by
        unfold dev
        apply sqrt_le_sqrt
        nlinarith
    _ = 2 * √(ℓ * M) := by
        rw [sqrt_mul (by norm_num), sqrt_sq (by norm_num)]

variable {n : ℕ} {γ : Type*} [Fintype γ]

/-- **Upper tail**: `P(X ≥ μ + dev ℓ μ) ≤ e^{-ℓ}` for a sum of independent indicators with
mean `μ` (the core `Dynamics.avg_bernstein_of_zero_one`). -/
theorem tail_up [Nonempty γ] (Y : Fin n → γ → ℝ) (hY : ∀ i x, Y i x = 0 ∨ Y i x = 1) {ℓ : ℝ}
    (hℓ : 0 < ℓ) :
    avg (fun ω : Fin n → γ =>
        if (∑ i, avg (Y i)) + dev ℓ (∑ i, avg (Y i)) ≤ ∑ i, Y i (ω i) then (1 : ℝ) else 0)
      ≤ exp (-ℓ) :=
  avg_bernstein_of_zero_one Y hY hℓ

/-- **Lower tail**: `P(X ≤ μ - dev ℓ μ) ≤ e^{-ℓ}` for a sum of independent indicators with
mean `μ` (the core `Dynamics.avg_bernstein_lower_of_zero_one`). -/
theorem tail_down [Nonempty γ] (Y : Fin n → γ → ℝ) (hY : ∀ i x, Y i x = 0 ∨ Y i x = 1)
    {ℓ : ℝ} (hℓ : 0 < ℓ) :
    avg (fun ω : Fin n → γ =>
        if ∑ i, Y i (ω i) ≤ (∑ i, avg (Y i)) - dev ℓ (∑ i, avg (Y i)) then (1 : ℝ) else 0)
      ≤ exp (-ℓ) := by
  simp only [le_sub_iff_add_le]
  exact avg_bernstein_lower_of_zero_one Y hY hℓ

end Undecided.Plurality
