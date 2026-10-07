import Dynamics.Concentration

/-! # Two-sided Bernstein bound for sums of independent indicators (UND-3)

For `X = ∑ᵢ Yᵢ(ωᵢ)` with independent `{0,1}`-valued coordinates and mean `μ`, Bernstein's
inequality (`Dynamics.avg_bernstein`, with variance bound `μ + 2ℓ` and `b = 1`) gives, for every
`ℓ > 0`,
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

/-- The exponent of Bernstein's bound with `σ² = M ≥ 2ℓ`, `b = 1` and `λ = √(3ℓM)` is at
least `ℓ`. -/
lemma bernstein_exponent {ℓ M : ℝ} (hℓ : 0 < ℓ) (hM : 2 * ℓ ≤ M) :
    exp (-(√(3 * ℓ * M) ^ 2 / (2 * M * (1 + 1 * √(3 * ℓ * M) / (3 * M))))) ≤ exp (-ℓ) := by
  apply exp_le_exp.mpr
  have hM0 : 0 < M := by linarith
  have hl0 : 0 ≤ √(3 * ℓ * M) := sqrt_nonneg _
  have hsq : √(3 * ℓ * M) ^ 2 = 3 * ℓ * M := sq_sqrt (by positivity)
  -- `2λ ≤ 3M`, from `4λ² = 12ℓM ≤ 9M²`
  have hlam : 2 * √(3 * ℓ * M) ≤ 3 * M := by nlinarith
  have hden : 0 < 2 * M * (1 + 1 * √(3 * ℓ * M) / (3 * M)) := by positivity
  rw [neg_le_neg_iff, le_div_iff₀ hden, hsq]
  have e : 2 * M * (1 + 1 * √(3 * ℓ * M) / (3 * M)) = 2 * M + 2 * √(3 * ℓ * M) / 3 := by
    field_simp
  rw [e]
  nlinarith

variable {n : ℕ} {γ : Type*} [Fintype γ]

/-- An indicator coordinate has variance at most its mean. -/
lemma variance_le_avg_of_01 [Nonempty γ] {f : γ → ℝ} (hf : ∀ x, f x = 0 ∨ f x = 1) :
    variance f ≤ avg f := by
  refine (variance_le_avg_sq f).trans_eq ?_
  congr 1
  funext x
  rcases hf x with h | h <;> simp [h]

lemma avg_01_nonneg {f : γ → ℝ} (hf : ∀ x, f x = 0 ∨ f x = 1) : 0 ≤ avg f :=
  avg_nonneg fun x => by rcases hf x with h | h <;> simp [h]

lemma avg_01_le_one [Nonempty γ] {f : γ → ℝ} (hf : ∀ x, f x = 0 ∨ f x = 1) : avg f ≤ 1 :=
  (avg_le_avg fun x => by rcases hf x with h | h <;> simp [h]).trans_eq (avg_const 1)

/-- **Upper tail**: `P(X ≥ μ + dev ℓ μ) ≤ e^{-ℓ}` for a sum of independent indicators with
mean `μ`. -/
theorem tail_up [Nonempty γ] (Y : Fin n → γ → ℝ) (hY : ∀ i x, Y i x = 0 ∨ Y i x = 1) {ℓ : ℝ}
    (hℓ : 0 < ℓ) :
    avg (fun ω : Fin n → γ =>
        if (∑ i, avg (Y i)) + dev ℓ (∑ i, avg (Y i)) ≤ ∑ i, Y i (ω i) then (1 : ℝ) else 0)
      ≤ exp (-ℓ) := by
  set μ := ∑ i, avg (Y i) with hμ
  have hμ0 : 0 ≤ μ := sum_nonneg fun i _ => avg_01_nonneg (hY i)
  have hM : 2 * ℓ ≤ μ + 2 * ℓ := by linarith
  have hσ : ∑ i, variance (Y i) ≤ μ + 2 * ℓ := by
    have : ∑ i, variance (Y i) ≤ μ := sum_le_sum fun i _ => variance_le_avg_of_01 (hY i)
    linarith
  have hb : ∀ i x, Y i x - avg (Y i) ≤ 1 := fun i x => by
    have := avg_01_nonneg (hY i)
    rcases hY i x with h | h <;> rw [h] <;> linarith
  refine (avg_bernstein Y one_pos hb hσ (by linarith) (dev_nonneg ℓ μ)).trans ?_
  exact bernstein_exponent hℓ hM

/-- **Lower tail**: `P(X ≤ μ - dev ℓ μ) ≤ e^{-ℓ}` for a sum of independent indicators with
mean `μ`. -/
theorem tail_down [Nonempty γ] (Y : Fin n → γ → ℝ) (hY : ∀ i x, Y i x = 0 ∨ Y i x = 1)
    {ℓ : ℝ} (hℓ : 0 < ℓ) :
    avg (fun ω : Fin n → γ =>
        if ∑ i, Y i (ω i) ≤ (∑ i, avg (Y i)) - dev ℓ (∑ i, avg (Y i)) then (1 : ℝ) else 0)
      ≤ exp (-ℓ) := by
  set μ := ∑ i, avg (Y i) with hμ
  have hμ0 : 0 ≤ μ := sum_nonneg fun i _ => avg_01_nonneg (hY i)
  have hM : 2 * ℓ ≤ μ + 2 * ℓ := by linarith
  set Z : Fin n → γ → ℝ := fun i x => -Y i x with hZ
  have havgZ (i : Fin n) : avg (Z i) = -avg (Y i) := by
    have := avg_const_mul (-1) (Y i)
    simp only [neg_one_mul] at this
    exact this
  have hvarZ (i : Fin n) : variance (Z i) = variance (Y i) := by
    unfold variance
    rw [havgZ]
    congr 1
    funext x
    simp only [hZ]
    ring
  have hσ : ∑ i, variance (Z i) ≤ μ + 2 * ℓ := by
    have : ∑ i, variance (Z i) ≤ μ := by
      simp_rw [hvarZ]
      exact sum_le_sum fun i _ => variance_le_avg_of_01 (hY i)
    linarith
  have hb : ∀ i x, Z i x - avg (Z i) ≤ 1 := fun i x => by
    rw [havgZ]
    have := avg_01_le_one (hY i)
    simp only [hZ]
    rcases hY i x with h | h <;> rw [h] <;> linarith
  have key := avg_bernstein Z one_pos hb hσ (by linarith) (dev_nonneg ℓ μ)
  have hsumZ : ∑ i, avg (Z i) = -μ := by
    simp_rw [havgZ]
    rw [sum_neg_distrib]
  rw [hsumZ] at key
  refine le_trans (le_of_eq ?_) (key.trans (bernstein_exponent hℓ hM))
  congr 1
  funext ω
  have e : ∑ i, Z i (ω i) = -∑ i, Y i (ω i) := by
    simp only [hZ]
    rw [sum_neg_distrib]
  rw [e]
  congr 1
  apply propext
  constructor <;> intro h <;> linarith

end Undecided.Plurality
