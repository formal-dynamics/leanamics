import Undecided.PluralityStages

/-! # The `Ω(md(c))` lower bound (UND-3, SODA 2015, Theorem 8): basic quantities

Becchetti, Clementi, Natale, Pasquale and Silvestri, *Plurality consensus in the gossip model*
(SODA 2015, arXiv:1407.2565), Section 2.1. Besides the monochromatic distance
`md(c) = ∑ᵢ (cᵢ / c₁)²` (`Undecided.Plurality.md`), the analysis of the lower bound uses

* the ratio `R(c) = ∑ᵢ cᵢ / c₁` (`ratioR`), where `c₁ = maxᵢ cᵢ` (`maxCount`);
* the ratio `Λ(c) = R(c)² / md(c)` (`ratioLam`), with `Λ(c) ≤ k` (the paper's (2),
  `ratioLam_le_card`).

Without undecided nodes, `R(c) = n / c₁` and `Λ(c) = n² / ∑ᵢ cᵢ²` (`ratioR_of_und_zero`,
`ratioLam_of_und_zero`), so that one round from `c` gives in expectation `c₁² / n = n / R(c)²`
nodes of the plurality colour and `n (1 - 1/Λ(c))` undecided nodes (the proof of Lemma 3).

In terms of `δ = q - n/2`, the expectations (3) and (4) read
`µᵢ = (1 + (2δ + cᵢ)/n) cᵢ` and `E[Q' - n/2] = (2δ² - ∑ⱼ cⱼ²)/n`: the paper's (19) and (20),
in the proof of Lemma 7 (`mu_eq_half`, `muU_sub_half`).
-/

namespace Undecided.Plurality
open Finset Dynamics Real

variable {n k : ℕ}

/-- The ratio `R(c) = ∑ᵢ cᵢ / c₁` of Section 2.1, where `c₁ = maxᵢ cᵢ` (`maxCount`). -/
noncomputable def ratioR (x : Config n k) : ℝ := ∑ i, (count x (some i) : ℝ) / maxCount x

/-- The ratio `Λ(c) = R(c)² / md(c)` of Section 2.1. -/
noncomputable def ratioLam (x : Config n k) : ℝ := ratioR x ^ 2 / md x

/-- Defining equation of `ratioR` (Section 2.1): `R(c) = ∑ᵢ cᵢ / c₁`. -/
theorem ratioR_def (x : Config n k) :
    ratioR x = ∑ i, (count x (some i) : ℝ) / maxCount x := rfl

/-- Defining equation of `ratioLam` (Section 2.1): `Λ(c) = R(c)² / md(c)`. -/
theorem ratioLam_def (x : Config n k) : ratioLam x = ratioR x ^ 2 / md x := rfl

/-! ### Elementary facts -/

lemma ratio_term_nonneg (x : Config n k) (i : Fin k) :
    0 ≤ (count x (some i) : ℝ) / maxCount x := by positivity

lemma ratio_term_le_one (x : Config n k) (i : Fin k) :
    (count x (some i) : ℝ) / maxCount x ≤ 1 := by
  rcases Nat.eq_zero_or_pos (maxCount x) with h | h
  · simp [h]
  · rw [div_le_one (by exact_mod_cast h)]
    exact_mod_cast count_le_maxCount x i

lemma ratioR_nonneg (x : Config n k) : 0 ≤ ratioR x :=
  sum_nonneg fun i _ => ratio_term_nonneg x i

lemma md_nonneg (x : Config n k) : 0 ≤ md x := by
  rw [md_def]
  exact sum_nonneg fun i _ => sq_nonneg _

/-- `md(c) ≤ R(c)`, since every ratio `cᵢ / c₁` lies in `[0, 1]`. -/
theorem md_le_ratioR (x : Config n k) : md x ≤ ratioR x := by
  rw [md_def, ratioR_def]
  refine sum_le_sum fun i _ => ?_
  have h0 := ratio_term_nonneg x i
  have h1 := ratio_term_le_one x i
  nlinarith

/-- `R(c) ≤ k`. -/
theorem ratioR_le_card (x : Config n k) : ratioR x ≤ k := by
  calc ratioR x ≤ ∑ _i : Fin k, (1 : ℝ) := sum_le_sum fun i _ => ratio_term_le_one x i
    _ = k := by simp

/-- `R(c)² ≤ k · md(c)` (Cauchy–Schwarz). -/
lemma ratioR_sq_le (x : Config n k) : ratioR x ^ 2 ≤ k * md x := by
  have h := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin k)))
    (f := fun i => (count x (some i) : ℝ) / maxCount x)
  rw [card_univ, Fintype.card_fin] at h
  rw [ratioR_def, md_def]
  exact h

/-- The paper's (2): `Λ(c) ≤ k`. -/
theorem ratioLam_le_card (x : Config n k) : ratioLam x ≤ k := by
  rw [ratioLam_def]
  rcases (md_nonneg x).eq_or_lt with h | h
  · rw [← h, div_zero]
    exact Nat.cast_nonneg k
  · rw [div_le_iff₀ h]
    exact ratioR_sq_le x

/-- `md(c) ≤ Λ(c)`, from `md(c) ≤ R(c)`. -/
theorem md_le_ratioLam (x : Config n k) : md x ≤ ratioLam x := by
  rw [ratioLam_def]
  rcases (md_nonneg x).eq_or_lt with h | h
  · rw [← h, div_zero]
  · rw [le_div_iff₀ h]
    have := md_le_ratioR x
    nlinarith

/-! ### Configurations without undecided nodes -/

lemma sum_count_of_und_zero (x : Config n k) (hq : count x none = 0) :
    ∑ i, (count x (some i) : ℝ) = n := by
  have h := count_none_add_sum x
  rw [hq, zero_add] at h
  exact_mod_cast h

lemma maxCount_pos_of_und_zero (x : Config n k) (hq : count x none = 0) (hn : 0 < n) :
    0 < maxCount x := by
  have h := count_none_add_sum x
  rw [hq, zero_add] at h
  by_contra h0
  have h0 : maxCount x = 0 := by omega
  have : ∑ i, count x (some i) = 0 :=
    sum_eq_zero fun i _ => Nat.eq_zero_of_le_zero (h0 ▸ count_le_maxCount x i)
  omega

/-- Without undecided nodes, `R(c) = n / c₁`. -/
theorem ratioR_of_und_zero (x : Config n k) (hq : count x none = 0) :
    ratioR x = n / maxCount x := by
  rw [ratioR_def, ← sum_div, sum_count_of_und_zero x hq]

/-- Without undecided nodes, `Λ(c) = n² / ∑ᵢ cᵢ²`. -/
theorem ratioLam_of_und_zero (x : Config n k) (hq : count x none = 0) (hn : 0 < n) :
    ratioLam x = (n : ℝ) ^ 2 / ∑ i, (count x (some i) : ℝ) ^ 2 := by
  have hM : (0 : ℝ) < maxCount x := by exact_mod_cast maxCount_pos_of_und_zero x hq hn
  rw [ratioLam_def, ratioR_of_und_zero x hq, md_def]
  simp_rw [div_pow]
  rw [← sum_div, div_div_div_cancel_right₀ (by positivity)]

/-! ### The expectations in terms of `δ = q - n/2` (proof of Lemma 7) -/

/-- The paper's (20): `µᵢ = (1 + (2δ + cᵢ)/n) cᵢ` with `δ = q - n/2`. -/
theorem mu_eq_half (x : Config n k) (i : Fin k) (hn : 0 < n) :
    mu x i = (1 + (2 * (und x - n / 2) + cnt x i) / n) * cnt x i := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold mu
  field_simp
  ring

/-- The paper's (19): `E[Q' - n/2] = (2δ² - ∑ⱼ cⱼ²)/n` with `δ = q - n/2`. -/
theorem muU_sub_half (x : Config n k) (hn : 0 < n) :
    muU x - n / 2 = (2 * (und x - n / 2) ^ 2 - ∑ j, cnt x j ^ 2) / n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold muU
  field_simp
  ring

end Undecided.Plurality
