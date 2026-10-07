import Averaging.ReconstructionSign

/-! # The probabilistic part: Rademacher initialization (Lemma B.1)

For `σ` uniform on `{-1, 1}^{2n}` (`V → ℤˣ`), `P(⟨σ, χ⟩ = 0) = C(2n, n) / 4ⁿ`: the sign vectors
with `⟨σ, χ⟩ = 0` correspond to the `n`-subsets `{v | σ v = χ v}` of the `2n` nodes. With Wallis'
product (`Real.Wallis.le_W`), `C(2n, n) / 4ⁿ ≤ 1 / √(π n)`. Proof of Theorem 3.2 and Lemma B.1 of
Becchetti et al. (arXiv:1511.03927), in exact form.
-/

namespace Averaging
open Finset Matrix Real Dynamics

variable {V : Type*} [Fintype V] [DecidableEq V] {V₁ V₂ : Finset V} {n : ℕ}

/-- The real vector of a sign vector `σ : V → ℤˣ`. -/
lemma cast_units_eq_one_or (u : ℤˣ) : ((u : ℤ) : ℝ) = 1 ∨ ((u : ℤ) : ℝ) = -1 := by
  rcases Int.units_eq_one_or u with h | h <;> simp [h]

/-- The sign vector `χ` as a vector of units. -/
def clusterUnits (V₁ : Finset V) (v : V) : ℤˣ := if v ∈ V₁ then 1 else -1

lemma cast_clusterUnits (hP : IsBalancedPartition V₁ V₂ n) (v : V) :
    ((clusterUnits V₁ v : ℤ) : ℝ) = clusterIndicator V₁ V₂ v := by
  by_cases hv : v ∈ V₁
  · simp [clusterUnits, hv, hP.clusterIndicator_of_mem_left hv]
  · have hv₂ : v ∈ V₂ := (hP.mem_or v).resolve_left hv
    simp [clusterUnits, hv, hP.clusterIndicator_of_mem_right hv₂]

/-- The number of sign vectors `σ` with `⟨σ, χ⟩ = 0` is `C(2n, n)`. -/
lemma card_filter_dotProduct_eq_zero (hP : IsBalancedPartition V₁ V₂ n) :
    (univ.filter fun σ : V → ℤˣ =>
        (fun v => ((σ v : ℤ) : ℝ)) ⬝ᵥ clusterIndicator V₁ V₂ = 0).card =
      (2 * n).choose n := by
  have hc (v : V) := hP.clusterIndicator_eq_one_or v
  have hsign (σ : V → ℤˣ) (v : V) := cast_units_eq_one_or (σ v)
  -- `σ ↦ {v | σ v = χ v}` and its inverse `S ↦ (v ↦ ±χ v)`
  let i : (V → ℤˣ) → Finset V :=
    fun σ => univ.filter fun v => ((σ v : ℤ) : ℝ) = clusterIndicator V₁ V₂ v
  let j : Finset V → V → ℤˣ :=
    fun S v => if v ∈ S then clusterUnits V₁ v else -clusterUnits V₁ v
  have hj (S : Finset V) (v : V) :
      ((j S v : ℤ) : ℝ) = clusterIndicator V₁ V₂ v ↔ v ∈ S := by
    by_cases hv : v ∈ S
    · simp [j, hv, cast_clusterUnits hP v]
    · simp only [j, hv, if_false, Units.val_neg, Int.cast_neg, cast_clusterUnits hP v, iff_false]
      rcases hc v with h | h <;> rw [h] <;> norm_num
  have hcard : (2 * n).choose n = (powersetCard n (univ : Finset V)).card := by
    rw [card_powersetCard, card_univ, hP.card_eq]
  rw [hcard]
  refine card_nbij' i j ?_ ?_ ?_ ?_
  · intro σ hσ
    rw [mem_coe, mem_filter, dotProduct_clusterIndicator_eq hP (hsign σ)] at hσ
    rw [mem_coe, mem_powersetCard]
    refine ⟨subset_univ _, ?_⟩
    have : ((i σ).card : ℝ) = n := by linarith [hσ.2]
    exact_mod_cast this
  · intro S hS
    rw [mem_coe, mem_powersetCard] at hS
    rw [mem_coe, mem_filter, dotProduct_clusterIndicator_eq hP (hsign (j S))]
    have hfilter : (univ.filter fun v => ((j S v : ℤ) : ℝ) = clusterIndicator V₁ V₂ v) = S := by
      ext v
      simp [hj S v]
    rw [hfilter, hS.2, sub_self, mul_zero]
    exact ⟨mem_univ _, rfl⟩
  · intro σ _
    funext v
    by_cases hv : ((σ v : ℤ) : ℝ) = clusterIndicator V₁ V₂ v
    · have hmem : v ∈ i σ := by simp [i, hv]
      simp only [j, hmem, if_true]
      rw [← cast_clusterUnits hP v] at hv
      exact Units.ext (Int.cast_injective hv).symm
    · have hmem : v ∉ i σ := by simp [i, hv]
      simp only [j, hmem, if_false]
      have hneg : ((σ v : ℤ) : ℝ) = -clusterIndicator V₁ V₂ v := by
        rcases hsign σ v with h1 | h1 <;> rcases hc v with h2 | h2 <;> rw [h1, h2] at hv ⊢ <;>
          first | exact absurd rfl hv | norm_num
      rw [← cast_clusterUnits hP v] at hneg
      apply Units.ext
      rw [Units.val_neg]
      exact_mod_cast hneg.symm
  · intro S _
    ext v
    simp [i, hj S v]

/-- **Lemma B.1, exact form**: `P(⟨σ, χ⟩ = 0) = C(2n, n) / 4ⁿ`. -/
theorem prob_dotProduct_clusterIndicator_eq_zero_aux (hP : IsBalancedPartition V₁ V₂ n) :
    (Distribution.uniform (V → ℤˣ)).prob
        (fun σ => (fun v => ((σ v : ℤ) : ℝ)) ⬝ᵥ clusterIndicator V₁ V₂ = 0) =
      ((2 * n).choose n : ℝ) / 4 ^ n := by
  classical
  rw [Distribution.prob, Distribution.uniform_expect, avg_indicator,
    card_filter_dotProduct_eq_zero hP, Fintype.card_fun, Fintype.card_units_int, hP.card_eq]
  push_cast
  rw [pow_mul]
  norm_num

/-- The central binomial bound `C(2n, n) / 4ⁿ ≤ 1 / √(π n)`, from Wallis' product
`(2n+1)/(2n+2) · π/2 ≤ W n = 16ⁿ / (C(2n, n)² (2n+1))` and `4n(n+1) ≤ (2n+1)²`. -/
theorem choose_div_four_pow_le_aux (hn : 0 < n) :
    ((2 * n).choose n : ℝ) / 4 ^ n ≤ 1 / √(π * n) := by
  have hW := Real.Wallis.le_W n
  rw [Real.Wallis.W_eq_factorial_ratio] at hW
  have hfac : ((2 * n).factorial : ℝ) =
      (2 * n).choose n * n.factorial * n.factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    rw [show 2 * n - n = n by omega] at h
    exact_mod_cast h.symm
  rw [hfac] at hW
  set C : ℝ := ((2 * n).choose n : ℝ) with hC
  set F : ℝ := (n.factorial : ℝ) with hF
  have hFpos : 0 < F := by positivity
  have hCpos : 0 < C := by
    rw [hC]
    exact_mod_cast Nat.choose_pos (by omega)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h4 : (0 : ℝ) < 4 ^ n := by positivity
  have hRHS : 2 ^ (4 * n) * F ^ 4 / ((C * F * F) ^ 2 * (2 * n + 1)) =
      (4 ^ n) ^ 2 / (C ^ 2 * (2 * n + 1)) := by
    have h16 : (2 : ℝ) ^ (4 * n) = (4 ^ n) ^ 2 := by
      rw [← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
      ring_nf
    rw [h16]
    field_simp
  rw [hRHS, le_div_iff₀ (by positivity)] at hW
  -- `(2n+1)² π C² ≤ (4n+4) (4ⁿ)²`
  have h1 : (2 * n + 1) ^ 2 * π * C ^ 2 ≤ (4 * n + 4) * (4 ^ n) ^ 2 := by
    have e : ((2 : ℝ) * n + 1) / (2 * n + 2) * (π / 2) * (C ^ 2 * (2 * n + 1)) =
        (2 * n + 1) ^ 2 * π * C ^ 2 / (4 * n + 4) := by
      field_simp
      ring
    rw [e, div_le_iff₀ (by positivity)] at hW
    linarith
  have h2 : C ^ 2 * (π * n) ≤ (4 ^ n) ^ 2 := by
    have h3 : n * ((2 * n + 1) ^ 2 * π * C ^ 2) ≤ n * ((4 * n + 4) * (4 ^ n) ^ 2) :=
      mul_le_mul_of_nonneg_left h1 hnR.le
    have h5 : (n : ℝ) * (4 * n + 4) * (4 ^ n) ^ 2 ≤ (2 * n + 1) ^ 2 * (4 ^ n) ^ 2 :=
      mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
    have h6 : (C ^ 2 * (π * n)) * (2 * n + 1) ^ 2 ≤ (4 ^ n) ^ 2 * (2 * n + 1) ^ 2 := by
      nlinarith
    exact le_of_mul_le_mul_right h6 (by positivity)
  have hsq : (C / 4 ^ n) ^ 2 ≤ (π * n)⁻¹ := by
    rw [div_pow, div_le_iff₀ (by positivity), ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
    linarith
  rw [one_div, ← Real.sqrt_inv]
  exact (le_abs_self _).trans (Real.abs_le_sqrt hsq)

/-- `T(n, δ) ≤ 10 log n / δ + 2` for `n ≥ 2` and `0 < δ ≤ 1`. -/
theorem reconstructionTime_le_aux (hn : 2 ≤ n) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (reconstructionTime n δ : ℝ) ≤ 10 * Real.log n / δ + 2 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hnR
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog1 : δ / 2 ≤ Real.log (1 + δ) := by
    have h := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + δ by linarith)
    have e : 1 - (1 + δ)⁻¹ = δ / (1 + δ) := by field_simp; ring
    rw [e] at h
    refine le_trans ?_ h
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]
    nlinarith
  have hlogpos : 0 < Real.log (1 + δ) := Real.log_pos (by linarith)
  have hL4 : Real.log (4 * (n : ℝ) ^ 3) ≤ 5 * Real.log n := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow,
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith
  have hL0 : 0 ≤ Real.log (4 * (n : ℝ) ^ 3) :=
    Real.log_nonneg (by nlinarith [pow_le_pow_left₀ (by norm_num) hnR 3])
  set L := Real.log (4 * (n : ℝ) ^ 3) / Real.log (1 + δ) with hL
  have hLle : L ≤ 10 * Real.log n / δ := by
    rw [hL, div_le_div_iff₀ hlogpos hδ]
    have := mul_le_mul hL4 hlog1 (by positivity) (by positivity)
    nlinarith
  unfold reconstructionTime
  rw [← hL]
  push_cast
  have := Nat.ceil_lt_add_one (div_nonneg hL0 hlogpos.le)
  rw [← hL] at this
  linarith

/-- If `s'` holds wherever `s` fails, then `P(s') ≥ 1 - P(s)`. -/
lemma one_sub_prob_le_prob {α : Type*} [Fintype α] (p : Distribution α) {s s' : α → Prop}
    (h : ∀ a, ¬ s a → s' a) : 1 - p.prob s ≤ p.prob s' := by
  classical
  have key (a : α) : (1 : ℝ) - (if s a then 1 else 0) ≤ if s' a then 1 else 0 := by
    by_cases hs : s a
    · simp only [hs, if_true, sub_self]
      split_ifs <;> norm_num
    · simp [hs, h a hs]
  calc 1 - p.prob s = p.expect (fun a => 1 - if s a then 1 else 0) := by
        rw [Distribution.expect_sub, Distribution.expect_const]
        rfl
    _ ≤ p.expect (fun a => if s' a then 1 else 0) := p.expect_mono key
    _ = p.prob s' := rfl

/-- **Theorem 3.2** (Strong reconstruction), probabilistic form. -/
theorem strong_reconstruction_aux {G : SimpleGraph V} [DecidableRel G.Adj] {d b : ℕ}
    (hG : IsClusteredRegular G V₁ V₂ n d b) (hconn : G.Connected) {δ : ℝ} (hδ : 0 < δ)
    (hgap : (1 + δ) * maxAbsOtherEigenvalue G d < 1 - 2 * (b : ℝ) / d) :
    1 - 1 / √(π * n) ≤ (Distribution.uniform (V → ℤˣ)).prob (fun σ =>
      ∀ t, reconstructionTime n δ ≤ t →
        IsStrongReconstruction V₁ V₂ (color G (fun v => ((σ v : ℤ) : ℝ)) t)) := by
  have hP := hG.toIsBalancedPartition
  have hn : 0 < n := by
    have h1 := hP.card_eq
    have h2 : 0 < Fintype.card V := Fintype.card_pos_iff.mpr hconn.nonempty
    omega
  calc 1 - 1 / √(π * n) ≤ 1 - ((2 * n).choose n : ℝ) / 4 ^ n := by
        linarith [choose_div_four_pow_le_aux hn]
    _ = 1 - (Distribution.uniform (V → ℤˣ)).prob
          (fun σ => (fun v => ((σ v : ℤ) : ℝ)) ⬝ᵥ clusterIndicator V₁ V₂ = 0) := by
        rw [prob_dotProduct_clusterIndicator_eq_zero_aux hP]
    _ ≤ _ := one_sub_prob_le_prob _ fun σ hσ t ht =>
        isStrongReconstruction_color_aux hG hconn hδ hgap
          (fun v => cast_units_eq_one_or (σ v)) hσ ht

end Averaging
