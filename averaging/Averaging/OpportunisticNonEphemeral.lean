import Averaging.OpportunisticGood
import Dynamics.GraphRounds

/-! # Non-ephemeral good nodes (Lemma 4.2): the probabilistic part

* `avg_le_of_mul_le` (anti-concentration of `‖y⁽⁰⁾‖²`): a quantity `g ≤ 1` of the initial signs with
  `g ‖y⁽⁰⁾‖² ≤ a ‖y⁽⁰⁾‖² + K²` has average at most `a + 1/√(n+1) + 2 K (1 + log n)`. Since
  `‖y⁽⁰⁾‖² = S²/n` with `S = ⟨σ, χ⟩` a sum of `n` independent signs, this follows from
  `P(S = 0) ≤ 1/√(n+1)` and `E[1/|S|; S ≠ 0] ≤ 2 (1 + log n)/√(n+1)`.
* Probabilities of a uniformly random dart: crossing the cut (`b/d`), with tail (or head) in a
  set `B` (`|B|/n`, the graph being regular).
-/

namespace Averaging.Opportunistic
open Finset Dynamics

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {V₁ : Finset V} {d b : ℕ} {lam3 : ℝ}

/-- The sum `⟨σ, χ⟩` has the law of a sum of independent uniform signs. -/
lemma avg_fun_cutSum (V₁ : Finset V) (F : ℝ → ℝ) :
    avg (fun σ : V → ℤˣ => F (∑ v, cutVec V₁ v * signVec σ v)) =
      avg (fun σ : V → ℤˣ => F (∑ v, signVec σ v)) := by
  simp_rw [cutVec_mul_signVec]
  exact avg_equiv (Equiv.mulLeft (cutUnit V₁)) (fun σ => F (∑ v, signVec σ v))

namespace IsClusteredRegular
variable (hG : IsClusteredRegular G V₁ d b)
include hG

/-- **Anti-concentration of `‖y⁽⁰⁾‖²`.** -/
theorem avg_le_of_mul_le {g : (V → ℤˣ) → ℝ} {a K : ℝ} (ha : 0 ≤ a) (hK : 0 ≤ K)
    (hg1 : ∀ σ, g σ ≤ 1)
    (hg : ∀ σ, g σ * (Fintype.card V * cutCoef V₁ (signVec σ) ^ 2) ≤
      a * (Fintype.card V * cutCoef V₁ (signVec σ) ^ 2) + K ^ 2) :
    avg g ≤ a + 1 / Real.sqrt (Fintype.card V + 1) +
      2 * K * (1 + Real.log (Fintype.card V)) := by
  have hn := hG.card_real_pos
  set N : ℝ := (Fintype.card V : ℝ)
  set S : (V → ℤˣ) → ℝ := fun σ => ∑ v, cutVec V₁ v * signVec σ v
  have hs0 : ∀ σ, N * cutCoef V₁ (signVec σ) ^ 2 = S σ ^ 2 / N := fun σ =>
    hG.card_mul_cutCoef_sq (signVec σ)
  have hpt : ∀ σ, g σ ≤ a + (if S σ = 0 then 1 else 0) +
      K * Real.sqrt N * (if S σ = 0 then 0 else 1 / |S σ|) := fun σ => by
    by_cases hS : S σ = 0
    · simp only [hS, if_true, mul_zero, add_zero]; linarith [hg1 σ]
    · simp only [hS, if_false, add_zero]
      have hSpos : 0 < |S σ| := abs_pos.mpr hS
      by_contra hlt
      have hlt := lt_of_not_ge hlt
      set u := g σ - a
      have hu : K * Real.sqrt N * (1 / |S σ|) < u := by linarith
      have hu0 : 0 < u := lt_of_le_of_lt (by positivity) hu
      have hu1 : u ≤ 1 := by have := hg1 σ; linarith
      have h1 := hg σ
      rw [hs0] at h1
      have h2 : u * (S σ ^ 2 / N) ≤ K ^ 2 := by nlinarith
      have h3 : (u * |S σ|) ^ 2 ≤ (K * Real.sqrt N) ^ 2 := by
        rw [mul_pow, mul_pow, sq_abs, Real.sq_sqrt hn.le]
        have : u ^ 2 * S σ ^ 2 ≤ u * S σ ^ 2 := by
          have hu2 : u ^ 2 ≤ u := by nlinarith
          exact mul_le_mul_of_nonneg_right hu2 (sq_nonneg _)
        have h4 : u * S σ ^ 2 ≤ K ^ 2 * N := by
          rw [mul_div_assoc'] at h2
          rwa [div_le_iff₀ hn] at h2
        linarith
      have h5 : u * |S σ| ≤ K * Real.sqrt N :=
        (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h3
      have : u ≤ K * Real.sqrt N * (1 / |S σ|) := by
        rw [mul_one_div, le_div_iff₀ hSpos]; exact h5
      linarith
  refine (avg_le_avg hpt).trans ?_
  rw [avg_add, avg_add, avg_const, avg_const_mul]
  have hz : avg (fun σ : V → ℤˣ => if S σ = 0 then (1 : ℝ) else 0) ≤ 1 / Real.sqrt (N + 1) := by
    have := avg_fun_cutSum V₁ (fun x => if x = 0 then (1 : ℝ) else 0)
    rw [this]
    exact avg_sum_signVec_eq_zero
  have hi : avg (fun σ : V → ℤˣ => if S σ = 0 then (0 : ℝ) else 1 / |S σ|) ≤
      2 * (1 + Real.log N) / Real.sqrt (N + 1) := by
    have := avg_fun_cutSum V₁ (fun x => if x = 0 then (0 : ℝ) else 1 / |x|)
    rw [this]
    exact avg_inv_abs_sum_signVec
  have hsq : Real.sqrt N ≤ Real.sqrt (N + 1) := Real.sqrt_le_sqrt (by linarith)
  have hsq1 : 0 < Real.sqrt (N + 1) := Real.sqrt_pos.mpr (by linarith)
  have hlog : 0 ≤ 1 + Real.log N := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ N by
      have := hG.four_le_card
      show (1 : ℝ) ≤ (Fintype.card V : ℝ)
      exact_mod_cast (by omega : 1 ≤ Fintype.card V))
    linarith
  have h3 : K * Real.sqrt N * (2 * (1 + Real.log N) / Real.sqrt (N + 1)) ≤
      2 * K * (1 + Real.log N) := by
    rw [mul_div_assoc', div_le_iff₀ hsq1]
    have : 0 ≤ K * (2 * (1 + Real.log N)) := by positivity
    nlinarith
  have h4 : K * Real.sqrt N * avg (fun σ : V → ℤˣ => if S σ = 0 then (0 : ℝ) else 1 / |S σ|) ≤
      K * Real.sqrt N * (2 * (1 + Real.log N) / Real.sqrt (N + 1)) :=
    mul_le_mul_of_nonneg_left hi (by positivity)
  linarith

/-- A uniformly random dart crosses the cut with probability `b/d`. -/
lemma avg_cross :
    avg (fun e : G.Dart => if IsCrossDart V₁ e then (1 : ℝ) else 0) = b / d := by
  have h : ∀ e : G.Dart, (if IsCrossDart V₁ e then (1 : ℝ) else 0) =
      ((cutVec V₁ e.fst - cutVec V₁ e.snd) / 2) ^ 2 * 1 := fun e => by
    rw [cutWeight_eq, mul_one]; rfl
  simp_rw [h]
  have h1 := hG.sum_dart_cutWeight_fst (fun _ => (1 : ℝ))
  rw [avg, h1, hG.card_dart_real]
  have := hG.card_real_pos
  have := hG.d_real_pos
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one]
  field_simp

/-- The tail of a uniformly random dart lies in `B` with probability `|B|/n`. -/
lemma avg_fst_mem (B : Finset V) :
    avg (fun e : G.Dart => if e.fst ∈ B then (1 : ℝ) else 0) = #B / Fintype.card V := by
  have h := avg_edgeRound_fst G (fun v => if v ∈ B then (1 : ℝ) else 0)
  simp only [EdgeRound] at h
  rw [h]
  have hE : (2 * #G.edgeFinset : ℝ) = Fintype.card V * d := by
    have h := G.sum_degrees_eq_twice_card_edges
    simp only [hG.degree_eq, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
    exact_mod_cast h.symm
  rw [hE]
  simp only [hG.degree_eq, mul_ite, mul_one, mul_zero, Finset.sum_ite_mem, Finset.univ_inter,
    sum_const, nsmul_eq_mul]
  have := hG.card_real_pos
  have := hG.d_real_pos
  field_simp

lemma avg_snd_mem (B : Finset V) :
    avg (fun e : G.Dart => if e.snd ∈ B then (1 : ℝ) else 0) = #B / Fintype.card V := by
  rw [← hG.avg_fst_mem B, avg, avg, ← sum_dart_symm]
  rfl

end IsClusteredRegular

end Averaging.Opportunistic
