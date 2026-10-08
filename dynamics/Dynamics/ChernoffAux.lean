import Dynamics.Concentration
import Dynamics.Distribution

/-!
# Helper lemmas for the Chernoff bounds

Auxiliary results for `Dynamics.Chernoff` (roadmap FND-3, Mitzenmacher–Upfal, Theorems 4.4
and 4.5 with Exercise 4.7). The proof is the textbook one: Markov's inequality applied to
`exp (t X)`, the moment-generating function of `X = ∑ᵢ Xᵢ` factors over the independent
coordinates, each `{0,1}`-valued factor is `1 + pᵢ (eᵗ - 1) ≤ exp (pᵢ (eᵗ - 1))`, and then
`t = log (1 + δ)` (upper tail) or `t = log (1 - δ)` (lower tail).

* Scalar inequalities: `two_mul_div_two_add_le_log_one_add` (`2δ/(2+δ) ≤ log (1+δ)`),
  `neg_add_sq_div_two_le_one_sub_mul_log` (`-δ + δ²/2 ≤ (1-δ) log (1-δ)`), and the identity
  `exp_div_rpow_self_rpow` rewriting the ratio forms as exponentials.
* `Distribution.prob_le_expect_exp`: Markov's inequality for `exp (t X)`.
* `Distribution.independent_expect_exp_sum_le`: `𝔼 exp (t X) ≤ exp (μ (eᵗ - 1))`.
* `Distribution.prob_ge_le_exp`, `Distribution.prob_le_le_exp`: the tails before optimizing
  `t`, with an upper (resp. lower) bound on the mean.
* `Distribution.sum_ite_mem_ite_eq_card`: the number of heads among the coins of `S` as a
  sum of `{0,1}` coordinates (the coin `Distribution.bernoulli` and its expectations are in
  `Dynamics.Chernoff`, next to the pinned definition).
* Uniform rounds: `Distribution.independent_expect_eq_avg` and
  `avg_indicator_le_of_independent`, which transfer a bound on `independent` products to
  `avg` over `ι → γ`.
-/

namespace Dynamics

open Finset Real

/-! ### Scalar inequalities -/

/-- `2δ / (2 + δ) ≤ log (1 + δ)` for `δ ≥ 0`: the first term of the series
`log (1 + x) - log (1 - x) = ∑ₖ 2 x^(2k+1) / (2k+1)` at `x = δ / (2 + δ)`. -/
lemma two_mul_div_two_add_le_log_one_add {δ : ℝ} (hδ : 0 ≤ δ) :
    2 * δ / (2 + δ) ≤ log (1 + δ) := by
  have h2 : 0 < 2 + δ := by linarith
  have hx0 : 0 ≤ δ / (2 + δ) := by positivity
  have hx1 : δ / (2 + δ) < 1 := by rw [div_lt_one h2]; linarith
  have hs := hasSum_log_sub_log_of_abs_lt_one (x := δ / (2 + δ)) (by rwa [abs_of_nonneg hx0])
  have h0 := le_hasSum hs 0 fun j _ =>
    mul_nonneg (mul_nonneg (by norm_num) (by positivity)) (pow_nonneg hx0 _)
  have hlog : log (1 + δ / (2 + δ)) - log (1 - δ / (2 + δ)) = log (1 + δ) := by
    rw [← log_div (by positivity) (by linarith)]
    congr 1
    rw [div_eq_iff (by linarith)]
    field_simp
    ring
  rw [hlog] at h0
  calc 2 * δ / (2 + δ) = 2 * (1 / (2 * ((0 : ℕ) : ℝ) + 1)) * (δ / (2 + δ)) ^ (2 * 0 + 1) := by
        simp only [Nat.cast_zero, mul_zero, zero_add, div_one, mul_one, pow_one]
        ring
    _ ≤ log (1 + δ) := h0

/-- `log x ≥ (x - 1/x)/2` for `0 < x ≤ 1`. -/
lemma half_sub_inv_le_log_of_le_one {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    (x - x⁻¹) / 2 ≤ log x := by
  -- `ψ x = log x - (x - 1/x)/2` has `ψ' = -(x-1)²/(2x²) ≤ 0` and `ψ 1 = 0`
  have hderiv (y : ℝ) (hy : 0 < y) :
      HasDerivAt (fun y => log y - (y - y⁻¹) / 2) (-(y - 1) ^ 2 / (2 * y ^ 2)) y := by
    have h := ((hasDerivAt_log hy.ne').sub
      (((hasDerivAt_id' y).sub (hasDerivAt_inv hy.ne')).div_const 2))
    refine h.congr_deriv ?_
    field_simp
    ring
  have hanti : AntitoneOn (fun y => log y - (y - y⁻¹) / 2) (Set.Ioi 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    · exact fun y hy => (hderiv y hy).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ioi] at hy
      exact (hderiv y hy).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ioi] at hy
      rw [(hderiv y hy).deriv]
      have : 0 < 2 * y ^ 2 := by have := Set.mem_Ioi.mp hy; positivity
      exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (y - 1)]) this.le
  have h := hanti (Set.mem_Ioi.mpr hx0) (Set.mem_Ioi.mpr one_pos) hx1
  simp only [log_one, inv_one, sub_self, zero_div] at h
  linarith

/-- `-δ + δ²/2 ≤ (1 - δ) log (1 - δ)` for `0 ≤ δ < 1`. -/
lemma neg_add_sq_div_two_le_one_sub_mul_log {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    -δ + δ ^ 2 / 2 ≤ (1 - δ) * log (1 - δ) := by
  have hx0 : 0 < 1 - δ := by linarith
  have h := half_sub_inv_le_log_of_le_one hx0 (by linarith)
  have h' := mul_le_mul_of_nonneg_left h hx0.le
  have e : (1 - δ) * ((1 - δ - (1 - δ)⁻¹) / 2) = -δ + δ ^ 2 / 2 := by
    field_simp
    ring
  linarith

/-- The exponent of the upper ratio form is at most `-δ²/(2 + δ)`. -/
lemma sub_one_add_mul_log_le {δ : ℝ} (hδ : 0 ≤ δ) :
    δ - (1 + δ) * log (1 + δ) ≤ -(δ ^ 2 / (2 + δ)) := by
  have h := mul_le_mul_of_nonneg_left (two_mul_div_two_add_le_log_one_add hδ)
    (by linarith : (0 : ℝ) ≤ 1 + δ)
  have e : δ - (1 + δ) * (2 * δ / (2 + δ)) = -(δ ^ 2 / (2 + δ)) := by
    have : (2 + δ) ≠ 0 := by linarith
    field_simp
    ring
  linarith

/-- The exponent of the lower ratio form is at most `-δ²/2`. -/
lemma neg_sub_one_sub_mul_log_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    -δ - (1 - δ) * log (1 - δ) ≤ -(δ ^ 2 / 2) := by
  linarith [neg_add_sq_div_two_le_one_sub_mul_log hδ0 hδ1]

/-- The ratio forms as exponentials: `(e^c / a^a)^μ = exp (μ (c - a log a))` for `a > 0`. -/
lemma exp_div_rpow_self_rpow {a : ℝ} (ha : 0 < a) (c μ : ℝ) :
    (exp c / a ^ a) ^ μ = exp (μ * (c - a * log a)) := by
  have hpow : 0 < a ^ a := rpow_pos_of_pos ha a
  rw [rpow_def_of_pos (div_pos (exp_pos c) hpow), log_div (exp_pos c).ne' hpow.ne', log_exp,
    log_rpow ha]
  congr 1
  ring

namespace Distribution

/-! ### Markov's inequality and the moment-generating function -/

section Markov

variable {β : Type*} [Fintype β]

/-- **Markov's inequality for `exp (t X)`**: if the event `s` forces `t k ≤ t X`, then
`P(s) ≤ 𝔼[exp (t X)] exp (-(t k))`. -/
lemma prob_le_expect_exp (p : Distribution β) (s : β → Prop) (X : β → ℝ) (t k : ℝ)
    (hs : ∀ ω, s ω → t * k ≤ t * X ω) :
    p.prob s ≤ p.expect (fun ω => exp (t * X ω)) * exp (-(t * k)) := by
  classical
  have hpt (ω : β) : (if s ω then (1 : ℝ) else 0) ≤ exp (-(t * k)) * exp (t * X ω) := by
    rw [← exp_add]
    split_ifs with h
    · linarith [add_one_le_exp (-(t * k) + t * X ω), hs ω h]
    · exact (exp_pos _).le
  calc p.prob s = p.expect (fun ω => if s ω then (1 : ℝ) else 0) := rfl
    _ ≤ p.expect (fun ω => exp (-(t * k)) * exp (t * X ω)) := p.expect_mono hpt
    _ = _ := by rw [expect_mul, mul_comm]

end Markov

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

/-- The moment-generating function of a sum of independent coordinates factors. -/
lemma independent_expect_exp_sum (P : ι → Distribution α) (Y : ι → α → ℝ) (t : ℝ) :
    (independent P).expect (fun ω => exp (t * ∑ i, Y i (ω i)))
      = ∏ i, (P i).expect (fun a => exp (t * Y i a)) := by
  simp_rw [mul_sum, exp_sum]
  exact independent_expect_prod P (fun i a => exp (t * Y i a))

/-- The moment-generating function of one `{0,1}`-valued trial:
`𝔼[e^{tY}] = 1 + 𝔼[Y] (eᵗ - 1) ≤ exp (𝔼[Y] (eᵗ - 1))`. -/
lemma expect_exp_mul_le (p : Distribution α) (Y : α → ℝ) (hY : ∀ a, Y a = 0 ∨ Y a = 1)
    (t : ℝ) : p.expect (fun a => exp (t * Y a)) ≤ exp (p.expect Y * (exp t - 1)) := by
  have h (a : α) : exp (t * Y a) = 1 + (exp t - 1) * Y a := by
    rcases hY a with h | h <;> simp [h]
  simp_rw [h]
  rw [expect_add, expect_const, expect_mul]
  linarith [add_one_le_exp (p.expect Y * (exp t - 1))]

/-- **MGF bound** for a sum of independent `{0,1}`-valued trials:
`𝔼[exp (t X)] ≤ exp (μ (eᵗ - 1))` with `μ = ∑ᵢ 𝔼[Y i]`, for every real `t`. -/
lemma independent_expect_exp_sum_le (P : ι → Distribution α) (Y : ι → α → ℝ)
    (hY : ∀ i a, Y i a = 0 ∨ Y i a = 1) (t : ℝ) :
    (independent P).expect (fun ω => exp (t * ∑ i, Y i (ω i)))
      ≤ exp ((∑ i, (P i).expect (Y i)) * (exp t - 1)) := by
  rw [independent_expect_exp_sum, sum_mul, exp_sum]
  exact prod_le_prod (fun i _ => (P i).expect_nonneg fun a => (exp_pos _).le)
    (fun i _ => expect_exp_mul_le (P i) (Y i) (hY i) t)

omit [DecidableEq ι] in
/-- The mean `∑ᵢ 𝔼[Y i]` of `{0,1}`-valued trials is nonnegative. -/
lemma sum_expect_nonneg (P : ι → Distribution α) (Y : ι → α → ℝ)
    (hY : ∀ i a, Y i a = 0 ∨ Y i a = 1) : 0 ≤ ∑ i, (P i).expect (Y i) :=
  sum_nonneg fun i _ => (P i).expect_nonneg fun a => by rcases hY i a with h | h <;> simp [h]

/-- **Upper tail before optimizing `t`**: for `t ≥ 0` and an upper bound `μH` on the mean,
`P(X ≥ k) ≤ exp (μH (eᵗ - 1) - t k)`. -/
lemma prob_ge_le_exp (P : ι → Distribution α) (Y : ι → α → ℝ)
    (hY : ∀ i a, Y i a = 0 ∨ Y i a = 1) {t μH : ℝ} (ht : 0 ≤ t)
    (hμH : ∑ i, (P i).expect (Y i) ≤ μH) (k : ℝ) :
    (independent P).prob (fun ω => k ≤ ∑ i, Y i (ω i))
      ≤ exp (μH * (exp t - 1) - t * k) := by
  have h1 := (independent P).prob_le_expect_exp (fun ω => k ≤ ∑ i, Y i (ω i))
    (fun ω => ∑ i, Y i (ω i)) t k fun ω h => mul_le_mul_of_nonneg_left h ht
  have h2 : exp ((∑ i, (P i).expect (Y i)) * (exp t - 1)) ≤ exp (μH * (exp t - 1)) :=
    exp_le_exp.mpr (mul_le_mul_of_nonneg_right hμH (by linarith [add_one_le_exp t]))
  calc _ ≤ _ := h1
    _ ≤ exp (μH * (exp t - 1)) * exp (-(t * k)) :=
        mul_le_mul_of_nonneg_right ((independent_expect_exp_sum_le P Y hY t).trans h2)
          (exp_pos _).le
    _ = _ := by rw [← exp_add]; ring_nf

/-- **Lower tail before optimizing `t`**: for `t ≤ 0` and a lower bound `μL` on the mean,
`P(X ≤ k) ≤ exp (μL (eᵗ - 1) - t k)`. -/
lemma prob_le_le_exp (P : ι → Distribution α) (Y : ι → α → ℝ)
    (hY : ∀ i a, Y i a = 0 ∨ Y i a = 1) {t μL : ℝ} (ht : t ≤ 0)
    (hμL : μL ≤ ∑ i, (P i).expect (Y i)) (k : ℝ) :
    (independent P).prob (fun ω => ∑ i, Y i (ω i) ≤ k)
      ≤ exp (μL * (exp t - 1) - t * k) := by
  have h1 := (independent P).prob_le_expect_exp (fun ω => ∑ i, Y i (ω i) ≤ k)
    (fun ω => ∑ i, Y i (ω i)) t k fun ω h => mul_le_mul_of_nonpos_left h ht
  have h2 : exp ((∑ i, (P i).expect (Y i)) * (exp t - 1)) ≤ exp (μL * (exp t - 1)) :=
    exp_le_exp.mpr (mul_le_mul_of_nonpos_right hμL (by linarith [exp_le_one_iff.mpr ht]))
  calc _ ≤ _ := h1
    _ ≤ exp (μL * (exp t - 1)) * exp (-(t * k)) :=
        mul_le_mul_of_nonneg_right ((independent_expect_exp_sum_le P Y hY t).trans h2)
          (exp_pos _).le
    _ = _ := by rw [← exp_add]; ring_nf

/-! ### Counting heads -/

/-- The number of heads among the coins of `S` as a sum of `{0,1}` coordinates. -/
lemma sum_ite_mem_ite_eq_card (S : Finset ι) (ω : ι → Bool) :
    ∑ i, (if i ∈ S then (if ω i = true then (1 : ℝ) else 0) else 0)
      = ((S.filter fun i => ω i = true).card : ℝ) := by
  rw [Fintype.sum_ite_mem, sum_boole]

/-! ### Uniform rounds -/

section Uniform

variable {γ : Type*} [Fintype γ]

/-- If every coordinate distribution has the uniform weights `(card γ)⁻¹`, the independent
product is the uniform average over `ι → γ`. -/
lemma independent_expect_eq_avg (P : ι → Distribution γ)
    (hP : ∀ i a, (P i).weight a = (Fintype.card γ : ℝ)⁻¹) (f : (ι → γ) → ℝ) :
    (independent P).expect f = avg f := by
  simp only [expect, independent, hP, prod_const, card_univ, avg, Fintype.card_fun,
    Nat.cast_pow, ← mul_sum, div_eq_inv_mul, inv_pow]

end Uniform

end Distribution

open Distribution in
/-- **Transfer to uniform rounds.** A bound on the probability of an event `E` under every
independent product whose factors are uniform (`(P i).expect = avg`) bounds the uniform
average of its indicator over `ι → γ`. No `Nonempty γ` is needed: if `ι → γ` is empty the
average vanishes, and if `γ` is empty but `ι → γ` is not, then `ι` is empty. -/
lemma avg_indicator_le_of_independent {ι γ : Type*} [Fintype ι] [DecidableEq ι] [Fintype γ]
    (E : (ι → γ) → Prop) [DecidablePred E] {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ P : ι → Distribution γ, (∀ i f, (P i).expect f = avg f) →
      (independent P).prob E ≤ B) :
    avg (fun ω => if E ω then (1 : ℝ) else 0) ≤ B := by
  rcases isEmpty_or_nonempty (ι → γ) with hω | hω
  · simpa [avg] using hB
  obtain ⟨P, hw⟩ : ∃ P : ι → Distribution γ,
      ∀ i a, (P i).weight a = (Fintype.card γ : ℝ)⁻¹ := by
    rcases isEmpty_or_nonempty γ with hγ | hγ
    · have : IsEmpty ι := ⟨fun i => hγ.false (hω.some i)⟩
      exact ⟨fun i => isEmptyElim i, fun i => isEmptyElim i⟩
    · exact ⟨fun _ => uniform γ, fun _ _ => rfl⟩
  have hP (i : ι) (f : γ → ℝ) : (P i).expect f = avg f := by
    simp only [Distribution.expect, hw, avg, ← mul_sum, div_eq_inv_mul]
  calc avg (fun ω => if E ω then (1 : ℝ) else 0)
      = (independent P).expect (fun ω => if E ω then (1 : ℝ) else 0) :=
        (independent_expect_eq_avg P hw _).symm
    _ = (independent P).prob E := by
        simp only [prob]
        congr 1
        funext ω
        split_ifs <;> rfl
    _ ≤ B := h P hP

end Dynamics
