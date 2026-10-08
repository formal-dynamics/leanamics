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

/-! ### Arithmetic of the bound `Yb` -/

lemma cutDevBound_le_small {N l2 l3 s z : ℝ} {T : ℕ} (hN : 16 ≤ N) (hl3 : 0 < l3) (hs : 0 ≤ s)
    (hz : 0 ≤ z) (hL0 : 0 ≤ T * l2 / N) (hL : T * l2 / N ≤ 1 / 8) (hr0 : 0 ≤ l2 / l3)
    (hr : l2 / l3 ≤ 1 / 8) :
    cutDevBound N l2 l3 s z T ≤ 2 * (T * l2 / N) * s + l2 / l3 * z := by
  have hN0 : 0 < N := by linarith
  set L := T * l2 / N with hL_def
  set r := l2 / l3 with hr_def
  have e : cutDevBound N l2 l3 s z T =
      L * (1 + 8 / N) * s + 4 * r / N * z + 4 * L * r * (s + z) / N := by
    unfold cutDevBound; rw [hL_def, hr_def]; field_simp
  rw [e]
  have h8 : 8 / N ≤ 1 / 2 := by rw [div_le_iff₀ hN0]; linarith
  have h4 : 4 / N ≤ 1 / 4 := by rw [div_le_iff₀ hN0]; linarith
  have e1 : 4 * r / N * z = r * z * (4 / N) := by ring
  have e2 : 4 * L * r * (s + z) / N = L * r * (s + z) * (4 / N) := by ring
  rw [e1, e2]
  have hLr : L * r ≤ 1 / 64 := by nlinarith
  have hLr0 : 0 ≤ L * r := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h8 (mul_nonneg hL0 hs),
    mul_le_mul_of_nonneg_left h4 (mul_nonneg hr0 hz),
    mul_le_mul_of_nonneg_left h4 (mul_nonneg hLr0 (add_nonneg hs hz)),
    mul_nonneg hr0 hz, mul_nonneg hL0 hs]

lemma cutDevBound_le_start {N l2 l3 s z : ℝ} {T : ℕ} (hN : 16 ≤ N) (hl3 : 0 < l3) (hs : 0 ≤ s)
    (hz : 0 ≤ z) (hzN : z ≤ N) (hszN : s + z ≤ N) (hL0 : 0 ≤ T * l2 / N)
    (hL : T * l2 / N ≤ 1 / 8) (hr0 : 0 ≤ l2 / l3) (hr : l2 / l3 ≤ 1 / 8) :
    cutDevBound N l2 l3 s z T ≤ 2 * (T * l2 / N) * s + 5 * (l2 / l3) := by
  have hN0 : 0 < N := by linarith
  set L := T * l2 / N with hL_def
  set r := l2 / l3 with hr_def
  have e : cutDevBound N l2 l3 s z T =
      L * (1 + 8 / N) * s + 4 * r * (z / N) + 4 * L * r * ((s + z) / N) := by
    unfold cutDevBound; rw [hL_def, hr_def]; field_simp
  rw [e]
  have h8 : 8 / N ≤ 1 / 2 := by rw [div_le_iff₀ hN0]; linarith
  have h1 : z / N ≤ 1 := (div_le_one hN0).mpr hzN
  have h2 : (s + z) / N ≤ 1 := (div_le_one hN0).mpr hszN
  have hLr : L * r ≤ 1 / 64 := by nlinarith
  have hLr0 : 0 ≤ L * r := by positivity
  have hz0 : 0 ≤ z / N := by positivity
  have hsz0 : 0 ≤ (s + z) / N := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h8 (mul_nonneg hL0 hs), mul_le_mul_of_nonneg_left h1 hr0,
    mul_le_mul_of_nonneg_left h2 hLr0]

/-! ### Expectation bounds for one choice of the initial signs -/

namespace IsClusteredRegular
variable (hG : IsClusteredRegular G V₁ d b) (h3 : ThirdEigenvalueLB G V₁ d lam3)
include hG h3

/-- The cut coefficient moves little up to the start of the phase:
`E ‖y⁽ᵗ¹⁾ - y⁽⁰⁾‖² ≤ 2 L₁ ‖y⁽⁰⁾‖² + 5 λ₂/λ₃` with `L₁ = λ₂ t₁/n`. -/
lemma expList_cutDev_signVec_le (hl3 : 0 < lam3) (hN : (16 : ℝ) ≤ Fintype.card V)
    (σ : V → ℤˣ) (t₁ : ℕ) (hL : (t₁ : ℝ) * (2 * b / d) / Fintype.card V ≤ 1 / 8)
    (hr : (2 * b / d) / lam3 ≤ 1 / 8) :
    expList G.Dart t₁ (fun l => Fintype.card V *
        (cutCoef V₁ (avgRun G (signVec σ) l) - cutCoef V₁ (signVec σ)) ^ 2) ≤
      2 * (t₁ * (2 * b / d) / Fintype.card V) * (Fintype.card V * cutCoef V₁ (signVec σ) ^ 2) +
        5 * ((2 * b / d) / lam3) := by
  have hNpos := hG.card_real_pos
  refine (hG.expList_secondMoment_le h3 hl3 (by linarith) (signVec σ) t₁).1.trans ?_
  exact cutDevBound_le_start hN hl3 (by positivity) (restSq_nonneg _) (hG.restSq_signVec_le σ)
    (hG.cutCoef_sq_add_restSq_signVec_le σ) (by positivity) hL (by positivity) hr

/-- The rest component is small at the start of the phase:
`E ‖z⁽ᵗ¹⁾‖² ≤ n (1 - λ₃/n)^{t₁} + 3 r ‖y⁽⁰⁾‖² + 10 r²` with `r = λ₂/λ₃`. -/
lemma expList_restSq_signVec_le (hl3 : 0 < lam3) (hN : (16 : ℝ) ≤ Fintype.card V)
    (σ : V → ℤˣ) (t₁ : ℕ) (hL : (t₁ : ℝ) * (2 * b / d) / Fintype.card V ≤ 1 / 8)
    (hr : (2 * b / d) / lam3 ≤ 1 / 8) :
    expList G.Dart t₁ (fun l => restSq V₁ (avgRun G (signVec σ) l)) ≤
      Fintype.card V * (1 - lam3 / Fintype.card V) ^ t₁ +
        3 * ((2 * b / d) / lam3) * (Fintype.card V * cutCoef V₁ (signVec σ) ^ 2) +
        10 * ((2 * b / d) / lam3) ^ 2 := by
  have hNpos := hG.card_real_pos
  have hl3le := hG.lam3_le_two h3
  refine (hG.expList_secondMoment_le h3 hl3 (by linarith) (signVec σ) t₁).2.trans ?_
  have hCD := cutDevBound_le_start hN hl3 (by positivity) (restSq_nonneg _)
    (hG.restSq_signVec_le σ) (hG.cutCoef_sq_add_restSq_signVec_le σ) (by positivity) hL
    (by positivity) hr (l2 := 2 * b / d) (T := t₁)
  set N : ℝ := (Fintype.card V : ℝ)
  set r := (2 * b / d : ℝ) / lam3
  set L := t₁ * (2 * b / d : ℝ) / N
  set s := N * cutCoef V₁ (signVec σ) ^ 2
  have hq0 : 0 ≤ 1 - lam3 / N := by rw [sub_nonneg, div_le_one hNpos]; linarith
  have hqz : (1 - lam3 / N) ^ t₁ * restSq V₁ (signVec σ) ≤ N * (1 - lam3 / N) ^ t₁ := by
    rw [mul_comm N]; exact mul_le_mul_of_nonneg_left (hG.restSq_signVec_le σ) (pow_nonneg hq0 _)
  have hr0 : 0 ≤ r := by positivity
  have hs : 0 ≤ s := by positivity
  have hL0 : 0 ≤ L := by positivity
  have := mul_le_mul_of_nonneg_left hCD (show 0 ≤ 2 * r by positivity)
  have hLs : r * (L * s) ≤ r * (s / 8) := by
    apply mul_le_mul_of_nonneg_left _ hr0; nlinarith
  nlinarith

/-- From an arbitrary state `x₁` (the start of the phase): the deviation `r` after `k` more
rounds satisfies `E ‖r⁽ᵏ⁾‖² ≤ (2.5 L_k + 2 r) ‖y₁‖² + 2 ‖z₁‖²`, with `L_k = λ₂ k/n`. -/
lemma expList_devVec_le (hl3 : 0 < lam3) (hN : (16 : ℝ) ≤ Fintype.card V)
    (x₁ : V → ℝ) (k : ℕ) (hL : (k : ℝ) * (2 * b / d) / Fintype.card V ≤ 1 / 8)
    (hr : (2 * b / d) / lam3 ≤ 1 / 8) :
    expList G.Dart k (fun p => ∑ v, devVec V₁ x₁ (avgRun G x₁ p) v ^ 2) ≤
      (5 / 2 * (k * (2 * b / d) / Fintype.card V) + 2 * ((2 * b / d) / lam3)) *
          (Fintype.card V * cutCoef V₁ x₁ ^ 2) + 2 * restSq V₁ x₁ := by
  have hNpos := hG.card_real_pos
  have hl3le := hG.lam3_le_two h3
  have hdev : ∀ p : List G.Dart, ∑ v, devVec V₁ x₁ (avgRun G x₁ p) v ^ 2 =
      Fintype.card V * (cutCoef V₁ (avgRun G x₁ p) - cutCoef V₁ x₁) ^ 2 +
        restSq V₁ (avgRun G x₁ p) := fun p => by
    rw [← sum_sq_dev_eq hG]
    have havg : avg (avgRun G x₁ p) = avg x₁ := by simp only [avg, sum_avgRun]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [devVec, projCut_eq, projRest, projOne, projCut, havg, cutCoef]
    ring
  simp_rw [hdev]
  rw [expList_add]
  obtain ⟨hY, hZ⟩ := hG.expList_secondMoment_le h3 hl3 (by linarith) x₁ k
  have hCD := cutDevBound_le_small hN hl3 (by positivity) (restSq_nonneg (V₁ := V₁) x₁)
    (by positivity) hL
    (by positivity) hr (l2 := 2 * b / d) (s := Fintype.card V * cutCoef V₁ x₁ ^ 2) (T := k)
  set N : ℝ := (Fintype.card V : ℝ)
  set r := (2 * b / d : ℝ) / lam3
  set L := k * (2 * b / d : ℝ) / N
  set s := N * cutCoef V₁ x₁ ^ 2
  set z := restSq V₁ x₁
  have hq0 : 0 ≤ 1 - lam3 / N := by rw [sub_nonneg, div_le_one hNpos]; linarith
  have hq1 : 1 - lam3 / N ≤ 1 := by have : 0 ≤ lam3 / N := by positivity
                                    linarith
  have hqz : (1 - lam3 / N) ^ k * z ≤ z :=
    mul_le_of_le_one_left (restSq_nonneg _) (pow_le_one₀ hq0 hq1)
  have hr0 : 0 ≤ r := by positivity
  have hs : 0 ≤ s := by positivity
  have hz : 0 ≤ z := restSq_nonneg _
  have hL0 : 0 ≤ L := by positivity
  have := mul_le_mul_of_nonneg_left hCD (show 0 ≤ 2 * r by positivity)
  have h1 : r * (L * s) ≤ (1 / 8) * (L * s) := mul_le_mul_of_nonneg_right hr (by positivity)
  have h2 : r * (r * z) ≤ (1 / 8) * (r * z) := mul_le_mul_of_nonneg_right hr (by positivity)
  nlinarith [mul_nonneg hr0 hz]

end IsClusteredRegular

end Averaging.Opportunistic
