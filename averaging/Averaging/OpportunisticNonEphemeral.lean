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
    simp only [devVec, projRest, projOne, projCut, havg, cutCoef]
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


/-! ### The good event -/

omit [DecidableRel G.Adj] in
lemma card_badSet_mul_le (θ : ℝ) (x₁ x : V → ℝ) :
    #(badSet V₁ θ x₁ x) * θ ≤ ∑ v, devVec V₁ x₁ x v ^ 2 := by
  calc #(badSet V₁ θ x₁ x) * θ = ∑ _v ∈ badSet V₁ θ x₁ x, θ := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ v ∈ badSet V₁ θ x₁ x, devVec V₁ x₁ x v ^ 2 := Finset.sum_le_sum fun v hv => by
        simp only [badSet, Finset.mem_filter, Finset.mem_univ, true_and] at hv; exact hv.le
    _ ≤ ∑ v, devVec V₁ x₁ x v ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _

omit [DecidableRel G.Adj] in
lemma card_badSet_le (θ : ℝ) (x₁ x : V → ℝ) : #(badSet V₁ θ x₁ x) ≤ Fintype.card V :=
  Finset.card_le_univ _

omit [DecidableRel G.Adj] in
/-- At the reference state itself the deviation is the rest component. -/
lemma devVec_self (x₁ : V → ℝ) (v : V) : devVec V₁ x₁ x₁ v = projRest V₁ x₁ v := by
  simp only [devVec, projRest, projOne, projCut, cutCoef]

omit [DecidableRel G.Adj] in
/-- Many bad nodes at the start force a large rest component: `|B| > ε n` gives
`‖z₁‖² > ε n θ`. -/
lemma restSq_gt_of_card_badSet_gt {θ ε : ℝ} (hθ : 0 ≤ θ) (hε : 0 ≤ ε) (x₁ : V → ℝ)
    (h : ε * Fintype.card V < #(badSet V₁ θ x₁ x₁)) :
    ε * Fintype.card V * θ < restSq V₁ x₁ := by
  have hne : (badSet V₁ θ x₁ x₁).Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < #(badSet V₁ θ x₁ x₁) := lt_of_le_of_lt (by positivity) h
    exact_mod_cast this
  have h1 : #(badSet V₁ θ x₁ x₁) * θ < ∑ v ∈ badSet V₁ θ x₁ x₁, devVec V₁ x₁ x₁ v ^ 2 := by
    rw [← nsmul_eq_mul, ← sum_const]
    exact Finset.sum_lt_sum_of_nonempty hne fun v hv => by
      simp only [badSet, Finset.mem_filter, Finset.mem_univ, true_and] at hv; exact hv
  have h2 : ∑ v ∈ badSet V₁ θ x₁ x₁, devVec V₁ x₁ x₁ v ^ 2 ≤ restSq V₁ x₁ := by
    simp_rw [devVec_self]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _
  have h3 : ε * Fintype.card V * θ ≤ #(badSet V₁ θ x₁ x₁) * θ :=
    mul_le_mul_of_nonneg_right h.le hθ
  linarith

omit [Fintype V] [DecidableRel G.Adj] in
lemma avgRun_take_append (x : V → ℝ) (l₁ l₂ : List G.Dart) {t : ℕ} (ht : l₁.length ≤ t) :
    avgRun G x ((l₁ ++ l₂).take t) = avgRun G (avgRun G x l₁) (l₂.take (t - l₁.length)) := by
  rw [List.take_append, List.take_of_length_le ht, avgRun_append]

/-- The threshold `θ = ε² ‖y⁽⁰⁾‖²/(4n)` for the deviation. -/
noncomputable def thr (V₁ : Finset V) (ε : ℝ) (x₀ : V → ℝ) : ℝ :=
  ε ^ 2 * (Fintype.card V * cutCoef V₁ x₀ ^ 2) / (4 * Fintype.card V)

/-- The cut coefficient has moved by the start of the phase: `4 n (β₁ - β₀)² > ε² ‖y⁽⁰⁾‖²`. -/
def CutMoved (V₁ : Finset V) (ε : ℝ) (x₀ x₁ : V → ℝ) : Prop :=
  ε ^ 2 * (Fintype.card V * cutCoef V₁ x₀ ^ 2) <
    4 * Fintype.card V * (cutCoef V₁ x₁ - cutCoef V₁ x₀) ^ 2

open scoped Classical in
/-- **Deterministic core of Lemma 4.2**: if the cut coefficient has not moved much by the start
of the phase (`4 n (β₁ - β₀)² ≤ ε² ‖y⁽⁰⁾‖²`), at most `ε n` nodes are bad at the start and at most
`ε n` rounds of the phase are bad, then at least `(1 - 3ε) n` nodes are `ε`-good at every round of
the phase. -/
theorem card_good_ge (hG : IsClusteredRegular G V₁ d b) (x₀ : V → ℝ) {ε : ℝ}
    (l₁ l₂ : List G.Dart)
    (hF : 4 * Fintype.card V * (cutCoef V₁ (avgRun G x₀ l₁) - cutCoef V₁ x₀) ^ 2 ≤
      ε ^ 2 * (Fintype.card V * cutCoef V₁ x₀ ^ 2))
    (hB : (#(badSet V₁ (thr V₁ ε x₀) (avgRun G x₀ l₁) (avgRun G x₀ l₁)) : ℝ) ≤
      ε * Fintype.card V)
    (hZ : (#{k ∈ range l₂.length | IsBadRound V₁ (thr V₁ ε x₀) (avgRun G x₀ l₁) l₂ k} : ℝ) ≤
      ε * Fintype.card V) :
    (1 - 3 * ε) * Fintype.card V ≤ #{v | ∀ t : ℕ, l₁.length ≤ t → t ≤ l₁.length + l₂.length →
      (avgRun G x₀ ((l₁ ++ l₂).take t) v - (projOne x₀ v + projCut V₁ x₀ v)) ^ 2 ≤
        ε ^ 2 / Fintype.card V * ∑ w, projCut V₁ x₀ w ^ 2} := by
  have hn := hG.card_real_pos
  set N : ℝ := (Fintype.card V : ℝ)
  set s₀ := N * cutCoef V₁ x₀ ^ 2
  set θ := thr V₁ ε x₀
  set x₁ := avgRun G x₀ l₁
  set Tch := (univ.filter fun v => v ∈ badSet V₁ θ x₁ x₁ ∨ ∃ k < l₂.length, ∃ e : G.Dart,
    l₂[k]? = some e ∧ (v = e.fst ∨ v = e.snd) ∧ IsBadStep V₁ θ x₁ (avgRun G x₁ (l₂.take k)) e)
  have hT := card_touched_le θ x₁ l₂ (V₁ := V₁)
  have hsub : univ \ Tch ⊆ (univ.filter fun v => ∀ t : ℕ, l₁.length ≤ t →
      t ≤ l₁.length + l₂.length →
      (avgRun G x₀ ((l₁ ++ l₂).take t) v - (projOne x₀ v + projCut V₁ x₀ v)) ^ 2 ≤
        ε ^ 2 / N * ∑ w, projCut V₁ x₀ w ^ 2) := by
    intro v hv
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Tch, Finset.mem_filter, not_or,
      not_exists, not_and] at hv
    obtain ⟨h0, hstep⟩ := hv
    have hgood := not_mem_badSet_avgRun θ x₁ v l₂ h0 fun k hk e he hve hbad =>
      hstep k hk e he hve hbad
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro t ht1 ht2
    rw [avgRun_take_append x₀ l₁ l₂ ht1]
    have hk := hgood (t - l₁.length) (by omega)
    simp only [badSet, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hk
    set y := avgRun G x₁ (l₂.take (t - l₁.length))
    have havg : avg x₁ = avg x₀ := by simp only [x₁, avg, sum_avgRun]
    have e1 : y v - (projOne x₀ v + projCut V₁ x₀ v) =
        devVec V₁ x₁ y v + (cutCoef V₁ x₁ - cutCoef V₁ x₀) * cutVec V₁ v := by
      simp only [devVec, projOne, projCut_eq, havg]; ring
    rw [e1, IsClusteredRegular.sum_sq_projCut]
    have hχ := cutVec_sq (V₁ := V₁) v
    have hF' : (cutCoef V₁ x₁ - cutCoef V₁ x₀) ^ 2 ≤ ε ^ 2 * s₀ / (4 * N) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have hθ : θ = ε ^ 2 * s₀ / (4 * N) := rfl
    have key : (devVec V₁ x₁ y v + (cutCoef V₁ x₁ - cutCoef V₁ x₀) * cutVec V₁ v) ^ 2 ≤
        2 * devVec V₁ x₁ y v ^ 2 + 2 * (cutCoef V₁ x₁ - cutCoef V₁ x₀) ^ 2 := by
      nlinarith [sq_nonneg (devVec V₁ x₁ y v - (cutCoef V₁ x₁ - cutCoef V₁ x₀) * cutVec V₁ v)]
    have e2 : ε ^ 2 / N * s₀ = 2 * (ε ^ 2 * s₀ / (4 * N)) + 2 * (ε ^ 2 * s₀ / (4 * N)) := by
      field_simp; ring
    rw [show N * cutCoef V₁ x₀ ^ 2 = s₀ from rfl, e2]
    linarith
  have hcard : (N - #Tch : ℝ) ≤ #(univ.filter fun v => ∀ t : ℕ, l₁.length ≤ t →
      t ≤ l₁.length + l₂.length →
      (avgRun G x₀ ((l₁ ++ l₂).take t) v - (projOne x₀ v + projCut V₁ x₀ v)) ^ 2 ≤
        ε ^ 2 / N * ∑ w, projCut V₁ x₀ w ^ 2) := by
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ] at h1
    have h2 : #Tch ≤ Fintype.card V := Finset.card_le_univ _
    have : ((Fintype.card V - #Tch : ℕ) : ℝ) = N - #Tch := by rw [Nat.cast_sub h2]
    rw [← this]; exact_mod_cast h1
  have hT' : (#Tch : ℝ) ≤ #(badSet V₁ θ x₁ x₁) +
      2 * #{k ∈ range l₂.length | IsBadRound V₁ θ x₁ l₂ k} := by exact_mod_cast hT
  linarith


omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma ite_exists_some {α : Type*} (o : Option α) (P : α → Prop) [DecidablePred P]
    [Decidable (∃ e, o = some e ∧ P e)] :
    (if ∃ e, o = some e ∧ P e then (1 : ℝ) else 0) =
      match o with
      | some e => if P e then 1 else 0
      | none => 0 := by
  cases o <;> simp

/-- One bad round: `P(bad) ≤ b/d + 2 |B|/n`. -/
lemma IsClusteredRegular.avg_isBadStep_le (hG : IsClusteredRegular G V₁ d b) (θ : ℝ)
    (x₁ y : V → ℝ) :
    avg (fun e : G.Dart => if IsBadStep V₁ θ x₁ y e then (1 : ℝ) else 0) ≤
      b / d + 2 * (#(badSet V₁ θ x₁ y) / Fintype.card V) := by
  have h : ∀ e : G.Dart, (if IsBadStep V₁ θ x₁ y e then (1 : ℝ) else 0) ≤
      (if IsCrossDart V₁ e then 1 else 0) + (if e.fst ∈ badSet V₁ θ x₁ y then 1 else 0) +
        (if e.snd ∈ badSet V₁ θ x₁ y then 1 else 0) := fun e => by
    unfold IsBadStep
    by_cases h1 : IsCrossDart V₁ e <;> by_cases h2 : e.fst ∈ badSet V₁ θ x₁ y <;>
      by_cases h3 : e.snd ∈ badSet V₁ θ x₁ y <;> simp [h1, h2, h3]
  refine (avg_le_avg h).trans (le_of_eq ?_)
  rw [avg_add, avg_add, hG.avg_cross, hG.avg_fst_mem, hG.avg_snd_mem]
  ring

open scoped Classical in
/-- **The good event, for fixed initial signs** (proof of Lemma 4.2): the probability that at
least `(1 - 3ε) n` nodes are `ε`-good throughout the phase `[t₁, t₁ + M]` is at least
`1 - P(cut moved) - P(|B| > ε n) - (1/(ε n)) ∑_{k < M} (b/d + 2 E[1 - 1_moved; |B_k|/n])`. -/
theorem IsClusteredRegular.expList_good_ge (hG : IsClusteredRegular G V₁ d b) (x₀ : V → ℝ)
    {ε : ℝ} (hε : 0 < ε) (t₁ M : ℕ) :
    1 - expList G.Dart t₁ (fun l₁ => if CutMoved V₁ ε x₀ (avgRun G x₀ l₁) then 1 else 0) -
        expList G.Dart t₁ (fun l₁ =>
          if ε * Fintype.card V < #(badSet V₁ (thr V₁ ε x₀) (avgRun G x₀ l₁) (avgRun G x₀ l₁))
          then 1 else 0) -
        1 / (ε * Fintype.card V) * ∑ k ∈ range M, (b / d + 2 * expList G.Dart t₁ (fun l₁ =>
          (if CutMoved V₁ ε x₀ (avgRun G x₀ l₁) then 0 else 1) * expList G.Dart k (fun p =>
            #(badSet V₁ (thr V₁ ε x₀) (avgRun G x₀ l₁) (avgRun G (avgRun G x₀ l₁) p)) /
              Fintype.card V))) ≤
      expList G.Dart (t₁ + M) (fun l =>
        if (1 - 3 * ε) * Fintype.card V ≤ #{v | ∀ t : ℕ, t₁ ≤ t → t ≤ t₁ + M →
          (avgRun G x₀ (l.take t) v - (projOne x₀ v + projCut V₁ x₀ v)) ^ 2 ≤
            ε ^ 2 / Fintype.card V * ∑ w, projCut V₁ x₀ w ^ 2} then 1 else 0) := by
  haveI := hG.nonempty_dart
  have hn := hG.card_real_pos
  set N : ℝ := (Fintype.card V : ℝ)
  have hεN : 0 < ε * N := by positivity
  set θ := thr V₁ ε x₀
  -- the inner bound, for a fixed start `l₁` of length `t₁`
  set F1 : List G.Dart → ℝ := fun l₁ => if CutMoved V₁ ε x₀ (avgRun G x₀ l₁) then 1 else 0
  set D1 : List G.Dart → ℝ := fun l₁ =>
    if ε * N < #(badSet V₁ θ (avgRun G x₀ l₁) (avgRun G x₀ l₁)) then 1 else 0
  set g3 : ℕ → List G.Dart → ℝ := fun k l₁ =>
    (if CutMoved V₁ ε x₀ (avgRun G x₀ l₁) then 0 else 1) * expList G.Dart k (fun p =>
      #(badSet V₁ θ (avgRun G x₀ l₁) (avgRun G (avgRun G x₀ l₁) p)) / N)
  have hinner : ∀ l₁ : List G.Dart, l₁.length = t₁ →
      1 - F1 l₁ - D1 l₁ - 1 / (ε * N) * ∑ k ∈ range M, (b / d + 2 * g3 k l₁) ≤
      expList G.Dart M (fun l₂ =>
        if (1 - 3 * ε) * N ≤ #{v | ∀ t : ℕ, t₁ ≤ t → t ≤ t₁ + M →
          (avgRun G x₀ ((l₁ ++ l₂).take t) v - (projOne x₀ v + projCut V₁ x₀ v)) ^ 2 ≤
            ε ^ 2 / N * ∑ w, projCut V₁ x₀ w ^ 2} then 1 else 0) := by
    intro l₁ hl₁
    set x₁ := avgRun G x₀ l₁
    let F : List G.Dart → Option G.Dart → ℝ := fun p o => match o with
      | some e => if IsBadStep V₁ θ x₁ (avgRun G x₁ p) e then 1 else 0
      | none => 0
    have hF0 : ∀ p o, 0 ≤ F p o := by
      intro p o
      cases o with
      | none => exact le_rfl
      | some e => simp only [F]; split_ifs <;> norm_num
    set Zc : List G.Dart → ℝ := fun l₂ => ∑ k ∈ range M, F (l₂.take k) l₂[k]?
    have hZc_ge : ∀ l₂, (#{k ∈ range M | IsBadRound V₁ θ x₁ l₂ k} : ℝ) ≤ Zc l₂ := by
      intro l₂
      rw [Finset.card_filter]
      push_cast
      refine Finset.sum_le_sum fun k _ => ?_
      by_cases h : IsBadRound V₁ θ x₁ l₂ k
      · obtain ⟨e, he, hb⟩ := h
        rw [if_pos ⟨e, he, hb⟩, he]
        simp [F, hb]
      · rw [if_neg h]; exact hF0 _ _
    have hZ0 : ∀ l₂, 0 ≤ Zc l₂ := fun l₂ => Finset.sum_nonneg fun k _ => hF0 _ _
    have hc01 : (if CutMoved V₁ ε x₀ x₁ then (0 : ℝ) else 1) = 1 - F1 l₁ := by
      simp only [F1, x₁]; split_ifs <;> norm_num
    -- pointwise in `l₂`
    have hpt : ∀ l₂ : List G.Dart, l₂.length = M →
        1 - F1 l₁ - D1 l₁ - (1 - F1 l₁) * (1 / (ε * N) * Zc l₂) ≤
        (if (1 - 3 * ε) * N ≤ #{v | ∀ t : ℕ, t₁ ≤ t → t ≤ t₁ + M →
          (avgRun G x₀ ((l₁ ++ l₂).take t) v - (projOne x₀ v + projCut V₁ x₀ v)) ^ 2 ≤
            ε ^ 2 / N * ∑ w, projCut V₁ x₀ w ^ 2} then 1 else 0) := by
      intro l₂ hl₂
      have hD0 : 0 ≤ D1 l₁ := by simp only [D1]; split_ifs <;> norm_num
      have hR0 : (0 : ℝ) ≤ if (1 - 3 * ε) * N ≤ #{v | ∀ t : ℕ, t₁ ≤ t → t ≤ t₁ + M →
          (avgRun G x₀ ((l₁ ++ l₂).take t) v - (projOne x₀ v + projCut V₁ x₀ v)) ^ 2 ≤
            ε ^ 2 / N * ∑ w, projCut V₁ x₀ w ^ 2} then 1 else 0 := by split_ifs <;> norm_num
      have hcZ : 0 ≤ 1 / (ε * N) * Zc l₂ := mul_nonneg (by positivity) (hZ0 l₂)
      by_cases hF : CutMoved V₁ ε x₀ x₁
      · have : F1 l₁ = 1 := by simp only [F1, x₁] at hF ⊢; simp [hF]
        rw [this]; nlinarith
      have hF1 : F1 l₁ = 0 := by simp only [F1, x₁] at hF ⊢; simp [hF]
      rw [hF1]
      by_cases hD : ε * N < #(badSet V₁ θ x₁ x₁)
      · have : D1 l₁ = 1 := by simp only [D1, x₁] at hD ⊢; simp [hD]
        rw [this]; nlinarith
      have hD1 : D1 l₁ = 0 := by simp only [D1, x₁] at hD ⊢; simp [hD]
      rw [hD1]
      by_cases hZ : ε * N < Zc l₂
      · have : 1 < 1 / (ε * N) * Zc l₂ := by
          rw [one_div, ← div_eq_inv_mul, lt_div_iff₀ hεN]; linarith
        linarith
      have hD' := le_of_not_gt hD
      have hZ' : (#{k ∈ range l₂.length | IsBadRound V₁ θ x₁ l₂ k} : ℝ) ≤ ε * N := by
        rw [hl₂]; exact (hZc_ge l₂).trans (le_of_not_gt hZ)
      have hgood := card_good_ge hG x₀ l₁ l₂ (le_of_not_gt hF) hD' hZ'
      rw [hl₁, hl₂] at hgood
      rw [if_pos hgood]
      linarith
    -- the expectation of `Zc`
    have hZc : expList G.Dart M Zc ≤ ∑ k ∈ range M, (b / d + 2 * expList G.Dart k (fun p =>
        #(badSet V₁ θ x₁ (avgRun G x₁ p)) / N)) := by
      rw [expList_sum]
      refine Finset.sum_le_sum fun k hk => ?_
      have hkM : k < M := Finset.mem_range.mp hk
      rw [expList_take_getElem? hkM]
      rw [← expList_const_mul, ← expList_const (α := G.Dart) k (b / d : ℝ), ← expList_add]
      exact expList_le_expList fun p => hG.avg_isBadStep_le θ x₁ _
    refine le_trans ?_ (expList_le_of_length hpt)
    have e1 : expList G.Dart M (fun l₂ => 1 - F1 l₁ - D1 l₁ - (1 - F1 l₁) * (1 / (ε * N) * Zc l₂)) =
        1 - F1 l₁ - D1 l₁ - (1 - F1 l₁) * (1 / (ε * N) * expList G.Dart M Zc) := by
      rw [← expList_const_mul, ← expList_const_mul]
      rw [show (fun l₂ => 1 - F1 l₁ - D1 l₁ - (1 - F1 l₁) * (1 / (ε * N) * Zc l₂)) =
          fun l₂ => (1 - F1 l₁ - D1 l₁) + (-1) * ((1 - F1 l₁) * (1 / (ε * N) * Zc l₂)) from
        funext fun l₂ => by ring]
      rw [expList_add, expList_const, expList_const_mul]
      ring
    rw [e1]
    have hF01 : 0 ≤ 1 - F1 l₁ := by simp only [F1]; split_ifs <;> norm_num
    have hF11 : 1 - F1 l₁ ≤ 1 := by simp only [F1]; split_ifs <;> norm_num
    have hc : 0 ≤ 1 / (ε * N) := by positivity
    have h1 : (1 - F1 l₁) * (1 / (ε * N) * expList G.Dart M Zc) ≤
        1 / (ε * N) * ∑ k ∈ range M, (b / d + 2 * g3 k l₁) := by
      have hsum : (1 - F1 l₁) * expList G.Dart M Zc ≤ ∑ k ∈ range M, (b / d + 2 * g3 k l₁) := by
        refine (mul_le_mul_of_nonneg_left hZc hF01).trans ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun k _ => ?_
        have hbd : 0 ≤ (b / d : ℝ) := by positivity
        have : (1 - F1 l₁) * (2 * expList G.Dart k (fun p =>
            #(badSet V₁ θ x₁ (avgRun G x₁ p)) / N)) = 2 * g3 k l₁ := by
          simp only [g3, x₁, F1]; split_ifs <;> ring
        nlinarith [mul_le_mul_of_nonneg_right hF11 hbd]
      calc (1 - F1 l₁) * (1 / (ε * N) * expList G.Dart M Zc)
          = 1 / (ε * N) * ((1 - F1 l₁) * expList G.Dart M Zc) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hsum hc
    linarith
  rw [expList_append]
  refine le_trans ?_ (expList_le_of_length hinner)
  have hsub : ∀ (F G' : List G.Dart → ℝ), expList G.Dart t₁ (fun l => F l - G' l) =
      expList G.Dart t₁ F - expList G.Dart t₁ G' := fun F G' => by
    rw [show (fun l => F l - G' l) = fun l => F l + (-1) * G' l from funext fun l => by ring,
      expList_add, expList_const_mul]; ring
  rw [hsub, hsub, hsub, expList_const, expList_const_mul, expList_sum]
  simp_rw [expList_add, expList_const, expList_const_mul]
  exact le_rfl


/-! ### Bounds for one choice of the initial signs, in the form used by anti-concentration -/

namespace IsClusteredRegular
variable (hG : IsClusteredRegular G V₁ d b) (h3 : ThirdEigenvalueLB G V₁ d lam3)
include hG h3

open scoped Classical in
/-- The cut coefficient moves by the start of the phase with probability `g₁` satisfying
`g₁ ‖y⁽⁰⁾‖² ≤ (8 L₁/ε²) ‖y⁽⁰⁾‖² + 20 r/ε²`. -/
lemma cutMoved_bound (hl3 : 0 < lam3) (hN : (16 : ℝ) ≤ Fintype.card V) {ε : ℝ} (hε : 0 < ε)
    (σ : V → ℤˣ) (t₁ : ℕ) (hL : (t₁ : ℝ) * (2 * b / d) / Fintype.card V ≤ 1 / 8)
    (hr : (2 * b / d) / lam3 ≤ 1 / 8) :
    expList G.Dart t₁ (fun l₁ => if CutMoved V₁ ε (signVec σ) (avgRun G (signVec σ) l₁) then 1
        else 0) * (Fintype.card V * cutCoef V₁ (signVec σ) ^ 2) ≤
      8 * (t₁ * (2 * b / d) / Fintype.card V) / ε ^ 2 *
          (Fintype.card V * cutCoef V₁ (signVec σ) ^ 2) + 20 * ((2 * b / d) / lam3) / ε ^ 2 := by
  have hb := hG.expList_cutDev_signVec_le h3 hl3 hN σ t₁ hL hr
  set N : ℝ := (Fintype.card V : ℝ)
  set s₀ := N * cutCoef V₁ (signVec σ) ^ 2
  rw [mul_comm, ← expList_const_mul]
  have hpt : ∀ l₁ : List G.Dart, s₀ * (if CutMoved V₁ ε (signVec σ) (avgRun G (signVec σ) l₁)
      then 1 else 0) ≤ 4 / ε ^ 2 * (N * (cutCoef V₁ (avgRun G (signVec σ) l₁) -
        cutCoef V₁ (signVec σ)) ^ 2) := fun l₁ => by
    split_ifs with h
    · unfold CutMoved at h
      rw [mul_one, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith
    · rw [mul_zero]; positivity
  refine (expList_le_expList hpt).trans ?_
  rw [expList_const_mul]
  have : 0 ≤ 4 / ε ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left hb this
  refine this.trans (le_of_eq ?_)
  field_simp
  ring

open scoped Classical in
/-- Many bad nodes at the start: probability `g₂` with
`g₂ ‖y⁽⁰⁾‖² ≤ (12 r/ε³) ‖y⁽⁰⁾‖² + (4/ε³)(n (1 - λ₃/n)^{t₁} + 10 r²)`. -/
lemma manyBad_bound (hl3 : 0 < lam3) (hN : (16 : ℝ) ≤ Fintype.card V) {ε : ℝ} (hε : 0 < ε)
    (σ : V → ℤˣ) (t₁ : ℕ) (hL : (t₁ : ℝ) * (2 * b / d) / Fintype.card V ≤ 1 / 8)
    (hr : (2 * b / d) / lam3 ≤ 1 / 8) :
    expList G.Dart t₁ (fun l₁ => if ε * Fintype.card V < #(badSet V₁ (thr V₁ ε (signVec σ))
        (avgRun G (signVec σ) l₁) (avgRun G (signVec σ) l₁)) then 1 else 0) *
        (Fintype.card V * cutCoef V₁ (signVec σ) ^ 2) ≤
      12 * ((2 * b / d) / lam3) / ε ^ 3 * (Fintype.card V * cutCoef V₁ (signVec σ) ^ 2) +
        4 / ε ^ 3 * (Fintype.card V * (1 - lam3 / Fintype.card V) ^ t₁ +
          10 * ((2 * b / d) / lam3) ^ 2) := by
  have hb := hG.expList_restSq_signVec_le h3 hl3 hN σ t₁ hL hr
  have hn := hG.card_real_pos
  set N : ℝ := (Fintype.card V : ℝ)
  set s₀ := N * cutCoef V₁ (signVec σ) ^ 2
  rw [mul_comm, ← expList_const_mul]
  have hpt : ∀ l₁ : List G.Dart, s₀ * (if ε * N < #(badSet V₁ (thr V₁ ε (signVec σ))
      (avgRun G (signVec σ) l₁) (avgRun G (signVec σ) l₁)) then 1 else 0) ≤
      4 / ε ^ 3 * restSq V₁ (avgRun G (signVec σ) l₁) := fun l₁ => by
    split_ifs with h
    · have hθ : 0 ≤ thr V₁ ε (signVec σ) := by unfold thr; positivity
      have := restSq_gt_of_card_badSet_gt hθ hε.le _ h
      unfold thr at this
      rw [mul_one, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      have e : ε * N * (ε ^ 2 * s₀ / (4 * N)) = ε ^ 3 * s₀ / 4 := by field_simp
      rw [e] at this
      nlinarith
    · rw [mul_zero]; exact mul_nonneg (by positivity) (restSq_nonneg _)
  refine (expList_le_expList hpt).trans ?_
  rw [expList_const_mul]
  have : 0 ≤ 4 / ε ^ 3 := by positivity
  have := mul_le_mul_of_nonneg_left hb this
  refine this.trans (le_of_eq ?_)
  ring

open scoped Classical in
/-- Bad rounds in the phase: `g₃ ‖y⁽⁰⁾‖² ≤ (4/ε²)(6.25 L_k + 11 r) ‖y⁽⁰⁾‖² +
(8/ε²)(n (1 - λ₃/n)^{t₁} + 10 r²)`, where `g₃` is the expected fraction of bad nodes after
`t₁ + k` rounds, on the event that the cut coefficient has not moved. -/
lemma badRound_bound (hl3 : 0 < lam3) (hN : (16 : ℝ) ≤ Fintype.card V) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (σ : V → ℤˣ) (t₁ k : ℕ)
    (hL : (t₁ : ℝ) * (2 * b / d) / Fintype.card V ≤ 1 / 8)
    (hLk : (k : ℝ) * (2 * b / d) / Fintype.card V ≤ 1 / 8)
    (hr : (2 * b / d) / lam3 ≤ 1 / 8) :
    expList G.Dart t₁ (fun l₁ =>
        (if CutMoved V₁ ε (signVec σ) (avgRun G (signVec σ) l₁) then 0 else 1) *
          expList G.Dart k (fun p => #(badSet V₁ (thr V₁ ε (signVec σ)) (avgRun G (signVec σ) l₁)
            (avgRun G (avgRun G (signVec σ) l₁) p)) / Fintype.card V)) *
        (Fintype.card V * cutCoef V₁ (signVec σ) ^ 2) ≤
      4 / ε ^ 2 * (25 / 4 * (k * (2 * b / d) / Fintype.card V) + 11 * ((2 * b / d) / lam3)) *
          (Fintype.card V * cutCoef V₁ (signVec σ) ^ 2) +
        8 / ε ^ 2 * (Fintype.card V * (1 - lam3 / Fintype.card V) ^ t₁ +
          10 * ((2 * b / d) / lam3) ^ 2) := by
  haveI := hG.nonempty_dart
  have hz1 := hG.expList_restSq_signVec_le h3 hl3 hN σ t₁ hL hr
  have hn := hG.card_real_pos
  set N : ℝ := (Fintype.card V : ℝ)
  set x₀ := signVec σ
  set s₀ := N * cutCoef V₁ x₀ ^ 2
  set r := (2 * b / d : ℝ) / lam3
  set Lk := (k : ℝ) * (2 * b / d) / N
  have hr0 : 0 ≤ r := by positivity
  have hLk0 : 0 ≤ Lk := by positivity
  have hs0 : 0 ≤ s₀ := by positivity
  rw [mul_comm, ← expList_const_mul]
  have hpt : ∀ l₁ : List G.Dart,
      s₀ * ((if CutMoved V₁ ε x₀ (avgRun G x₀ l₁) then 0 else 1) *
        expList G.Dart k (fun p => #(badSet V₁ (thr V₁ ε x₀) (avgRun G x₀ l₁)
          (avgRun G (avgRun G x₀ l₁) p)) / N)) ≤
      4 / ε ^ 2 * ((5 / 2 * Lk + 2 * r) * (5 / 2 * s₀)) +
        4 / ε ^ 2 * (2 * restSq V₁ (avgRun G x₀ l₁)) := fun l₁ => by
    set x₁ := avgRun G x₀ l₁
    have hz : 0 ≤ restSq V₁ x₁ := restSq_nonneg _
    have hc : 0 ≤ 4 / ε ^ 2 := by positivity
    split_ifs with h
    · rw [zero_mul, mul_zero]; positivity
    · rw [one_mul]
      -- the fraction of bad nodes against the deviation
      have hcard : ∀ p : List G.Dart, s₀ * (#(badSet V₁ (thr V₁ ε x₀) x₁ (avgRun G x₁ p)) / N) ≤
          4 / ε ^ 2 * ∑ v, devVec V₁ x₁ (avgRun G x₁ p) v ^ 2 := fun p => by
        have := card_badSet_mul_le (thr V₁ ε x₀) x₁ (avgRun G x₁ p) (V₁ := V₁)
        have ht : thr V₁ ε x₀ = ε ^ 2 * s₀ / (4 * N) := rfl
        generalize (#(badSet V₁ (thr V₁ ε x₀) x₁ (avgRun G x₁ p)) : ℝ) = B at this ⊢
        have e : s₀ * (B / N) = 4 / ε ^ 2 * (B * thr V₁ ε x₀) := by
          rw [ht]; field_simp
        rw [e]; exact mul_le_mul_of_nonneg_left this hc
      rw [← expList_const_mul]
      refine (expList_le_expList hcard).trans ?_
      rw [expList_const_mul]
      have hdev := hG.expList_devVec_le h3 hl3 hN x₁ k hLk hr
      have hs1 : N * cutCoef V₁ x₁ ^ 2 ≤ 5 / 2 * s₀ := by
        unfold CutMoved at h
        have h := le_of_not_gt h
        have hε2 : ε ^ 2 ≤ 1 := by nlinarith
        nlinarith [sq_nonneg (cutCoef V₁ x₁ - 2 * cutCoef V₁ x₀), hn]
      have h1 : (5 / 2 * Lk + 2 * r) * (N * cutCoef V₁ x₁ ^ 2) ≤
          (5 / 2 * Lk + 2 * r) * (5 / 2 * s₀) :=
        mul_le_mul_of_nonneg_left hs1 (by positivity)
      have := mul_le_mul_of_nonneg_left hdev hc
      nlinarith
  refine (expList_le_expList hpt).trans ?_
  rw [expList_add, expList_const, expList_const_mul]
  have hc : 0 ≤ 4 / ε ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left hz1 (show 0 ≤ 4 / ε ^ 2 * 2 by positivity)
  have e1 : 4 / ε ^ 2 * (25 / 4 * Lk + 11 * r) * s₀ =
      4 / ε ^ 2 * ((5 / 2 * Lk + 2 * r) * (5 / 2 * s₀)) + 4 / ε ^ 2 * 2 * (3 * r * s₀) := by ring
  rw [e1]
  have e2 : 8 / ε ^ 2 * (N * (1 - lam3 / N) ^ t₁ + 10 * r ^ 2) =
      4 / ε ^ 2 * 2 * (N * (1 - lam3 / N) ^ t₁ + 10 * r ^ 2) := by ring
  rw [e2]
  have e3 : 4 / ε ^ 2 * 2 * (N * (1 - lam3 / N) ^ t₁ + 3 * r * s₀ + 10 * r ^ 2) =
      4 / ε ^ 2 * 2 * (3 * r * s₀) + 4 / ε ^ 2 * 2 * (N * (1 - lam3 / N) ^ t₁ + 10 * r ^ 2) := by
    ring
  rw [e3] at this
  have e4 : (4 / ε ^ 2 * expList G.Dart t₁ fun l => 2 * restSq V₁ (avgRun G x₀ l)) =
      4 / ε ^ 2 * 2 * expList G.Dart t₁ fun l => restSq V₁ (avgRun G x₀ l) := by
    rw [expList_const_mul]; ring
  linarith

end IsClusteredRegular


/-! ### Lemma 4.2 -/

/-- `n (1 - λ₃/n)ᵗ ≤ 1/n⁵` once `λ₃ t/n ≥ 6 log n`. -/
lemma card_mul_pow_le_six {N l3 : ℝ} {T : ℕ} (hN : 0 < N) (hl3 : 0 < l3) (hq : 0 ≤ 1 - l3 / N)
    (hT : 6 * N / l3 * Real.log N ≤ T) :
    N * (1 - l3 / N) ^ T ≤ 1 / N ^ 5 := by
  have h1 : (1 - l3 / N) ^ T ≤ Real.exp (-(l3 / N)) ^ T :=
    pow_le_pow_left₀ hq (Real.one_sub_le_exp_neg _) T
  have h2 : Real.exp (-(l3 / N)) ^ T = Real.exp (-(l3 * T / N)) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have h3 : -(l3 * T / N) ≤ -(6 * Real.log N) := by
    have : 6 * Real.log N ≤ l3 * T / N := by
      rw [le_div_iff₀ hN]
      have := mul_le_mul_of_nonneg_left hT hl3.le
      rw [show l3 * (6 * N / l3 * Real.log N) = 6 * Real.log N * N by field_simp] at this
      linarith
    linarith
  have h4 : Real.exp (-(6 * Real.log N)) = 1 / N ^ 6 := by
    rw [Real.exp_neg, show 6 * Real.log N = (6 : ℕ) * Real.log N by norm_num, Real.exp_nat_mul,
      Real.exp_log hN]; simp
  calc N * (1 - l3 / N) ^ T ≤ N * Real.exp (-(l3 * T / N)) := by
        rw [← h2]; exact mul_le_mul_of_nonneg_left h1 hN.le
    _ ≤ N * (1 / N ^ 6) := by rw [← h4]; gcongr
    _ = 1 / N ^ 5 := by field_simp

lemma one_div_sqrt_le {N δ : ℝ} (hN : 0 ≤ N) (hδ : 0 < δ) (h : 1 ≤ δ ^ 2 * (N + 1)) :
    1 / Real.sqrt (N + 1) ≤ δ := by
  have hs : 0 < Real.sqrt (N + 1) := Real.sqrt_pos.mpr (by linarith)
  rw [div_le_iff₀ hs]
  have : Real.sqrt (δ ^ 2 * (N + 1)) = δ * Real.sqrt (N + 1) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hδ.le]
  rw [← this]
  exact Real.le_sqrt_of_sq_le (by simpa using h)

/-! ### The final arithmetic of Lemma 4.2 -/

section Arith
variable {N LN l3 ε r w u L : ℝ}

lemma arith_T1 (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hL : L ≤ 7 * (r * LN))
    (hrLN : 10 ^ 6 * (r * LN) ≤ 2 * ε ^ 4) : 8 * L / ε ^ 2 ≤ ε / 100 := by
  have h43 : ε ^ 4 ≤ ε ^ 3 := pow_le_pow_of_le_one hε0.le hε1 (by norm_num)
  rw [div_le_iff₀ (by positivity)]
  have : ε / 100 * ε ^ 2 = ε ^ 3 / 100 := by ring
  rw [this]
  have : 0 ≤ ε ^ 3 := by positivity
  linarith

lemma arith_T2 (hn : 0 < N) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hLN1 : 1 ≤ LN)
    (hNε : 5 * 10 ^ 5 * LN ^ 2 ≤ N * ε ^ 4) (hu : u = 1 / Real.sqrt (N + 1)) :
    u ≤ ε / 100 := by
  rw [hu]
  refine one_div_sqrt_le hn.le (by positivity) ?_
  have h42 : ε ^ 4 ≤ ε ^ 2 := pow_le_pow_of_le_one hε0.le hε1 (by norm_num)
  have h1 : N * ε ^ 4 ≤ N * ε ^ 2 := mul_le_mul_of_nonneg_left h42 hn.le
  have h2 : (1 : ℝ) ≤ LN ^ 2 := by nlinarith
  have e : (ε / 100) ^ 2 * (N + 1) = N * ε ^ 2 / 10000 + ε ^ 2 / 10000 := by ring
  rw [e]
  have : 0 ≤ ε ^ 2 / 10000 := by positivity
  linarith

lemma arith_T3 (hε0 : 0 < ε) (hLN1 : 1 ≤ LN) : 2 * (ε / (100 * LN)) * (1 + LN) ≤ ε / 25 := by
  have hLN : 0 < LN := by linarith
  have e : 2 * (ε / (100 * LN)) * (1 + LN) = ε * (1 + LN) / (50 * LN) := by field_simp; ring
  rw [e, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [mul_le_mul_of_nonneg_left hLN1 hε0.le]

lemma arith_T4 (hε0 : 0 < ε) (hLN1 : 1 ≤ LN) (hr0 : 0 ≤ r)
    (hrLN : 10 ^ 6 * (r * LN) ≤ 2 * ε ^ 4) : 12 * r / ε ^ 3 ≤ ε / 100 := by
  have : r ≤ r * LN := le_mul_of_one_le_right hr0 hLN1
  rw [div_le_iff₀ (by positivity)]
  have e : ε / 100 * ε ^ 3 = ε ^ 4 / 100 := by ring
  rw [e]
  linarith

lemma arith_wLN (hn : 0 < N) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hLN1 : 1 ≤ LN) (hNbig : 5 * 10 ^ 5 ≤ N)
    (hNε : 5 * 10 ^ 5 * LN ^ 2 ≤ N * ε ^ 4) (hw : w * N ^ 2 = 1) : 800 * (w * LN) ≤ ε ^ 3 := by
  have h43 : ε ^ 4 ≤ ε ^ 3 := pow_le_pow_of_le_one hε0.le hε1 (by norm_num)
  have hN2 : 0 < N ^ 2 := by positivity
  refine le_of_mul_le_mul_right ?_ hN2
  have e : 800 * (w * LN) * N ^ 2 = 800 * LN := by
    rw [show 800 * (w * LN) * N ^ 2 = 800 * LN * (w * N ^ 2) by ring, hw, mul_one]
  rw [e]
  have h1 : (N * ε ^ 4) * N ≤ ε ^ 3 * N ^ 2 := by
    rw [show ε ^ 3 * N ^ 2 = (N * ε ^ 3) * N by ring]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h43 hn.le) hn.le
  have h2 : 5 * 10 ^ 5 * LN ^ 2 * N ≤ (N * ε ^ 4) * N := mul_le_mul_of_nonneg_right hNε hn.le
  have h3 : LN ≤ LN ^ 2 := by nlinarith
  have h4 : 800 * LN ≤ 5 * 10 ^ 5 * LN ^ 2 * N := by nlinarith
  linarith

lemma arith_T5 (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hLN1 : 1 ≤ LN) (hw0 : 0 ≤ w) (hr0 : 0 ≤ r)
    (hwLN : 800 * (w * LN) ≤ ε ^ 3) (hrLN : 10 ^ 6 * (r * LN) ≤ 2 * ε ^ 4) :
    2 * (2 * (w + 4 * r) / ε ^ 2) * (1 + LN) ≤ ε / 50 := by
  have h43 : ε ^ 4 ≤ ε ^ 3 := pow_le_pow_of_le_one hε0.le hε1 (by norm_num)
  have h1 : 2 * (2 * (w + 4 * r) / ε ^ 2) * (1 + LN) ≤ 2 * (2 * (w + 4 * r) / ε ^ 2) * (2 * LN) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  refine h1.trans ?_
  have e : 2 * (2 * (w + 4 * r) / ε ^ 2) * (2 * LN) = 8 * (w * LN + 4 * (r * LN)) / ε ^ 2 := by
    ring
  rw [e, div_le_iff₀ (by positivity)]
  have e2 : ε / 50 * ε ^ 2 = ε ^ 3 / 50 := by ring
  rw [e2]
  have : 0 ≤ ε ^ 3 := by positivity
  linarith

lemma arith_T6 (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hl3 : 0 < l3) {l2 : ℝ} (hr : r = l2 / l3)
    (hrLN : 10 ^ 6 * (r * LN) ≤ 2 * ε ^ 4) : 6 * LN / (l3 * ε) * (l2 / 2) ≤ ε / 100 := by
  have h42 : ε ^ 4 ≤ ε ^ 2 := pow_le_pow_of_le_one hε0.le hε1 (by norm_num)
  have e : 6 * LN / (l3 * ε) * (l2 / 2) = 3 * (r * LN) / ε := by rw [hr]; field_simp; ring
  rw [e, div_le_iff₀ hε0]
  have e2 : ε / 100 * ε = ε ^ 2 / 100 := by ring
  rw [e2]
  have : 0 ≤ ε ^ 4 := by positivity
  linarith

lemma arith_T7 (hε0 : 0 < ε) (hl3 : 0 < l3) (hLN1 : 1 ≤ LN) (hr0 : 0 ≤ r)
    (hrLN2 : 10 ^ 6 * (r * LN ^ 2) ≤ l3 * ε ^ 4) :
    6 * LN / (l3 * ε) * (2 * (4 / ε ^ 2 * (25 / 4 * (6 * (r * LN)) + 11 * r))) ≤ ε / 100 := by
  have hrr : r ≤ r * LN := le_mul_of_one_le_right hr0 hLN1
  have h1 : 25 / 4 * (6 * (r * LN)) + 11 * r ≤ 49 * (r * LN) := by linarith
  have h2 : 6 * LN / (l3 * ε) * (2 * (4 / ε ^ 2 * (25 / 4 * (6 * (r * LN)) + 11 * r))) ≤
      6 * LN / (l3 * ε) * (2 * (4 / ε ^ 2 * (49 * (r * LN)))) := by
    have hLN : 0 ≤ LN := by linarith
    gcongr
  refine h2.trans ?_
  have e : 6 * LN / (l3 * ε) * (2 * (4 / ε ^ 2 * (49 * (r * LN)))) =
      2352 * (r * LN ^ 2) / (l3 * ε ^ 3) := by field_simp; ring
  rw [e, div_le_iff₀ (by positivity)]
  have e2 : ε / 100 * (l3 * ε ^ 3) = l3 * ε ^ 4 / 100 := by ring
  rw [e2]
  have : 0 ≤ l3 * ε ^ 4 := by positivity
  linarith

lemma arith_T8 (hn : 0 < N) (hε0 : 0 < ε) (hl3 : 0 < l3) (hLN1 : 1 ≤ LN)
    (hC : 2 * 10 ^ 6 * LN ^ 2 ≤ N * l3 ^ 2 * ε ^ 4) (hu : u = 1 / Real.sqrt (N + 1)) :
    6 * LN / (l3 * ε) * (2 * u) ≤ ε / 20 := by
  have hLN : 0 < LN := by linarith
  have hu' : u ≤ ε ^ 2 * l3 / (240 * LN) := by
    rw [hu]
    refine one_div_sqrt_le hn.le (by positivity) ?_
    have e : (ε ^ 2 * l3 / (240 * LN)) ^ 2 * (N + 1) =
        (N * l3 ^ 2 * ε ^ 4 + l3 ^ 2 * ε ^ 4) / (57600 * LN ^ 2) := by field_simp; ring
    rw [e, le_div_iff₀ (by positivity)]
    have : 0 ≤ l3 ^ 2 * ε ^ 4 := by positivity
    have : 0 ≤ LN ^ 2 := by positivity
    linarith
  calc 6 * LN / (l3 * ε) * (2 * u) ≤ 6 * LN / (l3 * ε) * (2 * (ε ^ 2 * l3 / (240 * LN))) := by
        gcongr
    _ = ε / 20 := by field_simp; ring

lemma arith_T9 (hn : 0 < N) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hl3 : 0 < l3) (hl3le : l3 ≤ 2)
    (hLN1 : 1 ≤ LN) (hw0 : 0 ≤ w) (hr0 : 0 ≤ r) (hw : w * N ^ 2 = 1) (hNbig : 5 * 10 ^ 5 ≤ N)
    (hC : 2 * 10 ^ 6 * LN ^ 2 ≤ N * l3 ^ 2 * ε ^ 4)
    (hrLN2 : 10 ^ 6 * (r * LN ^ 2) ≤ l3 * ε ^ 4) :
    6 * LN / (l3 * ε) * (2 * (2 * (3 * (w + 4 * r) / ε) * (1 + LN))) ≤ ε / 20 := by
  have hLN : 0 < LN := by linarith
  have h43 : ε ^ 4 ≤ ε ^ 3 := pow_le_pow_of_le_one hε0.le hε1 (by norm_num)
  have h1 : 6 * LN / (l3 * ε) * (2 * (2 * (3 * (w + 4 * r) / ε) * (1 + LN))) ≤
      6 * LN / (l3 * ε) * (2 * (2 * (3 * (w + 4 * r) / ε) * (2 * LN))) := by
    gcongr; linarith
  refine h1.trans ?_
  have e : 6 * LN / (l3 * ε) * (2 * (2 * (3 * (w + 4 * r) / ε) * (2 * LN))) =
      144 * (LN ^ 2 * w + 4 * (r * LN ^ 2)) / (l3 * ε ^ 2) := by field_simp; ring
  rw [e, div_le_iff₀ (by positivity)]
  have e2 : ε / 20 * (l3 * ε ^ 2) = l3 * ε ^ 3 / 20 := by ring
  rw [e2]
  -- `LN² w` is tiny
  have hwL : 5760 * (LN ^ 2 * w) ≤ l3 * ε ^ 3 := by
    have hN2 : 0 < N ^ 2 := by positivity
    refine le_of_mul_le_mul_right ?_ hN2
    have e3 : 5760 * (LN ^ 2 * w) * N ^ 2 = 5760 * LN ^ 2 := by
      rw [show 5760 * (LN ^ 2 * w) * N ^ 2 = 5760 * LN ^ 2 * (w * N ^ 2) by ring, hw, mul_one]
    rw [e3]
    have h4 : (N * l3 ^ 2 * ε ^ 4) * N ≤ 2 * (l3 * ε ^ 3 * N ^ 2) := by
      have : l3 ^ 2 * ε ^ 4 ≤ 2 * (l3 * ε ^ 3) := by
        have a1 : l3 ^ 2 ≤ 2 * l3 := by nlinarith
        have a2 : l3 ^ 2 * ε ^ 4 ≤ 2 * l3 * ε ^ 4 := mul_le_mul_of_nonneg_right a1 (by positivity)
        have a3 : 2 * l3 * ε ^ 4 ≤ 2 * l3 * ε ^ 3 := mul_le_mul_of_nonneg_left h43 (by positivity)
        linarith
      have := mul_le_mul_of_nonneg_left this (show 0 ≤ N * N by positivity)
      nlinarith
    have h5 : 2 * 10 ^ 6 * LN ^ 2 * N ≤ (N * l3 ^ 2 * ε ^ 4) * N :=
      mul_le_mul_of_nonneg_right hC hn.le
    have h6 : 5760 * LN ^ 2 ≤ 10 ^ 6 * LN ^ 2 * N := by nlinarith [sq_nonneg LN]
    nlinarith
  have : 0 ≤ l3 * ε ^ 3 := by positivity
  have : l3 * ε ^ 4 ≤ l3 * ε ^ 3 := mul_le_mul_of_nonneg_left h43 hl3.le
  linarith

end Arith

/-- The final arithmetic of Lemma 4.2 (`c = 10⁶`). -/
lemma lemma42_arith {N LN l2 l3 ε u : ℝ} {t₁ M : ℕ} (hn : 0 < N) (hLN1 : 1 ≤ LN)
    (hl3 : 0 < l3) (hl3le : l3 ≤ 2) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hl2 : 0 ≤ l2)
    (hcr : l2 / l3 * (10 ^ 6 * LN ^ 2) ≤ l3 * ε ^ 4) (hC : 2 * 10 ^ 6 * LN ^ 2 ≤ N * l3 ^ 2 * ε ^ 4)
    (hL1 : (t₁ : ℝ) * l2 / N ≤ 7 * (l2 / l3 * LN)) (hM : (M : ℝ) ≤ 6 * N / l3 * LN)
    (hu : u = 1 / Real.sqrt (N + 1)) :
    (8 * ((t₁ : ℝ) * l2 / N) / ε ^ 2 + u + 2 * (ε / (100 * LN)) * (1 + LN)) +
      (12 * (l2 / l3) / ε ^ 3 + u + 2 * (2 * (1 / N ^ 2 + 4 * (l2 / l3)) / ε ^ 2) * (1 + LN)) +
      1 / (ε * N) * (M * (l2 / 2 + 2 * (4 / ε ^ 2 * (25 / 4 * (6 * (l2 / l3 * LN)) +
        11 * (l2 / l3)) + u + 2 * (3 * (1 / N ^ 2 + 4 * (l2 / l3)) / ε) * (1 + LN)))) ≤ ε := by
  obtain ⟨r, hr⟩ : ∃ r, r = l2 / l3 := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w = 1 / N ^ 2 := ⟨_, rfl⟩
  rw [← hr, ← hw]
  rw [← hr] at hcr hL1
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  have hε4' : ε ^ 4 ≤ 1 := pow_le_one₀ hε0.le hε1
  have hLN2 : LN ≤ LN ^ 2 := by nlinarith
  have hrLN : 10 ^ 6 * (r * LN) ≤ 2 * ε ^ 4 := by
    have h1 : r * LN ≤ r * LN ^ 2 := mul_le_mul_of_nonneg_left hLN2 hr0
    have h2 : l3 * ε ^ 4 ≤ 2 * ε ^ 4 := mul_le_mul_of_nonneg_right hl3le (by positivity)
    linarith
  have hrLN2 : 10 ^ 6 * (r * LN ^ 2) ≤ l3 * ε ^ 4 := by linarith
  have hNε : 5 * 10 ^ 5 * LN ^ 2 ≤ N * ε ^ 4 := by
    have h1 : l3 ^ 2 ≤ 4 := by nlinarith
    have := mul_le_mul_of_nonneg_left h1 (show 0 ≤ N * ε ^ 4 by positivity)
    linarith
  have hNbig : 5 * 10 ^ 5 ≤ N := by
    have h1 : N * ε ^ 4 ≤ N := mul_le_of_le_one_right hn.le hε4'
    have h2 : (1 : ℝ) ≤ LN ^ 2 := by nlinarith
    linarith
  have hwN : w * N ^ 2 = 1 := by rw [hw]; field_simp
  have T1 := arith_T1 hε0 hε1 hL1 hrLN
  have T2 := arith_T2 hn hε0 hε1 hLN1 hNε hu
  have T3 := arith_T3 hε0 hLN1
  have T4 := arith_T4 hε0 hLN1 hr0 hrLN
  have T5 := arith_T5 hε0 hε1 hLN1 hw0 hr0 (arith_wLN hn hε0 hε1 hLN1 hNbig hNε hwN) hrLN
  have T6 := arith_T6 hε0 hε1 hl3 hr hrLN (LN := LN)
  have T7 := arith_T7 hε0 hl3 hLN1 hr0 hrLN2
  have T8 := arith_T8 hn hε0 hl3 hLN1 hC hu
  have T9 := arith_T9 hn hε0 hε1 hl3 hl3le hLN1 hw0 hr0 hwN hNbig hC hrLN2
  -- the factor `M/(ε n)`
  have hF : 1 / (ε * N) * M ≤ 6 * LN / (l3 * ε) := by
    rw [one_div_mul_eq_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_left hM (show 0 ≤ l3 * ε by positivity)
    have e : l3 * ε * (6 * N / l3 * LN) = 6 * LN * (ε * N) := by field_simp
    rw [e] at this
    linarith
  obtain ⟨X, hX⟩ : ∃ X, X = l2 / 2 + 2 * (4 / ε ^ 2 * (25 / 4 * (6 * (r * LN)) + 11 * r) + u +
      2 * (3 * (w + 4 * r) / ε) * (1 + LN)) := ⟨_, rfl⟩
  rw [← hX]
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hFX : 1 / (ε * N) * (M * X) ≤ 6 * LN / (l3 * ε) * X := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hF hX0
  have hsplit : 6 * LN / (l3 * ε) * X = 6 * LN / (l3 * ε) * (l2 / 2) +
      6 * LN / (l3 * ε) * (2 * (4 / ε ^ 2 * (25 / 4 * (6 * (r * LN)) + 11 * r))) +
      6 * LN / (l3 * ε) * (2 * u) +
      6 * LN / (l3 * ε) * (2 * (2 * (3 * (w + 4 * r) / ε) * (1 + LN))) := by rw [hX]; ring
  linarith

end Averaging.Opportunistic
