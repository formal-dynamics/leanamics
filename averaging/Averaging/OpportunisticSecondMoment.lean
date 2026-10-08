import Averaging.OpportunisticOneStep

/-! # Second moment analysis (Lemma C.4 and Theorem 4.1)

Unrolling the one-round bounds of `Averaging.OpportunisticOneStep` over `T` i.i.d. uniform rounds
from an arbitrary state `x` (with `s = n β² = ‖y‖²`, `‖z‖² = restSq`, `M = s + ‖z‖²`,
`λ₂ = 2b/d`, `q = 1 - λ₃/n`):

* `expList_cutDev_le`: `E ‖y⁽ᵀ⁾ - y‖² ≤ Yb(T)` with
  `Yb(T) = T (λ₂/n)(1 + 8/n) s + (4λ₂/(n λ₃)) ‖z‖² + 4 T λ₂² M/(n² λ₃)`;
* `expList_restSq_le`: `E ‖z⁽ᵀ⁾‖² ≤ qᵀ ‖z‖² + (λ₂/λ₃)(2 s + 2 Yb(T))`.

Together they bound `E‖y⁽ᵀ⁾ + z⁽ᵀ⁾ - y‖² = E‖y⁽ᵀ⁾ - y‖² + E‖z⁽ᵀ⁾‖²` (`sum_sq_dev_eq`), which gives
Theorem 4.1 after averaging over the initial signs (`E ‖y⁽⁰⁾‖² = 1`).
-/

namespace Averaging.Opportunistic
open Finset Matrix Dynamics

/-! ### Generic recursions -/

/-- The last draw of `t + 1` i.i.d. uniform draws, averaged first. -/
lemma expList_succ_last {α : Type*} [Fintype α] (t : ℕ) (F : List α → ℝ) :
    expList α (t + 1) F = expList α t (fun l => avg fun a => F (l ++ [a])) := by
  rw [expList_append t 1]
  rfl

/-- Unrolling `a (t + 1) ≤ q a t + c`. -/
lemma rec_le {a : ℕ → ℝ} {q c : ℝ} (hq : 0 ≤ q) (T : ℕ)
    (h : ∀ t < T, a (t + 1) ≤ q * a t + c) :
    a T ≤ q ^ T * a 0 + c * ∑ j ∈ range T, q ^ j := by
  induction T with
  | zero => simp
  | succ T ih =>
    have h0 := ih fun t ht => h t (by omega)
    have h1 := h T (by omega)
    have hS : ∑ j ∈ range (T + 1), q ^ j = q * ∑ j ∈ range T, q ^ j + 1 := by
      rw [sum_range_succ', Finset.mul_sum]; simp [pow_succ, mul_comm]
    rw [hS, pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left h0 hq]

/-- Geometric sums: `∑_{j < T} qʲ ≤ 1/(1 - q)` for `0 ≤ q < 1`. -/
lemma geom_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (T : ℕ) :
    ∑ j ∈ range T, q ^ j ≤ 1 / (1 - q) := by
  have := geom_sum_Ico_le_of_lt_one (m := 0) (n := T) hq0 hq1
  rw [pow_zero] at this
  rwa [Finset.range_eq_Ico]

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {V₁ : Finset V} {d b : ℕ} {lam3 : ℝ}

omit [Fintype V] [DecidableRel G.Adj] in
lemma avgRun_append_singleton (x : V → ℝ) (l : List G.Dart) (e : G.Dart) :
    avgRun G x (l ++ [e]) = edgeAvg G (avgRun G x l) e := by
  simp [avgRun, List.foldl_append]

omit [Fintype V] [DecidableRel G.Adj] in
lemma avgRun_append (x : V → ℝ) (l₁ l₂ : List G.Dart) :
    avgRun G x (l₁ ++ l₂) = avgRun G (avgRun G x l₁) l₂ := by
  simp [avgRun, List.foldl_append]

/-- `‖y' + z' - y‖² = n (β' - β)² + ‖z'‖²`. -/
lemma sum_sq_dev_eq (hG : IsClusteredRegular G V₁ d b) (x x' : V → ℝ) :
    ∑ v, (projCut V₁ x' v + projRest V₁ x' v - projCut V₁ x v) ^ 2 =
      Fintype.card V * (cutCoef V₁ x' - cutCoef V₁ x) ^ 2 + restSq V₁ x' := by
  have h : ∀ v, (projCut V₁ x' v + projRest V₁ x' v - projCut V₁ x v) ^ 2 =
      (cutCoef V₁ x' - cutCoef V₁ x) ^ 2 * cutVec V₁ v ^ 2 +
        2 * (cutCoef V₁ x' - cutCoef V₁ x) * (cutVec V₁ v * projRest V₁ x' v) +
        projRest V₁ x' v ^ 2 := fun v => by
    simp only [projCut_eq]; ring
  simp_rw [h, cutVec_sq]
  simp only [sum_add_distrib, ← Finset.mul_sum, hG.sum_cutVec_mul_projRest, mul_one, sum_const,
    card_univ, nsmul_eq_mul, mul_zero, add_zero, restSq]

namespace IsClusteredRegular
variable (hG : IsClusteredRegular G V₁ d b)
include hG

/-- The squared distance to the consensus never increases along a run. -/
lemma cutCoef_sq_add_restSq_avgRun_le (x : V → ℝ) (l : List G.Dart) :
    Fintype.card V * cutCoef V₁ (avgRun G x l) ^ 2 + restSq V₁ (avgRun G x l) ≤
      Fintype.card V * cutCoef V₁ x ^ 2 + restSq V₁ x := by
  induction l generalizing x with
  | nil => rfl
  | cons e l ih =>
    exact (ih (edgeAvg G x e)).trans (hG.cutCoef_sq_add_restSq_edgeAvg_le x e)

variable (h3 : ThirdEigenvalueLB G V₁ d lam3)
include h3

/-- The two recursions, in expectation. -/
lemma expList_restSq_succ_le (x : V → ℝ) (t : ℕ) :
    expList G.Dart (t + 1) (fun l => restSq V₁ (avgRun G x l)) ≤
      (1 - lam3 / Fintype.card V) * expList G.Dart t (fun l => restSq V₁ (avgRun G x l)) +
        (2 * b / d) * expList G.Dart t (fun l => cutCoef V₁ (avgRun G x l) ^ 2) := by
  rw [expList_succ_last, ← expList_const_mul, ← expList_const_mul, ← expList_add]
  refine expList_le_expList fun l => ?_
  simp_rw [avgRun_append_singleton]
  exact hG.avg_restSq_edgeAvg_le h3 _

omit h3 in
lemma expList_cutDev_succ_le (x : V → ℝ) (γ : ℝ) (t : ℕ) :
    expList G.Dart (t + 1) (fun l => Fintype.card V * (cutCoef V₁ (avgRun G x l) - γ) ^ 2) ≤
      (1 - (2 * b / d : ℝ) / Fintype.card V) *
          expList G.Dart t (fun l => Fintype.card V * (cutCoef V₁ (avgRun G x l) - γ) ^ 2) +
        (2 * b / d) * γ ^ 2 + 4 * (2 * b / d) / Fintype.card V ^ 2 *
          (Fintype.card V * expList G.Dart t (fun l => cutCoef V₁ (avgRun G x l) ^ 2) +
            expList G.Dart t (fun l => restSq V₁ (avgRun G x l))) := by
  haveI := hG.nonempty_dart
  rw [expList_succ_last]
  calc _ ≤ expList G.Dart t (fun l => (1 - (2 * b / d : ℝ) / Fintype.card V) *
          (Fintype.card V * (cutCoef V₁ (avgRun G x l) - γ) ^ 2) + (2 * b / d) * γ ^ 2 +
        4 * (2 * b / d) / Fintype.card V ^ 2 *
          (Fintype.card V * cutCoef V₁ (avgRun G x l) ^ 2 + restSq V₁ (avgRun G x l))) :=
        expList_le_expList fun l => by
          simp_rw [avgRun_append_singleton]; exact hG.avg_cutDev_edgeAvg_le _ γ
    _ = _ := by simp only [expList_add, expList_const_mul, expList_const]

end IsClusteredRegular

/-- The bound `Yb(T)` on `E ‖y⁽ᵀ⁾ - y‖²` (proof of Lemma C.4 and of Theorem 4.1). -/
noncomputable def cutDevBound (N l2 l3 s z : ℝ) (T : ℕ) : ℝ :=
  T * (l2 / N) * (1 + 8 / N) * s + 4 * l2 / (N * l3) * z + 4 * T * l2 ^ 2 * (s + z) / (N ^ 2 * l3)

lemma cutDevBound_mono {N l2 l3 s z : ℝ} (hN : 0 < N) (hl2 : 0 ≤ l2) (hl3 : 0 < l3) (hs : 0 ≤ s)
    (hz : 0 ≤ z) {t T : ℕ} (htT : t ≤ T) : cutDevBound N l2 l3 s z t ≤ cutDevBound N l2 l3 s z T := by
  unfold cutDevBound
  have ht : (t : ℝ) ≤ T := by exact_mod_cast htT
  have h1 : 0 ≤ (l2 / N) * (1 + 8 / N) * s := by positivity
  have h2 : 0 ≤ 4 * l2 ^ 2 * (s + z) / (N ^ 2 * l3) := by positivity
  have e1 : 4 * (t : ℝ) * l2 ^ 2 * (s + z) / (N ^ 2 * l3) = t * (4 * l2 ^ 2 * (s + z) / (N ^ 2 * l3)) := by ring
  have e2 : 4 * (T : ℝ) * l2 ^ 2 * (s + z) / (N ^ 2 * l3) = T * (4 * l2 ^ 2 * (s + z) / (N ^ 2 * l3)) := by ring
  rw [e1, e2, mul_assoc (t : ℝ), mul_assoc (T : ℝ), mul_assoc (t : ℝ), mul_assoc (T : ℝ)]
  have := mul_le_mul_of_nonneg_right ht h1
  have := mul_le_mul_of_nonneg_right ht h2
  nlinarith

namespace IsClusteredRegular
variable (hG : IsClusteredRegular G V₁ d b) (h3 : ThirdEigenvalueLB G V₁ d lam3)
include hG h3

/-- **Second moment bounds from an arbitrary state** (Lemmas C.2 to C.4 unrolled): with
`s = n β²`, `z = ‖z‖²` the components of the start `x`,
`E ‖y⁽ᵀ⁾ - y‖² ≤ Yb(T)` and `E ‖z⁽ᵀ⁾‖² ≤ (1 - λ₃/n)ᵀ z + (λ₂/λ₃)(2 s + 2 Yb(T))`. -/
theorem expList_secondMoment_le (hl3 : 0 < lam3) (hN : (8 : ℝ) ≤ Fintype.card V)
    (x : V → ℝ) (T : ℕ) :
    expList G.Dart T (fun l => Fintype.card V * (cutCoef V₁ (avgRun G x l) - cutCoef V₁ x) ^ 2) ≤
        cutDevBound (Fintype.card V) (2 * b / d) lam3 (Fintype.card V * cutCoef V₁ x ^ 2)
          (restSq V₁ x) T ∧
      expList G.Dart T (fun l => restSq V₁ (avgRun G x l)) ≤
        (1 - lam3 / Fintype.card V) ^ T * restSq V₁ x + (2 * b / d) / lam3 *
          (2 * (Fintype.card V * cutCoef V₁ x ^ 2) + 2 * cutDevBound (Fintype.card V) (2 * b / d)
            lam3 (Fintype.card V * cutCoef V₁ x ^ 2) (restSq V₁ x) T) := by
  haveI := hG.nonempty_dart
  have hNpos : (0 : ℝ) < Fintype.card V := hG.card_real_pos
  have hl3le := hG.lam3_le_two h3
  set N : ℝ := (Fintype.card V : ℝ) with hN_def
  set l2 : ℝ := 2 * b / d with hl2_def
  have hl2 : 0 ≤ l2 := by positivity
  set γ := cutCoef V₁ x
  set s := N * γ ^ 2 with hs_def
  set z0 := restSq V₁ x
  have hs : 0 ≤ s := by positivity
  have hz0 : 0 ≤ z0 := restSq_nonneg x
  set q := 1 - lam3 / N with hq_def
  have hq0 : 0 ≤ q := by
    rw [hq_def, sub_nonneg, div_le_one hNpos]; linarith
  have hq1 : q < 1 := by rw [hq_def]; have : 0 < lam3 / N := div_pos hl3 hNpos; linarith
  have hgeom : ∀ t, ∑ j ∈ range t, q ^ j ≤ N / lam3 := fun t => by
    have := geom_le hq0 hq1 t
    rwa [hq_def, sub_sub_cancel, one_div_div] at this
  set Ys : ℕ → ℝ := fun t =>
    expList G.Dart t (fun l => N * (cutCoef V₁ (avgRun G x l) - γ) ^ 2) with hYs
  set Zs : ℕ → ℝ := fun t => expList G.Dart t (fun l => restSq V₁ (avgRun G x l)) with hZs
  set Bs : ℕ → ℝ := fun t => expList G.Dart t (fun l => cutCoef V₁ (avgRun G x l) ^ 2) with hBs
  have hY0 : ∀ t, 0 ≤ Ys t := fun t => expList_nonneg fun l => by positivity
  have hZ0 : ∀ t, 0 ≤ Zs t := fun t => expList_nonneg fun l => restSq_nonneg _
  have hYzero : Ys 0 = 0 := by
    simp only [hYs, expList_zero, avgRun, List.foldl_nil, γ, sub_self]; ring
  have hZzero : Zs 0 = z0 := by simp only [hZs, expList_zero, avgRun, List.foldl_nil, z0]
  -- deterministic bound `N β² ≤ M`
  have hBM : ∀ t, N * Bs t ≤ s + z0 := fun t => by
    have : expList G.Dart t (fun l => N * cutCoef V₁ (avgRun G x l) ^ 2) ≤
        expList G.Dart t (fun _ => s + z0) := expList_le_expList fun l => by
      have := hG.cutCoef_sq_add_restSq_avgRun_le x l
      have := restSq_nonneg (V₁ := V₁) (avgRun G x l)
      linarith
    rwa [expList_const, expList_const_mul] at this
  have hBY : ∀ t, N * Bs t ≤ 2 * s + 2 * Ys t := fun t => by
    have : expList G.Dart t (fun l => N * cutCoef V₁ (avgRun G x l) ^ 2) ≤
        expList G.Dart t (fun l => 2 * s + 2 * (N * (cutCoef V₁ (avgRun G x l) - γ) ^ 2)) :=
      expList_le_expList fun l => by
        rw [hs_def]; nlinarith [sq_nonneg (cutCoef V₁ (avgRun G x l) - 2 * γ), hNpos]
    rwa [expList_add, expList_const, expList_const_mul, expList_const_mul] at this
  have hZrec : ∀ t, Zs (t + 1) ≤ q * Zs t + l2 * Bs t := fun t =>
    hG.expList_restSq_succ_le h3 x t
  have hYrec : ∀ t, Ys (t + 1) ≤ Ys t + (l2 / N) * (1 + 8 / N) * s + 4 * l2 / N ^ 2 * Zs t := by
    intro t
    have h := hG.expList_cutDev_succ_le x γ t
    have hb := hBY t
    have hYt := hY0 t
    have hk : 0 ≤ 4 * l2 / N ^ 2 := by positivity
    have h1 : 4 * l2 / N ^ 2 * (N * Bs t + Zs t) ≤ 4 * l2 / N ^ 2 * (2 * s + 2 * Ys t + Zs t) :=
      mul_le_mul_of_nonneg_left (by linarith) hk
    have h2 : 8 * l2 / N ^ 2 * Ys t ≤ l2 / N * Ys t := by
      apply mul_le_mul_of_nonneg_right _ hYt
      rw [div_le_div_iff₀ (by positivity) hNpos]
      nlinarith [mul_le_mul_of_nonneg_left hN (mul_nonneg hl2 hNpos.le)]
    have e : l2 * γ ^ 2 = l2 / N * s := by rw [hs_def]; field_simp
    have e2 : (1 - l2 / N) * Ys t = Ys t - l2 / N * Ys t := by ring
    have e3 : 4 * l2 / N ^ 2 * (2 * s + 2 * Ys t + Zs t) =
        8 * l2 / N ^ 2 * Ys t + l2 / N * (8 / N) * s + 4 * l2 / N ^ 2 * Zs t := by
      field_simp; ring
    change Ys (t + 1) ≤ (1 - l2 / N) * Ys t + l2 * γ ^ 2 + 4 * l2 / N ^ 2 * (N * Bs t + Zs t) at h
    have e4 : l2 / N * (1 + 8 / N) * s = l2 / N * s + l2 / N * (8 / N) * s := by ring
    rw [e4]
    linarith
  -- crude bound on `Zs`
  have hZcrude : ∀ t, Zs t ≤ q ^ t * z0 + l2 * (s + z0) / lam3 := fun t => by
    have h := rec_le (a := Zs) (c := l2 * (s + z0) / N) hq0 t fun j _ => by
      have := hZrec j
      have hb := hBM j
      have : l2 * Bs j ≤ l2 * (s + z0) / N := by
        rw [le_div_iff₀ hNpos]; nlinarith
      linarith
    rw [hZzero] at h
    have hc : 0 ≤ l2 * (s + z0) / N := by positivity
    have := mul_le_mul_of_nonneg_left (hgeom t) hc
    have e : l2 * (s + z0) / N * (N / lam3) = l2 * (s + z0) / lam3 := by field_simp
    linarith
  have hZsum : ∀ T, ∑ j ∈ range T, Zs j ≤ N / lam3 * z0 + T * (l2 * (s + z0) / lam3) := by
    intro T
    calc ∑ j ∈ range T, Zs j ≤ ∑ j ∈ range T, (q ^ j * z0 + l2 * (s + z0) / lam3) :=
          sum_le_sum fun j _ => hZcrude j
      _ = (∑ j ∈ range T, q ^ j) * z0 + T * (l2 * (s + z0) / lam3) := by
          rw [sum_add_distrib, ← sum_mul]; simp
      _ ≤ N / lam3 * z0 + T * (l2 * (s + z0) / lam3) := by
          gcongr; exact hgeom T
  -- bound on `Ys`
  have hYbound : ∀ T, Ys T ≤ cutDevBound N l2 lam3 s z0 T := by
    intro T
    have hsum : Ys T ≤ T * ((l2 / N) * (1 + 8 / N) * s) + 4 * l2 / N ^ 2 * ∑ j ∈ range T, Zs j := by
      induction T with
      | zero => simp [hYzero]
      | succ T ih =>
        rw [sum_range_succ, mul_add]
        have := hYrec T
        push_cast
        linarith
    have hk : 0 ≤ 4 * l2 / N ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left (hZsum T) hk
    unfold cutDevBound
    have e : 4 * l2 / N ^ 2 * (N / lam3 * z0 + T * (l2 * (s + z0) / lam3)) =
        4 * l2 / (N * lam3) * z0 + 4 * T * l2 ^ 2 * (s + z0) / (N ^ 2 * lam3) := by
      field_simp
    linarith
  refine ⟨hYbound T, ?_⟩
  -- refined bound on `Zs`
  have hc : 0 ≤ l2 / N * (2 * s + 2 * cutDevBound N l2 lam3 s z0 T) := by
    have : 0 ≤ cutDevBound N l2 lam3 s z0 T := (hY0 T).trans (hYbound T)
    positivity
  have h := rec_le (a := Zs) (c := l2 / N * (2 * s + 2 * cutDevBound N l2 lam3 s z0 T)) hq0 T
    fun j hj => by
      have h1 := hZrec j
      have h2 := hBY j
      have h3' := (hYbound j).trans (cutDevBound_mono hNpos hl2 hl3 hs hz0 hj.le)
      have : l2 * Bs j ≤ l2 / N * (2 * s + 2 * cutDevBound N l2 lam3 s z0 T) := by
        have : N * Bs j ≤ 2 * s + 2 * cutDevBound N l2 lam3 s z0 T := by linarith
        have hBj : Bs j ≤ (2 * s + 2 * cutDevBound N l2 lam3 s z0 T) / N := by
          rw [le_div_iff₀ hNpos]; linarith
        calc l2 * Bs j ≤ l2 * ((2 * s + 2 * cutDevBound N l2 lam3 s z0 T) / N) :=
              mul_le_mul_of_nonneg_left hBj hl2
          _ = _ := by ring
      linarith
  rw [hZzero] at h
  have := mul_le_mul_of_nonneg_left (hgeom T) hc
  have e : l2 / N * (2 * s + 2 * cutDevBound N l2 lam3 s z0 T) * (N / lam3) =
      l2 / lam3 * (2 * s + 2 * cutDevBound N l2 lam3 s z0 T) := by field_simp
  change Zs T ≤ q ^ T * z0 + l2 / lam3 * (2 * s + 2 * cutDevBound N l2 lam3 s z0 T)
  linarith

end IsClusteredRegular

end Averaging.Opportunistic
