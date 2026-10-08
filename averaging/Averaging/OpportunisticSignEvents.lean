import Averaging.OpportunisticNonEphemeral

/-! # The initial community averages (Lemma A.1 and the sign events)

With uniform initial signs `σ`, let `S₁ = ∑_{v ∈ V₁} σ_v` and `S₂ = ∑_{v ∉ V₁} σ_v`, two independent
sums of `n/2` signs. The initial average of community `h` is `μ_h = 2 S_h/n = x_∥ + y⁽⁰⁾` on that
community (`projOne_add_projCut_signVec`), and `‖y⁽⁰⁾‖² = (S₁ - S₂)²/n`.

* `avg_abs_blockSum_le_mul`: `P(|S₁| ≤ ε |S₂|) ≤ ε + 1/√(n/2 + 1)` (independence and the central
  binomial bound); likewise with the roles of the communities exchanged.
* `avg_blockSum_mul_neg`: `P(S₁ S₂ < 0) ≥ 1/2 - 1/√(n/2 + 1)`.
-/

namespace Averaging.Opportunistic
open Finset Dynamics

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The sum of the initial signs on a set of nodes. -/
noncomputable def blockSum (U : Finset V) (σ : V → ℤˣ) : ℝ := ∑ v ∈ U, signVec σ v

variable {G : SimpleGraph V} [DecidableRel G.Adj] {V₁ : Finset V} {d b : ℕ}

omit [Fintype V] [DecidableEq V] in
lemma sum_subtype_eq (U : Finset V) [Fintype {v // v ∈ U}] (σ : V → ℤˣ) :
    ∑ i : {v // v ∈ U}, signVec (fun i : {v // v ∈ U} => σ i) i = blockSum U σ := by
  rw [blockSum]
  exact (Finset.sum_subtype U (fun _ => Iff.rfl) (signVec σ)).symm

lemma sum_subtype_compl_eq (U : Finset V) [Fintype {v // ¬ v ∈ U}] (σ : V → ℤˣ) :
    ∑ i : {v // ¬ v ∈ U}, signVec (fun i : {v // ¬ v ∈ U} => σ i) i = blockSum Uᶜ σ := by
  rw [blockSum]
  exact (Finset.sum_subtype Uᶜ (fun _ => Finset.mem_compl) (signVec σ)).symm

/-- Independence of the two blocks of signs, through their sums. -/
lemma avg_split_block (U : Finset V) (F : ℝ → ℝ → ℝ) :
    avg (fun σ : V → ℤˣ => F (blockSum U σ) (blockSum Uᶜ σ)) =
      avg (fun τ₁ : {v // v ∈ U} → ℤˣ => avg (fun τ₂ : {v // ¬ v ∈ U} → ℤˣ =>
        F (∑ i, signVec τ₁ i) (∑ j, signVec τ₂ j))) := by
  have h := avg_split (I := V) (fun v => v ∈ U)
    (fun τ₁ τ₂ => F (∑ i, signVec τ₁ i) (∑ j, signVec τ₂ j))
  convert h using 3 with σ
  rw [sum_subtype_eq, sum_subtype_compl_eq]

namespace IsClusteredRegular
variable (hG : IsClusteredRegular G V₁ d b)
include hG

lemma card_subtype : (Fintype.card {v // v ∈ V₁} : ℝ) = Fintype.card V / 2 := by
  rw [Fintype.card_coe]
  have := hG.card_eq
  have : (2 * #V₁ : ℝ) = Fintype.card V := by exact_mod_cast this
  linarith

lemma card_subtype_compl : (Fintype.card {v // ¬ v ∈ V₁} : ℝ) = Fintype.card V / 2 := by
  have h1 := Fintype.card_subtype_compl (p := fun v => v ∈ V₁)
  have h2 : Fintype.card {v // v ∈ V₁} ≤ Fintype.card V := Fintype.card_subtype_le _
  have h3 : (Fintype.card {v // ¬ v ∈ V₁} : ℝ) =
      Fintype.card V - Fintype.card {v // v ∈ V₁} := by
    rw [h1, Nat.cast_sub h2]
  rw [h3, hG.card_subtype]; ring

omit hG in
lemma sum_signVec_split (V₁ : Finset V) (σ : V → ℤˣ) :
    ∑ v, signVec σ v = blockSum V₁ σ + blockSum V₁ᶜ σ := by
  rw [blockSum, blockSum, Finset.sum_add_sum_compl]

omit hG in
lemma sum_cutVec_mul_split (σ : V → ℤˣ) :
    ∑ v, cutVec V₁ v * signVec σ v = blockSum V₁ σ - blockSum V₁ᶜ σ := by
  rw [← Finset.sum_add_sum_compl V₁, blockSum, blockSum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · exact Finset.sum_congr rfl fun v hv => by simp [cutVec, hv]
  · exact Finset.sum_congr rfl fun v hv => by
      simp only [Finset.mem_compl] at hv; simp [cutVec, hv]

/-- `x_∥ + y⁽⁰⁾ = 2 S_h/n` on community `h`. -/
lemma projOne_add_projCut_signVec (σ : V → ℤˣ) (v : V) :
    projOne (signVec σ) v + projCut V₁ (signVec σ) v =
      if v ∈ V₁ then 2 * blockSum V₁ σ / Fintype.card V
      else 2 * blockSum V₁ᶜ σ / Fintype.card V := by
  have hn := hG.card_real_pos
  simp only [projOne, projCut, avg, sum_cutVec_mul_split]
  rw [sum_signVec_split V₁ σ]
  split_ifs with hv
  · simp only [cutVec, hv, if_true]; field_simp; ring
  · simp only [cutVec, hv, if_false]; field_simp; ring

/-- `‖y⁽⁰⁾‖² = (S₁ - S₂)²/n`. -/
lemma sum_sq_projCut_signVec (σ : V → ℤˣ) :
    ∑ w, projCut V₁ (signVec σ) w ^ 2 = (blockSum V₁ σ - blockSum V₁ᶜ σ) ^ 2 /
      Fintype.card V := by
  rw [IsClusteredRegular.sum_sq_projCut, hG.card_mul_cutCoef_sq, sum_cutVec_mul_split]

/-- **Lemma A.1, small initial average**: `P(|S₁| ≤ ε |S₂|) ≤ ε + 1/√(n/2 + 1)`. -/
theorem avg_abs_blockSum_le_mul {ε : ℝ} (hε : 0 ≤ ε) :
    avg (fun σ : V → ℤˣ => if |blockSum V₁ σ| ≤ ε * |blockSum V₁ᶜ σ| then (1 : ℝ) else 0) ≤
      ε + 1 / Real.sqrt (Fintype.card V / 2 + 1) := by
  have hsplit := avg_split_block V₁ (fun x y => if |x| ≤ ε * |y| then (1 : ℝ) else 0)
  rw [hsplit, avg_avg_swap]
  have hm : 0 < Real.sqrt (Fintype.card V / 2 + 1) := Real.sqrt_pos.mpr (by positivity)
  have hinner : ∀ τ₂ : {v // ¬ v ∈ V₁} → ℤˣ,
      avg (fun τ₁ : {v // v ∈ V₁} → ℤˣ =>
        if |∑ i, signVec τ₁ i| ≤ ε * |∑ j, signVec τ₂ j| then (1 : ℝ) else 0) ≤
      (ε * |∑ j, signVec τ₂ j| + 1) / Real.sqrt (Fintype.card V / 2 + 1) := fun τ₂ => by
    have := avg_abs_sum_signVec_le (I := {v // v ∈ V₁}) (ε * |∑ j, signVec τ₂ j|)
      (by positivity)
    rwa [hG.card_subtype] at this
  refine (avg_le_avg hinner).trans ?_
  set D := Real.sqrt (Fintype.card V / 2 + 1)
  have e : (fun τ₂ : {v // ¬ v ∈ V₁} → ℤˣ => (ε * |∑ j, signVec τ₂ j| + 1) / D) =
      fun τ₂ => ε / D * |∑ j, signVec τ₂ j| + 1 / D := funext fun τ₂ => by ring
  rw [e, avg_add, avg_const_mul, avg_const]
  have hE := avg_abs_sum_signVec_le_sqrt (I := {v // ¬ v ∈ V₁})
  rw [hG.card_subtype_compl] at hE
  have hsq : Real.sqrt (Fintype.card V / 2) ≤ D := Real.sqrt_le_sqrt (by linarith)
  have h1 : ε / D * avg (fun τ₂ : {v // ¬ v ∈ V₁} → ℤˣ => |∑ j, signVec τ₂ j|) ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hm]
    exact mul_le_mul_of_nonneg_left (hE.trans hsq) hε
  linarith

/-- The same with the communities exchanged: `P(|S₂| ≤ ε |S₁|) ≤ ε + 1/√(n/2 + 1)`. -/
theorem avg_abs_blockSum_compl_le_mul {ε : ℝ} (hε : 0 ≤ ε) :
    avg (fun σ : V → ℤˣ => if |blockSum V₁ᶜ σ| ≤ ε * |blockSum V₁ σ| then (1 : ℝ) else 0) ≤
      ε + 1 / Real.sqrt (Fintype.card V / 2 + 1) := by
  have hsplit := avg_split_block V₁ (fun x y => if |y| ≤ ε * |x| then (1 : ℝ) else 0)
  rw [hsplit]
  have hm : 0 < Real.sqrt (Fintype.card V / 2 + 1) := Real.sqrt_pos.mpr (by positivity)
  have hinner : ∀ τ₁ : {v // v ∈ V₁} → ℤˣ,
      avg (fun τ₂ : {v // ¬ v ∈ V₁} → ℤˣ =>
        if |∑ j, signVec τ₂ j| ≤ ε * |∑ i, signVec τ₁ i| then (1 : ℝ) else 0) ≤
      (ε * |∑ i, signVec τ₁ i| + 1) / Real.sqrt (Fintype.card V / 2 + 1) := fun τ₁ => by
    have := avg_abs_sum_signVec_le (I := {v // ¬ v ∈ V₁}) (ε * |∑ i, signVec τ₁ i|)
      (by positivity)
    rwa [hG.card_subtype_compl] at this
  refine (avg_le_avg hinner).trans ?_
  set D := Real.sqrt (Fintype.card V / 2 + 1)
  have e : (fun τ₁ : {v // v ∈ V₁} → ℤˣ => (ε * |∑ i, signVec τ₁ i| + 1) / D) =
      fun τ₁ => ε / D * |∑ i, signVec τ₁ i| + 1 / D := funext fun τ₁ => by ring
  rw [e, avg_add, avg_const_mul, avg_const]
  have hE := avg_abs_sum_signVec_le_sqrt (I := {v // v ∈ V₁})
  rw [hG.card_subtype] at hE
  have hsq : Real.sqrt (Fintype.card V / 2) ≤ D := Real.sqrt_le_sqrt (by linarith)
  have h1 : ε / D * avg (fun τ₁ : {v // v ∈ V₁} → ℤˣ => |∑ i, signVec τ₁ i|) ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hm]
    exact mul_le_mul_of_nonneg_left (hE.trans hsq) hε
  linarith

/-- **Opposite community averages**: `P(S₁ S₂ < 0) ≥ 1/2 - 1/√(n/2 + 1)`. -/
theorem avg_blockSum_mul_neg :
    1 / 2 - 1 / Real.sqrt (Fintype.card V / 2 + 1) ≤
      avg (fun σ : V → ℤˣ => if blockSum V₁ σ * blockSum V₁ᶜ σ < 0 then (1 : ℝ) else 0) := by
  have hpt : ∀ x y : ℝ, (if x * y < 0 then (1 : ℝ) else 0) =
      (if 0 < x then 1 else 0) * (if y < 0 then 1 else 0) +
        (if x < 0 then 1 else 0) * (if 0 < y then 1 else 0) := fun x y => by
    rcases lt_trichotomy x 0 with hx | hx | hx <;> rcases lt_trichotomy y 0 with hy | hy | hy
    · simp [hx, hy, not_lt.mpr hx.le, not_lt.mpr hy.le, (mul_pos_of_neg_of_neg hx hy).not_gt]
    · simp [hx, hy]
    · simp [hx, hy, not_lt.mpr hx.le, mul_neg_of_neg_of_pos hx hy, not_lt.mpr hy.le]
    · simp [hx, hy]
    · simp [hx, hy]
    · simp [hx, hy]
    · simp [hx, hy, mul_neg_of_pos_of_neg hx hy, not_lt.mpr hx.le, not_lt.mpr hy.le]
    · simp [hx, hy]
    · simp [hx, hy, (mul_pos hx hy).not_gt, not_lt.mpr hx.le, not_lt.mpr hy.le]
  have hsplit := avg_split_block V₁ (fun x y => if x * y < 0 then (1 : ℝ) else 0)
  rw [hsplit]
  simp_rw [hpt]
  -- the averages of the four sign indicators
  set p₁ := avg (fun τ₁ : {v // v ∈ V₁} → ℤˣ => if ∑ i, signVec τ₁ i = 0 then (1 : ℝ) else 0)
  set p₂ := avg (fun τ₂ : {v // ¬ v ∈ V₁} → ℤˣ => if ∑ j, signVec τ₂ j = 0 then (1 : ℝ) else 0)
  have hpos₁ := avg_sum_signVec_pos (I := {v // v ∈ V₁})
  have hpos₂ := avg_sum_signVec_pos (I := {v // ¬ v ∈ V₁})
  have hneg₁ : avg (fun τ₁ : {v // v ∈ V₁} → ℤˣ => if ∑ i, signVec τ₁ i < 0 then (1 : ℝ) else 0) =
      (1 - p₁) / 2 := by
    rw [← hpos₁]
    have := avg_fun_neg_sum_signVec (I := {v // v ∈ V₁}) (fun x => if 0 < x then (1 : ℝ) else 0)
    simp only [Left.neg_pos_iff] at this
    exact this
  have hneg₂ : avg (fun τ₂ : {v // ¬ v ∈ V₁} → ℤˣ => if ∑ j, signVec τ₂ j < 0 then (1 : ℝ) else 0) =
      (1 - p₂) / 2 := by
    rw [← hpos₂]
    have := avg_fun_neg_sum_signVec (I := {v // ¬ v ∈ V₁}) (fun x => if 0 < x then (1 : ℝ) else 0)
    simp only [Left.neg_pos_iff] at this
    exact this
  have hinner : ∀ τ₁ : {v // v ∈ V₁} → ℤˣ, avg (fun τ₂ : {v // ¬ v ∈ V₁} → ℤˣ =>
      (if 0 < ∑ i, signVec τ₁ i then (1 : ℝ) else 0) * (if ∑ j, signVec τ₂ j < 0 then 1 else 0) +
        (if ∑ i, signVec τ₁ i < 0 then 1 else 0) * (if 0 < ∑ j, signVec τ₂ j then 1 else 0)) =
      (if 0 < ∑ i, signVec τ₁ i then (1 : ℝ) else 0) * ((1 - p₂) / 2) +
        (if ∑ i, signVec τ₁ i < 0 then 1 else 0) * ((1 - p₂) / 2) := fun τ₁ => by
    rw [avg_add, avg_const_mul, avg_const_mul, hneg₂, hpos₂]
  simp_rw [hinner]
  have e : (fun τ₁ : {v // v ∈ V₁} → ℤˣ => (if 0 < ∑ i, signVec τ₁ i then (1 : ℝ) else 0) *
      ((1 - p₂) / 2) + (if ∑ i, signVec τ₁ i < 0 then 1 else 0) * ((1 - p₂) / 2)) =
      fun τ₁ => (1 - p₂) / 2 * (if 0 < ∑ i, signVec τ₁ i then (1 : ℝ) else 0) +
        (1 - p₂) / 2 * (if ∑ i, signVec τ₁ i < 0 then 1 else 0) := funext fun τ₁ => by ring
  rw [e, avg_add, avg_const_mul, avg_const_mul, hpos₁, hneg₁]
  have hp₁ := avg_sum_signVec_eq_zero (I := {v // v ∈ V₁})
  have hp₂ := avg_sum_signVec_eq_zero (I := {v // ¬ v ∈ V₁})
  rw [hG.card_subtype] at hp₁
  rw [hG.card_subtype_compl] at hp₂
  have hp₁0 : 0 ≤ p₁ := avg_nonneg fun _ => by split_ifs <;> norm_num
  have hp₂0 : 0 ≤ p₂ := avg_nonneg fun _ => by split_ifs <;> norm_num
  have hp₁1 : p₁ ≤ 1 := by
    have := avg_le_avg (f := fun τ₁ : {v // v ∈ V₁} → ℤˣ => if ∑ i, signVec τ₁ i = 0 then
      (1 : ℝ) else 0) (g := fun _ => 1) fun _ => by split_ifs <;> norm_num
    rwa [avg_const] at this
  nlinarith

end IsClusteredRegular

end Averaging.Opportunistic
