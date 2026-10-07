import Voter.ConductanceBasic
import Voter.ConductanceIndep

/-! # Ingredients of the potential drop (proof of Lemma 2.1 of BGKM16)

Berenbrink, Giakkoupis, Kermarrec, Mallmann-Trenn, *Bounds on the voter model in dynamic
networks*, ICALP 2016 (BGKM16). Fix a two-opinion configuration `s`, an opinion `b` and its class
`S = {u | s u = b}` of volume `P`. In one round of the lazy voter with neighbour choices `r`, the
new volume of opinion `b` is `P + ∑ u, X_u (r u)` with `X_u a = d_u (1[s a = b] - 1[s u = b])`
(`vol_class_step`). The proof of Lemma 2.1 replaces `X_u` for `u ∉ S` by
`Y_u a = λ_u 1[a ≠ u]`, which has the same mean and is less spread, so that `𝔼√(P + ·)` can only
grow (`expect_sqrt_le_comp`, BGKM16 Lemma A.1). The comparison variables `Y_u = compVar` are
two-point variables `compVal u · 1[compEvent]`, whose centred moments are computed exactly:
the sum has mean zero, second moment at least `∑_{u ∈ S} λ_u d_u / 4`
(`expect_compSum_sq_ge`) and nonpositive third moment (`expect_compSum_cube_le`).
-/

namespace Voter
open Dynamics Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The value of the comparison variable `Y_u` of BGKM16: `-d_u` on the class `S` of `b`
(where `Y_u = X_u`), `λ_u` outside it. -/
noncomputable def compVal (s : Config V Bool) (b : Bool) (u : V) : ℝ :=
  if s u = b then -(G.degree u : ℝ) else discordant G s u

/-- The comparison variable `Y_u a` of BGKM16: `-d_u 1[s a ≠ b]` for `u ∈ S`, and
`λ_u 1[a ≠ u]` for `u ∉ S`. -/
noncomputable def compVar (s : Config V Bool) (b : Bool) (u a : V) : ℝ :=
  if (s u = b ∧ s a ≠ b) ∨ (s u ≠ b ∧ a ≠ u) then compVal G s b u else 0

/-- The change `X_u a = d_u (1[s a = b] - 1[s u = b])` of the volume of opinion `b` when `u`
adopts the opinion of `a`. -/
noncomputable def volChange (s : Config V Bool) (b : Bool) (u a : V) : ℝ :=
  G.degree u * ((if s a = b then 1 else 0) - (if s u = b then 1 else 0))

/-- The lower bound `-d_u 1[s u = b]` of both `X_u` and `Y_u`. -/
noncomputable def compLow (s : Config V Bool) (b : Bool) (u : V) : ℝ :=
  if s u = b then -(G.degree u : ℝ) else 0

/-! ### From the potential to the volume of one opinion -/

omit [DecidableEq V] in
/-- The potential is at most the square root of the volume of either opinion. -/
lemma potential_le_sqrt_class (t : Config V Bool) (b : Bool) :
    potential G t ≤ Real.sqrt (vol G (univ.filter fun u => t u = b)) :=
  Real.sqrt_le_sqrt (by exact_mod_cast vol_minority_le G t b)

omit [DecidableEq V] in
/-- The volume of a colour class as a sum of indicators. -/
lemma vol_class_eq_sum (t : Config V Bool) (b : Bool) :
    (vol G (univ.filter fun u => t u = b) : ℝ) =
      ∑ u, (G.degree u : ℝ) * (if t u = b then 1 else 0) := by
  unfold vol
  push_cast
  rw [sum_filter]
  exact sum_congr rfl fun u _ => by split_ifs <;> simp

omit [DecidableEq V] in
/-- **The volume after one round** of the voter with choices `r`:
`vol{u | s (r u) = b} = vol{u | s u = b} + ∑ u, X_u (r u)`. -/
lemma vol_class_step (s : Config V Bool) (b : Bool) (r : V → V) :
    (vol G (univ.filter fun u => step s r u = b) : ℝ) =
      vol G (univ.filter fun u => s u = b) + ∑ u, volChange G s b u (r u) := by
  rw [vol_class_eq_sum, vol_class_eq_sum, ← sum_add_distrib]
  refine sum_congr rfl fun u _ => ?_
  simp only [volChange, step]
  split_ifs <;> ring

/-! ### Lower bounds and the replacement -/

omit [DecidableEq V] in
/-- The lower bounds add up to minus the volume of the class of `b`. -/
lemma sum_compLow (s : Config V Bool) (b : Bool) :
    ∑ u, compLow G s b u = -(vol G (univ.filter fun u => s u = b) : ℝ) := by
  rw [vol_class_eq_sum, ← sum_neg_distrib]
  refine sum_congr rfl fun u _ => ?_
  simp only [compLow]
  split_ifs <;> simp

omit [DecidableEq V] in
lemma compLow_le_volChange (s : Config V Bool) (b : Bool) (u a : V) :
    compLow G s b u ≤ volChange G s b u a := by
  have hd : (0 : ℝ) ≤ G.degree u := Nat.cast_nonneg _
  simp only [compLow, volChange]
  split_ifs <;> nlinarith

lemma compLow_le_compVar (s : Config V Bool) (b : Bool) (u a : V) :
    compLow G s b u ≤ compVar G s b u a := by
  have hd : (0 : ℝ) ≤ G.degree u := Nat.cast_nonneg _
  have hl : (0 : ℝ) ≤ discordant G s u := Nat.cast_nonneg _
  simp only [compLow, compVar, compVal]
  split_ifs <;> simp_all

/-- On the class of `b` the comparison variable is the volume change itself. -/
lemma volChange_eq_compVar (s : Config V Bool) (b : Bool) (u : V) (hu : s u = b) :
    volChange G s b u = compVar G s b u := by
  funext a
  simp only [volChange, compVar, compVal, hu]
  by_cases ha : s a = b <;> simp [ha]

/-- **The one-coordinate replacement** for `u ∉ S` (BGKM16, Lemma A.1): for `z ≥ 0`,
`𝔼√(z + X_u) ≤ 𝔼√(z + Y_u)`, i.e.
`q √(z + d) + (1 - q) √z ≤ ½ √(z + λ) + ½ √z` with `q = λ / (2d)`. -/
lemma expect_sqrt_volChange_le (hd : ∀ v, 0 < G.degree v) (s : Config V Bool) (b : Bool)
    (u : V) (hu : s u ≠ b) {z : ℝ} (hz : 0 ≤ z) :
    (lazyNeighbor G hd u).expect (fun a => Real.sqrt (z + volChange G s b u a)) ≤
      (lazyNeighbor G hd u).expect (fun a => Real.sqrt (z + compVar G s b u a)) := by
  have hd0 : (0 : ℝ) < G.degree u := by exact_mod_cast hd u
  have hl0 : (0 : ℝ) ≤ discordant G s u := Nat.cast_nonneg _
  have hld : (discordant G s u : ℝ) ≤ G.degree u := by
    exact_mod_cast discordant_le_degree G s u
  have hX : (fun a => Real.sqrt (z + volChange G s b u a)) =
      fun a => if s a ≠ s u then Real.sqrt (z + G.degree u) else Real.sqrt (z + 0) := by
    funext a
    simp only [volChange, hu, if_false, sub_zero]
    have : (s a = b) ↔ (s a ≠ s u) := by
      revert hu
      cases s a <;> cases s u <;> cases b <;> simp
    by_cases ha : s a = b
    · rw [if_pos ha, if_pos (this.mp ha), mul_one]
    · rw [if_neg ha, if_neg (fun h => ha (this.mpr h)), mul_zero]
  have hY : (fun a => Real.sqrt (z + compVar G s b u a)) =
      fun a => if a ≠ u then Real.sqrt (z + discordant G s u) else Real.sqrt (z + 0) := by
    funext a
    simp only [compVar, compVal, hu, if_false, false_and, false_or, ne_eq, not_false_eq_true,
      true_and]
    split_ifs <;> rfl
  rw [hX, hY, expect_ite_eq (lazyNeighbor G hd u) (fun a => s a ≠ s u),
    expect_ite_eq (lazyNeighbor G hd u) (fun a => a ≠ u), lazyNeighbor_expect_discordant G hd,
    lazyNeighbor_expect_ne_self G hd, add_zero]
  have hc := sqrt_chord hz hl0 hld
  generalize (G.degree u : ℝ) = d at *
  generalize (discordant G s u : ℝ) = l at *
  have key : l / (2 * d) * Real.sqrt (z + d) + (1 - l / (2 * d)) * Real.sqrt z -
      (1 / 2 * Real.sqrt (z + l) + (1 - 1 / 2) * Real.sqrt z) =
      (l * Real.sqrt (z + d) + (d - l) * Real.sqrt z - d * Real.sqrt (z + l)) / (2 * d) := by
    field_simp
    ring
  have hneg : (l * Real.sqrt (z + d) + (d - l) * Real.sqrt z - d * Real.sqrt (z + l)) /
      (2 * d) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  linarith

/-- **The replacement step of Lemma 2.1** (BGKM16, Lemma A.1): if `S = {u | s u = b}` has
volume `P`, then `𝔼√(P + ∑ X_u) ≤ 𝔼√(P + ∑ Y_u)` for one round of the lazy voter. -/
lemma expect_sqrt_le_comp (hd : ∀ v, 0 < G.degree v) (s : Config V Bool) (b : Bool) :
    (Distribution.independent (lazyNeighbor G hd)).expect (fun r =>
      Real.sqrt (vol G (univ.filter fun u => s u = b) + ∑ u, volChange G s b u (r u))) ≤
    (Distribution.independent (lazyNeighbor G hd)).expect (fun r =>
      Real.sqrt (vol G (univ.filter fun u => s u = b) + ∑ u, compVar G s b u (r u))) := by
  refine independent_expect_comp_sum_le _ Real.sqrt _ _ _ (compLow G s b)
    (compLow_le_volChange G s b) (compLow_le_compVar G s b) fun u z hz => ?_
  by_cases hu : s u = b
  · rw [volChange_eq_compVar G s b u hu]
  · refine expect_sqrt_volChange_le G hd s b u hu (le_trans ?_ hz)
    have h := sum_compLow G s b
    rw [← add_sum_erase _ _ (mem_univ u)] at h
    simp only [compLow, hu, if_false, zero_add] at h
    simp only [compLow] at h ⊢
    rw [h]
    simp

/-! ### Moments of the comparison sum -/

/-- The probability `q_u` of the event on which `Y_u ≠ 0`: `λ_u / (2 d_u)` on `S`, `1/2`
outside. -/
lemma expect_compEvent (hd : ∀ v, 0 < G.degree v) (s : Config V Bool) (b : Bool) (u : V) :
    (lazyNeighbor G hd u).expect
        (fun a => if (s u = b ∧ s a ≠ b) ∨ (s u ≠ b ∧ a ≠ u) then 1 else 0) =
      if s u = b then (discordant G s u : ℝ) / (2 * G.degree u) else 1 / 2 := by
  by_cases hu : s u = b
  · rw [if_pos hu, ← lazyNeighbor_expect_discordant G hd s u]
    congr 1
    funext a
    simp [hu]
  · rw [if_neg hu, ← lazyNeighbor_expect_ne_self G hd u]
    congr 1
    funext a
    simp [hu]

/-- The means of the comparison variables cancel: both sides of the cut count it. -/
lemma sum_mean_compVar (hd : ∀ v, 0 < G.degree v) (s : Config V Bool) (b : Bool) :
    ∑ u, (lazyNeighbor G hd u).expect
        (fun a => if (s u = b ∧ s a ≠ b) ∨ (s u ≠ b ∧ a ≠ u) then 1 else 0) *
      compVal G s b u = 0 := by
  simp_rw [expect_compEvent G hd s b]
  have hterm (u : V) : (if s u = b then (discordant G s u : ℝ) / (2 * G.degree u) else 1 / 2) *
      compVal G s b u =
      if s u = b then -((discordant G s u : ℝ) / 2) else (discordant G s u : ℝ) / 2 := by
    have hd0 : (G.degree u : ℝ) ≠ 0 := by exact_mod_cast (hd u).ne'
    simp only [compVal]
    split_ifs
    · field_simp
    · ring
  simp_rw [hterm]
  rw [sum_ite, sum_neg_distrib, ← sum_div, ← sum_div]
  have h1 := card_interedges_class G s b
  have h2 := card_interedges_class_compl G s b
  rw [h1] at h2
  have h3 : ∑ u ∈ univ.filter (fun u => s u = b), (discordant G s u : ℝ) =
      ∑ u ∈ univ.filter (fun u => ¬ s u = b), (discordant G s u : ℝ) := by
    rw [← compl_filter]
    exact_mod_cast h2
  rw [h3]
  ring

/-- The centred comparison variable `Y_u - 𝔼 Y_u`. -/
noncomputable def compCentred (hd : ∀ v, 0 < G.degree v) (s : Config V Bool) (b : Bool)
    (u a : V) : ℝ :=
  compVar G s b u a - (lazyNeighbor G hd u).expect
    (fun a => if (s u = b ∧ s a ≠ b) ∨ (s u ≠ b ∧ a ≠ u) then 1 else 0) * compVal G s b u

/-- The comparison sum is the sum of the centred variables. -/
lemma sum_compVar_eq_centred (hd : ∀ v, 0 < G.degree v) (s : Config V Bool) (b : Bool)
    (r : V → V) :
    ∑ u, compVar G s b u (r u) = ∑ u, compCentred G hd s b u (r u) := by
  simp only [compCentred, sum_sub_distrib, sum_mean_compVar G hd s b, sub_zero]

lemma compCentred_mean (hd : ∀ v, 0 < G.degree v) (s : Config V Bool) (b : Bool) (u : V) :
    (lazyNeighbor G hd u).expect (compCentred G hd s b u) = 0 :=
  expect_bernoulli_centred _ _ _

/-- **Second moment of the comparison sum**: `𝔼[Δ'²] ≥ ∑_{u ∈ S} λ_u d_u / 4`. -/
lemma expect_compSum_sq_ge (hd : ∀ v, 0 < G.degree v) (s : Config V Bool) (b : Bool) :
    (∑ u ∈ univ.filter (fun u => s u = b), (discordant G s u : ℝ) * G.degree u) / 4 ≤
      (Distribution.independent (lazyNeighbor G hd)).expect
        (fun r => (∑ u, compVar G s b u (r u)) ^ 2) := by
  simp_rw [sum_compVar_eq_centred G hd s b]
  rw [independent_expect_sum_sq _ _ (compCentred_mean G hd s b), sum_filter, sum_div]
  refine sum_le_sum fun u _ => ?_
  rw [show (fun a => compCentred G hd s b u a ^ 2) = fun a =>
      ((if (s u = b ∧ s a ≠ b) ∨ (s u ≠ b ∧ a ≠ u) then compVal G s b u else 0) -
        (lazyNeighbor G hd u).expect (fun a =>
          if (s u = b ∧ s a ≠ b) ∨ (s u ≠ b ∧ a ≠ u) then 1 else 0) * compVal G s b u) ^ 2
      from rfl, expect_bernoulli_sq, expect_compEvent G hd s b]
  have hd0 : (0 : ℝ) < G.degree u := by exact_mod_cast hd u
  have hl0 : (0 : ℝ) ≤ discordant G s u := Nat.cast_nonneg _
  have hld : (discordant G s u : ℝ) ≤ G.degree u := by
    exact_mod_cast discordant_le_degree G s u
  simp only [compVal]
  split_ifs with hu
  · rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
    field_simp
    nlinarith [mul_nonneg hl0 (sub_nonneg.mpr hld)]
  · norm_num

/-- **Third moment of the comparison sum**: `𝔼[Δ'³] ≤ 0`. -/
lemma expect_compSum_cube_le (hd : ∀ v, 0 < G.degree v) (s : Config V Bool) (b : Bool) :
    (Distribution.independent (lazyNeighbor G hd)).expect
        (fun r => (∑ u, compVar G s b u (r u)) ^ 3) ≤ 0 := by
  simp_rw [sum_compVar_eq_centred G hd s b]
  rw [independent_expect_sum_cube _ _ (compCentred_mean G hd s b)]
  refine sum_nonpos fun u _ => ?_
  rw [show (fun a => compCentred G hd s b u a ^ 3) = fun a =>
      ((if (s u = b ∧ s a ≠ b) ∨ (s u ≠ b ∧ a ≠ u) then compVal G s b u else 0) -
        (lazyNeighbor G hd u).expect (fun a =>
          if (s u = b ∧ s a ≠ b) ∨ (s u ≠ b ∧ a ≠ u) then 1 else 0) * compVal G s b u) ^ 3
      from rfl, expect_bernoulli_cube, expect_compEvent G hd s b]
  have hd0 : (0 : ℝ) < G.degree u := by exact_mod_cast hd u
  have hl0 : (0 : ℝ) ≤ discordant G s u := Nat.cast_nonneg _
  have hld : (discordant G s u : ℝ) ≤ G.degree u := by
    exact_mod_cast discordant_le_degree G s u
  simp only [compVal]
  split_ifs with hu
  · -- `q = λ / (2d) ∈ [0, 1/2]`, the value is `-d < 0`
    set q := (discordant G s u : ℝ) / (2 * G.degree u)
    have hq0 : 0 ≤ q := by positivity
    have hq1 : q ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    have : 0 ≤ q * (1 - q) * (1 - 2 * q) :=
      mul_nonneg (mul_nonneg hq0 (by linarith)) (by linarith)
    have hc : (-(G.degree u : ℝ)) ^ 3 ≤ 0 := by
      have : (0 : ℝ) ≤ (G.degree u : ℝ) ^ 3 := by positivity
      nlinarith
    exact mul_nonpos_of_nonpos_of_nonneg hc this
  · norm_num

/-- The comparison sum is at least `-P`. -/
lemma compSum_ge (s : Config V Bool) (b : Bool) (r : V → V) :
    -(vol G (univ.filter fun u => s u = b) : ℝ) ≤ ∑ u, compVar G s b u (r u) := by
  rw [← sum_compLow]
  exact sum_le_sum fun u _ => compLow_le_compVar G s b u (r u)

/-! ### The final computation -/

omit [Fintype V] [DecidableEq V] in
/-- Expectation of the cubic Taylor polynomial. -/
lemma expect_taylor {α : Type*} [Fintype α] (μ : Distribution α) (c P : ℝ) (Δ : α → ℝ) :
    μ.expect (fun r => c * (1 + Δ r / (2 * P) - Δ r ^ 2 / (8 * P ^ 2) + Δ r ^ 3 / (16 * P ^ 3))) =
      c * (1 + μ.expect Δ / (2 * P) - μ.expect (fun r => Δ r ^ 2) / (8 * P ^ 2) +
        μ.expect (fun r => Δ r ^ 3) / (16 * P ^ 3)) := by
  have h : (fun r => c * (1 + Δ r / (2 * P) - Δ r ^ 2 / (8 * P ^ 2) + Δ r ^ 3 / (16 * P ^ 3))) =
      fun r => (c + c / (2 * P) * Δ r - c / (8 * P ^ 2) * Δ r ^ 2) +
        c / (16 * P ^ 3) * Δ r ^ 3 := by
    funext r
    ring
  rw [h, Distribution.expect_add, Distribution.expect_sub, Distribution.expect_add,
    Distribution.expect_const, Distribution.expect_mul, Distribution.expect_mul,
    Distribution.expect_mul]
  ring

omit [Fintype V] [DecidableEq V] in
/-- The last step of Lemma 2.1: with `𝔼Δ' = 0`, `𝔼Δ'² ≥ L/4` and `𝔼Δ'³ ≤ 0`,
`√P (1 + 𝔼Δ'/(2P) - 𝔼Δ'²/(8P²) + 𝔼Δ'³/(16P³)) ≤ √P - L / (32 √P³)`. -/
lemma drift_arith {P L E1 E2 E3 : ℝ} (hP : 0 < P) (h1 : E1 = 0) (h2 : L / 4 ≤ E2)
    (h3 : E3 ≤ 0) :
    Real.sqrt P * (1 + E1 / (2 * P) - E2 / (8 * P ^ 2) + E3 / (16 * P ^ 3)) ≤
      Real.sqrt P - L / (32 * Real.sqrt P ^ 3) := by
  subst h1
  set r := Real.sqrt P with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr hP
  have hPr : P = r ^ 2 := (Real.sq_sqrt hP.le).symm
  rw [hPr]
  have hexp : r * (1 + 0 / (2 * r ^ 2) - E2 / (8 * (r ^ 2) ^ 2) + E3 / (16 * (r ^ 2) ^ 3)) =
      r - E2 / (8 * r ^ 3) + E3 / (16 * r ^ 5) := by
    field_simp
    ring
  rw [hexp]
  have ha : L / (32 * r ^ 3) ≤ E2 / (8 * r ^ 3) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 < r ^ 3 := by positivity
    nlinarith
  have hb : E3 / (16 * r ^ 5) ≤ 0 := div_nonpos_of_nonpos_of_nonneg h3 (by positivity)
  linarith

/-- The comparison sum has mean zero. -/
lemma expect_compSum (hd : ∀ v, 0 < G.degree v) (s : Config V Bool) (b : Bool) :
    (Distribution.independent (lazyNeighbor G hd)).expect
      (fun r => ∑ u, compVar G s b u (r u)) = 0 := by
  simp_rw [sum_compVar_eq_centred G hd s b]
  rw [Distribution.expect_sum]
  refine sum_eq_zero fun u _ => ?_
  rw [Distribution.independent_expect_eval]
  exact compCentred_mean G hd s b u

end Voter
