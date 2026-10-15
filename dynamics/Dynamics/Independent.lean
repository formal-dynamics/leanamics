import Dynamics.Distribution

/-!
# Independent coordinates: conditioning, factorization, moments

Tools for `Distribution.independent p`, the law of a random point `x : ι → α` whose coordinates
`x i ~ p i` are independent (the basic factorization `independent_expect_prod` and the marginal
`independent_expect_eval` are in `Dynamics.Distribution`).

* **Conditioning on one coordinate.** Resampling the coordinate `i` does not change the law
  (`independent_expect_update`), equivalently the expectation is the `p i`-average over the
  value `b` of `x i` of the expectation with `x i` set to `b`
  (`independent_expect_eq_sum_update`); for i.i.d. products over `Fin (m + 1)`, conditioning on
  the first coordinate (`independent_expect_fin_succ`, `independent_prob_fin_succ`).
* **Factorization.** `𝔼[g(x i) G(x)] = 𝔼[g] 𝔼[G]` when `G` ignores `x i`
  (`independent_expect_mul_of_update`); two distinct coordinates are independent
  (`independent_expect_pair`); functions of the coordinates in `S` and outside `S` are
  uncorrelated (`expect_mul_of_dep`).
* **Moments of sums.** For centred coordinate functions the second and third moments of
  `∑ i, W i (x i)` are the sums of the coordinate moments (`independent_expect_sum_sq`,
  `independent_expect_sum_cube`).
* **Coordinatewise combination.** If `x ~ independent P` and `y ~ independent Q` are
  independent, `fun i => φ i (x i) (y i)` has law `independent R`, where `R i` is the law of
  `φ i a b` (`expect_expect_coord`).

The uniform analogues for `avg` over dependent products `∀ i, β i` (`avg_pi_prod`, `avg_pi_eval`,
`avg_pi_split`) are in `Dynamics.Uniform`.
-/

namespace Dynamics.Distribution
open Finset

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

/-! ### Conditioning on one coordinate -/

/-- Moving the weight of one coordinate: `w(x) p_i(a) = p_i(x i) w(x[i ↦ a])`. -/
lemma independent_weight_update (p : ι → Distribution α) (x : ι → α) (i : ι) (a : α) :
    (independent p).weight x * (p i).weight a =
      (p i).weight (x i) * (independent p).weight (Function.update x i a) := by
  simp only [independent]
  rw [← mul_prod_erase univ (fun j => (p j).weight (x j)) (mem_univ i),
    ← mul_prod_erase univ (fun j => (p j).weight (Function.update x i a j)) (mem_univ i),
    Function.update_self]
  have h : ∏ j ∈ univ.erase i, (p j).weight (Function.update x i a j) =
      ∏ j ∈ univ.erase i, (p j).weight (x j) :=
    prod_congr rfl fun j hj => by rw [Function.update_of_ne (ne_of_mem_erase hj)]
  rw [h]
  ring

/-- **Resampling one coordinate**: replacing the coordinate `i` of an independent point by an
independent copy does not change the law. -/
theorem independent_expect_update (p : ι → Distribution α) (i : ι) (F : (ι → α) → ℝ) :
    (independent p).expect F = (independent p).expect
      (fun x => (p i).expect (fun a => F (Function.update x i a))) := by
  let e : (ι → α) × α ≃ (ι → α) × α :=
    { toFun := fun q => (Function.update q.1 i q.2, q.1 i)
      invFun := fun q => (Function.update q.1 i q.2, q.1 i)
      left_inv := fun q => by simp [Function.update_idem]
      right_inv := fun q => by simp [Function.update_idem] }
  set w := independent p
  unfold expect
  calc ∑ y, w.weight y * F y
      = ∑ q : (ι → α) × α, (p i).weight q.2 * (w.weight q.1 * F q.1) := by
        rw [Fintype.sum_prod_type]
        refine sum_congr rfl fun y _ => ?_
        dsimp only
        rw [← sum_mul, (p i).sum_one, one_mul]
    _ = ∑ q : (ι → α) × α, (p i).weight (e q).2 * (w.weight (e q).1 * F (e q).1) :=
        (Equiv.sum_comp e (fun q => (p i).weight q.2 * (w.weight q.1 * F q.1))).symm
    _ = ∑ q : (ι → α) × α, w.weight q.1 * ((p i).weight q.2 * F (Function.update q.1 i q.2)) := by
        refine sum_congr rfl fun q _ => ?_
        have h := independent_weight_update p q.1 i q.2
        simp only [e, Equiv.coe_fn_mk]
        rw [← mul_assoc, ← h]
        ring
    _ = ∑ x, w.weight x * ∑ a, (p i).weight a * F (Function.update x i a) := by
        rw [Fintype.sum_prod_type]
        simp_rw [mul_sum]

/-- **Conditioning on one coordinate**: the expectation is the average, over the value `b` of
coordinate `i`, of the expectation with that coordinate set to `b`. -/
theorem independent_expect_eq_sum_update (p : ι → Distribution α) (i : ι) (F : (ι → α) → ℝ) :
    (independent p).expect F =
      ∑ b, (p i).weight b * (independent p).expect (fun x => F (Function.update x i b)) := by
  rw [independent_expect_update p i]
  simp only [expect, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun b _ => sum_congr rfl fun x _ => by ring

/-- **Conditioning on the first coordinate**: an i.i.d. product over `Fin (m + 1)` is the
average, over the first coordinate `b`, of the product over `Fin m` with `b` prepended. -/
lemma independent_expect_fin_succ {m : ℕ} (q : Distribution α) (f : (Fin (m + 1) → α) → ℝ) :
    (independent fun _ : Fin (m + 1) => q).expect f =
      ∑ b, q.weight b * (independent fun _ : Fin m => q).expect (fun r => f (Fin.cons b r)) := by
  simp only [expect, independent, mul_sum]
  rw [← (Fin.consEquiv fun _ => α).sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun b _ => sum_congr rfl fun r _ => ?_
  simp [Fin.consEquiv, Fin.prod_univ_succ, mul_assoc]

/-- Probabilities under an i.i.d. product over `Fin (m + 1)`, conditioned on the first
coordinate. -/
lemma independent_prob_fin_succ {m : ℕ} (q : Distribution α) (s : (Fin (m + 1) → α) → Prop) :
    (independent fun _ : Fin (m + 1) => q).prob s =
      ∑ b, q.weight b * (independent fun _ : Fin m => q).prob (fun r => s (Fin.cons b r)) := by
  classical
  simp only [prob_eq_expect]
  exact independent_expect_fin_succ q _

/-! ### Factorization -/

/-- **Independence of one coordinate**: if `G` does not depend on the coordinate `i`, then
`𝔼[g(x i) G(x)] = 𝔼[g] 𝔼[G]`. -/
theorem independent_expect_mul_of_update (p : ι → Distribution α) (i : ι) (g : α → ℝ)
    (G : (ι → α) → ℝ) (hG : ∀ x a, G (Function.update x i a) = G x) :
    (independent p).expect (fun x => g (x i) * G x) =
      (p i).expect g * (independent p).expect G := by
  rw [independent_expect_update p i]
  simp_rw [Function.update_self, hG]
  have h (x : ι → α) : (p i).expect (fun a => g a * G x) = (p i).expect g * G x := by
    simp_rw [mul_comm _ (G x)]
    rw [expect_mul, mul_comm]
  simp_rw [h]
  exact expect_mul _ _ _

/-- Two distinct coordinates of an independent product are independent. -/
lemma independent_expect_pair (p : ι → Distribution α) {i j : ι} (hij : i ≠ j)
    (f : α → α → ℝ) :
    (independent p).expect (fun x => f (x i) (x j)) =
      (p i).expect fun a => (p j).expect fun b => f a b := by
  classical
  -- factor of coordinate `k` selecting the values `a` at `i` and `b` at `j`
  let φ : α → α → ι → α → ℝ := fun a b k c =>
    (if k = i then (if c = a then 1 else 0) else 1) *
      (if k = j then (if c = b then 1 else 0) else 1)
  have hprod (a b : α) (x : ι → α) :
      ∏ k, φ a b k (x k) = (if x i = a then 1 else 0) * (if x j = b then 1 else 0) := by
    simp only [φ, prod_mul_distrib, prod_ite_eq', mem_univ, if_true]
  have hfactor (a b : α) (k : ι) :
      (p k).expect (φ a b k) =
        (if k = i then (p i).weight a else 1) * (if k = j then (p j).weight b else 1) := by
    by_cases hki : k = i
    · subst hki
      simp [φ, hij, expect]
    · by_cases hkj : k = j
      · subst hkj
        simp [φ, hki, expect]
      · simp [φ, hki, hkj]
  have hdecomp (x : ι → α) :
      f (x i) (x j) = ∑ a, ∑ b, f a b * ∏ k, φ a b k (x k) := by
    simp only [hprod, mul_ite, mul_one, mul_zero, sum_ite_eq, mem_univ, if_true]
  calc
    (independent p).expect (fun x => f (x i) (x j))
        = ∑ a, ∑ b, f a b * (independent p).expect (fun x => ∏ k, φ a b k (x k)) := by
          simp_rw [hdecomp, expect_sum, expect_mul]
    _ = ∑ a, ∑ b, f a b * ((p i).weight a * (p j).weight b) := by
          refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
          rw [independent_expect_prod]
          simp only [hfactor, prod_mul_distrib, prod_ite_eq', mem_univ, if_true]
    _ = (p i).expect fun a => (p j).expect fun b => f a b := by
          simp only [expect, mul_sum]
          exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring

/-! ### Moments of sums of centred coordinates -/

/-- Two distinct coordinates are independent; for centred functions the mixed moment
vanishes. -/
lemma independent_expect_mul_centred (p : ι → Distribution α) {i j : ι} (hij : i ≠ j)
    (g : α → ℝ) (hg : (p i).expect g = 0) (G : α → ℝ) :
    (independent p).expect (fun x => g (x i) * G (x j)) = 0 := by
  rw [independent_expect_mul_of_update p i g (fun x => G (x j))
    (fun x a => by rw [Function.update_of_ne (Ne.symm hij)]), hg, zero_mul]

/-- **Second moment of a sum of independent centred coordinates.** -/
theorem independent_expect_sum_sq (p : ι → Distribution α) (W : ι → α → ℝ)
    (hW : ∀ i, (p i).expect (W i) = 0) :
    (independent p).expect (fun x => (∑ i, W i (x i)) ^ 2) =
      ∑ i, (p i).expect (fun a => W i a ^ 2) := by
  have hsq (x : ι → α) : (∑ i, W i (x i)) ^ 2 = ∑ i, ∑ j, W i (x i) * W j (x j) := by
    rw [sq, sum_mul_sum]
  simp_rw [hsq]
  rw [expect_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [expect_sum, sum_eq_single i]
  · rw [← independent_expect_eval p i (fun a => W i a ^ 2)]
    simp_rw [sq]
  · intro j _ hji
    exact independent_expect_mul_centred p (Ne.symm hji) (W i) (hW i) (W j)
  · simp

/-- The mixed third moments of independent centred coordinates vanish unless the three indices
agree. -/
lemma independent_expect_mul_three (p : ι → Distribution α) (W : ι → α → ℝ)
    (hW : ∀ i, (p i).expect (W i) = 0) (i j k : ι) :
    (independent p).expect (fun x => W i (x i) * W j (x j) * W k (x k)) =
      if j = i ∧ k = i then (p i).expect (fun a => W i a ^ 3) else 0 := by
  by_cases hji : j = i
  · by_cases hki : k = i
    · rw [if_pos ⟨hji, hki⟩, hji, hki, ← independent_expect_eval p i (fun a => W i a ^ 3)]
      congr 1
      funext x
      ring
    · rw [if_neg (fun h => hki h.2), hji]
      -- the coordinate `k` appears once
      have h := independent_expect_mul_of_update p k (W k) (fun x => W i (x i) * W i (x i))
        (fun x a => by rw [Function.update_of_ne (Ne.symm hki)])
      rw [hW k, zero_mul] at h
      rw [← h]
      congr 1
      funext x
      ring
  · rw [if_neg (fun h => hji h.1)]
    by_cases hki : k = i
    · rw [hki]
      -- the coordinate `j` appears once
      have h := independent_expect_mul_of_update p j (W j) (fun x => W i (x i) * W i (x i))
        (fun x a => by rw [Function.update_of_ne (Ne.symm hji)])
      rw [hW j, zero_mul] at h
      rw [← h]
      congr 1
      funext x
      ring
    · -- the coordinate `i` appears once
      have h := independent_expect_mul_of_update p i (W i) (fun x => W j (x j) * W k (x k))
        (fun x a => by rw [Function.update_of_ne hji, Function.update_of_ne hki])
      rw [hW i, zero_mul] at h
      rw [← h]
      congr 1
      funext x
      ring

/-- **Third moment of a sum of independent centred coordinates.** -/
theorem independent_expect_sum_cube (p : ι → Distribution α) (W : ι → α → ℝ)
    (hW : ∀ i, (p i).expect (W i) = 0) :
    (independent p).expect (fun x => (∑ i, W i (x i)) ^ 3) =
      ∑ i, (p i).expect (fun a => W i a ^ 3) := by
  have hcube (x : ι → α) : (∑ i, W i (x i)) ^ 3 =
      ∑ i, ∑ j, ∑ k, W i (x i) * W j (x j) * W k (x k) := by
    rw [pow_succ, sq, sum_mul_sum, sum_mul]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_mul]
    refine sum_congr rfl fun j _ => ?_
    rw [mul_sum]
  simp_rw [hcube]
  rw [expect_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [expect_sum]
  simp_rw [expect_sum, independent_expect_mul_three p W hW i, ite_and]
  simp

/-! ### Coordinatewise combination of independent families -/

section Coord

variable {β γ : Type*} [Fintype β] [Fintype γ]

/-- **Coordinatewise combination**: if `x ~ independent P` and `y ~ independent Q` are
independent, and `R i` is the law of `φ i a b` for `a ~ P i`, `b ~ Q i`, then
`fun i => φ i (x i) (y i)` has law `independent R`. -/
theorem expect_expect_coord (P : ι → Distribution α) (Q : ι → Distribution β)
    (R : ι → Distribution γ) (φ : ι → α → β → γ) [DecidableEq γ]
    (hR : ∀ i c, (R i).weight c =
      ∑ a, ∑ b, if φ i a b = c then (P i).weight a * (Q i).weight b else 0)
    (H : (ι → γ) → ℝ) :
    (independent P).expect (fun x =>
        (independent Q).expect fun y => H fun i => φ i (x i) (y i)) =
      (independent R).expect H := by
  classical
  set g : ι → γ → α → β → ℝ := fun i c a b =>
    if φ i a b = c then (P i).weight a * (Q i).weight b else 0 with hg
  have key (z : ι → γ) : (∏ i, (R i).weight (z i)) =
      ∑ x : ι → α, ∑ y : ι → β, ∏ i, g i (z i) (x i) (y i) := by
    have h1 : ∀ i, (R i).weight (z i) = ∑ ab : α × β, g i (z i) ab.1 ab.2 := fun i => by
      rw [hR, Fintype.sum_prod_type']
    simp_rw [h1]
    rw [Fintype.prod_sum, ← Fintype.sum_prod_type']
    exact Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow ι (fun _ => α) (fun _ => β)) _ _
      fun w => rfl
  have hpt (x : ι → α) (y : ι → β) (z : ι → γ) : (∏ i, g i (z i) (x i) (y i)) =
      if (fun i => φ i (x i) (y i)) = z then
        (∏ i, (P i).weight (x i)) * ∏ i, (Q i).weight (y i) else 0 := by
    split_ifs with hz
    · subst hz
      simp [hg, prod_mul_distrib]
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp hz
      exact prod_eq_zero (mem_univ i) (by simp [hg, hi])
  simp only [expect, independent]
  symm
  calc ∑ z : ι → γ, (∏ i, (R i).weight (z i)) * H z
      = ∑ z : ι → γ, ∑ x : ι → α, ∑ y : ι → β, (∏ i, g i (z i) (x i) (y i)) * H z := by
        simp_rw [key, sum_mul]
    _ = ∑ x : ι → α, ∑ y : ι → β, ∑ z : ι → γ, (∏ i, g i (z i) (x i) (y i)) * H z := by
        rw [sum_comm]
        exact sum_congr rfl fun x _ => sum_comm
    _ = ∑ x : ι → α, ∑ y : ι → β, (∏ i, (P i).weight (x i)) *
          ((∏ i, (Q i).weight (y i)) * H fun i => φ i (x i) (y i)) := by
        refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
        simp_rw [hpt, ite_mul, zero_mul]
        rw [sum_ite_eq]
        simp [mul_assoc]
    _ = _ := by simp_rw [mul_sum]

/-- **Independence of disjoint sets of coordinates**: under an independent product, a function
of the coordinates in `S` and a function of the coordinates outside `S` are uncorrelated. -/
theorem expect_mul_of_dep (P : ι → Distribution α) (S : Finset ι) {F G : (ι → α) → ℝ}
    (hF : ∀ ω ω', (∀ i ∈ S, ω i = ω' i) → F ω = F ω')
    (hG : ∀ ω ω', (∀ i ∉ S, ω i = ω' i) → G ω = G ω') :
    (independent P).expect (fun ω => F ω * G ω) =
      (independent P).expect F * (independent P).expect G := by
  classical
  set φ : ι → α → α → α := fun i a b => if i ∈ S then a else b with hφ
  have hR : ∀ i c, (P i).weight c =
      ∑ a, ∑ b, if φ i a b = c then (P i).weight a * (P i).weight b else 0 := by
    intro i c
    by_cases hi : i ∈ S
    · simp only [hφ, if_pos hi]
      rw [sum_eq_single c (fun a _ ha => sum_eq_zero fun b _ => if_neg ha) (by simp)]
      simp [← mul_sum, (P i).sum_one]
    · simp only [hφ, if_neg hi]
      rw [sum_comm, sum_eq_single c (fun b _ hb => sum_eq_zero fun a _ => if_neg hb)
        (by simp)]
      simp [← sum_mul, (P i).sum_one]
  have hmerge := expect_expect_coord P P P φ hR (fun ω => F ω * G ω)
  have hFm (x y : ι → α) : F (fun i => φ i (x i) (y i)) = F x :=
    hF _ _ fun i hi => by simp [hφ, hi]
  have hGm (x y : ι → α) : G (fun i => φ i (x i) (y i)) = G y :=
    hG _ _ fun i hi => by simp [hφ, hi]
  rw [← hmerge]
  simp_rw [hFm, hGm, expect_mul]
  rw [mul_comm, ← expect_mul]
  congr 1
  funext x
  ring

end Coord

end Dynamics.Distribution
