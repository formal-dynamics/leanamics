import Dynamics.Distribution

/-! # Independent coordinates: resampling, factorization, moments, concave comparison

Tools for `Dynamics.Distribution.independent p`, the law of a random point `x : ι → α` whose
coordinates `x i ~ p i` are independent, used for one round of the voter model (VOT-5).

* `independent_expect_update`: resampling one coordinate does not change the law;
* `independent_expect_mul_of_update`: `𝔼[g(x i) G(x)] = 𝔼[g] 𝔼[G]` when `G` ignores `x i`;
* `independent_expect_sum_sq`, `independent_expect_sum_cube`: for centred coordinate functions,
  the second and third moments of `∑ i, W i (x i)` are the sums of the coordinate moments;
* `independent_expect_comp_sum_le`: replacing the coordinate functions of a sum one at a time,
  each replacement being an improvement for `f`, improves `𝔼[f(c + ∑ i, g i (x i))]`
  (the comparison lemma behind Lemma 2.1 of Berenbrink, Giakkoupis, Kermarrec,
  Mallmann-Trenn, ICALP 2016, which is their Lemma A.1);
* `expect_ite_eq`, `expect_bernoulli_sq`, `expect_bernoulli_cube`: two-point laws.

All of these are candidates for `dynamics/`.
-/

namespace Voter
open Dynamics Finset

section TwoPoint
variable {α : Type*} [Fintype α]

/-- A two-valued observable has expectation `q x + (1 - q) y`, where `q` is the probability of
the event on which it takes the value `x`. -/
lemma expect_ite_eq (p : Distribution α) (P : α → Prop) [DecidablePred P] (x y : ℝ) :
    p.expect (fun a => if P a then x else y) =
      p.expect (fun a => if P a then 1 else 0) * x +
        (1 - p.expect (fun a => if P a then 1 else 0)) * y := by
  have h : (fun a => if P a then x else y) =
      fun a => (x - y) * (if P a then 1 else 0) + y := by
    funext a
    split_ifs <;> ring
  rw [h, Distribution.expect_add, Distribution.expect_mul, Distribution.expect_const]
  ring

/-- Second moment of a centred two-point variable `x (1_P - q)`: `x² q (1 - q)`. -/
lemma expect_bernoulli_sq (p : Distribution α) (P : α → Prop) [DecidablePred P] (x : ℝ) :
    p.expect (fun a => ((if P a then x else 0) -
        p.expect (fun b => if P b then 1 else 0) * x) ^ 2) =
      x ^ 2 * (p.expect (fun a => if P a then 1 else 0) *
        (1 - p.expect (fun a => if P a then 1 else 0))) := by
  set q := p.expect (fun a => if P a then 1 else 0)
  have h : (fun a => ((if P a then x else 0) - q * x) ^ 2) =
      fun a => if P a then (x - q * x) ^ 2 else (0 - q * x) ^ 2 := by
    funext a
    split_ifs <;> rfl
  rw [h, expect_ite_eq]
  ring

/-- Third moment of a centred two-point variable `x (1_P - q)`: `x³ q (1 - q) (1 - 2q)`. -/
lemma expect_bernoulli_cube (p : Distribution α) (P : α → Prop) [DecidablePred P] (x : ℝ) :
    p.expect (fun a => ((if P a then x else 0) -
        p.expect (fun b => if P b then 1 else 0) * x) ^ 3) =
      x ^ 3 * (p.expect (fun a => if P a then 1 else 0) *
        (1 - p.expect (fun a => if P a then 1 else 0)) *
          (1 - 2 * p.expect (fun a => if P a then 1 else 0))) := by
  set q := p.expect (fun a => if P a then 1 else 0)
  have h : (fun a => ((if P a then x else 0) - q * x) ^ 3) =
      fun a => if P a then (x - q * x) ^ 3 else (0 - q * x) ^ 3 := by
    funext a
    split_ifs <;> rfl
  rw [h, expect_ite_eq]
  ring

/-- A centred two-point variable has mean zero. -/
lemma expect_bernoulli_centred (p : Distribution α) (P : α → Prop) [DecidablePred P] (x : ℝ) :
    p.expect (fun a => (if P a then x else 0) -
        p.expect (fun b => if P b then 1 else 0) * x) = 0 := by
  rw [Distribution.expect_sub, Distribution.expect_const, expect_ite_eq]
  ring

end TwoPoint

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

/-- Moving the weight of one coordinate: `w(x) p_i(a) = p_i(x i) w(x[i ↦ a])`. -/
lemma independent_weight_update (p : ι → Distribution α) (x : ι → α) (i : ι) (a : α) :
    (Distribution.independent p).weight x * (p i).weight a =
      (p i).weight (x i) * (Distribution.independent p).weight (Function.update x i a) := by
  simp only [Distribution.independent]
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
    (Distribution.independent p).expect F = (Distribution.independent p).expect
      (fun x => (p i).expect (fun a => F (Function.update x i a))) := by
  let e : (ι → α) × α ≃ (ι → α) × α :=
    { toFun := fun q => (Function.update q.1 i q.2, q.1 i)
      invFun := fun q => (Function.update q.1 i q.2, q.1 i)
      left_inv := fun q => by simp [Function.update_idem]
      right_inv := fun q => by simp [Function.update_idem] }
  set w := Distribution.independent p
  unfold Distribution.expect
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

/-- **Independence of one coordinate**: if `G` does not depend on the coordinate `i`, then
`𝔼[g(x i) G(x)] = 𝔼[g] 𝔼[G]`. -/
theorem independent_expect_mul_of_update (p : ι → Distribution α) (i : ι) (g : α → ℝ)
    (G : (ι → α) → ℝ) (hG : ∀ x a, G (Function.update x i a) = G x) :
    (Distribution.independent p).expect (fun x => g (x i) * G x) =
      (p i).expect g * (Distribution.independent p).expect G := by
  rw [independent_expect_update p i]
  simp_rw [Function.update_self, hG]
  have h (x : ι → α) : (p i).expect (fun a => g a * G x) = (p i).expect g * G x := by
    simp_rw [mul_comm _ (G x)]
    rw [Distribution.expect_mul, mul_comm]
  simp_rw [h]
  exact Distribution.expect_mul _ _ _

omit [Fintype ι] [Fintype α] in
/-- A coordinate function evaluated at another coordinate ignores the resampled coordinate. -/
lemma update_apply_of_ne (x : ι → α) {i j : ι} (h : j ≠ i) (a : α) :
    Function.update x i a j = x j :=
  Function.update_of_ne h a x

/-- Two distinct coordinates are independent; for centred functions the mixed moment
vanishes. -/
lemma independent_expect_mul_centred (p : ι → Distribution α) {i j : ι} (hij : i ≠ j)
    (g : α → ℝ) (hg : (p i).expect g = 0) (G : α → ℝ) :
    (Distribution.independent p).expect (fun x => g (x i) * G (x j)) = 0 := by
  rw [independent_expect_mul_of_update p i g (fun x => G (x j))
    (fun x a => by rw [update_apply_of_ne x (Ne.symm hij)]), hg, zero_mul]

/-- **Second moment of a sum of independent centred coordinates.** -/
theorem independent_expect_sum_sq (p : ι → Distribution α) (W : ι → α → ℝ)
    (hW : ∀ i, (p i).expect (W i) = 0) :
    (Distribution.independent p).expect (fun x => (∑ i, W i (x i)) ^ 2) =
      ∑ i, (p i).expect (fun a => W i a ^ 2) := by
  have hsq (x : ι → α) : (∑ i, W i (x i)) ^ 2 = ∑ i, ∑ j, W i (x i) * W j (x j) := by
    rw [sq, sum_mul_sum]
  simp_rw [hsq]
  rw [Distribution.expect_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [Distribution.expect_sum, sum_eq_single i]
  · rw [← Distribution.independent_expect_eval p i (fun a => W i a ^ 2)]
    simp_rw [sq]
  · intro j _ hji
    exact independent_expect_mul_centred p (Ne.symm hji) (W i) (hW i) (W j)
  · simp

/-- The mixed third moments of independent centred coordinates vanish unless the three indices
agree. -/
lemma independent_expect_mul_three (p : ι → Distribution α) (W : ι → α → ℝ)
    (hW : ∀ i, (p i).expect (W i) = 0) (i j k : ι) :
    (Distribution.independent p).expect (fun x => W i (x i) * W j (x j) * W k (x k)) =
      if j = i ∧ k = i then (p i).expect (fun a => W i a ^ 3) else 0 := by
  by_cases hji : j = i
  · by_cases hki : k = i
    · rw [if_pos ⟨hji, hki⟩, hji, hki,
        ← Distribution.independent_expect_eval p i (fun a => W i a ^ 3)]
      congr 1
      funext x
      ring
    · rw [if_neg (fun h => hki h.2), hji]
      -- the coordinate `k` appears once
      have h := independent_expect_mul_of_update p k (W k) (fun x => W i (x i) * W i (x i))
        (fun x a => by rw [update_apply_of_ne x (Ne.symm hki)])
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
        (fun x a => by rw [update_apply_of_ne x (Ne.symm hji)])
      rw [hW j, zero_mul] at h
      rw [← h]
      congr 1
      funext x
      ring
    · -- the coordinate `i` appears once
      have h := independent_expect_mul_of_update p i (W i) (fun x => W j (x j) * W k (x k))
        (fun x a => by rw [update_apply_of_ne x hji, update_apply_of_ne x hki])
      rw [hW i, zero_mul] at h
      rw [← h]
      congr 1
      funext x
      ring

/-- **Third moment of a sum of independent centred coordinates.** -/
theorem independent_expect_sum_cube (p : ι → Distribution α) (W : ι → α → ℝ)
    (hW : ∀ i, (p i).expect (W i) = 0) :
    (Distribution.independent p).expect (fun x => (∑ i, W i (x i)) ^ 3) =
      ∑ i, (p i).expect (fun a => W i a ^ 3) := by
  have hcube (x : ι → α) : (∑ i, W i (x i)) ^ 3 =
      ∑ i, ∑ j, ∑ k, W i (x i) * W j (x j) * W k (x k) := by
    rw [pow_succ, sq, sum_mul_sum, sum_mul]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_mul]
    refine sum_congr rfl fun j _ => ?_
    rw [mul_sum]
  simp_rw [hcube]
  rw [Distribution.expect_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [Distribution.expect_sum]
  simp_rw [Distribution.expect_sum, independent_expect_mul_three p W hW i, ite_and]
  simp

/-- **Comparison of sums of independent coordinates through a function `f`** (the argument of
Lemma A.1 of BGKM16). Let `g i a` and `h i a` be at least `l i`. If for every coordinate `i` and
every `z ≥ c + ∑_{j ≠ i} l j` replacing `g i` by `h i` does not decrease
`𝔼_{a ~ p i}[f(z + · )]`, then `𝔼[f(c + ∑ i, g i (x i))] ≤ 𝔼[f(c + ∑ i, h i (x i))]`. -/
theorem independent_expect_comp_sum_le (p : ι → Distribution α) (f : ℝ → ℝ) (c : ℝ)
    (g h : ι → α → ℝ) (l : ι → ℝ) (hg : ∀ i a, l i ≤ g i a) (hh : ∀ i a, l i ≤ h i a)
    (hstep : ∀ i z, c + ∑ j ∈ univ.erase i, l j ≤ z →
      (p i).expect (fun a => f (z + g i a)) ≤ (p i).expect (fun a => f (z + h i a))) :
    (Distribution.independent p).expect (fun x => f (c + ∑ i, g i (x i))) ≤
      (Distribution.independent p).expect (fun x => f (c + ∑ i, h i (x i))) := by
  -- `k T`: the functions `h` on `T`, `g` elsewhere
  let k : Finset ι → ι → α → ℝ := fun T i => if i ∈ T then h i else g i
  have hk : ∀ T i a, l i ≤ k T i a := fun T i a => by
    simp only [k]
    split_ifs
    · exact hh i a
    · exact hg i a
  -- splitting off the coordinate `i`
  have hsplit (T : Finset ι) (x : ι → α) (i : ι) (a : α) :
      ∑ j, k T j (Function.update x i a j) =
        k T i a + ∑ j ∈ univ.erase i, k T j (x j) := by
    rw [← add_sum_erase univ _ (mem_univ i), Function.update_self]
    congr 1
    exact sum_congr rfl fun j hj => by rw [update_apply_of_ne x (ne_of_mem_erase hj)]
  have key : ∀ T : Finset ι,
      (Distribution.independent p).expect (fun x => f (c + ∑ i, g i (x i))) ≤
        (Distribution.independent p).expect (fun x => f (c + ∑ i, k T i (x i))) := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact le_of_eq (by simp [k])
    | @insert i T hi ih =>
      refine ih.trans ?_
      rw [independent_expect_update p i, independent_expect_update p i
        (fun x => f (c + ∑ j, k (insert i T) j (x j)))]
      refine (Distribution.independent p).expect_mono fun x => ?_
      simp only [hsplit]
      have hrest : ∑ j ∈ univ.erase i, k T j (x j) =
          ∑ j ∈ univ.erase i, k (insert i T) j (x j) := by
        refine sum_congr rfl fun j hj => ?_
        simp only [k, mem_insert, ne_of_mem_erase hj, false_or]
      have hz : c + ∑ j ∈ univ.erase i, l j ≤ c + ∑ j ∈ univ.erase i, k T j (x j) := by
        gcongr with j
        exact hk T j (x j)
      have hki : k T i = g i := by simp [k, hi]
      have hki' : k (insert i T) i = h i := by simp [k]
      rw [hki, hki', ← hrest]
      have := hstep i _ hz
      simpa only [add_comm, add_left_comm, add_assoc] using this
  have huniv : k univ = h := by
    funext i
    simp [k]
  simpa [huniv] using key univ

end Voter
