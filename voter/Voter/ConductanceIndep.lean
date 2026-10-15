import Dynamics.Independent

/-! # Independent coordinates: concave comparison and two-point laws

Tools for `Dynamics.Distribution.independent p`, the law of a random point `x : ι → α` whose
coordinates `x i ~ p i` are independent, used for one round of the voter model (VOT-5). The
general independence lemmas (resampling one coordinate `Distribution.independent_expect_update`,
factorization `Distribution.independent_expect_mul_of_update`, and the second and third moments of
sums of centred coordinates `Distribution.independent_expect_sum_sq`,
`Distribution.independent_expect_sum_cube`) are in `Dynamics.Independent`. This file adds:

* `independent_expect_comp_sum_le`: replacing the coordinate functions of a sum one at a time,
  each replacement being an improvement for `f`, improves `𝔼[f(c + ∑ i, g i (x i))]`
  (the comparison lemma behind Lemma 2.1 of Berenbrink, Giakkoupis, Kermarrec,
  Mallmann-Trenn, ICALP 2016, which is their Lemma A.1);
* `expect_ite_eq`, `expect_bernoulli_sq`, `expect_bernoulli_cube`: two-point laws.
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
    exact sum_congr rfl fun j hj => by rw [Function.update_of_ne (ne_of_mem_erase hj)]
  have key : ∀ T : Finset ι,
      (Distribution.independent p).expect (fun x => f (c + ∑ i, g i (x i))) ≤
        (Distribution.independent p).expect (fun x => f (c + ∑ i, k T i (x i))) := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact le_of_eq (by simp [k])
    | @insert i T hi ih =>
      refine ih.trans ?_
      rw [Distribution.independent_expect_update p i, Distribution.independent_expect_update p i
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
