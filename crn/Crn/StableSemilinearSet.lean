import Crn.StableThreshold
import Crn.StableRemainder
import Mathlib.ModelTheory.Arithmetic.Presburger.Semilinear.Basic

/-!
# Threshold and remainder sets are semilinear (CRN-3)

Helper lemmas for `IsSemilinearPred.isSemilinearSet`, through Mathlib's semilinear sets: the
solutions of a linear equation `A + ∑ⱼ pⱼ zⱼ = B + ∑ⱼ p'ⱼ zⱼ` over `ℕ` form a semilinear set
(`isSemilinearSet_setOf_eq`), and semilinear sets are closed under projection
(`IsSemilinearSet.proj`). Write `aᵢ = a⁺ᵢ - a⁻ᵢ`, `c = c⁺ - c⁻` with natural parts; then
* `∑ aᵢ xᵢ < c` iff `∃ k, ∑ a⁺ᵢ xᵢ + c⁻ + 1 + k = ∑ a⁻ᵢ xᵢ + c⁺` (one slack variable);
* `∑ aᵢ xᵢ ≡ c (mod m)` iff `∃ k₁ k₂, ∑ a⁺ᵢ xᵢ + c⁻ + m k₁ = ∑ a⁻ᵢ xᵢ + c⁺ + m k₂`.
-/

namespace Crn

open Finset

/-- The linear form `z ↦ ∑ⱼ pⱼ zⱼ` on `ℕ`-vectors. -/
def linForm {κ : Type*} [Fintype κ] (p : κ → ℕ) : (κ → ℕ) →+ ℕ where
  toFun z := ∑ j, p j * z j
  map_zero' := by simp
  map_add' z z' := by simp [mul_add, sum_add_distrib]

/-- The solutions of a linear equation over `ℕ` form a semilinear set. -/
lemma isSemilinearSet_linEq {κ : Type*} [Fintype κ] (A B : ℕ) (p p' : κ → ℕ) :
    IsSemilinearSet {z : κ → ℕ | A + ∑ j, p j * z j = B + ∑ j, p' j * z j} :=
  isSemilinearSet_setOf_eq A B (linForm p) (linForm p')

variable {X : Type*} [Fintype X]

/-- `∑ aᵢ xᵢ = ∑ a⁺ᵢ xᵢ - ∑ a⁻ᵢ xᵢ` with the natural parts `a⁺ = a.toNat`, `a⁻ = (-a).toNat`. -/
lemma sum_mul_eq_sub (a : X → ℤ) (x : X → ℕ) :
    ∑ i, a i * (x i : ℤ) =
      ((∑ i, (a i).toNat * x i : ℕ) : ℤ) - ((∑ i, (-a i).toNat * x i : ℕ) : ℤ) := by
  push_cast
  rw [← sum_sub_distrib]
  exact sum_congr rfl fun i _ => by rw [← sub_mul, Int.toNat_sub_toNat_neg]

/-- Threshold sets are semilinear. -/
lemma isSemilinearSet_threshold (a : X → ℤ) (c : ℤ) :
    IsSemilinearSet {x : X → ℕ | threshold a c x = true} := by
  have h := (isSemilinearSet_linEq (κ := X ⊕ Unit) ((-c).toNat + 1) c.toNat
    (Sum.elim (fun i => (a i).toNat) fun _ => 1)
    (Sum.elim (fun i => (-a i).toNat) fun _ => 0)).proj
  convert h using 1
  ext x
  simp only [Set.mem_setOf_eq, threshold, decide_eq_true_eq, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, one_mul, zero_mul, sum_const_zero, add_zero,
    Finset.univ_unique, sum_singleton]
  rw [sum_mul_eq_sub]
  have hc := Int.toNat_sub_toNat_neg c
  constructor
  · intro hlt
    refine ⟨fun _ => ∑ i, (-a i).toNat * x i + c.toNat - ∑ i, (a i).toNat * x i -
      (-c).toNat - 1, ?_⟩
    dsimp only
    omega
  · rintro ⟨y, hy⟩
    omega

/-- Remainder sets are semilinear. -/
lemma isSemilinearSet_remainder (a : X → ℤ) (c : ℤ) (m : ℕ) :
    IsSemilinearSet {x : X → ℕ | remainder a c m x = true} := by
  have h := (isSemilinearSet_linEq (κ := X ⊕ Bool) (-c).toNat c.toNat
    (Sum.elim (fun i => (a i).toNat) fun b => if b then m else 0)
    (Sum.elim (fun i => (-a i).toNat) fun b => if b then 0 else m)).proj
  convert h using 1
  ext x
  simp only [Set.mem_setOf_eq, remainder, decide_eq_true_eq, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, Fintype.sum_bool, if_true, Bool.false_eq_true, if_false,
    zero_mul, add_zero, zero_add]
  rw [Int.modEq_iff_dvd, sum_mul_eq_sub]
  push_cast
  have hc := Int.toNat_sub_toNat_neg c
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨fun b => if b then k.toNat else (-k).toNat, ?_⟩
    simp only [if_true, Bool.false_eq_true, if_false]
    have hk' := Int.toNat_sub_toNat_neg k
    zify
    linear_combination -hc + (m : ℤ) * hk' - hk
  · rintro ⟨y, hy⟩
    refine ⟨(y true : ℤ) - y false, ?_⟩
    have hy' := congrArg (fun z : ℕ => (z : ℤ)) hy
    push_cast at hy'
    linear_combination -hy' - hc

end Crn
