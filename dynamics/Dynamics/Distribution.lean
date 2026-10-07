import Dynamics.Equivalence

/-!
# Normalized finite distributions

Real weights make expectations finite sums. Unlike `avg`, a normalized distribution
cannot exist on an empty type. Uniform expectations retain their old empty-type convention.
-/

namespace Dynamics
open Finset

/-- Nonnegative real weights with total mass one. -/
structure Distribution (α : Type*) [Fintype α] where
  weight : α → ℝ
  nonneg : ∀ a, 0 ≤ weight a
  sum_one : ∑ a, weight a = 1

namespace Distribution
variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]

/-- Expectation of a real observable. -/
noncomputable def expect (p : Distribution α) (f : α → ℝ) : ℝ :=
  ∑ a, p.weight a * f a

/-- Probability of an event. -/
noncomputable def prob (p : Distribution α) (s : α → Prop) : ℝ := by
  classical
  exact p.expect fun a => if s a then 1 else 0

@[simp] lemma expect_const (p : Distribution α) (c : ℝ) :
    p.expect (fun _ => c) = c := by
  simp [expect, ← sum_mul, p.sum_one]

lemma expect_nonneg (p : Distribution α) {f : α → ℝ} (h : ∀ a, 0 ≤ f a) :
    0 ≤ p.expect f := sum_nonneg fun a _ => mul_nonneg (p.nonneg a) (h a)

lemma expect_mono (p : Distribution α) {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    p.expect f ≤ p.expect g :=
  sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (p.nonneg a)

lemma expect_add (p : Distribution α) (f g : α → ℝ) :
    p.expect (fun a => f a + g a) = p.expect f + p.expect g := by
  simp [expect, mul_add, sum_add_distrib]

lemma expect_sub (p : Distribution α) (f g : α → ℝ) :
    p.expect (fun a => f a - g a) = p.expect f - p.expect g := by
  simp [expect, mul_sub, sum_sub_distrib]

lemma expect_mul (p : Distribution α) (c : ℝ) (f : α → ℝ) :
    p.expect (fun a => c * f a) = c * p.expect f := by
  simp [expect, ← mul_sum, mul_left_comm]

lemma expect_sum (p : Distribution α) (f : ι → α → ℝ) :
    p.expect (fun a => ∑ i, f i a) = ∑ i, p.expect (f i) := by
  simp only [expect, mul_sum]
  exact sum_comm

lemma prob_nonneg (p : Distribution α) (s : α → Prop) : 0 ≤ p.prob s := by
  classical
  exact p.expect_nonneg fun a => by split <;> norm_num

lemma prob_le_one (p : Distribution α) (s : α → Prop) : p.prob s ≤ 1 := by
  classical
  calc p.prob s ≤ p.expect (fun _ => 1) := p.expect_mono fun a => by split <;> norm_num
       _ = 1 := p.expect_const 1

/-- `prob` computed with any decidability instance for the event. -/
lemma prob_eq_expect (p : Distribution α) (s : α → Prop) [DecidablePred s] :
    p.prob s = p.expect fun a => if s a then 1 else 0 := by
  unfold prob
  congr 1
  funext a
  congr

/-- Uniform distribution, available precisely when the sample type is nonempty. -/
noncomputable def uniform (α : Type*) [Fintype α] [Nonempty α] : Distribution α where
  weight _ := (Fintype.card α : ℝ)⁻¹
  nonneg _ := by positivity
  sum_one := by simp [ne_of_gt (card_cast_pos (α := α))]

lemma uniform_expect [Nonempty α] (f : α → ℝ) : (uniform α).expect f = avg f := by
  simp [expect, uniform, avg, ← sum_mul, div_eq_mul_inv, mul_comm]

/-- Point mass. -/
noncomputable def point (a : α) : Distribution α := by
  classical
  exact ⟨fun b => if b = a then 1 else 0,
    fun b => by split <;> norm_num, by simp⟩

@[simp] lemma point_expect (a : α) (f : α → ℝ) : (point a).expect f = f a := by
  classical
  simp [point, expect]

/-- Transport a distribution along a function, summing over its fibers. -/
noncomputable def map (p : Distribution α) (f : α → β) : Distribution β := by
  classical
  refine ⟨fun b => ∑ a, if f a = b then p.weight a else 0, ?_, ?_⟩
  · intro b
    exact sum_nonneg fun a _ => by split; exact p.nonneg a; rfl
  · rw [sum_comm]
    simpa using p.sum_one

lemma map_expect (p : Distribution α) (f : α → β) (g : β → ℝ) :
    (p.map f).expect g = p.expect (fun a => g (f a)) := by
  classical
  simp only [expect, map, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  simp

variable [DecidableEq ι]

/-- Independent product of a finite family of distributions. -/
noncomputable def independent (p : ι → Distribution α) : Distribution (ι → α) where
  weight x := ∏ i, (p i).weight (x i)
  nonneg x := prod_nonneg fun i _ => (p i).nonneg (x i)
  sum_one := by
    rw [← Fintype.prod_sum]
    simp only [(p _).sum_one, prod_const_one]

lemma independent_expect_prod (p : ι → Distribution α) (f : ι → α → ℝ) :
    (independent p).expect (fun x => ∏ i, f i (x i)) =
      ∏ i, (p i).expect (f i) := by
  simp only [expect, independent, ← prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => (p i).weight a * f i a)).symm

lemma independent_expect_eval (p : ι → Distribution α)
    (i : ι) (f : α → ℝ) : (independent p).expect (fun x => f (x i)) = (p i).expect f := by
  have h (x : ι → α) : f (x i) = ∏ j, if j = i then f (x j) else 1 := by simp
  simp_rw [h]
  rw [independent_expect_prod p (fun j a => if j = i then f a else 1)]
  rw [prod_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

end Distribution
end Dynamics
