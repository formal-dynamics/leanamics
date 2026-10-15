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

/-- An observable bounded by `1` that is strictly below `1` at a point of positive weight has
expectation strictly below `1` (it replaces `Moran.expect_lt_one` and `Voter.expect_lt_one`). -/
theorem expect_lt_one (p : Distribution α) (f : α → ℝ) (hf : ∀ a, f a ≤ 1) (b : α)
    (hb : 0 < p.weight b) (hfb : f b < 1) : p.expect f < 1 := by
  calc p.expect f < p.expect (fun _ => 1) :=
        sum_lt_sum (fun a _ => mul_le_mul_of_nonneg_left (hf a) (p.nonneg a))
          ⟨b, mem_univ b, mul_lt_mul_of_pos_left hfb hb⟩
    _ = 1 := p.expect_const 1

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

/-- **Monotonicity of probability**: a larger event has a larger probability. A set
inclusion `h : A ⊆ B` can be passed directly for the events `(· ∈ A)` and `(· ∈ B)`. -/
lemma prob_mono (p : Distribution α) {s t : α → Prop} (h : ∀ ⦃a⦄, s a → t a) :
    p.prob s ≤ p.prob t := by
  classical
  unfold prob
  refine p.expect_mono fun a => ?_
  by_cases ha : s a
  · simp [ha, h ha]
  · by_cases hb : t a <;> simp [ha, hb]

/-- `prob` computed with any decidability instance for the event. -/
lemma prob_eq_expect (p : Distribution α) (s : α → Prop) [DecidablePred s] :
    p.prob s = p.expect fun a => if s a then 1 else 0 := by
  unfold prob
  congr 1
  funext a
  congr

/-! ### Events -/

/-- Events that agree pointwise have the same probability. -/
lemma prob_congr (p : Distribution α) {s t : α → Prop} (h : ∀ a, s a ↔ t a) :
    p.prob s = p.prob t :=
  le_antisymm (p.prob_mono fun a => (h a).1) (p.prob_mono fun a => (h a).2)

/-- A sure event has probability one. -/
lemma prob_eq_one (p : Distribution α) {s : α → Prop} (h : ∀ a, s a) : p.prob s = 1 := by
  classical
  simp [p.prob_eq_expect, h]

/-- An impossible event has probability zero. -/
lemma prob_eq_zero (p : Distribution α) {s : α → Prop} (h : ∀ a, ¬s a) : p.prob s = 0 := by
  classical
  simp [p.prob_eq_expect, h, expect]

/-- **Complement rule**: `P(¬s) = 1 - P(s)`. -/
lemma prob_not (p : Distribution α) (s : α → Prop) :
    p.prob (fun a => ¬s a) = 1 - p.prob s := by
  classical
  rw [p.prob_eq_expect, p.prob_eq_expect, ← p.expect_const 1, ← expect_sub]
  congr 1
  funext a
  by_cases hs : s a <;> simp [hs]

/-- If `t` holds wherever `s` fails, then `1 - P(s) ≤ P(t)`. -/
lemma one_sub_prob_le_prob (p : Distribution α) {s t : α → Prop} (h : ∀ a, ¬s a → t a) :
    1 - p.prob s ≤ p.prob t := by
  rw [← prob_not]
  exact p.prob_mono h

/-- **Union bound** for two events. -/
lemma prob_or_le (p : Distribution α) (s t : α → Prop) :
    p.prob (fun a => s a ∨ t a) ≤ p.prob s + p.prob t := by
  classical
  rw [p.prob_eq_expect, p.prob_eq_expect, p.prob_eq_expect, ← expect_add]
  refine p.expect_mono fun a => ?_
  by_cases hs : s a <;> by_cases ht : t a <;> simp [hs, ht]

/-- **Union bound** over a finite family of events. -/
lemma prob_exists_le_sum {κ : Type*} (p : Distribution α) (I : Finset κ) (s : κ → α → Prop) :
    p.prob (fun a => ∃ i ∈ I, s i a) ≤ ∑ i ∈ I, p.prob (s i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [p.prob_eq_zero]
  | insert i I hi ih =>
    rw [sum_insert hi]
    calc p.prob (fun a => ∃ j ∈ insert i I, s j a)
        = p.prob (fun a => s i a ∨ ∃ j ∈ I, s j a) := p.prob_congr fun a => by simp
      _ ≤ p.prob (s i) + p.prob (fun a => ∃ j ∈ I, s j a) := p.prob_or_le _ _
      _ ≤ p.prob (s i) + ∑ j ∈ I, p.prob (s j) := by linarith

/-- **Inclusion–exclusion** for two events, through their complements. -/
lemma prob_and_eq (p : Distribution α) (s t : α → Prop) :
    p.prob (fun a => s a ∧ t a) =
      1 - p.prob (fun a => ¬s a) - p.prob (fun a => ¬t a) +
        p.prob (fun a => ¬s a ∧ ¬t a) := by
  classical
  rw [p.prob_eq_expect, p.prob_eq_expect, p.prob_eq_expect, p.prob_eq_expect,
    ← p.expect_const 1, ← expect_sub, ← expect_sub, ← expect_add]
  congr 1
  funext a
  by_cases hs : s a <;> by_cases ht : t a <;> simp [hs, ht]

/-- **Markov's inequality**: `P(c ≤ X) ≤ 𝔼X / c` for `X ≥ 0` and `c > 0`. The uniform case is
`avg_markov`. -/
lemma prob_le_expect_div (p : Distribution α) (X : α → ℝ) (hX : ∀ a, 0 ≤ X a) {c : ℝ}
    (hc : 0 < c) : p.prob (fun a => c ≤ X a) ≤ p.expect X / c := by
  classical
  rw [p.prob_eq_expect, le_div_iff₀ hc, mul_comm, ← expect_mul]
  refine p.expect_mono fun a => ?_
  split_ifs with h
  · linarith
  · linarith [hX a]

/-- **Markov's inequality on the square** (the core of Chebyshev's inequality):
`P(c ≤ |Z|) ≤ 𝔼[Z²] / c²` for `c > 0`. -/
lemma markov_sq (p : Distribution α) (Z : α → ℝ) {c : ℝ} (hc : 0 < c) :
    p.prob (fun a => c ≤ |Z a|) ≤ p.expect (fun a => Z a ^ 2) / c ^ 2 :=
  calc p.prob (fun a => c ≤ |Z a|) = p.prob (fun a => c ^ 2 ≤ Z a ^ 2) :=
        p.prob_congr fun a => by rw [sq_le_sq, abs_of_pos hc]
    _ ≤ _ := p.prob_le_expect_div _ (fun a => sq_nonneg (Z a)) (pow_pos hc 2)

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

/-- A biased coin: `true` with probability `p`. -/
noncomputable def bernoulli (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : Distribution Bool where
  weight b := if b then p else 1 - p
  nonneg b := by cases b <;> simp [h0, h1]
  sum_one := by simp

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

/-- The probability of an event under `p.map f` is that of its preimage under `p`. -/
lemma prob_map (p : Distribution α) (f : α → β) (s : β → Prop) :
    (p.map f).prob s = p.prob (fun a => s (f a)) := by
  classical
  rw [prob_eq_expect, prob_eq_expect, map_expect]

/-- A point of positive weight is carried to its image with positive weight (it replaces
`Moran.map_weight_pos`). -/
lemma map_weight_pos (p : Distribution α) (f : α → β) (a : α) (ha : 0 < p.weight a) :
    0 < (p.map f).weight (f a) := by
  classical
  dsimp only [map]
  refine lt_of_lt_of_le ?_ (single_le_sum (fun x _ => ?_) (mem_univ a))
  · rw [if_pos rfl]
    exact ha
  · split
    · exact p.nonneg x
    · exact le_rfl

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
