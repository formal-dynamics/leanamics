import Crn.Condition

/-!
# Lemmas on finite distributions

Extensionality of `Dynamics.Distribution` (by weights or by expectations) and the
expectations of uniform, point, normalized and conditioned distributions.
-/

namespace Crn
open Dynamics Finset

variable {α : Type*} [Fintype α]

/-- Distributions with the same weights are equal. -/
lemma dist_ext {p q : Distribution α} (h : ∀ a, p.weight a = q.weight a) : p = q := by
  obtain ⟨wp, _, _⟩ := p
  obtain ⟨wq, _, _⟩ := q
  obtain rfl : wp = wq := funext h
  rfl

/-- The weight of `a` is the expectation of the indicator of `a`. -/
lemma weight_eq_expect [DecidableEq α] (p : Distribution α) (a : α) :
    p.weight a = p.expect fun b => if b = a then 1 else 0 := by
  simp [Distribution.expect]

/-- Distributions with the same expectations are equal. -/
lemma dist_ext_expect {p q : Distribution α} (h : ∀ f, p.expect f = q.expect f) : p = q := by
  classical
  exact dist_ext fun a => by rw [weight_eq_expect, weight_eq_expect, h]

/-- The probability of an event, as a sum of weights, for any decidability instance. -/
lemma prob_eq_sum (p : Distribution α) (E : α → Prop) [DecidablePred E] :
    p.prob E = ∑ a, if E a then p.weight a else 0 := by
  unfold Distribution.prob Distribution.expect
  refine sum_congr rfl fun a _ => ?_
  by_cases h : E a <;> simp [h]

/-- The probability of an event is the expectation of its indicator, for any decidability
instance. -/
lemma prob_eq_expect (p : Distribution α) (E : α → Prop) [DecidablePred E] :
    p.prob E = p.expect fun a => if E a then 1 else 0 := by
  unfold Distribution.prob Distribution.expect
  refine sum_congr rfl fun a _ => ?_
  by_cases h : E a <;> simp [h]

/-- Expectation of an observable vanishing off `E`, for any decidability instance. -/
lemma expect_ite (p : Distribution α) (E : α → Prop) [DecidablePred E] (f : α → ℝ) :
    p.expect (fun a => if E a then f a else 0) = ∑ a, if E a then p.weight a * f a else 0 := by
  unfold Distribution.expect
  refine sum_congr rfl fun a _ => ?_
  by_cases h : E a <;> simp [h]

/-- Expectation under normalized weights: `∑ w·f / ∑ w`. -/
lemma normalize_expect (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (h : ∑ a, w a ≠ 0) (f : α → ℝ) :
    (normalize w hw h).expect f = (∑ a, w a * f a) / ∑ a, w a := by
  simp only [Distribution.expect, normalize, sum_div]
  exact sum_congr rfl fun a _ => by ring

/-- Expectation under a conditioned distribution. -/
lemma condition_expect (p : Distribution α) (E : α → Prop) [DecidablePred E]
    (h : p.prob E ≠ 0) (f : α → ℝ) :
    (condition p E h).expect f = p.expect (fun a => if E a then f a else 0) / p.prob E := by
  unfold condition
  rw [normalize_expect]
  simp only [Distribution.prob, Distribution.expect]
  congr 1 <;> refine sum_congr rfl fun a _ => ?_ <;> by_cases hE : E a <;> simp [hE]

/-- Uniform expectation as a sum divided by the cardinality. -/
lemma uniform_expect_sum [Nonempty α] (f : α → ℝ) :
    (Distribution.uniform α).expect f = (∑ a, f a) / Fintype.card α := by
  rw [Distribution.uniform_expect, avg]

/-- Uniform probability as a counting ratio. -/
lemma uniform_prob [Nonempty α] (E : α → Prop) [DecidablePred E] :
    (Distribution.uniform α).prob E = (univ.filter E).card / Fintype.card α := by
  rw [prob_eq_sum, ← sum_filter]
  simp [Distribution.uniform, div_eq_mul_inv]

/-- Uniform expectation over a product, the first coordinate averaged first. -/
lemma uniform_prod_expect {β : Type*} [Fintype β] [Nonempty α] [Nonempty β]
    (f : α × β → ℝ) :
    (Distribution.uniform (α × β)).expect f =
      (∑ b, (Distribution.uniform α).expect fun a => f (a, b)) / Fintype.card β := by
  simp only [uniform_expect_sum, Fintype.card_prod, Fintype.sum_prod_type, ← sum_div]
  rw [sum_comm, div_div, Nat.cast_mul]

end Crn
