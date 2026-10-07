import Epidemics.ReedFrost

/-! # Finite-probability helpers for EPI-2

Elementary facts about `Dynamics.Distribution` used by the subcritical percolation proofs:
monotonicity, complements and the union bound for `prob`; Markov's inequality on an exponential
moment; and two ways of conditioning an independent product on one coordinate (an arbitrary
coordinate, through `Function.update`, and the first coordinate of `Fin (m + 1)`, through
`Fin.cons`). They are stated for any `Distribution` and are candidates to move to `dynamics/`.
-/

namespace Epidemics
open Finset Dynamics

variable {α ι β : Type*} [Fintype α] [Fintype ι] [Fintype β]

section Prob
variable (q : Distribution α)

lemma prob_congr {s t : α → Prop} (h : ∀ a, s a ↔ t a) : q.prob s = q.prob t := by
  rw [funext fun a => propext (h a)]

lemma prob_mono {s t : α → Prop} (h : ∀ a, s a → t a) : q.prob s ≤ q.prob t := by
  unfold Distribution.prob
  refine q.expect_mono fun a => ?_
  by_cases hs : s a
  · rw [if_pos hs, if_pos (h a hs)]
  · rw [if_neg hs]
    split <;> norm_num

lemma prob_eq_one {s : α → Prop} (h : ∀ a, s a) : q.prob s = 1 := by
  unfold Distribution.prob
  simp only [h, if_true]
  exact q.expect_const 1

lemma prob_eq_zero {s : α → Prop} (h : ∀ a, ¬s a) : q.prob s = 0 := by
  unfold Distribution.prob
  simp only [h, if_false]
  exact q.expect_const 0

/-- An event and its complement have total probability one. -/
lemma prob_add_prob_not (s : α → Prop) : q.prob s + q.prob (fun a => ¬s a) = 1 := by
  unfold Distribution.prob
  rw [← Distribution.expect_add, ← q.expect_const 1]
  congr 1
  funext a
  by_cases hs : s a
  · rw [if_pos hs, if_neg (not_not_intro hs)]
    norm_num
  · rw [if_neg hs, if_pos hs]
    norm_num

/-- **Union bound.** -/
lemma prob_exists_le_sum (s : ι → α → Prop) :
    q.prob (fun a => ∃ i, s i a) ≤ ∑ i, q.prob (s i) := by
  classical
  unfold Distribution.prob
  rw [← Distribution.expect_sum]
  refine q.expect_mono fun a => ?_
  have hnn (i : ι) : (0 : ℝ) ≤ if s i a then 1 else 0 := by split <;> norm_num
  by_cases h : ∃ i, s i a
  · obtain ⟨i, hi⟩ := h
    rw [if_pos ⟨i, hi⟩]
    calc (1 : ℝ) = if s i a then 1 else 0 := by rw [if_pos hi]
      _ ≤ ∑ j, if s j a then 1 else 0 :=
        single_le_sum (f := fun j => if s j a then (1 : ℝ) else 0) (fun j _ => hnn j)
          (mem_univ i)
  · rw [if_neg h]
    exact sum_nonneg fun i _ => hnn i

/-- **Markov's inequality on an exponential moment**: for `t ≥ 0`,
`P(k ≤ X) ≤ 𝔼[exp (t X)] · exp (-(t k))`. -/
lemma prob_le_expect_exp (X : α → ℝ) {t : ℝ} (ht : 0 ≤ t) (k : ℝ) :
    q.prob (fun a => k ≤ X a) ≤
      q.expect (fun a => Real.exp (t * X a)) * Real.exp (-(t * k)) := by
  unfold Distribution.prob
  have hpt (a : α) :
      (if k ≤ X a then (1 : ℝ) else 0) ≤ Real.exp (-(t * k)) * Real.exp (t * X a) := by
    rw [← Real.exp_add]
    split_ifs with h
    · exact Real.one_le_exp (by nlinarith)
    · exact (Real.exp_pos _).le
  calc q.expect (fun a => if k ≤ X a then (1 : ℝ) else 0)
      ≤ q.expect (fun a => Real.exp (-(t * k)) * Real.exp (t * X a)) := q.expect_mono hpt
    _ = _ := by rw [Distribution.expect_mul, mul_comm]

end Prob

section Independent

/-- **Conditioning an independent product on one coordinate**: the expectation is the average,
over the value `b` of coordinate `i`, of the expectation with that coordinate set to `b`. -/
lemma independent_expect_update [DecidableEq ι] (q : ι → Distribution β) (i : ι)
    (f : (ι → β) → ℝ) :
    (Distribution.independent q).expect f =
      ∑ b, (q i).weight b *
        (Distribution.independent q).expect (fun x => f (Function.update x i b)) := by
  set e := Equiv.funSplitAt i β with he
  have hi (b : β) (r : {j // j ≠ i} → β) : e.symm (b, r) i = b := by simp [he]
  have hj (b : β) (r : {j // j ≠ i} → β) (j : {j // j ≠ i}) : e.symm (b, r) j = r j := by
    simp [he, j.2]
  have hW (b : β) (r : {j // j ≠ i} → β) :
      ∏ j, (q j).weight (e.symm (b, r) j) =
        (q i).weight b * ∏ j : {j // j ≠ i}, (q j).weight (r j) := by
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ i, hi]
    simp only [hj]
  have hU (b b' : β) (r : {j // j ≠ i} → β) :
      Function.update (e.symm (b, r)) i b' = e.symm (b', r) := by
    funext j
    by_cases hji : j = i
    · subst hji
      rw [Function.update_self, hi]
    · rw [Function.update_of_ne hji]
      exact (hj b r ⟨j, hji⟩).trans (hj b' r ⟨j, hji⟩).symm
  have hsum (F : (ι → β) → ℝ) : ∑ x, F x = ∑ b, ∑ r, F (e.symm (b, r)) := by
    rw [← Fintype.sum_prod_type']
    exact (e.symm.sum_comp F).symm
  simp only [Distribution.expect, Distribution.independent]
  rw [hsum]
  simp_rw [hsum (fun x => (∏ j, (q j).weight (x j)) * f (Function.update x i _)), hU, hW]
  refine sum_congr rfl fun b _ => ?_
  have hb : ∑ c, ∑ r, (q i).weight c * (∏ j : {j // j ≠ i}, (q j).weight (r j)) *
        f (e.symm (b, r)) =
      ∑ r, (∏ j : {j // j ≠ i}, (q j).weight (r j)) * f (e.symm (b, r)) := by
    simp_rw [mul_assoc, ← mul_sum]
    rw [← sum_mul, (q i).sum_one, one_mul]
  rw [hb, mul_sum]
  exact sum_congr rfl fun r _ => by ring

/-- **Conditioning on the first coordinate**: an i.i.d. product over `Fin (m + 1)` is the
average, over the first coordinate `b`, of the product over `Fin m` with `b` prepended. -/
lemma independent_expect_fin_succ {m : ℕ} (q : Distribution β) (f : (Fin (m + 1) → β) → ℝ) :
    (Distribution.independent fun _ : Fin (m + 1) => q).expect f =
      ∑ b, q.weight b *
        (Distribution.independent fun _ : Fin m => q).expect (fun r => f (Fin.cons b r)) := by
  simp only [Distribution.expect, Distribution.independent, mul_sum]
  rw [← (Fin.consEquiv fun _ => β).sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun b _ => sum_congr rfl fun r _ => ?_
  simp [Fin.consEquiv, Fin.prod_univ_succ, mul_assoc]

/-- Expectation under a Bernoulli coin. -/
lemma bernoulli_expect (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (f : Bool → ℝ) :
    (bernoulli p h0 h1).expect f = p * f true + (1 - p) * f false := by
  simp [Distribution.expect, bernoulli]

/-- Conditioning the percolation coins on the coin of one pair. -/
lemma coins_prob_split [DecidableEq α] (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (e : α)
    (s : (α → Bool) → Prop) :
    (Distribution.independent fun _ : α => bernoulli p h0 h1).prob s =
      p * (Distribution.independent fun _ : α => bernoulli p h0 h1).prob
          (fun ω => s (Function.update ω e true)) +
        (1 - p) * (Distribution.independent fun _ : α => bernoulli p h0 h1).prob
          (fun ω => s (Function.update ω e false)) := by
  unfold Distribution.prob
  rw [independent_expect_update _ e, Fintype.sum_bool]
  simp [bernoulli]

end Independent

end Epidemics
