import Epidemics.KurtzDefs

/-! # Kurtz's law of large numbers for SIR: counting one step (CRN-2, helpers)

How one `step` of the uniformized SIR chain changes the counts `count c x`, and the total change
summed over all `Round`s. These are the combinatorial inputs of the drift identity
(`Epidemics.KurtzDrift`). Indicators are written `if c' = c then 1 else 0`.
-/

namespace Epidemics.Kurtz

open Finset

variable {N : ℕ}

/-- A count is a sum of indicators. -/
lemma count_eq_sum (c : Compartment) (x : Config N) :
    (count c x : ℝ) = ∑ v, if x v = c then (1 : ℝ) else 0 := by
  rw [Finset.sum_boole]
  rfl

/-- Moving the agent `v` to the compartment `c'` removes it from the count of its old compartment
and adds it to the count of `c'`. -/
lemma count_update (c c' : Compartment) (x : Config N) (v : Fin N) :
    (count c (Function.update x v c') : ℝ)
      = count c x - (if x v = c then 1 else 0) + (if c' = c then 1 else 0) := by
  rw [count_eq_sum, count_eq_sum, ← Finset.add_sum_erase _ _ (mem_univ v),
    ← Finset.add_sum_erase _ _ (mem_univ v)]
  have h : ∑ w ∈ univ.erase v, (if Function.update x v c' w = c then (1 : ℝ) else 0)
      = ∑ w ∈ univ.erase v, (if x w = c then (1 : ℝ) else 0) :=
    Finset.sum_congr rfl fun w hw ↦ by rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)]
  rw [h, Function.update_self]
  ring

/-- The counts after an infection round `(u, v, inl a)`: if `u` is infected and `v` susceptible,
one agent moves from `susceptible` to `infected`. -/
lemma count_step_inl (β γ : ℕ) (x : Config N) (u v : Fin N) (a : Fin β) (c : Compartment) :
    (count c (step β γ x (u, v, .inl a)) : ℝ) = count c x +
      if x u = .infected ∧ x v = .susceptible then
        (if Compartment.infected = c then 1 else 0) - (if Compartment.susceptible = c then 1 else 0)
      else 0 := by
  by_cases h : x u = .infected ∧ x v = .susceptible
  · simp only [step]
    rw [if_pos h, if_pos h, count_update, h.2]
    ring
  · simp only [step]
    rw [if_neg h, if_neg h, add_zero]

/-- The counts after a recovery round `(u, v, inr a)`: if `u` is infected, one agent moves from
`infected` to `recovered`. -/
lemma count_step_inr (β γ : ℕ) (x : Config N) (u v : Fin N) (a : Fin γ) (c : Compartment) :
    (count c (step β γ x (u, v, .inr a)) : ℝ) = count c x +
      if x u = .infected then
        (if Compartment.recovered = c then 1 else 0) - (if Compartment.infected = c then 1 else 0)
      else 0 := by
  by_cases h : x u = .infected
  · simp only [step]
    rw [if_pos h, if_pos h, count_update, h]
    ring
  · simp only [step]
    rw [if_neg h, if_neg h, add_zero]

/-- The total change of the count of `c` over all `N² (β + γ)` rounds: `β I S` infection rounds
move an agent from `S` to `I`, `γ N I` recovery rounds move one from `I` to `R`. -/
lemma sum_count_step (β γ : ℕ) (x : Config N) (c : Compartment) :
    ∑ ρ : Round N β γ, ((count c (step β γ x ρ) : ℝ) - count c x)
      = β * count .infected x * count .susceptible x *
          ((if Compartment.infected = c then 1 else 0) -
            (if Compartment.susceptible = c then 1 else 0))
        + γ * N * count .infected x *
          ((if Compartment.recovered = c then 1 else 0) -
            (if Compartment.infected = c then 1 else 0)) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_sum_type, count_step_inl, count_step_inr,
    add_sub_cancel_left, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, sum_add_distrib,
    ← mul_sum, ite_and, sum_ite_irrel, sum_ite]
  simp only [count]
  ring

/-- One step changes every count by at most one. -/
lemma abs_count_step_sub_le (β γ : ℕ) (x : Config N) (ρ : Round N β γ) (c : Compartment) :
    |(count c (step β γ x ρ) : ℝ) - count c x| ≤ 1 := by
  obtain ⟨u, v, a | a⟩ := ρ
  · rw [count_step_inl, add_sub_cancel_left]
    split_ifs <;> norm_num
  · rw [count_step_inr, add_sub_cancel_left]
    split_ifs <;> norm_num

/-- The number of rounds. -/
lemma card_round (β γ : ℕ) : (Fintype.card (Round N β γ) : ℝ) = N * (N * (β + γ)) := by
  simp [Fintype.card_prod, Fintype.card_sum]

end Epidemics.Kurtz
