import Epidemics.CobraCoverRound

/-! # Independent coordinates of a uniform round (EPI-4, Corollary 1 and Theorem 3)

Under the uniform distribution on a finite dependent product `(u : V) → Ω u`, the coordinates
are independent: averages of products factor (`avg_pi_prod`), and an observable of one
coordinate has the same average as on that coordinate alone (`avg_pi_eval`). Consequently, the
number `N` of coordinates `u` whose value satisfies an event `X u` has the moment generating
function bound `E e^{-φ N} ≤ exp(-(1 - e^{-φ}) E N)` (`pi_count_mgf_le`), the computation (12) of
the paper, and `E N = ∑_u P(X u)` (`avg_pi_count`). `Choices G k` is the case
`Ω u = Fin k → G.neighborSet u` (`avg_choices_prod`, `bips_mgf_le`).
-/

namespace Epidemics
open Finset Dynamics Real

variable {V : Type*} [Fintype V] [DecidableEq V] {Ω : V → Type*} [∀ u, Fintype (Ω u)]

/-- **Independence over coordinates**: the average of a product of one-coordinate observables
is the product of their averages. -/
lemma avg_pi_prod (f : (u : V) → Ω u → ℝ) :
    avg (fun ω : (u : V) → Ω u => ∏ u, f u (ω u)) = ∏ u, avg (f u) := by
  unfold avg
  rw [← Fintype.prod_sum, Fintype.card_pi, Nat.cast_prod, ← Finset.prod_div_distrib]

/-- **Marginal of one coordinate.** -/
lemma avg_pi_eval [∀ u, Nonempty (Ω u)] (u : V) (g : Ω u → ℝ) :
    avg (fun ω : (w : V) → Ω w => g (ω u)) = avg g := by
  rw [← avg_fst_mul (δ := (i : {j // j ≠ u}) → Ω i) g]
  exact avg_equiv (Equiv.piSplitAt u Ω) (fun p => g p.1)

omit [DecidableEq V] [∀ u, Fintype (Ω u)] in
/-- The number of coordinates whose value satisfies its event, as a sum of indicators. -/
lemma card_filter_pi_eq_sum (X : (u : V) → Ω u → Prop) [∀ u, DecidablePred (X u)]
    (ω : (u : V) → Ω u) :
    ((univ.filter fun u => X u (ω u)).card : ℝ) = ∑ u, if X u (ω u) then (1 : ℝ) else 0 := by
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  split_ifs <;> simp

/-- **Expected count**: `E N = ∑_u P(X u)`. -/
lemma avg_pi_count [∀ u, Nonempty (Ω u)] (X : (u : V) → Ω u → Prop)
    [∀ u, DecidablePred (X u)] :
    avg (fun ω : (u : V) → Ω u => ((univ.filter fun u => X u (ω u)).card : ℝ)) =
      ∑ u, avg (fun a : Ω u => if X u a then (1 : ℝ) else 0) := by
  simp_rw [card_filter_pi_eq_sum, avg_sum]
  exact Finset.sum_congr rfl fun u _ => avg_pi_eval u (fun a => if X u a then (1 : ℝ) else 0)

/-- **Moment generating function of a count of independent events** (computation (12)):
`E e^{-φ N} = ∏_u (1 - (1 - e^{-φ}) P(X u)) ≤ exp(-(1 - e^{-φ}) E N)`. -/
theorem pi_count_mgf_le (X : (u : V) → Ω u → Prop) [∀ u, DecidablePred (X u)] (φ : ℝ) :
    avg (fun ω : (u : V) → Ω u => exp (-φ * ((univ.filter fun u => X u (ω u)).card : ℝ))) ≤
      exp (-(1 - exp (-φ)) *
        avg (fun ω : (u : V) → Ω u => ((univ.filter fun u => X u (ω u)).card : ℝ))) := by
  by_cases hne : ∀ u, Nonempty (Ω u)
  · let p : V → ℝ := fun u => avg (fun a : Ω u => if X u a then (1 : ℝ) else 0)
    have hp0 (u : V) : 0 ≤ p u := avg_nonneg fun a => by split_ifs <;> norm_num
    have hp1 (u : V) : p u ≤ 1 := by
      haveI := hne u
      exact (avg_le_avg fun a => by split_ifs <;> norm_num).trans_eq (avg_const (1 : ℝ))
    set a : ℝ := 1 - exp (-φ) with ha
    have ha1 : a ≤ 1 := by linarith [exp_nonneg (-φ)]
    have hfac0 (u : V) : 0 ≤ 1 - a * p u := by
      rcases le_total 0 a with h | h
      · nlinarith [hp1 u, hp0 u]
      · nlinarith [hp0 u]
    have hexp (ω : (u : V) → Ω u) :
        exp (-φ * ((univ.filter fun u => X u (ω u)).card : ℝ)) =
          ∏ u, exp (-φ * if X u (ω u) then (1 : ℝ) else 0) := by
      rw [card_filter_pi_eq_sum, Finset.mul_sum, exp_sum]
    have havg (u : V) : avg (fun b : Ω u => exp (-φ * if X u b then (1 : ℝ) else 0)) =
        1 - a * p u := by
      haveI := hne u
      exact avg_exp_bernoulli φ (X u)
    haveI := hne
    calc avg (fun ω : (u : V) → Ω u => exp (-φ * ((univ.filter fun u => X u (ω u)).card : ℝ)))
        = ∏ u, (1 - a * p u) := by
          simp_rw [hexp]
          rw [avg_pi_prod (fun u b => exp (-φ * if X u b then (1 : ℝ) else 0))]
          exact Finset.prod_congr rfl fun u _ => havg u
      _ ≤ ∏ u, exp (-(a * p u)) :=
          Finset.prod_le_prod (fun u _ => hfac0 u)
            (fun u _ => by linarith [add_one_le_exp (-(a * p u))])
      _ = exp (-(a * ∑ u, p u)) := by
          rw [← exp_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      _ = exp (-(1 - exp (-φ)) *
            avg (fun ω : (u : V) → Ω u => ((univ.filter fun u => X u (ω u)).card : ℝ))) := by
          rw [avg_pi_count X, ha, neg_mul]
  · push Not at hne
    obtain ⟨u, hu⟩ := hne
    haveI : IsEmpty ((u : V) → Ω u) := ⟨fun ω => hu.elim (ω u)⟩
    rw [avg_eq_zero_of_isEmpty]
    exact (exp_pos _).le

end Epidemics
