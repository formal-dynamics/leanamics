import Dynamics.Kernel

/-! # Synchronous weighted voter dynamics (Section 2.1)

Each vertex independently samples one row of the stochastic matrix and copies
that neighbor's previous color. Colors need not be Boolean.
-/

namespace Voter
open Finset Dynamics
variable {V C D : Type*} [Fintype V] [DecidableEq V]

/-- A configuration assigns a color to each vertex. -/
abbrev Config (V C : Type*) := V → C

/-- Simultaneous copying for a fixed vector of sampled neighbors. -/
def step (s : Config V C) (r : V → V) : Config V C := fun i => s (r i)

omit [Fintype V] [DecidableEq V] in
@[simp] lemma step_constant (c : C) (r : V → V) : step (fun _ => c) r = fun _ => c := rfl

omit [Fintype V] [DecidableEq V] in
/-- Color projections commute with every realization of a round. -/
lemma step_project (f : C → D) (s : Config V C) (r : V → V) :
    step (f ∘ s) r = f ∘ step s r := rfl

/-- Expected observable after independently sampling one neighbor per vertex. -/
noncomputable def round (H : Kernel V) (s : Config V C) (f : Config V C → ℝ) : ℝ :=
  (Distribution.independent H).expect (fun r => f (step s r))

/-- The configuration transition kernel is the pushforward of independent sampling. -/
noncomputable def transition [Fintype C] (H : Kernel V) : Kernel (Config V C) :=
  fun s => (Distribution.independent H).map (step s)

lemma transition_apply [Fintype C] (H : Kernel V) (s : Config V C)
    (f : Config V C → ℝ) : (transition H).apply f s = round H s f :=
  Distribution.map_expect _ _ _

/-- One coordinate has precisely the distribution of its sampled neighbor. -/
lemma round_eval (H : Kernel V) (s : Config V C) (i : V) (f : C → ℝ) :
    round H s (fun t => f (t i)) = (H i).expect (fun j => f (s j)) := by
  classical
  exact Distribution.independent_expect_eval H i (fun j => f (s j))

/-- Product observables factor over the independently updated vertices. -/
lemma round_prod (H : Kernel V) (s : Config V C) (f : V → C → ℝ) :
    round H s (fun t => ∏ i, f i (t i)) = ∏ i, (H i).expect (fun j => f i (s j)) := by
  classical
  exact Distribution.independent_expect_prod H (fun i j => f i (s j))

/-- The product formula for the probability of a configuration (Section 2.1). -/
lemma transition_product [Fintype C] (H : Kernel V) (s t : Config V C) :
    (transition H s).weight t = ∏ i, (H i).prob (fun j => s j = t i) := by
  classical
  have h (r : V → V) : (if step s r = t then (1 : ℝ) else 0) =
      ∏ i, if s (r i) = t i then 1 else 0 := by
    simp [step, funext_iff, Finset.prod_boole]
  calc
    (transition H s).weight t = round H s (fun u => if u = t then 1 else 0) := by
      simp only [transition, Distribution.map, round, Distribution.expect, mul_ite, mul_one, mul_zero]
      apply sum_congr rfl
      intro r _
      by_cases hr : step s r = t <;> simp [hr]
    _ = round H s (fun u => ∏ i, if u i = t i then 1 else 0) := by
      unfold round
      congr 1
      funext r
      exact h r
    _ = _ := round_prod H s (fun i c => if c = t i then 1 else 0)

/-- The Boolean white/black factorization displayed in Section 2.1. -/
lemma transition_product_bool (H : Kernel V) (s t : Config V Bool) :
    (transition H s).weight t = ∏ i,
      if t i then (H i).expect (fun j => if s j then 1 else 0)
      else 1 - (H i).expect (fun j => if s j then 1 else 0) := by
  classical
  rw [transition_product]
  apply prod_congr rfl
  intro i _
  cases ht : t i
  · simp only [Bool.false_eq_true, if_false]
    calc
      (H i).prob (fun j => s j = false) =
          (H i).expect (fun j => 1 - (if s j then 1 else 0)) := by
        unfold Distribution.prob
        congr 1
        funext j
        cases hsj : s j <;> simp [hsj]
      _ = _ := by rw [Distribution.expect_sub, Distribution.expect_const]
  · simp only [if_true]
    unfold Distribution.prob
    congr 1
    funext j
    cases hsj : s j <;> simp [hsj]

/-- Weighted color mass for any real-valued color observable. -/
noncomputable def mass (p : Distribution V) (f : C → ℝ) (s : Config V C) : ℝ :=
  p.expect (fun i => f (s i))

/-- Stationary mass is preserved by one round, without graph assumptions (Lemma 2.3). -/
lemma round_mass (H : Kernel V) (p : Distribution V) (hp : H.Stationary p)
    (f : C → ℝ) (s : Config V C) : round H s (mass p f) = mass p f s := by
  classical
  change (Distribution.independent H).expect
    (fun r => ∑ i, p.weight i * f (s (r i))) = p.expect (fun i => f (s i))
  rw [Distribution.expect_sum]
  simp_rw [Distribution.expect_mul]
  have he (i : V) : (Distribution.independent H).expect (fun r => f (s (r i))) =
      (H i).expect (fun j => f (s j)) :=
    Distribution.independent_expect_eval H i (fun j => f (s j))
  simp_rw [he]
  exact H.stationary_expect p hp (fun i => f (s i))

/-- Iterated stationary-mass preservation (Lemma 2.3). -/
lemma iterate_mass [Fintype C] (H : Kernel V) (p : Distribution V) (hp : H.Stationary p)
    (f : C → ℝ) (n : ℕ) (s : Config V C) :
    (transition H).iterate n (mass p f) s = mass p f s := by
  apply congrFun ((transition H).iterate_invariant (f := mass p f) ?_ n) s
  funext t
  rw [transition_apply, round_mass H p hp]

end Voter
