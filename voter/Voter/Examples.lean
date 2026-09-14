import Voter.Corollaries

/-! # Checked examples and the bipartite two-cycle -/
namespace Voter.Examples
open Dynamics Finset

/-- The triangle is connected and nonbipartite. -/
abbrev triangle : SimpleGraph (Fin 3) := ⊤

lemma triangle_connected : triangle.Connected := SimpleGraph.connected_top

lemma triangle_nonbipartite : ¬ triangle.Colorable 2 := by
  intro h
  have hh := h.card_le_of_pairwise_adj (fun i : Fin 3 => i) (fun _ _ hij => hij)
  norm_num at hh

lemma triangle_regular : ∀ v, triangle.degree v = 2 := by decide

/-- One initially white vertex on the triangle wins with probability one third. -/
lemma triangle_one_white :
    eventualColor (uniformNeighbor triangle (graph_degree_pos triangle triangle_connected triangle_nonbipartite))
      true (fun i => decide (i = 0)) = 1 / 3 := by
  rw [regular_consensus_probability triangle triangle_connected triangle_nonbipartite 2 triangle_regular]
  norm_num [Fin.sum_univ_succ, Finset.filter_eq', Fintype.card_fin]

/-- A nonuniform distribution assigning weights one third and two thirds. -/
noncomputable def biased : Distribution Bool where
  weight b := if b then 2 / 3 else 1 / 3
  nonneg b := by cases b <;> norm_num
  sum_one := by norm_num [Fintype.sum_bool]

/-- A nonuniform stochastic matrix whose rows both equal `biased`. -/
noncomputable def biasedKernel : Kernel Bool := fun _ => biased

lemma biased_stationary : biasedKernel.Stationary biased := by
  intro b
  simp only [biasedKernel, ← sum_mul, biased.sum_one, one_mul]

/-- The invariant has value two thirds on the configuration with only `true` white. -/
lemma biased_mass : whiteMass biased (fun b => b) = 2 / 3 := by
  norm_num [whiteMass, mass, Distribution.expect, biased, Fintype.sum_bool]

example (n : ℕ) : (transition biasedKernel).iterate n (whiteMass biased) (fun b => b) = 2 / 3 := by
  rw [show whiteMass biased = mass biased (fun b : Bool => if b then 1 else 0) from rfl,
    iterate_mass biasedKernel biased biased_stationary]
  exact biased_mass

example {V : Type*} [Fintype V] [DecidableEq V] (H : Kernel V) (c : Bool)
    (f : Config V Bool → ℝ) : (transition H).apply f (fun _ => c) = f (fun _ => c) :=
  transition_constant H c f

example {V : Type*} [Fintype V] [DecidableEq V] (s : Config V (Fin 3)) (r : V → V) :
    step (colorIndicator (0 : Fin 3) ∘ s) r = colorIndicator (0 : Fin 3) ∘ step s r :=
  step_project _ _ _

example {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (H : Kernel V) :
    eventualColor H (2 : Fin 3) (fun _ => 2) = 1 := eventualColor_constant H 2

/-- On the two-vertex graph, the only neighbor of a Boolean vertex is its complement. -/
lemma twoVertex_unique_neighbor (r : Bool → Bool) (h : ∀ b, b ≠ r b) : r = Bool.not := by
  funext b
  cases b <;> specialize h <;> cases hr : r _ <;> simp_all

/-- The alternating coloring flips in one round. -/
lemma twoVertex_flip : step (fun b : Bool => b) Bool.not = Bool.not := rfl

/-- It returns after two rounds, so connectedness alone cannot force consensus. -/
lemma twoVertex_cycle : step (step (fun b : Bool => b) Bool.not) Bool.not = (fun b => b) := by
  funext b
  cases b <;> rfl

lemma twoVertex_never_consensus : ¬ (∃ c, (fun b : Bool => b) = fun _ => c) ∧
    ¬ (∃ c, Bool.not = fun _ => c) := by
  constructor
  · rintro ⟨c, h⟩
    have hbad : (false : Bool) = true := (congrFun h false).trans (congrFun h true).symm
    cases hbad
  · rintro ⟨c, h⟩
    have hbad : (false : Bool) = true := (congrFun h true).trans (congrFun h false).symm
    cases hbad

end Voter.Examples
