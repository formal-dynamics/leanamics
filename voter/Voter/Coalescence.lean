import Voter.Absorption
import Dynamics.Uniform

/-! # Coalescing random walks and consensus time on the complete graph (VOT-3)

Hassin–Peleg §2.4 and Survey Theorems 6–7, on the complete graph with self-loops
(Wright–Fisher sampling): in every round each vertex copies the colour of a uniformly random
vertex, itself included.

*Duality.* After rounds `r₁, …, r_T` the colour of `u` is `s (r₁ (r₂ (⋯ (r_T u))))`: running
the voter forward reads the initial colours through the backward map `r₁ ∘ ⋯ ∘ r_T`, whose
point images are coalescing random walks. Consensus holds as soon as the backward map is
constant.

*Time.* Backward walks from two distinct vertices have not met after `T` rounds with
probability exactly `(1 - 1/n)^T`. A union bound over the walks that must meet the walk of a
fixed vertex gives consensus within `2 n log n` rounds with probability at least `1 - 1/n`.
-/

namespace Voter
open Dynamics Finset

variable {V C : Type*} [Fintype V] [DecidableEq V]

/-- Run the synchronous voter along a list of rounds, first round first. -/
def runRounds (s : Config V C) : List (V → V) → Config V C
  | [] => s
  | r :: l => runRounds (step s r) l

/-- The backward map `r₁ ∘ r₂ ∘ ⋯ ∘ r_T` of the rounds `[r₁, …, r_T]`. -/
def backward (l : List (V → V)) : V → V := l.foldr (fun r g => r ∘ g) id

/-- Nonconsensus indicator for an arbitrary colour type. -/
noncomputable def disagreement (s : Config V C) : ℝ := by
  classical
  exact if ∃ c, s = fun _ => c then 0 else 1

/-- Wright–Fisher sampling: every vertex picks a uniformly random vertex, itself included. -/
noncomputable def wfKernel (V : Type*) [Fintype V] [Nonempty V] : Kernel V :=
  fun _ => Distribution.uniform V

/-- **Duality.** Running the voter forward reads the initial colours through the backward map. -/
theorem runRounds_eq_comp (s : Config V C) (l : List (V → V)) :
    runRounds s l = s ∘ backward l := by
  sorry

/-- A constant backward map forces consensus. -/
theorem disagreement_runRounds_eq_zero [Nonempty V] (s : Config V C) (l : List (V → V))
    (h : ∀ u v, backward l u = backward l v) : disagreement (runRounds s l) = 0 := by
  sorry

/-- For Boolean colours, `disagreement` is the survival indicator of `Voter.Absorption`. -/
theorem disagreement_eq_survival (s : Config V Bool) : disagreement s = survival s := by
  sorry

/-- The configuration kernel of Wright–Fisher sampling is the average over `T` i.i.d.
uniform rounds. -/
theorem iterate_wfKernel_eq_expList [Nonempty V] [Fintype C] (f : Config V C → ℝ) (T : ℕ)
    (s : Config V C) :
    (transition (wfKernel V)).iterate T f s =
      expList (V → V) T (fun l => f (runRounds s l)) := by
  sorry

/-- **Meeting probability.** Backward walks from distinct vertices have not met after `T`
rounds with probability exactly `(1 - 1/n)^T`. -/
theorem expList_backward_ne {u v : V} (huv : u ≠ v) (T : ℕ) :
    expList (V → V) T (fun l => if backward l u = backward l v then 0 else 1) =
      (1 - 1 / (Fintype.card V : ℝ)) ^ T := by
  sorry

/-- **Consensus time, union bound.** -/
theorem iterate_disagreement_le [Nonempty V] [Fintype C] (s : Config V C) (T : ℕ) :
    (transition (wfKernel V)).iterate T disagreement s ≤
      ((Fintype.card V : ℝ) - 1) * (1 - 1 / (Fintype.card V : ℝ)) ^ T := by
  sorry

/-- **Consensus within `2 n log n` rounds with probability at least `1 - 1/n`.** -/
theorem voter_consensus_whp [Nonempty V] [Fintype C] (s : Config V C) (T : ℕ)
    (hT : 2 * (Fintype.card V : ℝ) * Real.log (Fintype.card V) ≤ (T : ℝ)) :
    (transition (wfKernel V)).iterate T disagreement s ≤ 1 / (Fintype.card V : ℝ) := by
  sorry

end Voter
