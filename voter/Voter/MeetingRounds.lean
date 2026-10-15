import Voter.Model

/-! # Rounds composed on the left and on the right (VOT-6 helpers)

Generic facts behind the duality of `Voter/Meeting.lean`, for an arbitrary sampling kernel `H`:

* finite expectations and finite sums commute with `Kernel.iterate`;
* under `Distribution.independent H`, two distinct coordinates of a round are independent
  (`Distribution.independent_expect_pair`, in `Dynamics.Independent`);
* running the voter dynamics on maps from `id` composes the rounds on the right,
  `B ↦ B ∘ r`; composing them on the left, `W ↦ r ∘ W` (kernel `leftRounds H`), gives the same
  expectations at every finite time (`iterate_transition_eq_leftRounds`). This is the time
  reversal of i.i.d. rounds behind the duality with coalescing random walks.
-/

namespace Voter
open Dynamics Finset

section Kernel
variable {α β : Type*} [Fintype α] [Fintype β]

/-- Finite expectations commute with the iterated transition operator. -/
lemma kernel_iterate_expect (K : Kernel α) (p : Distribution β) (g : β → α → ℝ) (n : ℕ)
    (a : α) :
    K.iterate n (fun b => p.expect fun r => g r b) a = p.expect fun r => K.iterate n (g r) a := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    have hfun : K.iterate n (fun b => p.expect fun r => g r b) =
        fun c => p.expect fun r => K.iterate n (g r) c := funext ih
    simp only [Kernel.iterate_succ, Kernel.apply]
    rw [hfun]
    simp only [Distribution.expect, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun c _ => by ring

/-- Finite sums commute with the iterated transition operator. -/
lemma kernel_iterate_finset_sum {ι : Type*} (K : Kernel α) (s : Finset ι) (g : ι → α → ℝ)
    (n : ℕ) (a : α) :
    K.iterate n (fun b => ∑ i ∈ s, g i b) a = ∑ i ∈ s, K.iterate n (g i) a := by
  classical
  induction s using Finset.induction_on generalizing a with
  | empty => simpa using congrFun (K.iterate_const n 0) a
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [K.iterate_add n (g i) (fun b => ∑ j ∈ s, g j b)]
    simp only [ih]

end Kernel

section Rounds
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Rounds composed on the left: from the map `W`, one round `r` drawn from
`Distribution.independent H` leads to `r ∘ W`. -/
noncomputable def leftRounds (H : Kernel V) : Kernel (V → V) :=
  fun W => (Distribution.independent H).map fun r => r ∘ W

/-- **Time reversal of i.i.d. rounds.** The voter dynamics on maps started from `B` composes
the rounds on the right; its expectations are those of the rounds composed on the left, started
from `id` and read through `B`. -/
lemma iterate_transition_eq_leftRounds (H : Kernel V) (T : ℕ) (f : (V → V) → ℝ) (B : V → V) :
    (transition H).iterate T f B = (leftRounds H).iterate T (fun W => f (B ∘ W)) id := by
  induction T generalizing B with
  | zero => rfl
  | succ T ih =>
    rw [Kernel.iterate_succ, transition_apply]
    unfold round
    have hstep (r : V → V) : (transition H).iterate T f (step B r) =
        (leftRounds H).iterate T (fun W => f ((B ∘ r) ∘ W)) id := ih (step B r)
    simp_rw [hstep]
    rw [Kernel.iterate_add_time (leftRounds H) T 1]
    have happly : (leftRounds H).iterate 1 (fun W => f (B ∘ W)) =
        fun W => (Distribution.independent H).expect fun r => f (B ∘ (r ∘ W)) := by
      funext W
      simp only [Kernel.iterate_succ, Kernel.iterate_zero, Kernel.apply, leftRounds,
        Distribution.map_expect]
    rw [happly, kernel_iterate_expect]
    rfl

end Rounds

end Voter
