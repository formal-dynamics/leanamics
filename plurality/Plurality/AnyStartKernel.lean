import Dynamics.DriftHitting
import Dynamics.Tail

/-!
# Hitting a set, then reaching an absorbing event

Facts about an arbitrary finite Markov kernel `K`, used to compose the two stages of binary
3-Majority from any configuration (`Plurality.majority3_any_start`):

* `hitProb_le_one`, `hitProb_mono`: the probability of hitting `B` within `t` steps is at most `1`
  and grows with `B`;
* `hitProb_sub_le_event` (**hit, then absorb**): if from every state of `B` the chain is in an
  absorbing event `P` after `T` steps with probability at least `1 - ε`, and `B` is hit within `t`
  steps with probability `h`, then the chain is in `P` at time `t + T` with probability at least
  `h - ε`. This is the strong Markov property at the hitting time of `B`, proved by induction on
  `t` through the recursion of `hitProb`, without stopping times.
-/

namespace Plurality

open Dynamics Dynamics.Kernel

variable {α : Type*} [Fintype α]

/-- A hitting probability is at most `1`. -/
lemma hitProb_le_one (K : Kernel α) (B : α → Prop) (t : ℕ) (a : α) : K.hitProb B t a ≤ 1 := by
  induction t generalizing a with
  | zero =>
    by_cases h : B a
    · rw [hitProb_of_mem K h]
    · rw [hitProb_zero_of_not_mem K h]; norm_num
  | succ t ih =>
    by_cases h : B a
    · rw [hitProb_of_mem K h]
    · rw [hitProb_succ_of_not_mem K h]
      calc (K a).expect (K.hitProb B t) ≤ (K a).expect (fun _ => 1) := (K a).expect_mono ih
        _ = 1 := Distribution.expect_const _ 1

/-- A hitting probability is nonnegative. -/
lemma hitProb_nonneg (K : Kernel α) (B : α → Prop) (t : ℕ) (a : α) : 0 ≤ K.hitProb B t a := by
  induction t generalizing a with
  | zero =>
    by_cases h : B a
    · rw [hitProb_of_mem K h]; norm_num
    · rw [hitProb_zero_of_not_mem K h]
  | succ t ih =>
    by_cases h : B a
    · rw [hitProb_of_mem K h]; norm_num
    · rw [hitProb_succ_of_not_mem K h]
      exact (K a).expect_nonneg ih

/-- Hitting a larger set is more likely. -/
lemma hitProb_mono (K : Kernel α) {B B' : α → Prop} (hB : ∀ a, B a → B' a) (t : ℕ) (a : α) :
    K.hitProb B t a ≤ K.hitProb B' t a := by
  induction t generalizing a with
  | zero =>
    by_cases h : B a
    · rw [hitProb_of_mem K h, hitProb_of_mem K (hB a h)]
    · rw [hitProb_zero_of_not_mem K h]
      exact hitProb_nonneg K B' 0 a
  | succ t ih =>
    by_cases h' : B' a
    · rw [hitProb_of_mem K h']
      exact hitProb_le_one K B _ a
    · have h : ¬ B a := fun h => h' (hB a h)
      rw [hitProb_succ_of_not_mem K h, hitProb_succ_of_not_mem K h']
      exact (K a).expect_mono ih

/-- **Hit, then absorb.** Let `P` be absorbing for `K`. If from every state of `B` the chain is in
`P` after `T` steps with probability at least `1 - ε` (`ε ≥ 0`), then from any state `a` it is in
`P` at time `t + T` with probability at least `P_a(T_B ≤ t) - ε`. -/
theorem hitProb_sub_le_event (K : Kernel α) {B P : α → Prop}
    (habs : ∀ a, P a → (K a).prob P = 1) {T : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (hB : ∀ b, B b → 1 - ε ≤ K.event P T b) (t : ℕ) (a : α) :
    K.hitProb B t a - ε ≤ K.event P (t + T) a := by
  classical
  induction t generalizing a with
  | zero =>
    by_cases h : B a
    · rw [hitProb_of_mem K h, zero_add]
      exact hB a h
    · rw [hitProb_zero_of_not_mem K h]
      linarith [K.event_nonneg P (0 + T) a]
  | succ t ih =>
    by_cases h : B a
    · rw [hitProb_of_mem K h]
      have hmono := K.event_monotone habs a (show T ≤ t + 1 + T by omega)
      linarith [hB a h]
    · have e : K.event P (t + 1 + T) a = (K a).expect (fun b => K.event P (t + T) b) := by
        rw [show t + 1 + T = (t + T) + 1 by omega, event_eq_iterate, iterate_succ, apply]
        simp only [event_eq_iterate]
      rw [hitProb_succ_of_not_mem K h, e]
      calc (K a).expect (K.hitProb B t) - ε
          = (K a).expect (fun b => K.hitProb B t b - ε) := by
            rw [Distribution.expect_sub, Distribution.expect_const]
        _ ≤ (K a).expect (fun b => K.event P (t + T) b) := (K a).expect_mono ih

end Plurality
