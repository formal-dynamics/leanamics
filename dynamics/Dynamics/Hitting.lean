import Dynamics.DriftHittingStop
import Dynamics.Phases
import Dynamics.Tail

/-!
# Facts about hitting probabilities

General facts about `K.hitProb B t a = P_a(T_B ≤ t)` for an arbitrary finite Markov kernel `K`,
proved by induction on `t` through the recursion of `hitProb` (`hitProb_of_mem`,
`hitProb_zero_of_not_mem`, `hitProb_succ_of_not_mem`), without stopping times:

* `hitProb_nonneg`, `hitProb_le_one`: hitting probabilities are probabilities;
* `hitProb_mono`, `hitProb_mono_time`: they grow with the target set and with the time horizon;
* `hitProb_sub_le_event` (**hit, then absorb**): if from every state of `B` the chain is in an
  absorbing event `P` after `T` steps with probability at least `1 - ε`, and `B` is hit within `t`
  steps with probability `h`, then the chain is in `P` at time `t + T` with probability at least
  `h - ε`. This is the strong Markov property at the hitting time of `B`;
* `event_amplify` (**amplification**): if an absorbing event is reached within `T₁` steps with
  probability at least `1 - ε` from every state, then a first block of `T₀` steps that fails with
  probability at most `δ` is followed by a block that fails with probability at most `ε`, so both
  fail with probability at most `δ ε`.
-/

namespace Dynamics.Kernel

variable {α : Type*} [Fintype α]

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

/-- Hitting probabilities grow with the time horizon (one step). -/
lemma hitProb_le_hitProb_succ (K : Kernel α) (B : α → Prop) (s : ℕ) (a : α) :
    K.hitProb B s a ≤ K.hitProb B (s + 1) a := by
  induction s generalizing a with
  | zero =>
    by_cases h : B a
    · rw [hitProb_of_mem K h, hitProb_of_mem K h]
    · rw [hitProb_zero_of_not_mem K h]
      exact hitProb_nonneg K B 1 a
  | succ s ih =>
    by_cases h : B a
    · rw [hitProb_of_mem K h, hitProb_of_mem K h]
    · rw [hitProb_succ_of_not_mem K h, hitProb_succ_of_not_mem K h]
      exact (K a).expect_mono ih

/-- Hitting probabilities grow with the time horizon. -/
lemma hitProb_mono_time (K : Kernel α) (B : α → Prop) {s t : ℕ} (h : s ≤ t) (a : α) :
    K.hitProb B s a ≤ K.hitProb B t a :=
  monotone_nat_of_le_succ (fun s => hitProb_le_hitProb_succ K B s a) h

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

/-- **Amplification.** Let `P` be absorbing for `K`, and suppose that from every state the chain
is in `P` after `T₁` steps with probability at least `1 - ε` (`ε ≥ 0`). If from `a` it is in `P`
after `T₀` steps with probability at least `1 - δ`, then it is in `P` after `T₀ + T₁` steps with
probability at least `1 - δ ε`. -/
theorem event_amplify (K : Kernel α) {P : α → Prop} (habs : ∀ a, P a → (K a).prob P = 1)
    {T₀ T₁ : ℕ} {ε δ : ℝ} (hε : 0 ≤ ε) (h₁ : ∀ b, 1 - ε ≤ K.event P T₁ b) (a : α)
    (h₀ : 1 - δ ≤ K.event P T₀ a) : 1 - δ * ε ≤ K.event P (T₀ + T₁) a := by
  classical
  have e (m : ℕ) (b : α) : K.event P m b = 1 - K.iterate m (outside {b | P b}) b :=
    event_eq_one_sub K {b | P b} m b
  rw [e] at h₀ ⊢
  -- after `T₁` steps, the probability of being outside `P` is at most `ε` times the indicator
  -- of being outside `P` now
  have hpt (b : α) : K.iterate T₁ (outside {b | P b}) b ≤ ε * outside {b | P b} b := by
    by_cases hb : P b
    · rw [outside_of_mem (B := {b | P b}) hb, mul_zero]
      have h0 : K.event P 0 b = 1 := by
        rw [event_eq_iterate, iterate_zero, if_pos hb]
      have hm := K.event_monotone habs b (Nat.zero_le T₁)
      have h1 := K.event_le_one P T₁ b
      simp only at hm
      simp only [e] at h0 hm h1
      linarith
    · rw [outside_of_not_mem (B := {b | P b}) hb, mul_one]
      have := h₁ b
      rw [e] at this
      linarith
  have hδ : K.iterate T₀ (outside {b | P b}) a ≤ δ := by linarith
  have hnn : 0 ≤ K.iterate T₀ (outside {b | P b}) a :=
    K.iterate_nonneg T₀ (outside_nonneg _) a
  calc 1 - δ * ε ≤ 1 - ε * K.iterate T₀ (outside {b | P b}) a := by nlinarith
    _ = 1 - K.iterate T₀ (fun b => ε * outside {b | P b} b) a := by rw [iterate_mul]
    _ ≤ 1 - K.iterate T₀ (K.iterate T₁ (outside {b | P b})) a := by
        linarith [K.iterate_mono T₀ hpt a]
    _ = 1 - K.iterate (T₀ + T₁) (outside {b | P b}) a := by rw [iterate_add_time]

end Dynamics.Kernel
