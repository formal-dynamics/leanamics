import Dynamics.Kernel

/-!
# Progress through nested phases

A finite Markov chain that, from every state of `Aᵢ`, stays in `Aᵢ` with
probability `≥ 1 - ε` and moves into the smaller set `Aᵢ₊₁` with
probability `≥ 1 - ν`, reaches the innermost set `A_T` within `ℓ T` steps
except with probability `T (ℓ ε + ν^ℓ)`. This is Lemma A.4 of Becchetti,
Clementi, Natale, Pasquale, Silvestri, Trevisan, *Simple dynamics for
plurality consensus* (SPAA 2014); its proof is omitted there.

The proof works phase by phase with the survival observable `outside B`
(the indicator of having left `B`): within `ℓ` steps the chain leaves `Aᵢ`
with probability at most `ℓ ε` and fails to jump in each of the `ℓ` steps
with probability at most `ν^ℓ`. The hypothesis `ε ≤ ν` of the paper is not
needed.
-/

namespace Dynamics.Kernel
open Finset
variable {α : Type*} [Fintype α]

/-- Indicator of lying outside `B`. -/
noncomputable def outside (B : Set α) (b : α) : ℝ := by
  classical
  exact if b ∈ B then 0 else 1

omit [Fintype α] in
lemma outside_of_mem {B : Set α} {b : α} (h : b ∈ B) : outside B b = 0 := by
  classical
  simp [outside, h]

omit [Fintype α] in
lemma outside_of_not_mem {B : Set α} {b : α} (h : b ∉ B) : outside B b = 1 := by
  classical
  simp [outside, h]

omit [Fintype α] in
lemma outside_nonneg (B : Set α) (b : α) : 0 ≤ outside B b := by
  classical
  unfold outside
  split <;> norm_num

omit [Fintype α] in
lemma outside_le_one (B : Set α) (b : α) : outside B b ≤ 1 := by
  classical
  unfold outside
  split <;> norm_num

lemma iterate_le_one (K : Dynamics.Kernel α) (n : ℕ) {f : α → ℝ} (h : ∀ a, f a ≤ 1) (a : α) :
    K.iterate n f a ≤ 1 := by
  simpa [iterate_const] using K.iterate_mono n h a

/-- One step leaves `B` with probability `1 - P(stay in B)`. -/
lemma apply_outside (K : Dynamics.Kernel α) (B : Set α) (a : α) :
    K.apply (outside B) a = 1 - (K a).prob (· ∈ B) := by
  classical
  have h : outside B = fun b => 1 - (if b ∈ B then (1 : ℝ) else 0) := by
    funext b
    unfold outside
    split <;> norm_num
  rw [h]
  simp only [apply, Distribution.expect_sub, Distribution.expect_const, Distribution.prob]

/-- Occupation probability is one minus the survival observable. -/
lemma event_eq_one_sub (K : Dynamics.Kernel α) (B : Set α) (n : ℕ) (a : α) :
    K.event (· ∈ B) n a = 1 - K.iterate n (outside B) a := by
  classical
  have h : (fun b => if b ∈ B then (1 : ℝ) else 0) = fun b => 1 + (-1) * outside B b := by
    funext b
    unfold outside
    split <;> norm_num
  unfold event
  simp only [h, iterate_add, iterate_mul, iterate_const]
  ring

/-- **Staying**: if from every state of `B` the chain stays in `B` with
probability `≥ 1 - ε`, then it has left `B` after `ℓ` steps with probability
at most `ℓ ε`. -/
lemma iterate_outside_le_of_stay (K : Dynamics.Kernel α) (B : Set α) {ε : ℝ} (hε : 0 ≤ ε)
    (hstay : ∀ a ∈ B, 1 - ε ≤ (K a).prob (· ∈ B)) :
    ∀ ℓ : ℕ, ∀ a ∈ B, K.iterate ℓ (outside B) a ≤ ℓ * ε := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro a ha
    simp [outside_of_mem ha]
  | succ ℓ ih =>
    intro a ha
    have hpt (b : α) : K.iterate ℓ (outside B) b ≤ ℓ * ε + outside B b := by
      by_cases hb : b ∈ B
      · rw [outside_of_mem hb]
        linarith [ih b hb]
      · rw [outside_of_not_mem hb]
        have := K.iterate_le_one ℓ (outside_le_one B) b
        have : (0 : ℝ) ≤ ℓ * ε := by positivity
        linarith
    rw [iterate_succ]
    calc K.apply (K.iterate ℓ (outside B)) a
        ≤ (K a).expect (fun b => ℓ * ε + outside B b) := (K a).expect_mono hpt
      _ = ℓ * ε + K.apply (outside B) a := by
          rw [Distribution.expect_add, Distribution.expect_const]
          rfl
      _ ≤ ((ℓ + 1 : ℕ) : ℝ) * ε := by
          rw [apply_outside]
          have := hstay a ha
          push_cast
          linarith

/-- **One phase**: from `A`, which is left with probability `≤ ε` per step,
the chain is outside `B ⊆ A` after `ℓ` steps with probability at most
`ℓ ε + ν^ℓ`, if every step from `A` enters `B` with probability `≥ 1 - ν` and
`B` itself is left with probability `≤ ε` per step. -/
lemma iterate_outside_le_of_move (K : Dynamics.Kernel α) {A B : Set α} (hBA : B ⊆ A)
    {ε ν : ℝ} (hε : 0 ≤ ε) (hν : 0 ≤ ν)
    (hstayA : ∀ a ∈ A, 1 - ε ≤ (K a).prob (· ∈ A))
    (hstayB : ∀ a ∈ B, 1 - ε ≤ (K a).prob (· ∈ B))
    (hmove : ∀ a ∈ A, 1 - ν ≤ (K a).prob (· ∈ B)) :
    ∀ ℓ : ℕ, ∀ a ∈ A, K.iterate ℓ (outside B) a ≤ ℓ * ε + ν ^ ℓ := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro a _
    simpa using outside_le_one B a
  | succ ℓ ih =>
    intro a ha
    have hpt (b : α) :
        K.iterate ℓ (outside B) b ≤ ℓ * ε + ν ^ ℓ * outside B b + outside A b := by
      have hℓε : (0 : ℝ) ≤ ℓ * ε := by positivity
      have hνℓ : (0 : ℝ) ≤ ν ^ ℓ := pow_nonneg hν ℓ
      by_cases hb : b ∈ B
      · rw [outside_of_mem hb, outside_of_mem (hBA hb)]
        linarith [K.iterate_outside_le_of_stay B hε hstayB ℓ b hb]
      · by_cases hbA : b ∈ A
        · rw [outside_of_not_mem hb, outside_of_mem hbA]
          linarith [ih b hbA]
        · rw [outside_of_not_mem hb, outside_of_not_mem hbA]
          have := K.iterate_le_one ℓ (outside_le_one B) b
          linarith
    rw [iterate_succ]
    calc K.apply (K.iterate ℓ (outside B)) a
        ≤ (K a).expect (fun b => ℓ * ε + ν ^ ℓ * outside B b + outside A b) :=
          (K a).expect_mono hpt
      _ = ℓ * ε + ν ^ ℓ * K.apply (outside B) a + K.apply (outside A) a := by
          rw [Distribution.expect_add, Distribution.expect_add, Distribution.expect_const,
            Distribution.expect_mul]
          rfl
      _ ≤ ((ℓ + 1 : ℕ) : ℝ) * ε + ν ^ (ℓ + 1) := by
          rw [apply_outside, apply_outside]
          have h1 := hmove a ha
          have h2 := hstayA a ha
          have h3 : ν ^ ℓ * (1 - (K a).prob (· ∈ B)) ≤ ν ^ ℓ * ν :=
            mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hν ℓ)
          push_cast
          rw [pow_succ]
          linarith

/-- **Lemma A.4 (nested phases).** Let `A₁ ⊇ A₂ ⊇ ⋯ ⊇ A_T` be such that
from every state of `Aᵢ` the chain stays in `Aᵢ` with probability
`≥ 1 - ε`, and for `i < T` moves into `Aᵢ₊₁` with probability `≥ 1 - ν`.
Then from any state of `A₁`, after `ℓ T` steps the chain lies in `A_T` with
probability at least `1 - T (ℓ ε + ν^ℓ)`. -/
theorem nested_phases (K : Dynamics.Kernel α) (A : ℕ → Set α) {T : ℕ} (hT : 1 ≤ T) (ℓ : ℕ)
    {ε ν : ℝ} (hε : 0 ≤ ε) (hν : 0 ≤ ν)
    (hnest : ∀ i, 1 ≤ i → i < T → A (i + 1) ⊆ A i)
    (hstay : ∀ i, 1 ≤ i → i ≤ T → ∀ a ∈ A i, 1 - ε ≤ (K a).prob (· ∈ A i))
    (hmove : ∀ i, 1 ≤ i → i < T → ∀ a ∈ A i, 1 - ν ≤ (K a).prob (· ∈ A (i + 1))) :
    ∀ a ∈ A 1, 1 - T * (ℓ * ε + ν ^ ℓ) ≤ K.event (· ∈ A T) (ℓ * T) a := by
  have hc : (0 : ℝ) ≤ ℓ * ε + ν ^ ℓ := by positivity
  -- after `j` phases the chain is in `A (j+1)` except with probability `j (ℓ ε + ν^ℓ)`
  have hphase : ∀ j : ℕ, j + 1 ≤ T → ∀ a ∈ A 1,
      K.iterate (ℓ * j) (outside (A (j + 1))) a ≤ j * (ℓ * ε + ν ^ ℓ) := by
    intro j
    induction j with
    | zero =>
      intro _ a ha
      simp [outside_of_mem ha]
    | succ j ih =>
      intro hj a ha
      have hpt (b : α) : K.iterate ℓ (outside (A (j + 2))) b
          ≤ (ℓ * ε + ν ^ ℓ) + outside (A (j + 1)) b := by
        by_cases hb : b ∈ A (j + 1)
        · rw [outside_of_mem hb, add_zero]
          exact K.iterate_outside_le_of_move (hnest (j + 1) (by omega) (by omega)) hε hν
            (hstay (j + 1) (by omega) (by omega)) (hstay (j + 2) (by omega) (by omega))
            (hmove (j + 1) (by omega) (by omega)) ℓ b hb
        · rw [outside_of_not_mem hb]
          have := K.iterate_le_one ℓ (outside_le_one (A (j + 2))) b
          linarith
      have hsplit : ℓ * (j + 1) = ℓ * j + ℓ := by ring
      rw [hsplit, iterate_add_time]
      calc K.iterate (ℓ * j) (K.iterate ℓ (outside (A (j + 1 + 1)))) a
          ≤ K.iterate (ℓ * j) (fun b => (ℓ * ε + ν ^ ℓ) + outside (A (j + 1)) b) a :=
            K.iterate_mono _ hpt a
        _ = (ℓ * ε + ν ^ ℓ) + K.iterate (ℓ * j) (outside (A (j + 1))) a := by
            rw [iterate_add, iterate_const]
        _ ≤ (ℓ * ε + ν ^ ℓ) + j * (ℓ * ε + ν ^ ℓ) := by
            linarith [ih (by omega) a ha]
        _ = ((j + 1 : ℕ) : ℝ) * (ℓ * ε + ν ^ ℓ) := by push_cast; ring
  intro a ha
  obtain ⟨j, rfl⟩ : ∃ j, T = j + 1 := ⟨T - 1, by omega⟩
  have hpt (b : α) : K.iterate ℓ (outside (A (j + 1))) b ≤ ℓ * ε + outside (A (j + 1)) b := by
    by_cases hb : b ∈ A (j + 1)
    · rw [outside_of_mem hb, add_zero]
      exact K.iterate_outside_le_of_stay _ hε (hstay (j + 1) (by omega) le_rfl) ℓ b hb
    · rw [outside_of_not_mem hb]
      have := K.iterate_le_one ℓ (outside_le_one (A (j + 1))) b
      have : (0 : ℝ) ≤ ℓ * ε := by positivity
      linarith
  have hsplit : ℓ * (j + 1) = ℓ * j + ℓ := by ring
  rw [event_eq_one_sub, hsplit, iterate_add_time]
  have hfin : K.iterate (ℓ * j) (K.iterate ℓ (outside (A (j + 1)))) a
      ≤ ℓ * ε + j * (ℓ * ε + ν ^ ℓ) := by
    calc K.iterate (ℓ * j) (K.iterate ℓ (outside (A (j + 1)))) a
        ≤ K.iterate (ℓ * j) (fun b => ℓ * ε + outside (A (j + 1)) b) a :=
          K.iterate_mono _ hpt a
      _ = ℓ * ε + K.iterate (ℓ * j) (outside (A (j + 1))) a := by
          rw [iterate_add, iterate_const]
      _ ≤ ℓ * ε + j * (ℓ * ε + ν ^ ℓ) := by
          linarith [hphase j le_rfl a ha]
  have hν' : (0 : ℝ) ≤ ν ^ ℓ := pow_nonneg hν ℓ
  push_cast
  nlinarith

end Dynamics.Kernel
