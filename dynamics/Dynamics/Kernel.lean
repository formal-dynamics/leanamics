import Dynamics.Distribution

/-! # Finite transition kernels and expectations at finite times -/

namespace Dynamics
open Finset

/-- A stochastic transition matrix, with its row normalization built in. -/
abbrev Kernel (α : Type*) [Fintype α] := α → Distribution α

namespace Kernel
variable {α : Type*} [Fintype α]

/-- The transition operator on real observables. -/
noncomputable def apply (K : Kernel α) (f : α → ℝ) (a : α) : ℝ := (K a).expect f

/-- Expected observable after `n` steps, starting at `a`. -/
noncomputable def iterate (K : Kernel α) : ℕ → (α → ℝ) → α → ℝ
  | 0, f => f
  | n + 1, f => K.apply (K.iterate n f)

@[simp] lemma iterate_zero (K : Kernel α) (f : α → ℝ) : K.iterate 0 f = f := rfl
@[simp] lemma iterate_succ (K : Kernel α) (n : ℕ) (f : α → ℝ) :
    K.iterate (n + 1) f = K.apply (K.iterate n f) := rfl

lemma iterate_const (K : Kernel α) (n : ℕ) (c : ℝ) :
    K.iterate n (fun _ => c) = fun _ => c := by
  induction n with
  | zero => rfl
  | succ n ih => funext a; simp [iterate, ih, apply]

lemma iterate_mono (K : Kernel α) (n : ℕ) {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    ∀ a, K.iterate n f a ≤ K.iterate n g a := by
  induction n with
  | zero => exact h
  | succ n ih => exact fun a => (K a).expect_mono ih

lemma iterate_nonneg (K : Kernel α) (n : ℕ) {f : α → ℝ} (h : ∀ a, 0 ≤ f a) :
    ∀ a, 0 ≤ K.iterate n f a := by
  simpa [iterate_const] using K.iterate_mono n h

lemma iterate_mul (K : Kernel α) (n : ℕ) (c : ℝ) (f : α → ℝ) :
    K.iterate n (fun a => c * f a) = fun a => c * K.iterate n f a := by
  induction n with
  | zero => rfl
  | succ n ih => funext a; simp [iterate, ih, apply, Distribution.expect_mul]

lemma iterate_add (K : Kernel α) (n : ℕ) (f g : α → ℝ) :
    K.iterate n (fun a => f a + g a) = fun a => K.iterate n f a + K.iterate n g a := by
  induction n with
  | zero => rfl
  | succ n ih => funext a; simp [iterate, ih, apply, Distribution.expect_add]

lemma iterate_add_time (K : Kernel α) (m n : ℕ) (f : α → ℝ) :
    K.iterate (m + n) f = K.iterate m (K.iterate n f) := by
  induction m with
  | zero => simp
  | succ m ih => simp [Nat.succ_add, ih]

/-- A harmonic observable has constant expectation at every finite time. -/
lemma iterate_invariant (K : Kernel α) {f : α → ℝ} (h : K.apply f = f) (n : ℕ) :
    K.iterate n f = f := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate_succ, ih, h]

/-- Probability of occupying an event at a finite time. -/
noncomputable def event (K : Kernel α) (s : α → Prop) (n : ℕ) (a : α) : ℝ := by
  classical
  exact K.iterate n (fun b => if s b then 1 else 0) a

lemma event_nonneg (K : Kernel α) (s : α → Prop) (n : ℕ) (a : α) :
    0 ≤ K.event s n a := by
  classical
  exact K.iterate_nonneg n (fun b => by split <;> norm_num) a

lemma event_le_one (K : Kernel α) (s : α → Prop) (n : ℕ) (a : α) :
    K.event s n a ≤ 1 := by
  classical
  have h := K.iterate_mono n (f := fun b => if s b then 1 else 0)
    (g := fun _ => 1) (fun b => by split <;> norm_num) a
  simpa [event, iterate_const] using h

/-- `event` computed with any decidability instance for the event. -/
lemma event_eq_iterate (K : Kernel α) (s : α → Prop) [DecidablePred s] (n : ℕ) (a : α) :
    K.event s n a = K.iterate n (fun b => if s b then 1 else 0) a := by
  unfold event
  congr 1
  funext b
  congr

/-- Stationarity of a distribution for a finite transition kernel. -/
def Stationary (K : Kernel α) (p : Distribution α) : Prop :=
  ∀ b, ∑ a, p.weight a * (K a).weight b = p.weight b

lemma stationary_expect (K : Kernel α) (p : Distribution α) (h : K.Stationary p)
    (f : α → ℝ) : p.expect (K.apply f) = p.expect f := by
  unfold Stationary at h
  simp only [apply, Distribution.expect, mul_sum]
  rw [sum_comm]
  simp_rw [← mul_assoc, ← sum_mul, h]

end Kernel
end Dynamics
