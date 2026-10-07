import Dynamics.Kernel

/-!
# Time-dependent finite chains

A time-dependent chain moves from time `t` to time `t + 1` with the kernel `K t`. This is the
setting of the voter model on a dynamic graph sequence `G₁, G₂, …` in Berenbrink, Giakkoupis,
Kermarrec, Mallmann-Trenn, *Bounds on the voter model in dynamic networks* (ICALP 2016), whose
drift lemma (Lemma 2.2) lets the drift depend on the time through the conductance `φ_t`.

`iterateSeq K n f a` is the expected value of `f` after the steps `K 0, …, K (n - 1)`, started at
`a`. For a constant family it is `Kernel.iterate` (`iterateSeq_const`).
-/

namespace Dynamics.Kernel
variable {α : Type*} [Fintype α]

/-- Expected value of `f` after `n` steps of the time-dependent chain that moves from time `t` to
time `t + 1` with the kernel `K t`, started at `a`. The last step `K n` is applied first to `f`. -/
noncomputable def iterateSeq (K : ℕ → Dynamics.Kernel α) : ℕ → (α → ℝ) → α → ℝ
  | 0, f => f
  | n + 1, f => iterateSeq K n ((K n).apply f)

/-- A constant family of kernels is a time-homogeneous chain. -/
theorem iterateSeq_const (K : Dynamics.Kernel α) (n : ℕ) (f : α → ℝ) :
    iterateSeq (fun _ => K) n f = K.iterate n f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    show iterateSeq (fun _ => K) n (K.apply f) = K.iterate (n + 1) f
    rw [ih, K.iterate_add_time n 1]
    rfl

/-- Zero steps leave the observable unchanged. -/
@[simp] lemma iterateSeq_zero (K : ℕ → Dynamics.Kernel α) (f : α → ℝ) :
    iterateSeq K 0 f = f := rfl

/-- The last of `n + 1` steps acts first on the observable. -/
lemma iterateSeq_succ (K : ℕ → Dynamics.Kernel α) (n : ℕ) (f : α → ℝ) :
    iterateSeq K (n + 1) f = iterateSeq K n ((K n).apply f) := rfl

/-! ### Linearity and monotonicity -/

/-- One step is additive in the observable. -/
lemma apply_add (K : Dynamics.Kernel α) (f g : α → ℝ) :
    K.apply (fun a => f a + g a) = fun a => K.apply f a + K.apply g a :=
  funext fun a => (K a).expect_add f g

/-- One step commutes with scalar multiplication. -/
lemma apply_mul (K : Dynamics.Kernel α) (c : ℝ) (f : α → ℝ) :
    K.apply (fun a => c * f a) = fun a => c * K.apply f a :=
  funext fun a => (K a).expect_mul c f

/-- One step fixes constant observables. -/
lemma apply_const (K : Dynamics.Kernel α) (c : ℝ) : K.apply (fun _ => c) = fun _ => c :=
  funext fun a => (K a).expect_const c

/-- Expectations are monotone in the observable. -/
lemma iterateSeq_mono (K : ℕ → Dynamics.Kernel α) (n : ℕ) {f g : α → ℝ}
    (h : ∀ a, f a ≤ g a) : ∀ a, iterateSeq K n f a ≤ iterateSeq K n g a := by
  induction n generalizing f g with
  | zero => exact h
  | succ n ih => exact ih fun a => (K n a).expect_mono h

/-- Expectations are additive in the observable. -/
lemma iterateSeq_add (K : ℕ → Dynamics.Kernel α) (n : ℕ) (f g : α → ℝ) :
    iterateSeq K n (fun a => f a + g a) =
      fun a => iterateSeq K n f a + iterateSeq K n g a := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih => simp only [iterateSeq_succ, apply_add, ih]

/-- Expectations commute with scalar multiplication. -/
lemma iterateSeq_mul (K : ℕ → Dynamics.Kernel α) (n : ℕ) (c : ℝ) (f : α → ℝ) :
    iterateSeq K n (fun a => c * f a) = fun a => c * iterateSeq K n f a := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => simp only [iterateSeq_succ, apply_mul, ih]

/-- Constant observables keep their value. -/
lemma iterateSeq_const_fun (K : ℕ → Dynamics.Kernel α) (n : ℕ) (c : ℝ) :
    iterateSeq K n (fun _ => c) = fun _ => c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterateSeq_succ, apply_const, ih]

/-- Nonnegative observables have nonnegative expectations. -/
lemma iterateSeq_nonneg (K : ℕ → Dynamics.Kernel α) (n : ℕ) {f : α → ℝ}
    (h : ∀ a, 0 ≤ f a) (a : α) : 0 ≤ iterateSeq K n f a := by
  simpa [iterateSeq_const_fun] using iterateSeq_mono K n (f := fun _ => 0) h a

/-- `iterateSeq` of a linear combination of two observables. -/
lemma iterateSeq_lin (K : ℕ → Dynamics.Kernel α) (n : ℕ) (u v : ℝ) (f g : α → ℝ) (a : α) :
    iterateSeq K n (fun x => u * f x + v * g x) a =
      u * iterateSeq K n f a + v * iterateSeq K n g a := by
  rw [iterateSeq_add K n (fun x => u * f x) (fun x => v * g x), iterateSeq_mul, iterateSeq_mul]

/-- Expectation of a complement: `𝔼[1 - f] = 1 - 𝔼[f]`. -/
lemma iterateSeq_one_sub (K : ℕ → Dynamics.Kernel α) (n : ℕ) (f : α → ℝ) (a : α) :
    iterateSeq K n (fun x => 1 - f x) a = 1 - iterateSeq K n f a := by
  have h : (fun x => 1 - f x) = fun x => 1 * (fun _ => (1 : ℝ)) x + (-1) * f x := by
    funext x
    ring
  rw [h, iterateSeq_lin, iterateSeq_const_fun]
  ring

/-- `Kernel.event` (classical decidability) as an `iterateSeq` of a constant family, with any
decidability instance. -/
lemma event_eq_iterateSeq (K : Dynamics.Kernel α) (s : α → Prop) [DecidablePred s] (n : ℕ)
    (a : α) : K.event s n a = iterateSeq (fun _ => K) n (fun b => if s b then 1 else 0) a := by
  rw [iterateSeq_const, event]
  congr!

end Dynamics.Kernel
