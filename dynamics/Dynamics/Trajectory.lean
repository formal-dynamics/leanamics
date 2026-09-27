import Dynamics.Kernel

/-! # Expectations of finite weighted trajectories -/
namespace Dynamics.Kernel
variable {α : Type*} [Fintype α]

/-- Expected functional of the history and endpoint of `n` transitions.
The history contains the initial state and the following `n - 1` states;
the endpoint is supplied separately, so the definition also handles zero steps. -/
noncomputable def trajectory (K : Dynamics.Kernel α) :
    ℕ → α → (List α → α → ℝ) → ℝ
  | 0, a, F => F [] a
  | n + 1, a, F => (K a).expect (fun b => K.trajectory n b (fun l c => F (a :: l) c))

/-- Endpoint observables agree with transition-operator iteration. -/
lemma trajectory_endpoint (K : Dynamics.Kernel α) (n : ℕ) (a : α) (f : α → ℝ) :
    K.trajectory n a (fun _ b => f b) = K.iterate n f a := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    change (K a).expect (fun b => K.trajectory n b (fun _ c => f c)) = _
    simp_rw [ih]
    rfl

end Dynamics.Kernel
