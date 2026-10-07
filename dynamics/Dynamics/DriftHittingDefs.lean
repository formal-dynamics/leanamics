import Dynamics.Trajectory

/-!
# Hitting probabilities of finite chains

`K.hitProb B n a` is the probability that the chain with kernel `K`, started at `a`, visits `B`
at one of the times `0, 1, …, n`, that is `P_a(T_B ≤ n)` for the hitting time
`T_B = min {t : X_t ∈ B}`. It is the expectation over the first `n` transitions
(`Kernel.trajectory`) of the indicator that the history or the endpoint lies in `B`, so no path
space is needed.

This is the event of the hitting-time bound of Doerr, Goldberg, Minder, Sauerwald, Scheideler,
*Stabilizing consensus with the power of two choices*, SPAA 2011, Claim 2.9
(`Dynamics.Kernel.drift_hitting`).
-/

namespace Dynamics.Kernel
variable {α : Type*} [Fintype α]

/-- Probability that the chain with kernel `K` started at `a` visits `B` at one of the times
`0, 1, …, n`, i.e. `P_a(T_B ≤ n)` for the hitting time `T_B = min {t : X_t ∈ B}` (the event of
Claim 2.9 of Doerr et al., SPAA 2011). In `Kernel.trajectory` the history holds the states at the
times `0, …, n - 1` and the endpoint is the state at time `n`. -/
noncomputable def hitProb (K : Dynamics.Kernel α) (B : α → Prop) (n : ℕ) (a : α) : ℝ := by
  classical
  exact K.trajectory n a (fun l b => if (∃ x ∈ l, B x) ∨ B b then 1 else 0)

end Dynamics.Kernel
