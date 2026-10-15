import Dynamics.Azuma

/-! # A maximal Azuma–Hoeffding inequality along i.i.d. uniform rounds (CRN-2)

The martingale concentration behind Kurtz's law of large numbers (`Epidemics.Kurtz`): over `n`
i.i.d. uniform rounds, a martingale `M_k = incrementSum step D x (l.take k)` with centred
increments bounded by `c` satisfies

  `P(∃ k ≤ n, M_k ≥ λ) ≤ exp(-λ² / (2 n c²))`.

The inequality is generic and proved in the core library (`Dynamics.expList_azuma`, in
`Dynamics.Azuma`, with Hoeffding's lemma `Dynamics.avg_exp_mul_le` and Ville's maximal inequality
`Dynamics.expList_ville`); `Epidemics.Kurtz.expList_azuma` is the pinned name of CRN-2.
-/

namespace Epidemics.Kurtz

open Dynamics

variable {σ R : Type*} [Fintype R]

/-- **Maximal Azuma–Hoeffding inequality** (Azuma 1967; Hoeffding 1963, Theorem 2, for independent
summands): `Dynamics.expList_azuma`, under its CRN-2 name. If the increments have zero mean over a
uniform round, `avg (D y) = 0`, and are bounded, `|D y a| ≤ c`, then over `n` i.i.d. uniform rounds
the martingale `M_k = incrementSum step D x (l.take k)` reaches `λ ≥ 0` at some step `k ≤ n` with
probability at most `exp(-λ² / (2 n c²))`. -/
theorem expList_azuma (step : σ → R → σ) (D : σ → R → ℝ) {c : ℝ}
    (hmean : ∀ y, avg (D y) = 0) (hbound : ∀ y a, |D y a| ≤ c) (x : σ) (n : ℕ) {lam : ℝ}
    (hlam : 0 ≤ lam) :
    expList R n (fun l ↦ if ∃ k ≤ n, lam ≤ incrementSum step D x (l.take k) then 1 else 0)
      ≤ Real.exp (-(lam ^ 2 / (2 * n * c ^ 2))) :=
  Dynamics.expList_azuma step D hmean hbound x n hlam

end Epidemics.Kurtz
