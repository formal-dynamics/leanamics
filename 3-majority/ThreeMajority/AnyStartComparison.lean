import ThreeMajority.AnyStartMajorization
import Dynamics.Kernel

/-!
# Comparing anonymous consensus processes (BCEKMN17, Sections 2.2 and 2.3)

An *anonymous consensus* (AC) process (Definition 1) is given by a process function `α` that
maps the current configuration to a probability vector over the colours; in one round every agent
independently adopts colour `a` with probability `α(c)_a`. Its one-round kernel on configurations
is `acKernel α`, the independent product over the agents of `α c`. Protocol dominance
(Definition 2) is `Dominates α α'`: `c ⪰ c'` implies `α(c) ⪰ α'(c')`.

* `multinomial_schurConvex`: Proposition 1 (Rinott; Marshall, Olkin, Arnold, Proposition
  11.E.11), in agent form: if `p ⪰ q` then every Schur-convex observable has a larger
  expectation when the agents draw their colours i.i.d. from `p` than from `q`.
* `ac_comparison`: Theorem 2, in the form of expectations of Schur-convex observables at every
  fixed time `T`, from configurations `c ⪰ c'`.
* `ac_numColours`: Theorem 2 for the number of colours: the probability that at most `κ`
  colours remain at time `T` is at least as large for the dominating process. This is the
  stochastic domination `T^κ_{P'}(c) ≥st T^κ_P(c)` of the hitting times for processes that never
  create colours (such as 3-Majority and Voter), since then "at most `κ` colours at time `T`"
  is "`T^κ ≤ T`".

The paper proves Theorem 2 through a coupling (Lemma 1) obtained from Strassen's theorem
(Theorem 3). Here Theorem 2 is stated in its distributional form, which needs no coupling: it
follows from Proposition 1 alone by induction on `T` (see `PROGRESS-MAJ6B.md`).
-/

namespace ThreeMajority

open Finset Dynamics

variable {n : ℕ} {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The one-round kernel of the anonymous consensus process with process function `α`
(BCEKMN17, Definition 1): from configuration `c`, the agents adopt colours independently, each
with law `α c`. -/
noncomputable def acKernel (α : (Fin n → σ) → Distribution σ) : Kernel (Fin n → σ) :=
  fun c => Distribution.independent fun _ : Fin n => α c

/-- Protocol dominance for AC-processes (BCEKMN17, Definition 2 and the remark after it):
`P_α` dominates `P_α'` if `c ⪰ c'` implies `α(c) ⪰ α'(c')`. -/
def Dominates (α α' : (Fin n → σ) → Distribution σ) : Prop :=
  ∀ c c' : Fin n → σ, Majorizes (countVec c) (countVec c') →
    Majorizes (α c).weight (α' c').weight

/-- **Proposition 1** (BCEKMN17; Rinott 1973, Marshall–Olkin–Arnold Proposition 11.E.11), in
agent form: the expectation of a Schur-convex observable of the multinomial configuration
`Mult(n, Θ)` is a Schur-convex function of `Θ`. -/
theorem multinomial_schurConvex (p q : Distribution σ) (hpq : Majorizes p.weight q.weight)
    (φ : (Fin n → σ) → ℝ) (hφ : SchurConvex φ) :
    (Distribution.independent fun _ : Fin n => q).expect φ ≤
      (Distribution.independent fun _ : Fin n => p).expect φ := by
  sorry

/-- **Theorem 2** (BCEKMN17), distributional form: if the AC-process `P_α` dominates `P_α'` and
`c ⪰ c'`, then at every time `T` every Schur-convex observable has at least the expectation
under `P_α` from `c` that it has under `P_α'` from `c'`. -/
theorem ac_comparison (α α' : (Fin n → σ) → Distribution σ) (h : Dominates α α')
    (φ : (Fin n → σ) → ℝ) (hφ : SchurConvex φ) (c c' : Fin n → σ)
    (hc : Majorizes (countVec c) (countVec c')) (T : ℕ) :
    (acKernel α').iterate T φ c' ≤ (acKernel α).iterate T φ c := by
  sorry

/-- **Theorem 2** (BCEKMN17), for the number of colours: started from the same configuration,
the dominating AC-process has at most `κ` colours at time `T` with at least the probability of
the dominated one. -/
theorem ac_numColours (α α' : (Fin n → σ) → Distribution σ) (h : Dominates α α')
    (c : Fin n → σ) (κ T : ℕ) :
    (acKernel α').event (fun x => numColours x ≤ κ) T c ≤
      (acKernel α).event (fun x => numColours x ≤ κ) T c := by
  rw [Kernel.event_eq_iterate, Kernel.event_eq_iterate]
  exact ac_comparison α α' h _ (schurConvex_numColours_le κ) c c (Majorizes.refl _) T

end ThreeMajority
