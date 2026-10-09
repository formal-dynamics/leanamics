import ThreeMajority.AnyStartComparison
import Dynamics.Rounds

/-!
# 3-Majority is at least as fast as Voter (BCEKMN17, Lemma 2)

Both processes are anonymous consensus processes (Definition 1), with the process functions
`alpha3M` and `alphaVoter`, defined here as the law of the colour adopted by one agent: the
image of one uniform sample triple under `majColour c`, resp. of one uniform sample under `c`.

* `alphaVoter_weight`, `alpha3M_weight`: Equations (1) and (2), `α^V_a(c) = x_a` and
  `α^{3M}_a(c) = x_a (1 + x_a − ‖x‖₂²)` with `x = c/n`.
* `apply_ofStep_stepCol`, `apply_ofStep_voterStep`: one uniformly random round of the
  round-based processes `stepCol` and `voterStep` is one step of the AC-processes `alpha3M` and
  `alphaVoter` (the agents' samples are independent).
* `dominates_alpha3M_alphaVoter`: the inequality proved in Lemma 2, `c ⪰ c'` implies
  `α^{3M}(c) ⪰ α^V(c')`.
* `voter_le_threeMaj`: Lemma 2, started from the same configuration, 3-Majority has at most `κ`
  colours at time `T` with at least the probability that Voter has.
-/

namespace ThreeMajority

open Finset Dynamics

variable {n : ℕ} [NeZero n] {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The process function of 3-Majority (BCEKMN17, Section 2.2): the law of `majColour c s` for
a uniform sample triple `s`. -/
noncomputable def alpha3M (c : Fin n → σ) : Distribution σ :=
  (Distribution.uniform (Fin n × Fin n × Fin n)).map (majColour c)

/-- The process function of Voter (BCEKMN17, Section 2.2): the law of `c u` for a uniform
agent `u`. -/
noncomputable def alphaVoter (c : Fin n → σ) : Distribution σ :=
  (Distribution.uniform (Fin n)).map c

/-- **Equation (1)** (BCEKMN17): `α^V_a(c) = c_a / n`. -/
theorem alphaVoter_weight (c : Fin n → σ) (a : σ) :
    (alphaVoter c).weight a = (colourCount c a : ℝ) / n := by
  sorry

/-- **Equation (2)** (BCEKMN17): with `x = c/n`, `α^{3M}_a(c) = x_a (1 + x_a − ‖x‖₂²)`. -/
theorem alpha3M_weight (c : Fin n → σ) (a : σ) :
    (alpha3M c).weight a = (colourCount c a : ℝ) / n *
      (1 + (colourCount c a : ℝ) / n - ∑ b, ((colourCount c b : ℝ) / n) ^ 2) := by
  sorry

/-- One uniformly random round of `stepCol` is one step of the AC-process `alpha3M`
(3-Majority is an AC-process, BCEKMN17, Section 2.2). -/
theorem apply_ofStep_stepCol (f : (Fin n → σ) → ℝ) (c : Fin n → σ) :
    (Kernel.ofStep (stepCol (n := n) (σ := σ))).apply f c = (acKernel alpha3M).apply f c := by
  sorry

omit [DecidableEq σ] in
/-- One uniformly random round of `voterStep` is one step of the AC-process `alphaVoter`
(Voter is an AC-process, BCEKMN17, Section 2.2). -/
theorem apply_ofStep_voterStep (f : (Fin n → σ) → ℝ) (c : Fin n → σ) :
    (Kernel.ofStep (voterStep (n := n) (σ := σ))).apply f c =
      (acKernel alphaVoter).apply f c := by
  sorry

/-- The inequality of the proof of **Lemma 2** (BCEKMN17): 3-Majority dominates Voter,
`c ⪰ c'` implies `α^{3M}(c) ⪰ α^V(c')`. -/
theorem dominates_alpha3M_alphaVoter :
    Dominates (alpha3M (n := n) (σ := σ)) alphaVoter := by
  sorry

omit [Fintype σ] in
/-- **Lemma 2** (BCEKMN17): started from the same configuration `c`, after `T` rounds
3-Majority has at most `κ` colours with at least the probability that Voter has. Since neither
process creates colours, this is `T^κ_{3M}(c) ≤st T^κ_V(c)`. -/
theorem voter_le_threeMaj [Finite σ] (c : Fin n → σ) (κ T : ℕ) :
    expList (Fin n → Fin n) T (fun l => if numColours (voterRun c l) ≤ κ then 1 else 0) ≤
      expList (Tgt3 n) T (fun l => if numColours (runCol c l) ≤ κ then 1 else 0) := by
  sorry

end ThreeMajority
