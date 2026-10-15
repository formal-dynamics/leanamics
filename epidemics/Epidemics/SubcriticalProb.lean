import Epidemics.GiantCoins
import Dynamics.Independent

/-! # Finite-probability helpers for EPI-2

The event lemmas (monotonicity, congruence, sure and impossible events, the complement rule and
the union bound) are the core's `Distribution.prob_mono`, `prob_congr`, `prob_eq_one`,
`prob_eq_zero`, `prob_not` and `prob_exists_le_sum`; Markov's inequality on an exponential moment
and the expectation of a coin are the core's `Distribution.prob_le_expect_exp` and
`Distribution.bernoulli_expect` (FND-3). This file adds the conditioning of the percolation coins
on one coin (`coins_prob_split`, through the core's `Distribution.independent_expect_eq_sum_update`
in `Dynamics.Independent`).
-/

namespace Epidemics
open Finset Dynamics

variable {α ι β : Type*} [Fintype α] [Fintype ι] [Fintype β]

section Independent

/-- Conditioning the percolation coins on the coin of one pair. -/
lemma coins_prob_split [DecidableEq α] (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (e : α)
    (s : (α → Bool) → Prop) :
    (Distribution.independent fun _ : α => bernoulli p h0 h1).prob s =
      p * (Distribution.independent fun _ : α => bernoulli p h0 h1).prob
          (fun ω => s (Function.update ω e true)) +
        (1 - p) * (Distribution.independent fun _ : α => bernoulli p h0 h1).prob
          (fun ω => s (Function.update ω e false)) := by
  classical
  simp only [Distribution.prob_eq_expect]
  rw [Distribution.independent_expect_eq_sum_update _ e, Fintype.sum_bool]
  simp [bernoulli, Distribution.bernoulli]

end Independent

end Epidemics
