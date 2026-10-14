import Epidemics.GiantCoins
import Dynamics.Independent

/-! # Finite-probability helpers for EPI-2

Monotonicity of `prob` is the core's `Distribution.prob_mono`; congruence, the complement rule
`prob_not` and the union bound `prob_exists_le_sum` are those of `Epidemics.GiantCoins` (EPI-3);
Markov's inequality on an exponential moment and the expectation of a coin are the core's
`Distribution.prob_le_expect_exp` and `Distribution.bernoulli_expect` (FND-3). This file adds
`prob_eq_one`, `prob_eq_zero` and the conditioning of the percolation coins on one coin
(`coins_prob_split`, through the core's `Distribution.independent_expect_eq_sum_update` in
`Dynamics.Independent`). The event lemmas are stated for any `Distribution`; their move to
`dynamics/` is tracked in issue #42.
-/

namespace Epidemics
open Finset Dynamics

variable {α ι β : Type*} [Fintype α] [Fintype ι] [Fintype β]

section Prob
variable (q : Distribution α)

lemma prob_eq_one {s : α → Prop} (h : ∀ a, s a) : q.prob s = 1 := by
  unfold Distribution.prob
  simp only [h, if_true]
  exact q.expect_const 1

lemma prob_eq_zero {s : α → Prop} (h : ∀ a, ¬s a) : q.prob s = 0 := by
  unfold Distribution.prob
  simp only [h, if_false]
  exact q.expect_const 0

end Prob

section Independent

/-- Conditioning the percolation coins on the coin of one pair. -/
lemma coins_prob_split [DecidableEq α] (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (e : α)
    (s : (α → Bool) → Prop) :
    (Distribution.independent fun _ : α => bernoulli p h0 h1).prob s =
      p * (Distribution.independent fun _ : α => bernoulli p h0 h1).prob
          (fun ω => s (Function.update ω e true)) +
        (1 - p) * (Distribution.independent fun _ : α => bernoulli p h0 h1).prob
          (fun ω => s (Function.update ω e false)) := by
  unfold Distribution.prob
  rw [Distribution.independent_expect_eq_sum_update _ e, Fintype.sum_bool]
  simp [bernoulli]

end Independent

end Epidemics
