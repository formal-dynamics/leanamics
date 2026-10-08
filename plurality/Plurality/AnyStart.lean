import Plurality.Corollaries
import Dynamics.DriftHitting

/-!
# Two opinions from any configuration

Binary 3-Majority reaches consensus from **any** configuration, including the perfectly balanced
one, within `O(log n)` rounds with high probability (Becchetti, Clementi, Natale, *Consensus
dynamics: an overview*, SIGACT News 2020, §4 Case 3, where the argument is given for the binary
median dynamics of Doerr, Goldberg, Minder, Sauerwald, Scheideler, SPAA 2011).

The gap `s = |I| - (n - |I|)` evolves in two stages.

* **Symmetry breaking** (`majority3_symmetry_breaking`). Near balance the expected drift of the
  gap is too weak for step-by-step concentration. Instead, by the variance of one round, the gap
  jumps to order `√n` with constant probability (`jump_near_balance`), and above that it grows by
  a constant factor except with probability exponentially small in its size (`growth_far`). The
  hitting-time bound of Doerr et al. (Claim 2.9, `Dynamics.Kernel.drift_hitting_log`), applied
  to `X = ⌊|s| / (√n / 100)⌋`, then shows that `|s|` reaches `22 √(3 n log n)` within
  `O(log n)` rounds except with probability `1/n`.
* **Vanishing bias** (`majority3_vanishing_bias`). From a gap `22 √(3 n log n)`, consensus
  follows within `390 log n` rounds with probability `1 - 429 log n / n`; a negative gap is the
  same statement for the complementary set.
-/

namespace Plurality

open Finset Dynamics
open ThreeMajority (Tgt3)

variable {n : ℕ}

/-- The gap `|I| - (n - |I|)` between the nodes holding opinion `1` (the set `I`) and the
others. -/
noncomputable def gap (I : Finset (Fin n)) : ℝ := (I.card : ℝ) - (n - I.card)

/-- Binary 3-Majority as a finite Markov kernel on the set of nodes holding opinion `1`. -/
noncomputable def binKernel (n : ℕ) [NeZero n] : Kernel (Finset (Fin n)) :=
  Kernel.ofStep (ThreeMajority.step (n := n))

/-- **A `√n` jump near balance** (the variance of one round). If the gap is at most `4√n/25` in
absolute value and `n ≥ 5`, then after one round it is at least `√n/5` in absolute value with
probability at least `9/64`. -/
theorem jump_near_balance [NeZero n] (hn : 5 ≤ n) (I : Finset (Fin n))
    (hI : |gap I| ≤ 4 * √(n : ℝ) / 25) :
    9 / 64 ≤ (binKernel n I).prob (fun J => √(n : ℝ) / 5 ≤ |gap J|) := by
  sorry

/-- **Growth above `√n`** (the drift of one round, with Hoeffding's inequality). If
`0 ≤ s ≤ n/2` for the gap `s`, then for every `λ ≥ 0` the next gap exceeds `11 s/8 - 2λ` except
with probability at most `exp (-2λ²/n)`. -/
theorem growth_far [NeZero n] (I : Finset (Fin n)) (h0 : 0 ≤ gap I) (h1 : gap I ≤ n / 2)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    1 - Real.exp (-(2 * lam ^ 2 / n))
      ≤ (binKernel n I).prob (fun J => 11 / 8 * gap I - 2 * lam < gap J) := by
  sorry

/-- **Symmetry breaking.** There is `C > 0` such that, for `log n ≥ 40`, from any configuration
`I₀` the gap reaches `22 √(3 n log n)` in absolute value within any `t ≥ C log n` rounds with
probability at least `1 - 1/n`. -/
theorem majority3_symmetry_breaking : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) [NeZero n],
    40 ≤ Real.log n → ∀ (I₀ : Finset (Fin n)) (t : ℕ), C * Real.log n ≤ t →
      1 - 1 / (n : ℝ)
        ≤ (binKernel n).hitProb (fun I => 22 * √(3 * n * Real.log n) ≤ |gap I|) t I₀ := by
  sorry

/-- **Binary 3-Majority from any configuration.** There is `C > 0` such that, for `log n ≥ 40`,
from any configuration `I₀` (in particular from a perfectly balanced one), all nodes hold the same
opinion after any `T ≥ C log n` rounds with probability at least `1 - C log n / n`. -/
theorem majority3_any_start : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 40 ≤ Real.log n →
    ∀ (I₀ : Finset (Fin n)) (T : ℕ), C * Real.log n ≤ T →
      1 - C * Real.log n / n
        ≤ expList (Tgt3 n) T (fun l =>
            if ThreeMajority.run I₀ l = univ ∨ ThreeMajority.run I₀ l = ∅ then (1 : ℝ) else 0) := by
  sorry

end Plurality
