import Median.ExpanderGeneralPhaseI

/-! # Two-sample voting on expanders with a small imbalance

Cooper, Elsässer and Radzik, *The power of two choices in distributed voting* (ICALP 2014,
arXiv:1404.7479), Theorem 2: on a `d`-regular `n`-vertex graph, if the initial imbalance is
`ν₀ = (A − B)/n ≥ K λ_G` for an absolute constant `K`, two-sample voting completes in
`O(log n)` rounds and the initial majority wins.

The proof follows the paper's Section 7 ("Putting the phases together"): Phase I
(Corollary 2, `phaseI_expander`) brings the minority down to `n/20`, and Phases II and III,
formalized as Theorem 4 (`two_choices_expander_explicit`, applied with `ε = 1/4`, which needs
`λ_G ≤ 7/20`), take it from `n/20` to `0`.

* `two_choices_expander_general_explicit`: the explicit form, with `K = 4000`, `c = 1/20`,
  `α = ν₀/4000` in Phase I, and `T₂` further rounds.
* `two_choices_expander_general`: the `O(log n)` form, after `⌈C log n⌉` rounds with failure
  probability at most `1/n + (2 C log n + C) e^{−ν₀² n / C}`.

The paper states the failure probability as `o(1)`. Phase I (the paper's Lemma 2 and
Corollary 2) only gives the failure probability `e^{−Θ(α² n)}` per round with `α ≥ λ_G`, so the
bound here is in terms of `ν₀² n` (taking `α = ν₀/K`): it tends to `0` once `ν₀² n` is large
compared with `log log n` (for instance for fixed `ν₀ > 0`), that is, once the initial
difference `|A − B| = ν₀ n` is somewhat larger than `√n`. Without such a condition the
statement of Theorem 2 needs a major correction: on the complete graph `λ_G = 1/(n − 1)`,
and an initial difference `|A − B|` bounded by a constant does not let the majority win with
probability tending to `1`.
-/

namespace Median.ExpanderGeneral
open Finset Dynamics Real

/-- **Theorem 2, explicit form**: on a `d`-regular `n`-vertex graph with
`ν₀ = imbalance a x > 0` and `4000 λ_G ≤ ν₀`, after `T₁ + T₂` rounds, where
`T₁ = phaseIRounds ν₀ (1/20)`, every vertex holds `a`, except with probability at most
`T₁ (e^{−α² n / 120} + e^{−α² n / 800}) + (24/25)^{T₂} n + (T₁ + T₂) e^{−n / 97000}` with
`α = ν₀ / 4000`. -/
theorem two_choices_expander_general_explicit {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ} (hd : 0 < d)
    (hreg : G.IsRegularOfDegree d) (a : Bool) (x : V → Bool) (hν0 : 0 < imbalance a x)
    (hlam : 4000 * lambdaG G d ≤ imbalance a x) (T₂ : ℕ) :
    1 - ((phaseIRounds (imbalance a x) (1 / 20) : ℝ)
            * (exp (-((imbalance a x / 4000) ^ 2 * (1 / 20) * Fintype.card V / 6))
              + exp (-((imbalance a x / 4000) ^ 2 * (1 / 20) ^ 2 * Fintype.card V / 2)))
          + (24 / 25 : ℝ) ^ T₂ * Fintype.card V
          + ((phaseIRounds (imbalance a x) (1 / 20) : ℝ) + T₂)
            * exp (-((Fintype.card V : ℝ) / 97000)))
      ≤ expList (GraphRound G) (phaseIRounds (imbalance a x) (1 / 20) + T₂)
          (fun l => if graphRun G x l = fun _ => a then (1 : ℝ) else 0) := by
  sorry

/-- **Theorem 2** (`O(log n)` form): there are absolute constants `K` and `C` such that on every
`d`-regular `n`-vertex graph, if the initial imbalance in favour of `a` is
`ν₀ = (A − B)/n ≥ K λ_G`, then after `⌈C log n⌉` rounds every vertex holds `a`, except with
probability at most `1/n + (2 C log n + C) e^{−ν₀² n / C}`. -/
theorem two_choices_expander_general : ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
    ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ},
      0 < d → G.IsRegularOfDegree d → ∀ (a : Bool) (x : V → Bool),
        K * lambdaG G d ≤ imbalance a x →
        1 - (1 / (Fintype.card V : ℝ) + (2 * C * log (Fintype.card V) + C)
              * exp (-(imbalance a x ^ 2 * Fintype.card V / C)))
          ≤ expList (GraphRound G) ⌈C * log (Fintype.card V)⌉₊
              (fun l => if graphRun G x l = fun _ => a then (1 : ℝ) else 0) := by
  sorry

end Median.ExpanderGeneral
