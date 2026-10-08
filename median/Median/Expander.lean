import Median.ExpanderDefs

/-! # Two-sample voting on expanders

Cooper, Elsässer and Radzik, *The power of two choices in distributed voting* (ICALP 2014,
arXiv:1404.7479), Theorem 4: on a `d`-regular `n`-vertex graph with `λ_G = 3/5 − ε`, a minority
of size at most `(ε/5) n` disappears within `O(log n)` rounds with high probability, and the
initial majority wins.

* `expander_mixing`: the expander mixing lemma (the paper's Lemma 5),
  `|E(S, T) − d |S| |T| / n| ≤ λ_G d √(|S| |T|)`.
* `phaseII_step`: the paper's Lemma 12 with `α = 3/10` (so `γ = 1/50`): if every superset `S` of
  the minority `B` with `|S| ≤ (1 + 1/α) |B|` spans at most `α d |S|` edges, one round reduces
  `|B|` by the factor `1 − γ` except with probability `e^{−|B|/4850}`.
* `two_choices_expander_explicit`: Theorem 4 with an explicit failure probability after `T`
  rounds, `(24/25)^T |B| + T e^{−ε n / 24250}`.
* `two_choices_expander`: Theorem 4 in `O(log n)` form, after `⌈C log n⌉` rounds with failure
  probability `1/n + (C log n + 1) e^{−ε n / C}`, which tends to `0`
  (`two_choices_failure_tendsto`).
-/

namespace Median
open Finset Dynamics Real Filter Topology

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Expander mixing lemma** (the paper's Lemma 5): on a `d`-regular `n`-vertex graph, for all
vertex sets `S` and `T`, `|E(S, T) − d |S| |T| / n| ≤ λ_G d √(|S| |T|)`. -/
theorem expander_mixing {d : ℕ} (hreg : G.IsRegularOfDegree d) (S T : Finset V) :
    |(edgeCount G S T : ℝ) - d * S.card * T.card / Fintype.card V|
      ≤ lambdaG G d * d * √((S.card : ℝ) * T.card) := by
  sorry

/-- **One round shrinks a sparse minority** (the paper's Lemma 12 with `α = 3/10`,
`γ = (1 − 2α)(1 − 3α)/2 = 1/50`): if every superset `S ⊇ B` of the minority `B` with
`|S| ≤ (1 + 1/α) |B|` spans at most `α d |S|` edges (`E(S, S) ≤ 2 α d |S|`), then one round
reduces the minority to at most `(1 − γ) |B|`, with probability at least `1 − e^{−|B|/4850}`. -/
theorem phaseII_step {d : ℕ} (hd : 0 < d) (hreg : G.IsRegularOfDegree d) (a : Bool)
    (x : V → Bool)
    (hsparse : ∀ S : Finset V, univ.filter (fun v => x v ≠ a) ⊆ S →
      (S.card : ℝ) ≤ (1 + 1 / (3 / 10)) * minority a x →
        (edgeCount G S S : ℝ) ≤ 2 * (3 / 10 * d * S.card)) :
    1 - exp (-((minority a x : ℝ) / 4850))
      ≤ avg (fun r : GraphRound G =>
          if (minority a (graphStep G x r) : ℝ) ≤ (1 - 1 / 50) * minority a x then (1 : ℝ)
          else 0) := by
  sorry

/-- **Theorem 4, explicit form**: on a `d`-regular `n`-vertex graph with `λ_G ≤ 3/5 − ε`, if the
minority (the vertices whose opinion differs from `a`) has size at most `(ε/5) n`, then after `T`
rounds every vertex holds `a`, except with probability at most
`(24/25)^T |B| + T e^{−ε n / 24250}`. -/
theorem two_choices_expander_explicit {d : ℕ} (hd : 0 < d) (hreg : G.IsRegularOfDegree d)
    {ε : ℝ} (hε : 0 < ε) (hlam : lambdaG G d ≤ 3 / 5 - ε) (a : Bool) (x : V → Bool)
    (hx : (minority a x : ℝ) ≤ ε / 5 * Fintype.card V) (T : ℕ) :
    1 - ((24 / 25 : ℝ) ^ T * minority a x + T * exp (-(ε * Fintype.card V / 24250)))
      ≤ expList (GraphRound G) T
          (fun l => if graphRun G x l = fun _ => a then (1 : ℝ) else 0) := by
  sorry

/-- **Theorem 4** (`O(log n)` form): there is an absolute constant `C` such that on every
`d`-regular `n`-vertex graph with `λ_G ≤ 3/5 − ε`, a minority of size at most `(ε/5) n`
disappears and the majority opinion `a` wins within `⌈C log n⌉` rounds, except with probability
at most `1/n + (C log n + 1) e^{−ε n / C}` (which tends to `0`, `two_choices_failure_tendsto`).
The proof gives `C = 25000`. -/
theorem two_choices_expander : ∃ C : ℝ, 0 < C ∧
    ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ},
      0 < d → G.IsRegularOfDegree d → ∀ {ε : ℝ}, 0 < ε → lambdaG G d ≤ 3 / 5 - ε →
      ∀ (a : Bool) (x : V → Bool), (minority a x : ℝ) ≤ ε / 5 * Fintype.card V →
        1 - (1 / (Fintype.card V : ℝ)
              + (C * log (Fintype.card V) + 1) * exp (-(ε * Fintype.card V / C)))
          ≤ expList (GraphRound G) ⌈C * log (Fintype.card V)⌉₊
              (fun l => if graphRun G x l = fun _ => a then (1 : ℝ) else 0) := by
  sorry

/-- The failure probability of `two_choices_expander` is `o(1)`: for fixed `C > 0` and `ε > 0`,
`1/n + (C log n + 1) e^{−ε n / C} → 0`. -/
theorem two_choices_failure_tendsto {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => 1 / (n : ℝ) + (C * log n + 1) * exp (-(ε * n / C))) atTop (𝓝 0) := by
  sorry

end Median
