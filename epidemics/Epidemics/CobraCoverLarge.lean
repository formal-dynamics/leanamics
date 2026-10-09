import Epidemics.CobraCoverGrowth

/-! # BIPS for large sets: growth to `9n/10` and the end phase (EPI-4, Lemmas 3 and 4)

Cooper, Radzik, Rivera, PODC 2016 (arXiv:1602.05768), Section 5, Lemmas 3 and 4.

Both lemmas start BIPS with source `v` from an arbitrary infected set `A₀` (the state reached by
the previous phase).

* **Lemma 3** (`bips_large_phase`): from `|A₀| ≥ 4000 log n/(1 - λ)²`, the infected set reaches
  `9n/10` within `24 log n/(1 - λ)` rounds, except with probability `T n^{-5}`: while
  `|A| < 9n/10`, Lemma 1 gives `E|A'| ≥ |A| (1 + (1 - λ)/10)` and the Chernoff bound (18) with
  `ε = √(10 log n/|A|) ≤ (1 - λ)/20` gives `|A'| ≥ |A| (1 + (1 - λ)/23)` except with probability
  `n^{-5}`.
* **Lemma 4** (`bips_end_phase`): from `|A₀| ≥ 9n/10`, when `(9/10) n ≥ 4000 log n/(1 - λ)²`,
  all vertices are infected after `8 log n/(1 - λ)` rounds, except with probability `n^{-5}`: the
  infected set stays above `9n/10` except with probability `t n^{-8}` (22), and the number `B_t`
  of healthy vertices satisfies `E B_{t+1} ≤ θ E B_t + t n^{-7}` with `θ = 1 - (9/10)(1 - λ²)`
  (21)–(23).
-/

namespace Epidemics
open Finset Dynamics

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {k : ℕ}

/-- **Lemma 3** (Section 5). Let `G` be `r`-regular (`r > 0`) with `λ = lambdaG G r < 1`, and
`k ≥ 2`. If BIPS with source `v` starts from a set `A₀` with `|A₀| ≥ 4000 log n/(1 - λ)²`, then
for every `T ≥ 24 log n/(1 - λ)` the probability that `|A_s| < 9n/10` for all `s ≤ T` is at most
`T/n⁵`. The paper states `23 log n/(1 - λ)` rounds and probability `1 - n^{-4}`; its doubling
count needs a minor correction (`log₂ n` doublings, not `ln n`), and `24 log n/(1 - λ)` rounds
suffice since `(1 + (1 - λ)/23)^T ≥ e^{T(1 - λ)/24}`. -/
theorem bips_large_phase {r : ℕ} (hreg : G.IsRegularOfDegree r) (hr : 0 < r) (hk : 2 ≤ k)
    (hlam : lambdaG G r < 1) (v : V) (A₀ : Finset V)
    (hA₀ : 4000 * Real.log (Fintype.card V) / (1 - lambdaG G r) ^ 2 ≤ A₀.card) {T : ℕ}
    (hT : 24 * Real.log (Fintype.card V) / (1 - lambdaG G r) ≤ T) :
    expList (Choices G k) T
        (fun l => if ∀ s ≤ T, 10 * (bipsRun v A₀ (l.take s)).card < 9 * Fintype.card V
          then (1 : ℝ) else 0) ≤
      T / (Fintype.card V : ℝ) ^ 5 := by
  sorry

/-- **Lemma 4** (Section 5). Let `G` be `r`-regular (`r > 0`) with `λ = lambdaG G r < 1`, `k ≥ 2`,
and assume `4000 log n/(1 - λ)² ≤ (9/10) n` (the paper's `1 - λ ≫ √(log n / n)`). If BIPS with
source `v` starts from a set `A₀` with `|A₀| ≥ 9n/10`, then for every `T ≥ 8 log n/(1 - λ)` the
whole graph is infected at time `T` except with probability at most `n^{-5}`. The paper's proof
gives `n^{-5} + O(T² n^{-7})` (its `E B_T ≤ θ^T + ⋯` needs a minor correction to
`θ^T (n/10) + ⋯`, and its `T = 5 log n/log(1/θ)` should be `6 log n/log(1/θ)`); with
`B₀ ≤ n/10` and `T² ≤ n²` the total is at most `n^{-5}`. -/
theorem bips_end_phase {r : ℕ} (hreg : G.IsRegularOfDegree r) (hr : 0 < r) (hk : 2 ≤ k)
    (hlam : lambdaG G r < 1)
    (hn : 4000 * Real.log (Fintype.card V) / (1 - lambdaG G r) ^ 2 ≤ 9 * Fintype.card V / 10)
    (v : V) (A₀ : Finset V) (hA₀ : 9 * Fintype.card V ≤ 10 * A₀.card) {T : ℕ}
    (hT : 8 * Real.log (Fintype.card V) / (1 - lambdaG G r) ≤ T) :
    expList (Choices G k) T (fun l => if bipsRun v A₀ l = univ then (0 : ℝ) else 1) ≤
      1 / (Fintype.card V : ℝ) ^ 5 := by
  sorry

end Epidemics
