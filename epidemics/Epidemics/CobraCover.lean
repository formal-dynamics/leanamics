import Epidemics.CobraCoverSmall
import Epidemics.CobraCoverLarge

/-! # The BIPS infection time and the COBRA cover time on expanders (EPI-4, Theorems 1 and 2)

Cooper, Radzik, Rivera, *The coalescing-branching random walk on expanders and the dual epidemic
process*, PODC 2016 (arXiv:1602.05768), Theorems 1 and 2.

Let `G` be an `n`-vertex `r`-regular graph whose random walk has absolute second eigenvalue `λ`
(`lambdaG G r`), with `1 - λ ≫ √(log n / n)`, i.e. `1 - λ ≥ C₀ √(log n / n)` for a suitably large
constant `C₀` (the paper's footnote to Theorem 1), and let `k ≥ 2`.

* **Theorem 2** (`bips_infection_time`, `bips_infection_time_expectation`): BIPS with source `v`
  from `A₀ = {v}` has infected all of `V` after `T = O(log n/(1 - λ)³)` rounds with probability
  `1 - O(n^{-3})`, and `infec(v) = min {t : A_t = V}` has expectation `O(log n/(1 - λ)³)`.
  Proof: Lemma 2 with `m = 4000 log n/(1 - λ)²` and `C = 3`, then Lemma 3, then Lemma 4, chained
  at the first hitting times of the phases.
* **Theorem 1** (`cobra_cover_time`, `cobra_cover_time_expectation`): COBRA from any `u` visits
  every vertex at some time `1 ≤ t ≤ T`, `T = O(log n/(1 - λ)³)`, with probability
  `1 - O(n^{-2})`, and `cov(u) = min {T : ⋃_{t=1}^T C_t = V}` has expectation
  `O(log n/(1 - λ)³)`. Proof: the duality (Theorem 4, `cobra_bips_duality`) gives
  `P(Hit_C(w) > t) = P(C ∩ A_t = ∅ ∣ A₀ = {w}) ≤ P(infec(w) > t)` for nonempty `C`, then a union
  bound over `w`; the expectation by restarting every `T` rounds, equation (1).

*Finite form.* "With probability `1 - O(f)`" is `∃ C, P(failure) ≤ C f` with `C` independent of
the graph, of `n`, `r`, `k` and the vertices. An expectation `E τ` of a time `τ` is written through
its tail sum `E τ = ∑_{s ≥ 0} P(τ > s)`, bounded uniformly over all partial sums `s < H`. The
event "`A_s = V`" for BIPS is persistent (`bipsStep_univ`), so `P(infec(v) > s) = P(A_s ≠ V)`.
-/

namespace Epidemics
open Finset Dynamics

/-- **Theorem 2** (Section 1; proved in Sections 3 to 5), probability bound. There are constants
`C₀, C` such that for every `r`-regular graph (`r > 0`) on `n` vertices with
`1 - λ ≥ C₀ √(log n / n)`, every `k ≥ 2`, every source `v` and every `T ≥ C log n/(1 - λ)³`,
BIPS with source `v` from `A₀ = {v}` has not infected all vertices at time `T` with probability at
most `C / n³`. (The paper assumes `G` connected and `k = 2`; `1 - λ > 0` forces connectivity.) -/
theorem bips_infection_time :
    ∃ C₀ C : ℝ, ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj] (r k : ℕ), G.IsRegularOfDegree r → 0 < r → 2 ≤ k →
      C₀ * √(Real.log (Fintype.card V) / Fintype.card V) ≤ 1 - lambdaG G r →
      ∀ (v : V) (T : ℕ), C * Real.log (Fintype.card V) / (1 - lambdaG G r) ^ 3 ≤ T →
      expList (Choices G k) T (fun l => if bipsRun v {v} l = univ then (0 : ℝ) else 1) ≤
        C / (Fintype.card V : ℝ) ^ 3 := by
  sorry

/-- **Theorem 2** (Section 1), expectation bound `Infec(G) = O(log n/(1 - λ)³)`: under the same
hypotheses, every partial tail sum `∑_{s < H} P(infec(v) > s) = ∑_{s < H} P(A_s ≠ V)` (that is,
`E min (infec(v), H)`) is at most `C log n/(1 - λ)³`. -/
theorem bips_infection_time_expectation :
    ∃ C₀ C : ℝ, ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj] (r k : ℕ), G.IsRegularOfDegree r → 0 < r → 2 ≤ k →
      C₀ * √(Real.log (Fintype.card V) / Fintype.card V) ≤ 1 - lambdaG G r →
      ∀ (v : V) (H : ℕ),
      ∑ s ∈ range H,
          expList (Choices G k) s (fun l => if bipsRun v {v} l = univ then (0 : ℝ) else 1) ≤
        C * Real.log (Fintype.card V) / (1 - lambdaG G r) ^ 3 := by
  sorry

/-- **Theorem 1** (Section 1), probability bound. There are constants `C₀, C` such that for every
`r`-regular graph (`r > 0`) on `n` vertices with `1 - λ ≥ C₀ √(log n / n)`, every `k ≥ 2`, every
start vertex `u` and every `T ≥ C log n/(1 - λ)³`, COBRA started from `{u}` fails to visit every
vertex at the times `1, …, T` (`⋃_{t=1}^T C_t ≠ V`, i.e. `cov(u) > T`) with probability at most
`C / n²`. (The paper assumes `G` connected and `k = 2`.) -/
theorem cobra_cover_time :
    ∃ C₀ C : ℝ, ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj] (r k : ℕ), G.IsRegularOfDegree r → 0 < r → 2 ≤ k →
      C₀ * √(Real.log (Fintype.card V) / Fintype.card V) ≤ 1 - lambdaG G r →
      ∀ (u : V) (T : ℕ), C * Real.log (Fintype.card V) / (1 - lambdaG G r) ^ 3 ≤ T →
      expList (Choices G k) T
          (fun l => if (Icc 1 T).biUnion (fun s => cobraRun {u} (l.take s)) = univ
            then (0 : ℝ) else 1) ≤
        C / (Fintype.card V : ℝ) ^ 2 := by
  sorry

/-- **Theorem 1** (Section 1), expectation bound `COV(G) = max_u E cov(u) = O(log n/(1 - λ)³)`:
under the same hypotheses, every partial tail sum
`∑_{s < H} P(cov(u) > s) = ∑_{s < H} P(⋃_{t=1}^s C_t ≠ V)` is at most `C log n/(1 - λ)³`. -/
theorem cobra_cover_time_expectation :
    ∃ C₀ C : ℝ, ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj] (r k : ℕ), G.IsRegularOfDegree r → 0 < r → 2 ≤ k →
      C₀ * √(Real.log (Fintype.card V) / Fintype.card V) ≤ 1 - lambdaG G r →
      ∀ (u : V) (H : ℕ),
      ∑ s ∈ range H,
          expList (Choices G k) s
            (fun l => if (Icc 1 s).biUnion (fun t => cobraRun {u} (l.take t)) = univ
              then (0 : ℝ) else 1) ≤
        C * Real.log (Fintype.card V) / (1 - lambdaG G r) ^ 3 := by
  sorry

end Epidemics
