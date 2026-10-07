import Averaging.RateGap

/-! # Rate of convergence of the averaging dynamics

Theorem 33 of Becchetti, Clementi, Natale, *Consensus Dynamics: An Overview*, SIGACT News
51(1), 2020 (the Survey), Section 7.2, which is Theorem 5.1 of Lovász, *Random walks on graphs:
a survey*, 1993. For the random walk `P = D⁻¹A` with stationary distribution `π(v) = d(v) / 2m`
and `λ = max {|λ₂(P)|, |λₙ(P)|}`,
`|Pᵗ(u, v) - π(v)| ≤ √(d(v) / d(u)) λᵗ` for all nodes `u, v` and times `t`
(the Survey prints `√(d(v) / d(v))`, a typo). Unless `G` is bipartite, `λ < 1`, so the
averaging dynamics `x⁽ᵗ⁾ = Pᵗ x⁽⁰⁾` converges exponentially fast to `∑ π(v) x⁽⁰⁾(v)` at every
node.

The bridges `walkMatrix_pow_apply` and `avgIter_eq_walkMatrix_pow_mulVec` identify `Pᵗ` with the
`t`-step transition probabilities `transW` and the averaging dynamics `avgIter` of
`Averaging.Basic`; `charpoly_walkMatrix` shows that `walkLambda` is computed from the spectrum
of `P`.
-/

namespace Averaging
open Finset Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `Pᵗ(u, v)` is the probability that the random walk started at `u` is at `v` after `t` steps
(Survey, Section 7.2, before Theorem 33). -/
theorem walkMatrix_pow_apply (t : ℕ) (u v : V) : (walkMatrix G ^ t) u v = transW G t u v := by
  exact walkMatrix_pow_apply_eq_transW G t u v

/-- A round of the averaging dynamics applies `P` (Survey, Section 7.2):
`x⁽ᵗ⁾ = P x⁽ᵗ⁻¹⁾ = ⋯ = Pᵗ x⁽⁰⁾`. -/
theorem avgIter_eq_walkMatrix_pow_mulVec (t : ℕ) (x : V → ℝ) :
    avgIter G t x = walkMatrix G ^ t *ᵥ x := by
  exact avgIter_eq_walkMatrix_pow_mulVec' G t x

/-- `P = D⁻¹A` and `N = D^{-1/2} A D^{-1/2}` have the same characteristic polynomial when every
degree is positive. Hence the eigenvalues of `P` with multiplicity, sorted decreasingly, are
`eigenvalues₀` of `N` (`Matrix.IsHermitian.sort_roots_charpoly_eq_eigenvalues₀`), and
`walkLambda` is the `λ` of Theorem 33. -/
theorem charpoly_walkMatrix (hdeg : ∀ v, 0 < G.degree v) :
    (walkMatrix G).charpoly = (normAdjMatrix G).charpoly := by
  exact charpoly_walkMatrix_eq G hdeg

/-- **Theorem 33** (Survey; Lovász 1993, Theorem 5.1). Let `λ = max {|λ₂(P)|, |λₙ(P)|}`. For
every `u, v ∈ V` and every `t ≥ 0`, `|Pᵗ(u, v) - π(v)| ≤ √(d(v) / d(u)) λᵗ`. -/
theorem abs_walkMatrix_pow_sub_walkStationary_le (hdeg : ∀ v, 0 < G.degree v) (u v : V)
    (t : ℕ) :
    |(walkMatrix G ^ t) u v - walkStationary G v| ≤
      √((G.degree v : ℝ) / G.degree u) * walkLambda G ^ t := by
  exact abs_walkMatrix_pow_sub_walkStationary_le' G hdeg u v t

/-- Unless `G` is bipartite, `λ < 1` (Survey, after Theorem 33): on a connected graph with a
closed walk of odd length, `λ < 1`. -/
theorem walkLambda_lt_one (hc : G.Connected)
    (hodd : ∃ (u : V) (p : G.Walk u u), Odd p.length) : walkLambda G < 1 := by
  exact walkLambda_lt_one' G hc hodd

/-- Theorem 33 for the averaging dynamics: the value of node `u` after `t` rounds is within
`λᵗ ∑ᵥ √(d(v) / d(u)) |x(v)|` of the stationary average `∑ᵥ π(v) x(v)` of the initial values
(Survey, Section 7.2: `Pᵗx → (∑ᵥ π(v) x(v)) 𝟙`). -/
theorem abs_avgIter_sub_walkStationary_le (hdeg : ∀ v, 0 < G.degree v) (x : V → ℝ) (u : V)
    (t : ℕ) :
    |avgIter G t x u - ∑ v, walkStationary G v * x v| ≤
      walkLambda G ^ t * ∑ v, √((G.degree v : ℝ) / G.degree u) * |x v| := by
  have hdiff : (walkMatrix G ^ t *ᵥ x) u - ∑ v, walkStationary G v * x v =
      ∑ v, ((walkMatrix G ^ t) u v - walkStationary G v) * x v := by
    simp only [mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib]
  rw [avgIter_eq_walkMatrix_pow_mulVec' G t x, hdiff, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun v _ => ?_)
  rw [abs_mul]
  calc |(walkMatrix G ^ t) u v - walkStationary G v| * |x v|
      ≤ (√((G.degree v : ℝ) / G.degree u) * walkLambda G ^ t) * |x v| :=
        mul_le_mul_of_nonneg_right (abs_walkMatrix_pow_sub_walkStationary_le' G hdeg u v t)
          (abs_nonneg _)
    _ = walkLambda G ^ t * (√((G.degree v : ℝ) / G.degree u) * |x v|) := by ring

end Averaging
