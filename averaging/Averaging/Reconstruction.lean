import Averaging.ReconstructionCount

/-! # Strong reconstruction by averaging (roadmap AVG-2)

Theorem 3.2 of Becchetti, Clementi, Natale, Pasquale, Trevisan, *Find your place: simple
distributed algorithms for community detection*, SODA 2017; SIAM J. Comput. 49(4), 2020
(arXiv:1511.03927): on a connected `(2n, d, b)`-clustered regular graph with
`1 - 2b/d > (1 + δ) λ`, the Averaging protocol started from a uniformly random `x ∈ {-1, 1}^{2n}`
produces a strong reconstruction of the two clusters within `O(log n)` rounds, w.h.p.

The argument is deterministic once `⟨x, χ⟩ ≠ 0`:
* `avgIter_eq_transitionMatrix_pow_mulVec`: `x⁽ᵗ⁾ = Pᵗ x` (Section 2);
* `transitionMatrix_mulVec_clusterIndicator`: `P χ = (1 - 2b/d) χ` (Observation A.3);
* `abs_avgIter_sub_le`: `x⁽ᵗ⁾ = α₁ 𝟙 + α₂ λ₂ᵗ χ + e⁽ᵗ⁾` with `‖e⁽ᵗ⁾‖_∞ ≤ λᵗ √(2n)` (Lemma C.1);
* `sign_avgIter_sub_eq`, `exists_sign_avgIter_sub_clusters`, `isStrongReconstruction_color`:
  from round `T(n, δ)` on, the sign of `x⁽ᵗ⁻¹⁾(u) - x⁽ᵗ⁾(u)` is `sgn (⟨x, χ⟩ χ(u))`, so the
  coloring separates the clusters (proof of Theorem 3.2);
* `reconstructionTime_le`: `T(n, δ) = O(log n / δ)`.

The only probability is the exact count `P(⟨x, χ⟩ = 0) = C(2n, n) / 4ⁿ ≤ 1 / √(π n)`
(`prob_dotProduct_clusterIndicator_eq_zero`, `choose_div_four_pow_le`; Lemma B.1), which gives
`strong_reconstruction`.
-/

namespace Averaging
open Finset Matrix Real Dynamics

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {V₁ V₂ : Finset V} {n d b : ℕ}

/-! ### The deterministic part -/

/-- `x⁽ᵗ⁾ = Pᵗ x` (Section 2): on a `d`-regular graph, `t` rounds of averaging multiply the
initial values by the `t`-th power of the transition matrix. -/
theorem avgIter_eq_transitionMatrix_pow_mulVec (hreg : G.IsRegularOfDegree d) (t : ℕ)
    (x : V → ℝ) : avgIter G t x = (transitionMatrix G d ^ t) *ᵥ x := by
  exact avgIter_eq_pow_mulVec hreg t x

/-- **Observation A.3.** The partition indicator vector `χ` of a `(2n, d, b)`-clustered regular
graph is an eigenvector of the transition matrix with eigenvalue `1 - 2b/d`. -/
theorem transitionMatrix_mulVec_clusterIndicator (hG : IsClusteredRegular G V₁ V₂ n d b)
    (hd : 0 < d) :
    transitionMatrix G d *ᵥ clusterIndicator V₁ V₂ =
      (1 - 2 * (b : ℝ) / d) • clusterIndicator V₁ V₂ := by
  exact transitionMatrix_mulVec_clusterIndicator_aux hG hd

/-- **Lemma C.1.** Run the Averaging dynamics on a `(2n, d, b)`-clustered regular graph from any
`x ∈ {-1, 1}^{2n}`. If `λ < 1 - 2b/d`, then at every round `t`,
`x⁽ᵗ⁾ = α₁ 𝟙 + α₂ λ₂ᵗ χ + e⁽ᵗ⁾` with `α₁ = ⟨x, 𝟙⟩ / 2n`, `α₂ = ⟨x, χ⟩ / 2n`, `λ₂ = 1 - 2b/d` and
`‖e⁽ᵗ⁾‖_∞ ≤ λᵗ √(2n)`. -/
theorem abs_avgIter_sub_le (hG : IsClusteredRegular G V₁ V₂ n d b) (hd : 0 < d)
    (hlam : maxAbsOtherEigenvalue G d < 1 - 2 * (b : ℝ) / d) {x : V → ℝ}
    (hx : ∀ v, x v = 1 ∨ x v = -1) (t : ℕ) (v : V) :
    |avgIter G t x v - ((∑ u, x u) / (2 * n) +
        (x ⬝ᵥ clusterIndicator V₁ V₂) / (2 * n) * (1 - 2 * (b : ℝ) / d) ^ t *
          clusterIndicator V₁ V₂ v)| ≤
      maxAbsOtherEigenvalue G d ^ t * √(2 * n) := by
  exact abs_avgIter_sub_le_aux hG hd hlam hx t v

/-- **Theorem 3.2, deterministic part** (inequality (3) in its proof). Let `G` be a connected
`(2n, d, b)`-clustered regular graph with `1 - 2b/d > (1 + δ) λ` for some `δ > 0`, and let
`x ∈ {-1, 1}^{2n}` with `⟨x, χ⟩ ≠ 0`. Then at every round `t ≥ T(n, δ)`, for every node `u`,
`sgn (x⁽ᵗ⁻¹⁾(u) - x⁽ᵗ⁾(u)) = sgn (⟨x, χ⟩ χ(u))`. -/
theorem sign_avgIter_sub_eq (hG : IsClusteredRegular G V₁ V₂ n d b) (hconn : G.Connected)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : (1 + δ) * maxAbsOtherEigenvalue G d < 1 - 2 * (b : ℝ) / d) {x : V → ℝ}
    (hx : ∀ v, x v = 1 ∨ x v = -1) (hχ : x ⬝ᵥ clusterIndicator V₁ V₂ ≠ 0) {t : ℕ}
    (ht : reconstructionTime n δ ≤ t) (u : V) :
    SignType.sign (avgIter G (t - 1) x u - avgIter G t x u) =
      SignType.sign ((x ⬝ᵥ clusterIndicator V₁ V₂) * clusterIndicator V₁ V₂ u) := by
  exact sign_avgIter_sub_eq_aux hG hconn hδ hgap hx hχ ht u

/-- **Theorem 3.2, deterministic part, cluster form.** Under the hypotheses of
`sign_avgIter_sub_eq`, there is a nonzero sign `s` such that at every round `t ≥ T(n, δ)` the
sign of `x⁽ᵗ⁻¹⁾(u) - x⁽ᵗ⁾(u)` is `s` at every node `u ∈ V₁` and `-s` at every node `u ∈ V₂`. -/
theorem exists_sign_avgIter_sub_clusters (hG : IsClusteredRegular G V₁ V₂ n d b)
    (hconn : G.Connected) {δ : ℝ} (hδ : 0 < δ)
    (hgap : (1 + δ) * maxAbsOtherEigenvalue G d < 1 - 2 * (b : ℝ) / d) {x : V → ℝ}
    (hx : ∀ v, x v = 1 ∨ x v = -1) (hχ : x ⬝ᵥ clusterIndicator V₁ V₂ ≠ 0) :
    ∃ s : SignType, s ≠ 0 ∧ ∀ t, reconstructionTime n δ ≤ t →
      (∀ u ∈ V₁, SignType.sign (avgIter G (t - 1) x u - avgIter G t x u) = s) ∧
        ∀ u ∈ V₂, SignType.sign (avgIter G (t - 1) x u - avgIter G t x u) = -s := by
  exact exists_sign_avgIter_sub_clusters_aux hG hconn hδ hgap hx hχ

/-- **Theorem 3.2, deterministic part, coloring form.** Under the hypotheses of
`sign_avgIter_sub_eq`, the coloring computed by the Averaging protocol at every round
`t ≥ T(n, δ)` is a strong reconstruction of `(V₁, V₂)`. -/
theorem isStrongReconstruction_color (hG : IsClusteredRegular G V₁ V₂ n d b)
    (hconn : G.Connected) {δ : ℝ} (hδ : 0 < δ)
    (hgap : (1 + δ) * maxAbsOtherEigenvalue G d < 1 - 2 * (b : ℝ) / d) {x : V → ℝ}
    (hx : ∀ v, x v = 1 ∨ x v = -1) (hχ : x ⬝ᵥ clusterIndicator V₁ V₂ ≠ 0) {t : ℕ}
    (ht : reconstructionTime n δ ≤ t) :
    IsStrongReconstruction V₁ V₂ (color G x t) := by
  exact isStrongReconstruction_color_aux hG hconn hδ hgap hx hχ ht

/-- The number of rounds is `O(log n)` for constant `δ` (Theorem 3.2): for `n ≥ 2` and
`0 < δ ≤ 1`, `T(n, δ) ≤ 10 log n / δ + 2`. -/
theorem reconstructionTime_le (hn : 2 ≤ n) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (reconstructionTime n δ : ℝ) ≤ 10 * Real.log n / δ + 2 := by
  exact reconstructionTime_le_aux hn hδ hδ1

/-! ### The probabilistic part -/

/-- **Lemma B.1, exact form** (proof of Theorem 3.2). For `x` uniform in `{-1, 1}^{2n}`
(Rademacher initialization, `{-1, 1} = ℤˣ`), `⟨x, χ⟩` is a sum of `2n` independent Rademacher
signs, so `P(⟨x, χ⟩ = 0) = C(2n, n) / 4ⁿ`. -/
theorem prob_dotProduct_clusterIndicator_eq_zero (hV : IsBalancedPartition V₁ V₂ n) :
    (Distribution.uniform (V → ℤˣ)).prob
        (fun σ => (fun v => ((σ v : ℤ) : ℝ)) ⬝ᵥ clusterIndicator V₁ V₂ = 0) =
      ((2 * n).choose n : ℝ) / 4 ^ n := by
  exact prob_dotProduct_clusterIndicator_eq_zero_aux hV

/-- The central binomial bound of Lemma B.1: `C(2n, n) / 4ⁿ ≤ 1 / √(π n)` for `n ≥ 1`. -/
theorem choose_div_four_pow_le (hn : 0 < n) :
    ((2 * n).choose n : ℝ) / 4 ^ n ≤ 1 / √(π * n) := by
  exact choose_div_four_pow_le_aux hn

/-- **Theorem 3.2** (Strong reconstruction). Let `G` be a connected `(2n, d, b)`-clustered
regular graph with `1 - 2b/d > (1 + δ) λ` for some `δ > 0`. With probability at least
`1 - 1 / √(π n)` over the Rademacher initialization `x ∈ {-1, 1}^{2n}`, the Averaging protocol
produces a strong reconstruction at every round `t ≥ T(n, δ)`, and `T(n, δ) = O(log n / δ)`
(`reconstructionTime_le`). -/
theorem strong_reconstruction (hG : IsClusteredRegular G V₁ V₂ n d b) (hconn : G.Connected)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : (1 + δ) * maxAbsOtherEigenvalue G d < 1 - 2 * (b : ℝ) / d) :
    1 - 1 / √(π * n) ≤ (Distribution.uniform (V → ℤˣ)).prob (fun σ =>
      ∀ t, reconstructionTime n δ ≤ t →
        IsStrongReconstruction V₁ V₂ (color G (fun v => ((σ v : ℤ) : ℝ)) t)) := by
  exact strong_reconstruction_aux hG hconn hδ hgap

end Averaging
