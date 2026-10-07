import Averaging.Basic
import Dynamics.Distribution

/-! # Strong reconstruction by averaging: definitions

Definitions for the strong-reconstruction theorem for the Averaging protocol (roadmap AVG-2) of
Becchetti, Clementi, Natale, Pasquale, Trevisan, *Find your place: simple distributed algorithms
for community detection*, SODA 2017; SIAM J. Comput. 49(4), 2020 (arXiv:1511.03927), Sections 2–3.

* `IsBalancedPartition`, `IsClusteredRegular`: `(2n, d, b)`-clustered regular graphs with
  clusters `V₁`, `V₂` (Definition 3.1);
* `clusterIndicator`: the partition indicator vector `χ = 𝟙_{V₁} - 𝟙_{V₂}` (Section 2);
* `transitionMatrix`: the transition matrix `P = (1/d) A` of a `d`-regular graph (Section 3);
* `maxAbsOtherEigenvalue`: `λ = max {|λᵢ| : i = 3, …, 2n}` for the eigenvalues
  `λ₁ ≥ λ₂ ≥ ⋯ ≥ λ_{2n}` of `P` (Section 2);
* `color`, `IsStrongReconstruction`: the coloring rule of the Averaging protocol and strong
  reconstruction (Section 2);
* `reconstructionTime`: an explicit number of rounds `T(n, δ)` for Theorem 3.2.

The values after `t` rounds are `x⁽ᵗ⁾ = avgIter G t x` (defined in `Averaging.Basic`).
-/

namespace Averaging
open Finset Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The clusters of Definition 3.1: `V₁` and `V₂` partition the nodes and `|V₁| = |V₂| = n`. -/
structure IsBalancedPartition (V₁ V₂ : Finset V) (n : ℕ) : Prop where
  disjoint : Disjoint V₁ V₂
  union_eq_univ : V₁ ∪ V₂ = univ
  card_left : V₁.card = n
  card_right : V₂.card = n

/-- **Definition 3.1** (Clustered regular graph). `G` is a `(2n, d, b)`-clustered regular graph
with clusters `V₁` and `V₂`: they partition the nodes with `|V₁| = |V₂| = n`, every node has
degree `d`, every node of `V₁` has exactly `b` neighbours in `V₂` and every node of `V₂` has
exactly `b` neighbours in `V₁`. -/
structure IsClusteredRegular (G : SimpleGraph V) [DecidableRel G.Adj] (V₁ V₂ : Finset V)
    (n d b : ℕ) : Prop extends IsBalancedPartition V₁ V₂ n where
  regular : G.IsRegularOfDegree d
  cross_left : ∀ v ∈ V₁, (G.neighborFinset v ∩ V₂).card = b
  cross_right : ∀ v ∈ V₂, (G.neighborFinset v ∩ V₁).card = b

/-- The partition indicator vector `χ = 𝟙_{V₁} - 𝟙_{V₂}` (Section 2). -/
noncomputable def clusterIndicator (V₁ V₂ : Finset V) : V → ℝ :=
  fun v => (if v ∈ V₁ then 1 else 0) - (if v ∈ V₂ then 1 else 0)

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The transition matrix `P = (1/d) A` of the random walk on a `d`-regular graph with adjacency
matrix `A` (Section 3; it is `D⁻¹ A` of Section 2 when every degree is `d`). -/
noncomputable def transitionMatrix (d : ℕ) : Matrix V V ℝ :=
  (d : ℝ)⁻¹ • G.adjMatrix ℝ

omit [Fintype V] [DecidableEq V] in
/-- `P = (1/d) A` is real symmetric (Section 3). -/
lemma transitionMatrix_isHermitian (d : ℕ) : (transitionMatrix G d).IsHermitian :=
  (G.isHermitian_adjMatrix ℝ).smul (IsSelfAdjoint.all _)

/-- `λ = max {|λᵢ| : i = 3, …, 2n}`: the largest absolute value among all but the two largest
eigenvalues `λ₁ ≥ λ₂ ≥ ⋯` of the transition matrix (Section 2), with the eigenvalues listed in
decreasing order and with multiplicity by Mathlib's `Matrix.IsHermitian.eigenvalues₀`. It is `0`
when there are at most two eigenvalues. -/
noncomputable def maxAbsOtherEigenvalue (d : ℕ) : ℝ :=
  ⨆ i : {i : Fin (Fintype.card V) // 2 ≤ i.val},
    |(transitionMatrix_isHermitian G d).eigenvalues₀ i.1|

/-- The coloring rule of the Averaging protocol (Section 2): at round `t ≥ 1`, node `v` is blue
(`true`) if `x⁽ᵗ⁾(v) ≥ x⁽ᵗ⁻¹⁾(v)` and red (`false`) otherwise, where `x⁽ᵗ⁾ = avgIter G t x`. -/
noncomputable def color (x : V → ℝ) (t : ℕ) (v : V) : Bool :=
  decide (avgIter G (t - 1) x v ≤ avgIter G t x v)

/-- A two-coloring `f` of the nodes is a strong reconstruction of the clusters `(V₁, V₂)` if
`f(V₁) ∩ f(V₂) = ∅` (Section 2: an `ε`-weak reconstruction with `ε = 0`). -/
def IsStrongReconstruction (V₁ V₂ : Finset V) (f : V → Bool) : Prop :=
  Disjoint (V₁.image f) (V₂.image f)

/-- Explicit number of rounds for Theorem 3.2: `T(n, δ) = ⌈log (4 n³) / log (1 + δ)⌉ + 1`, of
order `log n / δ` (`reconstructionTime_le`). -/
noncomputable def reconstructionTime (n : ℕ) (δ : ℝ) : ℕ :=
  ⌈Real.log (4 * (n : ℝ) ^ 3) / Real.log (1 + δ)⌉₊ + 1

end Averaging
