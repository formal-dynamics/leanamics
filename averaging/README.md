# Averaging dynamics on graphs

Every node of a finite graph replaces its value by the average of its neighbours' values. Main results in [`Averaging/Basic.lean`](Averaging/Basic.lean), namespace `Averaging`; see the
[blueprint](blueprint/src/content.tex) for the statements and the map to Lean declarations.

## Strong reconstruction (roadmap AVG-2)

Theorem 3.2 of Becchetti, Clementi, Natale, Pasquale, Trevisan, *Find your place: simple
distributed algorithms for community detection* (SODA 2017; SIAM J. Comput. 2020,
[arXiv:1511.03927](https://arxiv.org/abs/1511.03927)): on a connected `(2n, d, b)`-clustered regular
graph with `1 - 2b/d > (1 + δ) λ`, the Averaging protocol from a uniformly random
`x ∈ {-1, 1}^{2n}` separates the two clusters by the sign of `x⁽ᵗ⁻¹⁾(u) - x⁽ᵗ⁾(u)` at every round
`t ≥ T(n, δ) = ⌈log (4n³) / log (1 + δ)⌉ + 1 = O(log n / δ)`, with probability at least
`1 - 1/√(πn)`. Statements in [`Averaging/Reconstruction.lean`](Averaging/Reconstruction.lean)
(definitions in `ReconstructionDefs.lean`), all proved:

| Paper | Lean |
| --- | --- |
| Definition 3.1, `χ`, `P`, `λ`, coloring rule, strong reconstruction | `IsClusteredRegular`, `clusterIndicator`, `transitionMatrix`, `maxAbsOtherEigenvalue`, `color`, `IsStrongReconstruction` |
| `x⁽ᵗ⁾ = Pᵗ x` (Section 2) | `avgIter_eq_transitionMatrix_pow_mulVec` |
| Observation A.3 | `transitionMatrix_mulVec_clusterIndicator` |
| Lemma C.1 | `abs_avgIter_sub_le` |
| Theorem 3.2, deterministic part (inequality (3)) | `sign_avgIter_sub_eq`, `exists_sign_avgIter_sub_clusters`, `isStrongReconstruction_color`, `reconstructionTime_le` |
| Lemma B.1 (exact form), `C(2n,n)/4ⁿ ≤ 1/√(πn)` | `prob_dotProduct_clusterIndicator_eq_zero`, `choose_div_four_pow_le` |
| Theorem 3.2 | `strong_reconstruction` |

Proof files: `ReconstructionSpectral.lean` (eigenbasis of a real symmetric matrix on plain vectors,
Parseval, contraction off two eigenvectors), `ReconstructionMatrix.lean`,
`ReconstructionDecomp.lean` (Lemma C.1), `ReconstructionSign.lean` (deterministic core),
`ReconstructionCount.lean` (counting and Wallis). Deviations from the paper are listed in
[`FORMALIZATION_DIFFERENCES.md`](FORMALIZATION_DIFFERENCES.md).

**Provenance.** The statements were written and pinned by hand; the proofs were produced by a Grok
agent under a fixed-statement protocol and verified mechanically (statements unchanged, no
placeholders, warning-free build, axiom audit). The AVG-2 statements were pinned by a Claude agent,
reviewed by hand against the paper, and then proved by the agent under the same protocol.

Build and audit:

```bash
lake exe cache get
lake build
python3 ../scripts/check_axioms.py
```

This package uses the sibling `dynamics/` package's Lean 4.32.0 toolchain and exact Mathlib pin.
