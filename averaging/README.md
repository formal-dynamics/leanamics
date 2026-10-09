# Averaging dynamics on graphs

Every node of a finite graph replaces its value by the average of its neighbours' values. Conservation and
convergence on connected non-bipartite graphs in [`Averaging/Basic.lean`](Averaging/Basic.lean), namespace
`Averaging`; see the [blueprint](blueprint/src/content.tex) for the statements and the map to Lean
declarations, and [`FORMALIZATION_DIFFERENCES.md`](FORMALIZATION_DIFFERENCES.md) for the deviations
from the sources.

## Rate of convergence and sequential averaging (roadmap AVG-1)

Section 7.2 of Becchetti, Clementi, Natale, *Consensus Dynamics: An Overview* (SIGACT News
51(1), 2020; the Survey), with Theorem 5.1 of Lovász, *Random walks on graphs: a survey* (1993)
and equations (4)–(5) after Boyd, Ghosh, Prabhakar, Shah, *Randomized gossip algorithms* (2006).
For the random walk `P = D⁻¹A`, its stationary distribution `π(v) = d(v)/2m` and
`λ = max {|λ₂|, |λₙ|}`, `|Pᵗ(u,v) - π(v)| ≤ √(d(v)/d(u)) λᵗ`, and `λ < 1` on connected
non-bipartite graphs, so the averaging dynamics converges exponentially fast. In the random
sequential model (one uniformly random edge averages its endpoints), the expected step matrix is
`I - L/2m` and `𝔼[x⁽ᵗ⁾] = (I - L/2m)ᵗ x⁽⁰⁾`. Statements in [`Averaging/Rate.lean`](Averaging/Rate.lean)
and [`Averaging/Sequential.lean`](Averaging/Sequential.lean) (definitions in `RateDefs.lean`,
`SequentialDefs.lean`), all proved:

| Source | Lean |
| --- | --- |
| `P = D⁻¹A`, `N = D^{-1/2}AD^{-1/2}`, `λ`, `π` | `walkMatrix`, `normAdjMatrix`, `walkLambda`, `walkStationary` |
| `Pᵗ(u,v)` is the `t`-step walk probability; `x⁽ᵗ⁾ = Pᵗ x⁽⁰⁾` | `walkMatrix_pow_apply`, `avgIter_eq_walkMatrix_pow_mulVec` |
| `P` and `N` have the same spectrum | `charpoly_walkMatrix` |
| Survey Theorem 33 (Lovász Theorem 5.1) | `abs_walkMatrix_pow_sub_walkStationary_le` |
| Unless `G` is bipartite, `λ < 1` | `walkLambda_lt_one` |
| Rate of the averaging dynamics | `abs_avgIter_sub_walkStationary_le` |
| Edge step `W` (equation (2)), doubly stochastic, `WᵀW = W` | `Sequential.edgeMatrix`, `edgeMatrix_mulVec`, `edgeMatrix_mem_doublyStochastic`, `transpose_edgeMatrix_mul_self` |
| Equation (4) and its regular case (5) | `Sequential.avg_expect_edgeMatrix`, `gossipMeanMatrix_of_isRegular` |
| Uniform random edge: `𝔼[W] = I - L/2m`, regular case (5) | `Sequential.avg_edgeMatrix`, `meanMatrix_of_isRegular` |
| Second moment `𝔼[WᵀW] = 𝔼[W]`, `𝔼‖Wx‖² = xᵀW̄x` | `Sequential.avg_transpose_edgeMatrix_mul_self`, `avg_sum_sq_edgeMatrix_mulVec` |
| First moment `𝔼[x⁽ᵗ⁾] = W̄ᵗ x⁽⁰⁾` (Section 7.3.2) | `Sequential.expList_seqRun` |

Proof files: `RateMatrix.lean`, `RateSpectral.lean`, `RateGap.lean`, `RateBound.lean`,
`SequentialMatrix.lean`. The Survey's Theorem 33 prints `√(d(v)/d(v))`, a typo for `√(d(v)/d(u))`.
`transitionMatrix` (AVG-2) and `walkMatrix` coincide on regular graphs and the two parts prove
similar spectral lemmas; their unification is tracked in issue #53.

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

**Provenance.** The statements were written and pinned by a second agent; the proofs were produced by a Grok
agent under a fixed-statement protocol and verified mechanically (statements unchanged, no
placeholders, warning-free build, axiom audit). The AVG-1 statements (the rate bound
`Averaging/Rate*.lean`, Lovász's Theorem 5.1, and the sequential-averaging identities
`Averaging/Sequential*.lean`) and the AVG-2 statements were pinned by a Claude agent, reviewed by a second
agent against the sources, and then proved by the agent under the same protocol.

Build and audit:

```bash
lake exe cache get
lake build
python3 ../scripts/check_axioms.py
```

This package uses the sibling `dynamics/` package's Lean 4.32.0 toolchain and exact Mathlib pin.

## Averaging whenever you meet (roadmap AVG-3)

Becchetti, Clementi, Manurangsi, Natale, Pasquale, Raghavendra, Trevisan, *Average whenever you
meet: opportunistic protocols for community detection* (ESA 2018,
[arXiv:1703.05045](https://arxiv.org/abs/1703.05045)). One uniformly random edge is activated per
round; a node activated for the first time draws a uniform sign `±1`, and the two endpoints
replace their values by their average (`Averaging(1/2)`, Algorithm 1). On an `(n, d, b)`-clustered
regular graph whose cut is sparse with respect to the inner expansion (`λ₂ = 2b/d ≪ λ₃`), the
values stay close to the initial average of each community over the phase
`6 (n/λ₃) log n ≤ t ≤ 12 (n/λ₃) log n`, so their signs recover the communities. Namespace
`Averaging.Opportunistic`, files `Averaging/Opportunistic*.lean`, all proved:

| Paper | Lean |
| --- | --- |
| Algorithm 1, first activations by deferred decisions | `oppStep`, `oppRun`, `oppRun_getD`, `oppRun_isSome_iff` |
| Uniform edge as uniform dart; conservation | `avg_dart_edge`, `sum_avgRun` |
| Equations (1), (2), Observation A.2, equation (15) | `stepMatrix`, `meanStepMatrix`, `stepMatrix_mulVec`, `stepMatrix_isSymm`, `stepMatrix_mul_self`, `avg_stepMatrix`, `meanStepMatrix_isSymm`, `meanStepMatrix_mem_doublyStochastic`, `avg_edgeAvg`, `expList_avgRun`, `avg_sum_sq_edgeAvg` |
| Definition 2.2, `χ`, `Q₁`, `Q₂`, `Q₃⋯ₙ` (equation (7)), `λ₃` | `IsClusteredRegular`, `cutVec`, `projOne`, `projCut`, `projRest`, `ThirdEigenvalueLB` |
| Theorem 3.1 on clustered regular graphs (Lemmas B.1, B.3, B.4) | `meanStepMatrix_mulVec_cutVec`, `expList_projCut`, `expList_avgRun_decomp`, `sum_sq_meanStepMatrix_pow_le`, `monotone_criterion`, `sign_criterion` |
| Lemmas C.2, C.3 (one round) | `IsClusteredRegular.avg_cutDev_edgeAvg_le`, `IsClusteredRegular.avg_restSq_edgeAvg_le` |
| Lemma C.4 (unrolled recursions) | `IsClusteredRegular.expList_secondMoment_le` |
| Theorem 4.1 (second moment analysis) | `secondMoment_bound` (`c = 100`) |
| Definitions 4.1, 2.3 | `IsGood`, `IsWeakReconstruction` |
| Lemma 4.2 (non-ephemeral good nodes) | `nonEphemeral_good` (`c = 10⁶`) |
| Sign of the values over the phase (Section 4.2, Lemma A.1) | `sign_phase` (`c = 10⁶`, `C = 4`) |
| Weak reconstruction over the phase | `weakReconstruction_phase` (`c = 10⁶`, `C = 6`) |

Proof files: `OpportunisticOneStep.lean` (one round: Lemmas C.2, C.3),
`OpportunisticSecondMoment.lean` (Lemma C.4, Theorem 4.1), `OpportunisticGood.lean` (good nodes
stay good: the deterministic part of Lemma 4.2), `OpportunisticNonEphemeral.lean` (expectation
bounds, anti-concentration of `‖y⁽⁰⁾‖²`, Lemma 4.2), `OpportunisticSigns.lean` and
`OpportunisticSignEvents.lean` (sums of independent signs, Lemma A.1). The general-graph theorems
`IsClusteredRegular.prob_good_window`, `prob_sign_window` and `prob_weakReconstruction_window`
state the last three results on any finite vertex type. The proofs of Theorem 4.1 and Lemma 4.2
follow the paper's strategy but not its bookkeeping; see
[`FORMALIZATION_DIFFERENCES.md`](FORMALIZATION_DIFFERENCES.md). The step matrix of this part and
`Sequential.edgeMatrix` (AVG-1) describe the same uniform-edge step.

Provenance of AVG-3: the statements were fixed by a Claude agent before the proofs and reviewed
by a second Claude agent against the paper (the review led to `±1` labels in Definition 2.3); the
proofs are by Claude agents under the fixed-statement protocol, verified mechanically (no
placeholders, warning-free build, axiom audit).

## How to cite

See [How to cite](../README.md#how-to-cite) in the main README.
