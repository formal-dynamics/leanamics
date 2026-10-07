# Weighted synchronous voter dynamics

A Lean formalization of Sections 2.1–2.3 of Hassin and Peleg,
*Distributed Probabilistic Polling and Applications to Proportionate Agreement*,
Information and Computation 171 (2001), 248–268, DOI: 10.1006/inco.2001.3088.

For a finite nonempty vertex type, each round independently samples a neighbor
at each vertex from a stochastic matrix `H`, then simultaneously copies its
previous color. On a connected nonbipartite undirected graph with
`G.Adj i j → 0 < H i j` (extra support such as self-loops is allowed, which
covers lazy chains and Wright–Fisher sampling), eventual all-white consensus probability is exactly the
initial white mass under any stationary distribution. Uniform neighbor sampling
gives `degree / (2 * edge count)`, regular graphs give the initial white fraction,
and indicator projections give the probability for every color in a finite palette.

| Paper result | Lean declarations |
| --- | --- |
| Section 2.1 | `step`, `transition`, `transition_product` |
| Stationary distribution existence | `Dynamics.Kernel.exists_stationary` (generic library result) |
| Lemma 2.1 | `monochromatic_edge`, `propagate_region`, `possible_consensus`, `consensus_tendsto` |
| Lemma 2.2 | `whiteMass_bounds`, `whiteProbability_error`, `whiteProbability_tendsto` |
| Lemma 2.3 | `round_mass`, `iterate_mass` |
| Theorem 2.1 | `consensus_probability` |
| Corollary 2.2 | `degree_stationary`, `uniform_consensus_probability` |
| Regular graphs | `regular_consensus_probability` |
| Section 2.3 | `iterate_project`, `color_consensus_probability` |
| Section 2.4 on the complete graph: duality with coalescing random walks | `runRounds_eq_comp`, `disagreement_runRounds_eq_zero` |
| Section 2.4 on the complete graph: consensus within `2 n log n` rounds w.p. `≥ 1 - 1/n` | `expList_backward_ne`, `iterate_disagreement_le`, `voter_consensus_whp` |
| Remark p. 254: Theorem 2.1 on bipartite graphs given one self-loop | `propagate_kernel_region`, `consensus_tendsto_of_selfLoop`, `consensus_probability_of_selfLoop`, `color_consensus_probability_of_selfLoop` |
| Lazy voter `(I + D⁻¹A)/2` on any connected graph (VOT-2) | `lazy`, `lazyNeighbor`, `lazy_stationary_iff`, `lazy_consensus_probability`, `lazyNeighbor_consensus_probability` |
| Neutral Wright–Fisher: allele `a` fixes w.p. `c_a / n` (VOT-2) | `wrightFisher_fixation_of_three_le`, `wrightFisher_fixation` |
| BGKM16 Section 2: volume, conductance `φ`, minority side, potential `Ψ = √vol(s_t)` (VOT-5) | `vol`, `conductance`, `discordant`, `minority`, `potential`, `dynamicLazy` |
| BGKM16 Lemma 2.1 (corrected: sum over the minority side): `𝔼Ψ' ≤ Ψ - ∑_{u∈s_t} λ_u d_u / (32 Ψ³)` (VOT-5) | `potential_drift`, `potential_drift_conductance` |
| BGKM16 Lemma 2.2 and Theorem 1.1 (i), two opinions: consensus within `128 m / (d_min φ)` rounds w.p. `≥ 1/2`, expected time `≤ 2·` that, dynamic graphs with fixed degrees (VOT-5) | `lazy_consensus_of_minority`, `lazy_consensus_conductance`, `lazy_expected_consensus_time`, `dynamic_consensus_conductance` |
| BGKM16 Theorem 1.1 (i) via Lemma 2.3, any number of opinions: `O(m / (d_min φ))` w.p. `≥ 1/2` and in expectation (VOT-5) | `lazy_expected_consensus_time_many`, `lazy_consensus_conductance_many` |

All names in the table except the explicitly qualified shared declaration are
in namespace `Voter`. The invariant-weight results have no graph assumptions.
The graph assumptions enter the absorption proof. Stationarity existence uses
Cesàro averages and compactness; no uniqueness assumption is needed.

`eventualColor` is the supremum of the increasing finite-time probabilities of
a specified consensus color. The proof bounds the difference between invariant
white mass and all-white probability by nonconsensus probability; this is the
shared finite-horizon optional stopping theorem
`Dynamics.Kernel.event_error_of_invariant` with the two consensus configurations as
targets. The shared finite-chain theorem makes that bound tend to zero geometrically in
blocks.
This formalizes the paper's transience argument through survival probabilities,
without introducing a separate classification of recurrent states.

`Examples.lean` checks constant configurations, a triangle with winning probability
one third, a nonuniform stochastic matrix, and color projection. It also proves
that the two-vertex alternating coloring flips and returns after two steps;
neither configuration is constant. The unique-neighbor lemma explains why every
legal round on that graph has exactly this behavior.

Build and audit:

```bash
lake exe cache get
lake build
python3 ../scripts/check_axioms.py
```

This package imports the sibling `dynamics/` package and shares its Lean 4.32.0
and exact Mathlib pin. The [blueprint](blueprint/src/content.tex) maps the paper
results to declarations, separates generic library results, and generates the
dependency graph. The repository's Pages workflow builds the blueprint and API
documentation alongside the existing projects.

On the complete graph with self-loops (Wright–Fisher sampling), `Coalescence.lean`
proves the duality with coalescing random walks and the consensus-time bound; the
backward walks from two distinct vertices fail to meet in `T` rounds with probability
exactly `(1 - 1/n)^T`.

Hassin and Peleg remark (p. 254) that one self-loop, even at a single vertex, removes the
nonbipartiteness hypothesis. `LazyPropagation.lean` and `LazyLoop.lean` formalize this: rounds are
taken in the kernel support, so the self-loop vertex starts the propagation of Lemma 2.1. Two
corollaries follow. The lazy voter `(I + D⁻¹A)/2` (`Lazy.lean`) reaches consensus in colour `c`
with probability `∑_{i coloured c} dᵢ / 2m` on every connected graph, bipartite ones included.
Neutral Wright–Fisher (`WrightFisher.lean`) fixes allele `a` with probability `c_a / n` for every
`n ≥ 1`; for `n ≥ 3` this already follows from the nonbipartite theorem on `K_n`.

Future work: convergence-time bounds on general graphs, dynamic networks, and extremal
coalition results.
