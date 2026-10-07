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
| Section 2.4, any sampling kernel: duality with two coalescing tokens; Theorem 2.4 (tail form) | `pairWalk`, `iterate_disagreement_le_pairWalk`, `iterate_disagreement_le_of_meeting` |
| Section 2.4, Fact 2.3 and Lemma 2.4 for lazy walks: meeting within `51 n³` steps w.p. `≥ 1/2` | `hitting_add_hitting_le`, `lazyNeighbor`, `lazy_meeting_le_half`, `lazy_meeting_le_pow` |
| Theorem 2.5 (Survey Thm 8), lazy voter: consensus within `255 n³ log n` rounds w.p. `≥ 1 - 1/n` on every connected graph | `lazy_voter_consensus_whp` |

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

On every connected graph, `Meeting*.lean` (VOT-6) proves the duality for an arbitrary
sampling kernel and the `O(n³ log n)` consensus time of the lazy voter dynamics (every vertex
keeps its colour with probability `1/2`, otherwise copies a uniform neighbour). Hitting times
are solutions of the Laplacian system (`MeetingHitting.lean`), and the meeting time follows
Kanade, Mallmann-Trenn, Sauerwald's comparison of synchronous and sequential walks
(`MeetingDrift.lean`). Hassin–Peleg's plain walk on nonbipartite graphs is covered only
conditionally on a meeting bound (`iterate_disagreement_le_of_meeting`); see
`PROGRESS-VOT6.md`.

Future work: dynamic networks and extremal coalition results.
