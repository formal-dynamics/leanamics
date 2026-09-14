# Weighted synchronous voter dynamics

A Lean formalization of Sections 2.1–2.3 of Hassin and Peleg,
*Distributed Probabilistic Polling and Applications to Proportionate Agreement*,
Information and Computation 171 (2001), 248–268, DOI: 10.1006/inco.2001.3088.

For a finite nonempty vertex type, each round independently samples a neighbor
at each vertex from a stochastic matrix `H`, then simultaneously copies its
previous color. On a connected nonbipartite undirected graph with
`0 < H i j ↔ G.Adj i j`, eventual all-white consensus probability is exactly the
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

All names in the table except the explicitly qualified shared declaration are
in namespace `Voter`. The invariant-weight results have no graph assumptions.
The graph assumptions enter the absorption proof. Stationarity existence uses
Cesàro averages and compactness; no uniqueness assumption is needed.

`eventualColor` is the supremum of the increasing finite-time probabilities of
a specified consensus color. The proof bounds the difference between invariant
white mass and all-white probability by nonconsensus probability. The shared
finite-chain theorem makes that bound tend to zero geometrically in blocks.
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

Future work: convergence-time bounds, dynamic networks, and extremal coalition
results. These are outside this milestone.
