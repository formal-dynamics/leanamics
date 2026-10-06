# Reed–Frost epidemics and bond percolation

A Lean formalization of the pathwise correspondence between the Reed–Frost (Independent Cascade)
epidemic and bond percolation (after Kempe, Kleinberg and Tardos, KDD 2003; see also Becchetti et
al., arXiv:2103.16398, Theorem A.3).

**Model.** Every edge of a finite graph `G` carries one coin `ω e : Bool`; the open edges form the
percolated graph `perc G ω`. In each round, a susceptible node with an infected neighbour across an
open edge becomes infected, and every infected node recovers for good.

**Main results** (in [`Epidemics/ReedFrost.lean`](Epidemics/ReedFrost.lean), namespace `Epidemics`):

| Result | Lean declaration |
| --- | --- |
| Nodes infected in round `t` = nodes at distance `t` from `I₀` in `perc G ω` | `infected_iff` |
| Nodes recovered by round `t` = nodes at distance `< t` | `recovered_iff` |
| The epidemic is over after `card V` rounds, and as soon as all finite distances are `< t` | `extinct`, `extinct_of_dist_lt` |
| Final outbreak = nodes connected to `I₀` by open edges | `final_recovered_iff` |
| With i.i.d. Bernoulli(`p`) coins, P(`v` eventually infected) = P(`v` connected to `I₀`) | `coins_prob_open`, `prob_infected_eq_prob_connected` |

The coupling holds for every coin assignment, which is stronger than the distributional
equivalence usually stated (with fresh coins in each round); that distributional version is not
formalized here.

**Provenance.** The statements were written and pinned by hand; the proofs were produced by a Grok
agent under a fixed-statement protocol and verified mechanically (statements unchanged, no
placeholders, warning-free build, axiom audit).

## COBRA ⇔ BIPS duality (EPI-4)

After Cooper, Radzik and Rivera, *The coalescing-branching random walk on expanders and the dual
epidemic process*, PODC 2016 ([arXiv:1602.05768](https://arxiv.org/abs/1602.05768)), Theorem 4.

**Model.** In every round each vertex samples `k` uniform neighbours with replacement (a uniform
element of `Choices G k`). COBRA: every vertex of the current set pushes to its sampled neighbours,
and the next set is the set of chosen vertices. BIPS with persistent source `v`: `v` is always
infected, and any other vertex is infected next iff one of its sampled neighbours is infected now.

**Main results** (in [`Epidemics/CobraDuality.lean`](Epidemics/CobraDuality.lean)):

| Result | Lean declaration |
| --- | --- |
| Pathwise: COBRA from `C` visits `v` within the rounds iff BIPS from `{v}` along the reversed rounds infects a vertex of `C` | `cobra_hit_iff_bips_reverse` |
| Theorem 4: `P(Hit_C(v) > t ∣ C₀ = C) = P(C ∩ A_t = ∅ ∣ A₀ = {v})` | `cobra_bips_duality` |
| Equation (2): `P(Hit_u(v) > t) = P(u ∉ A_t ∣ A₀ = {v})` | `cobra_bips_duality_singleton` |
| Time reversal of i.i.d. rounds (roadmap FND-6) | `expList_reverse` |

The paper assumes `G` connected and regular and `k ≥ 1`; the duality holds for every finite graph
and every `k`. On a connected graph with at least two vertices the rounds exist
(`choices_nonempty`), so both sides are genuine probabilities.

Build and audit:

```bash
lake exe cache get
lake build
python3 ../scripts/check_axioms.py
```

This package requires the sibling `dynamics/` package and shares its Lean 4.32.0 toolchain and exact
Mathlib pin. The [blueprint](blueprint/src/content.tex) maps the results to declarations.
