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

Build and audit:

```bash
lake exe cache get
lake build
python3 ../scripts/check_axioms.py
```

This package requires the sibling `dynamics/` package and shares its Lean 4.32.0 toolchain and exact
Mathlib pin. The [blueprint](blueprint/src/content.tex) maps the results to declarations.
