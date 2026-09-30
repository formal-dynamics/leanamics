# The Moran process and the isothermal theorem

A Lean formalization of the Birth–death Moran process on a finite graph and of the
"if" direction of the isothermal theorem (Lieberman, Hauert and Nowak, *Evolutionary dynamics
on graphs*, Nature 433, 2005), with Moran's formula (1958) as a corollary.

**Model.** Mutants have fitness `r > 0`, residents fitness `1`. In each step a parent is chosen
with probability proportional to its fitness, and its offspring replaces a uniformly random
neighbour (an isolated parent replaces itself). This is the "invasion process", i.e. a
sequential PUSH voter with fitness-biased senders.

**Main results** (all in [`Moran/Isothermal.lean`](Moran/Isothermal.lean), namespace `Moran`):

| Result | Lean declaration |
| --- | --- |
| The Birth–death kernel is well defined | `pair_weight_nonneg`, `pair_weight_sum_one`, `moranKernel` |
| On a regular graph, `(1/r)^(#mutants)` is invariant in expectation | `moran_potential_invariant` |
| On a regular graph with `r = 1`, `#mutants` is invariant in expectation | `moran_mutants_invariant` |
| On a connected graph, fixation or extinction happens with probability 1 | `moran_unfixed_tendsto` |
| **Isothermal theorem:** on a connected regular graph, `P(fixation from k mutants) = (1 - r^-k)/(1 - r^-n)` | `isothermal` |
| Neutral case `r = 1`: `P(fixation) = k/n` | `isothermal_neutral` |
| **Moran's formula** on the complete graph | `moran_formula` |

The key identity is that on a regular graph a step adds a mutant with exactly `r` times the
probability that it removes one, in every configuration, because the numbers of
mutant–resident and resident–mutant edges coincide (`orientedCut_symm`, `birth_eq_r_death`).
The fixation probability is the supremum of the increasing finite-time fixation
probabilities, identified through an invariant potential and the shared absorption theorem of
[`dynamics/`](../dynamics); no path-space measure is used.

Only the "if" direction is formalized: the commonly quoted "if and only if" is false
(Galanis, Göbel, Goldberg, Lapinskas and Richerby, *Amplifiers for the Moran process*, J. ACM
2017, Proposition 12), and the classical proof, which projects onto the number of mutants,
needs care because that projection is not Markov in general (Keller and Uğurlu,
arXiv:2403.12598).

**Provenance.** The statements were written and pinned by hand; the proofs were produced by a
Grok agent under a fixed-statement protocol and verified mechanically (statements unchanged,
no placeholders, warning-free build, axiom audit).

Build and audit:

```bash
lake exe cache get
lake build
python3 ../scripts/check_axioms.py
```

This package requires the sibling `dynamics/` package and shares its Lean 4.32.0 toolchain
and exact Mathlib pin. The [blueprint](blueprint/src/content.tex) maps the results to
declarations and generates the dependency graph.
