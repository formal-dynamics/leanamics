# The Moran process and the isothermal theorem

A Lean formalization of the Birth–death Moran process on a finite graph and of the
"if" direction of the isothermal theorem (Lieberman, Hauert and Nowak, *Evolutionary dynamics
on graphs*, Nature 433, 2005), with Moran's formula (Moran 1959) as a corollary.

**Model.** Mutants have fitness `r > 0`, residents fitness `1`. In each step a parent is chosen
with probability proportional to its fitness, and its offspring replaces a uniformly random
neighbour (an isolated parent replaces itself). This is the "invasion process", i.e. a
sequential PUSH voter with fitness-biased senders.

**Main results** (in [`Moran/Isothermal.lean`](Moran/Isothermal.lean) unless noted, namespace `Moran`):

| Result | Lean declaration |
| --- | --- |
| The Birth–death kernel is well defined | `pair_weight_nonneg`, `pair_weight_sum_one`, `moranKernel` |
| On a regular graph, `(1/r)^(#mutants)` is invariant in expectation | `moran_potential_invariant` |
| On a regular graph with `r = 1`, `#mutants` is invariant in expectation | `moran_mutants_invariant` |
| On a connected graph, fixation or extinction happens with probability 1 | `moran_unfixed_tendsto` |
| **Isothermal theorem:** on a connected regular graph, `P(fixation from k mutants) = (1 - r^-k)/(1 - r^-n)` | `isothermal` |
| Neutral case `r = 1`: `P(fixation) = k/n` | `isothermal_neutral` |
| **Moran's formula** on the complete graph | `moran_formula` |
| **Push vs pull** (in [`Moran/PushPull.lean`](Moran/PushPull.lean)): on a connected graph, neutral push fixes a mutant set `S` with probability `∑_{v∈S} 1/deg v / ∑_v 1/deg v`, pull with probability `∑_{v∈S} deg v / 2|E|` | `push_fixation`, `pull_fixation` |
| **Neutral Moran chains on counts** (in [`Moran/Counts.lean`](Moran/Counts.lean)): death–Birth on `K_n` (`pullKernel ⊤`, no self-loops) lumps to the count chain with steps `±1` of probability `k(n-k)/(n(n-1))` each; Moran's model (reproducer and dying individual drawn independently, steps of probability `k(n-k)/n²`) has the same jump chain, the walk with steps `±1` of probability `1/2` absorbed at `0` and `n`; for `n ≥ 2` both fix from `k` mutants w.p. `k/n` | `birthDeath`, `moranCountKernel`, `pullCountKernel`, `pullKernel_top_lumps`, `moranCountKernel_sameJumpChain`, `pullCountKernel_jump`, `pullCountKernel_fixation`, `moranCountKernel_fixation` |
| **Moran's chain with selection on counts** (in [`Moran/Selection.lean`](Moran/Selection.lean)): Birth–death with fitness `r` on `K_n` (`moranKernel ⊤ r`: parent drawn proportionally to fitness, offspring placed on another vertex) lumps to the count chain with steps `+1` and `-1` of probabilities `rk(n-k)/((rk+n-k)(n-1))` and `k(n-k)/((rk+n-k)(n-1))`; Moran's chain (the dying individual drawn uniformly among all `n`, steps of probabilities `rk(n-k)/((rk+n-k)n)` and `k(n-k)/((rk+n-k)n)`) has the same jump chain, the walk with steps `+1` w.p. `r/(1+r)` and `-1` w.p. `1/(1+r)` absorbed at `0` and `n`; for `r ≠ 1` and `n ≥ 1` both fix from `k` mutants w.p. `(1 - r^{-k})/(1 - r^{-n})`; for `r = 1` they are the neutral count chains | `birthDeathChain`, `birthDeathCountKernel`, `moranSelectionCountKernel`, `biasedWalk`, `moranKernel_top_lumps`, `moranSelectionCountKernel_sameJumpChain`, `birthDeathCountKernel_jump`, `moranSelectionCountKernel_jump`, `birthDeathCountKernel_fixation`, `moranSelectionCountKernel_fixation`, `birthDeathCountKernel_one`, `moranSelectionCountKernel_one` |
| **Neutral push and pull on regular graphs** (in [`Moran/Selection.lean`](Moran/Selection.lean)): on `K_n` the number of mutants under neutral push is the count chain of pull; on every regular graph neutral push and pull are the same kernel on configurations | `moranKernel_top_one_lumps`, `moranKernel_one_eq_pullKernel` |
| **Star** (in [`Moran/Star.lean`](Moran/Star.lean)), `n` leaves, `q = (n+r)/(r(nr+1))`, `κ = (nr+1)/(r(n+r))`: the potential `q^(#mutant leaves) · κ^[centre mutant]` is invariant | `star_potential_invariant` |
| Fixation on the star from any configuration `s` (`r ≠ 1`): `(1 - Φ s)/(1 - κ q^n)` | `star_fixation` |
| Single mutant: `(1-q)/(1-κq^n)` from a leaf, `(1-κ)/(1-κq^n)` from the centre, their average from a uniformly random vertex | `star_fixation_leaf`, `star_fixation_centre`, `star_fixation_uniform` |
| The geometric-sum formula of Broom and Rychtář (2008), for every `r > 0` | `star_fixation_uniform_sum` |
| **The star is an amplifier**: for every `n ≥ 2`, uniform-start fixation exceeds Moran's `(1-1/r)/(1-1/r^N)` for `r > 1` and is below it for `r < 1` | `star_amplifier`, `star_amplifier_deleterious` |
| Large stars amplify `r` to `r²`: uniform-start fixation tends to `1 - 1/r²` (`r > 1`) | `star_fixation_uniform_tendsto` |

The key identity is that on a regular graph a step adds a mutant with exactly `r` times the
probability that it removes one, in every configuration, because the numbers of
mutant–resident and resident–mutant edges coincide (`orientedCut_symm`, `birth_eq_r_death`).
The fixation probability is the supremum of the increasing finite-time fixation
probabilities, identified through an invariant potential (`fixation_eq_of_invariant`) by the
shared finite-horizon optional stopping theorem `Dynamics.Kernel.iSup_event_of_invariant` and
the shared absorption theorem of [`dynamics/`](../dynamics); no path-space measure is used.

Only the "if" direction is formalized: the commonly quoted "if and only if" does not hold in general
(Galanis, Göbel, Goldberg, Lapinskas and Richerby, *Amplifiers for the Moran process*, J. ACM
2017, Proposition 12), and the classical proof, which projects onto the number of mutants,
needs care because that projection is not Markov in general (Keller and Uğurlu,
arXiv:2403.12598).

**Provenance.** The statements were written and pinned by a second agent; the proofs (of both files) were produced by a
Grok agent under a fixed-statement protocol and verified mechanically (statements unchanged,
no placeholders, warning-free build, axiom audit). The star files (`Moran/Star*.lean`, roadmap MOR-3, first item) were pinned
and proved by a Claude agent under the same protocol; the closed forms were also checked exactly
against the full `2^(n+1)`-state chain for small `n`.

Build and audit:

```bash
lake exe cache get
lake build
python3 ../scripts/check_axioms.py
```

Deviations from the sources are listed in [FORMALIZATION_DIFFERENCES.md](FORMALIZATION_DIFFERENCES.md).

This package requires the sibling `dynamics/` package and shares its Lean 4.32.0 toolchain
and exact Mathlib pin. The [blueprint](blueprint/src/content.tex) maps the results to
declarations and generates the dependency graph.

## How to cite

See [How to cite](../README.md#how-to-cite) in the main README.
