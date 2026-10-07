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

## Supercritical giant component (EPI-3)

The random graph `G(n, p)` is bond percolation on the complete graph (`perc ⊤ ω`, `ω ~ coins p`).
Following M. Krivelevich and B. Sudakov, *The phase transition in random graphs: a simple proof*
(Random Structures & Algorithms 43, 2013, arXiv:1201.6529), a depth-first search fed with the edge
coins gives, with `p n = 1 + ε` and "with high probability" made quantitative as "with probability
at least `1 - C / n`":

| Result | Lean declaration |
| --- | --- |
| Theorem 1(2): a path of length `≥ ε² n / 5`, for small `ε` | `exists_long_path` |
| Theorem 2: a component with `≥ ε n / 2` vertices, for small `ε` | `exists_giant_component` |
| Every `ε > 0`: a component with `≥ c n` vertices | `exists_linear_component` |
| Reed–Frost on `K_n`, `R₀ = 1 + ε`: outbreak `≥ ε n / 2` w.p. `≥ ε/2 - C/n` | `reedFrost_large_outbreak_explicit` |
| Reed–Frost on `K_n`, any `R₀ > 1`: outbreak `≥ c n` w.p. `≥ q > 0` | `reedFrost_large_outbreak` |

Reusable pieces: the principle of deferred decisions for adaptive queries to independent coins
(`prob_queryAnswers`, [`Epidemics/GiantCoins.lean`](Epidemics/GiantCoins.lean)); the search
itself and its invariant ([`Epidemics/GiantDFS.lean`](Epidemics/GiantDFS.lean)); the
deterministic analysis ([`Epidemics/GiantAnalysis.lean`](Epidemics/GiantAnalysis.lean)); Lemma 1(2)
with the Chernoff bounds of `dynamics/` ([`Epidemics/GiantProb.lean`](Epidemics/GiantProb.lean));
parametric versions of both theorems (`core_path`, `core_component`,
[`Epidemics/Giant.lean`](Epidemics/Giant.lean)); the epidemic reading
([`Epidemics/GiantEpidemic.lean`](Epidemics/GiantEpidemic.lean)). Deviations from the paper are
listed in [`PROGRESS-EPI3.md`](PROGRESS-EPI3.md).

**Provenance (EPI-1).** The statements were written and pinned by hand; the proofs were produced by a Grok
agent under a fixed-statement protocol and verified mechanically (statements unchanged, no
placeholders, warning-free build, axiom audit).

**Provenance (EPI-3).** The statements were pinned before any proof was written and then kept
fixed by a mechanical gate (statement text unchanged, no placeholders, warning-free build, axiom
audit); statements and proofs were produced by Claude (Anthropic) and verified mechanically; the
statements were reviewed by hand against the paper.

Build and audit:

```bash
lake exe cache get
lake build
python3 ../scripts/check_axioms.py
```

This package requires the sibling `dynamics/` package and shares its Lean 4.32.0 toolchain and exact
Mathlib pin. The [blueprint](blueprint/src/content.tex) maps the results to declarations.
