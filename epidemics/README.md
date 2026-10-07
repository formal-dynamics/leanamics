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

## Subcritical percolation and small outbreaks (EPI-2)

After Becchetti et al., arXiv:2103.16398, Theorem 2.3 and its proof, Theorem E.1. Let the degrees
of `G` be at most `d`, let `n = |V|`, and let `p (d - 1) ≤ 1 - ε` with `0 < ε < 1`
(results in [`Epidemics/Subcritical.lean`](Epidemics/Subcritical.lean)):

| Result | Lean declaration |
| --- | --- |
| Deferred decisions: P(component of `s` has `> t` vertices) ≤ P(`≥ t` successes in `t (d - 1) + 1` Bernoulli(`p`) trials) | `prob_cluster_gt_le_binomial` |
| Theorem E.1: P(component of `s` has `> t` vertices) ≤ `exp (ε - ε² t / 2)` | `prob_cluster_gt_le` |
| Theorem 2.3: with probability `≥ 1 - 1/n`, every component of `G_p` has `≤ (10 / ε²) log n` vertices | `prob_components_small` |
| Reed–Frost with `R₀ = p (d - 1) ≤ 1 - ε`: with probability `≥ 1 - 1/n`, at most `|I₀| (10 / ε²) log n` nodes infected, none in round `⌊(10 / ε²) log n⌋` | `reedFrost_subcritical` |
| Erdős–Rényi `G(n, c/n)`, `c ≤ 1 - ε`: with probability `≥ 1 - 1/n`, all components have `≤ (10 / ε²) log n` vertices | `erdosRenyi_subcritical` |

The crux is the principle of deferred decisions. It is proved for every state of an exploration
(discovered vertices, examined edges forced closed) by induction on a budget, conditioning on the
coin of one frontier edge, which reproduces the recursion of the binomial tail
([`SubcriticalExploration.lean`](Epidemics/SubcriticalExploration.lean)). The Chernoff bound
([`SubcriticalChernoff.lean`](Epidemics/SubcriticalChernoff.lean)) is Markov's inequality on an
exponential moment, local to this package until FND-3 provides one in `dynamics/`. Deviations from
the paper (explicit constants, the threshold written as `p (d - 1) ≤ 1 - ε`) are recorded in
[`PROGRESS-EPI2.md`](PROGRESS-EPI2.md).

**Provenance.** EPI-1: the statements were written and pinned by hand; the proofs were produced by
a Grok agent under a fixed-statement protocol and verified mechanically (statements unchanged, no
placeholders, warning-free build, axiom audit). EPI-2: statements and proofs were written by a
Claude agent under the same protocol and checks; the statements were reviewed by hand against the
paper.

Build and audit:

```bash
lake exe cache get
lake build
python3 ../scripts/check_axioms.py
```

This package requires the sibling `dynamics/` package and shares its Lean 4.32.0 toolchain and exact
Mathlib pin. The [blueprint](blueprint/src/content.tex) maps the results to declarations.
