# Leanamics

Lean 4 + Mathlib formalizations of classical results on opinion dynamics and
related distributed processes. Each project is paired with a
[leanblueprint](https://github.com/PatrickMassot/leanblueprint) connecting the
paper proof to the Lean code statement-by-statement.

**[https://formal-dynamics.github.io/leanamics/](https://formal-dynamics.github.io/leanamics/)** — landing
page, blueprints, dependency graphs and API docs for everything below.

The project was called Leanamycs until October 2026, a misspelling of Leanamics (Lean +
dynamics); links to the old repository and site redirect here.

| Project | Result | Main theorem |
| --- | --- | --- |
| [`rumor_spread/`](rumor_spread) | In the uniform *push* model on the complete graph `K_n`, one initially informed node informs all `n` nodes within `O(log n)` rounds w.h.p. | `RumorPush.push_informs_all_whp` |
| [`dynamics/`](dynamics) | Shared finite weighted distributions, trajectory expectations, stationary distributions, and geometric absorption | `Dynamics.Kernel.finite_absorption` |
| [`voter/`](voter) | Hassin–Peleg Sections 2.1–2.3: weighted synchronous consensus probabilities, uniform-neighbor and multiple-color corollaries. On the complete graph, a duality with coalescing random walks gives consensus within `2 n log n` rounds with probability `≥ 1 - 1/n`. | `Voter.consensus_probability`, `Voter.voter_consensus_whp` |
| [`moran/`](moran) | Birth–death Moran process with mutant fitness `r`: on a connected regular graph the fixation probability from `k` mutants is `(1 - r^-k)/(1 - r^-n)` (`k/n` if `r = 1`), the "if" direction of the isothermal theorem; Moran's formula on the complete graph; neutral push vs pull fixation on arbitrary connected graphs (weights `1/deg` vs `deg`). | `Moran.isothermal`, `Moran.moran_formula`, `Moran.push_fixation`, `Moran.pull_fixation` |
| [`epidemics/`](epidemics) | Reed–Frost (Independent Cascade) epidemic with one coin per edge: pathwise, the nodes infected in round `t` are those at distance `t` from the initial set in the graph of open edges; final outbreak = nodes connected to the initial set, so with i.i.d. Bernoulli(`p`) coins P(infected) = P(connected) in bond percolation. | `Epidemics.infected_iff`, `Epidemics.prob_infected_eq_prob_connected` |
| [`undecided/`](undecided) | Synchronous undecided-state dynamics with two opinions on `K_n`: exact one-round expectations of the three counts, so the bias grows in expectation by the factor `1 + q/n` (`q` undecided nodes); almost-sure absorption in a monochromatic configuration. | `Undecided.expected_bias`, `Undecided.absorbed` |
| [`averaging/`](averaging) | Averaging dynamics on a graph (each node takes the average of its neighbours): conservation of the degree-weighted sum, maximum principle, convergence to the degree-weighted average on connected graphs with an odd closed walk, non-convergence on connected bipartite graphs. | `Averaging.tendsto_degAvg`, `Averaging.not_tendsto_of_colorable` |
| [`median/`](median) | Median dynamics (Doerr et al., SPAA 2011): every node adopts the median of its own value and two random ones. Thresholding gives the binary median process (2-Choices); with two values, consensus from a gap of `128√(n log n)` within `⌈128 log n⌉` rounds with probability `1 − 128/n` (for `log n ≥ 128`). | `Median.threshold_run`, `Median.consensus_whp` |
| [`crn/`](crn) | Chemical reaction networks are population protocols: for a count-conserving bimolecular CRN (`A + B → C + D`) with a common rate constant, the jump chain of stochastic mass-action kinetics equals the population protocol that draws a uniformly random ordered pair of distinct agents, conditioned on the pair reacting, as kernels on count vectors. Worked instance: the approximate-majority CRN. | `Crn.jumpKernel_eq_ppKernel`, `Crn.ApproxMajority.network_jumpKernel_eq_ppKernel` |
| [`plurality/`](plurality), [`3-majority/`](3-majority) | **Majority dynamics.** 3-Majority with `k` colors (Becchetti et al., SPAA 2014): if the plurality color has `≥ n/λ` nodes and leads every other color by `≥ 22√(λ n log n)`, all nodes adopt it within `O(λ log n)` rounds w.h.p. With two opinions: consensus from a gap of `22√(3 n log n)` (a fraction `1/2 + O(√(log n / n))`) within `390 log n` rounds. Also the `Ω(k log n)` lower bound, the characterization of good 3-input rules, and `h`-plurality. | `Plurality.theorem_3_8`, `Plurality.majority3_vanishing_bias`, `ThreeMajority.majority3_consensus_whp` |

The developments are complete and `sorry`-free, and are built on a
minimal finite-probability layer: no measure theory, no `PMF`/`ENNReal`, no
martingales, no appeal to Mathlib's `ProbabilityTheory` library. Push and
3-majority sit in different regimes — the push protocol's informed set only grows, so a
counting argument over "good rounds" suffices, whereas the 3-majority opinion
count is not monotone in the round index and so needs genuine concentration
in every round, supplied by a self-contained Chernoff bound proved from
`1 + x ≤ exp x`.

## Layout

Every project is a **separate Lake package** with its own `lakefile.toml`,
`lake-manifest.json` and `lean-toolchain`. The `dynamics/` package is shared by
`3-majority/`, `voter/`, `moran/`, `epidemics/`, `undecided/`, `averaging/`, `median/`, `crn/` and `plurality/` (which also requires `3-majority/`). All
projects use the same Lean 4.32.0 toolchain and exact Mathlib revision; there is no root-level
Lake package. Each has the same shape:

```
<project>/
  README.md            what it proves, how it is proved, how to build it
  CLAUDE.md            optional orientation for automated contributors
  lakefile.toml        the Lake package (Mathlib + checkdecls, + dynamics if shared)
  lean-toolchain       the pinned Lean version
  <Lib>.lean, <Lib>/   the formalization
  blueprint/src/       the leanblueprint sources
  latex/               optional standalone paper proof
```

Shared at the repository root:

```
home_page/             the Jekyll landing page, deployed at the Pages root
.github/workflows/     per-project build CI, plus the shared Pages deployment
```

To work on one project, `cd` into it and use Lake as usual:

```bash
cd voter               # or: dynamics, moran, epidemics, undecided, averaging, median, crn, 3-majority, plurality, rumor_spread
lake exe cache get     # download prebuilt Mathlib oleans (once)
lake build             # verifies every proof in that project
```

## Continuous integration

- `.github/workflows/rumor_spread-ci.yml`, `.github/workflows/three_majority-ci.yml` —
  `lake build` + lint for one project each. Shared-library changes also rebuild
  3-majority.
- `.github/workflows/plurality-ci.yml` builds the plurality package, audits its
  main theorem axioms and rejects `sorry`; changes to `dynamics/` or `3-majority/`
  also rebuild it.
- `.github/workflows/dynamics-ci.yml` builds the shared library and the voter, moran, epidemics, undecided, averaging, median and crn packages
  and audits the main theorem axioms.
- `.github/workflows/pages.yml` — builds every project's blueprint (web and
  pdf) and API docs, checks that every declaration named in a blueprint
  actually exists (`lake exe checkdecls`), assembles them under `home_page/`
  and deploys the result to GitHub Pages:

  ```
  /                         home_page/index.md
  /<project>/blueprint/     leanblueprint web version
  /<project>/blueprint.pdf  leanblueprint pdf version
  /<project>/docs/          doc-gen4 API docs
  ```


## Adding a project

Copy the layout above into a new top-level directory, then add a
`<project>-ci.yml` workflow and one entry to the `matrix.include` list in
`pages.yml` (its directory, its Lake package name, and the `lean_lib` whose
docs to build). Set `\home{../..}` and `\dochome{../docs}` in the project's
`blueprint/src/web.tex`, since blueprints are served one level below the
landing page, and add a section for it to `home_page/index.md`.

## Contributing

Contributions are very welcome. [ROADMAP.md](ROADMAP.md) lists the results we would
like to formalize next (voter model and Wright–Fisher, Moran process, epidemics and
percolation, majority and undecided-state dynamics, chemical reaction networks, averaging),
each with an ID, a
source, the infrastructure it needs and a size estimate.

To take one on, **pick a target and open an issue** titled `[ID] short name` (for
example `[EPI-1] Reed–Frost ⇔ bond percolation`) saying that you are working on it.
That is all it takes to claim it, and it keeps two people from formalizing the same
result. Then open a (draft) pull request whenever you have something to show. To
propose a result that is not on the roadmap, just open an issue.

[PROVENANCE.md](PROVENANCE.md) records, for every result, its source paper, whether the formal
proof follows a published proof or takes a different route, its explicit constants, and who
produced it. Please add an entry for each result you contribute.

## License

Leanamics is released under the [MIT License](LICENSE). By contributing, you agree that your
contributions are released under the same license.
