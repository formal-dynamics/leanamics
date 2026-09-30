# Leanamycs

Lean 4 + Mathlib formalizations of classical results on opinion dynamics and
related distributed processes. Each project is paired with a
[leanblueprint](https://github.com/PatrickMassot/leanblueprint) connecting the
paper proof to the Lean code statement-by-statement.

**[https://formal-dynamics.github.io/leanamycs/](https://formal-dynamics.github.io/leanamycs/)** — landing
page, blueprints, dependency graphs and API docs for everything below.

| Project | Result | Main theorem |
| --- | --- | --- |
| [`rumor_spread/`](rumor_spread) | In the uniform *push* model on the complete graph `K_n`, one initially informed node informs all `n` nodes within `O(log n)` rounds w.h.p. | `RumorPush.push_informs_all_whp` |
| [`dynamics/`](dynamics) | Shared finite weighted distributions, trajectory expectations, stationary distributions, and geometric absorption | `Dynamics.Kernel.finite_absorption` |
| [`voter/`](voter) | Hassin–Peleg Sections 2.1–2.3: weighted synchronous consensus probabilities, uniform-neighbor and multiple-color corollaries | `Voter.consensus_probability` |
| [`moran/`](moran) | Birth–death Moran process with mutant fitness `r`: on a connected regular graph the fixation probability from `k` mutants is `(1 - r^-k)/(1 - r^-n)` (`k/n` if `r = 1`), the "if" direction of the isothermal theorem; Moran's formula on the complete graph. | `Moran.isothermal`, `Moran.moran_formula` |
| [`3-majority/`](3-majority) | `n` fully-mixing agents, each adopting the majority opinion among three uniformly sampled agents, reach consensus within `O(log n)` rounds with probability `1 - O(1/n)` from a `60%` initial majority. | `ThreeMajority.majority3_consensus_whp` |

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
`3-majority/`, `voter/` and `moran/`, using the same
Lean 4.32.0 toolchain and exact Mathlib revision. Rumor spreading retains its
independent Lean 4.26.0-rc2 pin; there is no root-level Lake package. Each has the same shape:

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
cd voter               # or: dynamics, moran, 3-majority, rumor_spread
lake exe cache get     # download prebuilt Mathlib oleans (once)
lake build             # verifies every proof in that project
```

## Continuous integration

- `.github/workflows/rumor_spread-ci.yml`, `.github/workflows/three_majority-ci.yml` —
  `lake build` + lint for one project each. Shared-library changes also rebuild
  3-majority.
- `.github/workflows/dynamics-ci.yml` builds the shared library and the voter and moran packages
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
