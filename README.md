# Leanamics

Lean 4 + Mathlib formalizations of classical results on opinion dynamics and
related distributed processes. Each project is paired with a
[leanblueprint](https://github.com/PatrickMassot/leanblueprint) connecting the
paper proof to the Lean code statement-by-statement.

**[https://formal-dynamics.github.io/leanamics/](https://formal-dynamics.github.io/leanamics/)** (landing
page, blueprints, dependency graphs and API docs for everything below).

## Results

[RESULTS.md](RESULTS.md) lists everything formalized so far, area by area (voter, Moran,
majority and plurality, median and 2-Choices, undecided-state, epidemics and rumor spreading,
chemical reaction networks, averaging), with its source, the main Lean theorems and the roadmap
ID. [ROADMAP.md](ROADMAP.md) lists the results we would like to formalize next, and
[PROVENANCE.md](PROVENANCE.md) records, for each result, the proof route, the explicit constants
and who produced it.

The developments are `sorry`-free. Probability is finite: randomness lives on finite types and
expectations are finite sums, in the shared `dynamics/` package (whose expectations agree with
Mathlib's `Finset.expect`); no measure theory, `PMF`/`ENNReal` or Mathlib `ProbabilityTheory`
is used. Concentration bounds (Chernoff, Hoeffding, Bernstein, a maximal Azuma–Hoeffding
inequality) and (super)martingale arguments are proved within this layer, and the deterministic
parts use Mathlib's analysis and linear algebra (integral curves and the discrete Gronwall
inequality for the SIR model, the spectrum of symmetric matrices for averaging).

## Layout

Every project is a **separate Lake package** with its own `lakefile.toml`,
`lake-manifest.json` and `lean-toolchain`. The `dynamics/` package is shared by
`rumor_spread/`, `3-majority/`, `voter/`, `moran/`, `epidemics/`, `undecided/`, `averaging/`, `median/`, `crn/` and `plurality/` (which also requires `3-majority/`). All
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
landing page, add a section for it to `home_page/index.md`, and list its results in
[RESULTS.md](RESULTS.md).

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
produced it. Please add an entry there, and a row to [RESULTS.md](RESULTS.md), for each result
you contribute.

## License

Leanamics is released under the [MIT License](LICENSE). By contributing, you agree that your
contributions are released under the same license.
