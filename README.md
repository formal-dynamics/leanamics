# Leanamics

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23265329.svg)](https://doi.org/10.5281/zenodo.23265329)

Lean 4 + Mathlib formalizations of classical results on opinion dynamics and
related distributed processes. Each project is paired with a
[leanblueprint](https://github.com/PatrickMassot/leanblueprint) connecting the
paper proof to the Lean code statement-by-statement.

**[https://formal-dynamics.github.io/leanamics/](https://formal-dynamics.github.io/leanamics/)** (landing
page, blueprints, dependency graphs and API docs for everything below). To cite Leanamics, see
[How to cite](#how-to-cite).

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

## How to cite

If you use Leanamics, please cite it. The metadata are in [CITATION.cff](CITATION.cff) (GitHub's
"Cite this repository" button shows them as APA and BibTeX), and every release is archived on
[Zenodo](https://zenodo.org/) with its own DOI; [10.5281/zenodo.23265329](https://doi.org/10.5281/zenodo.23265329) always resolves to the
latest release. Please cite the version you used (here v0.1.0):

```bibtex
@software{leanamics,
  author  = {Kumar, Aakash and Bucarelli, Maria Sofia and D'Archivio, Niccol{\`o} and Natale, Emanuele},
  title   = {Leanamics: {Lean} 4 formalizations of opinion dynamics and related distributed processes},
  year    = {2026},
  version = {0.1.0},
  doi     = {10.5281/zenodo.23265330},
  url     = {https://github.com/formal-dynamics/leanamics}
}
```

The same section is on the [website](https://formal-dynamics.github.io/leanamics/#cite), and every
blueprint page links to it.

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
.github/pull_request_template.md   the documentation checklist of every pull request
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
[RESULTS.md](RESULTS.md). The documentation rule below applies to the pull request that adds it.

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
produced it.

**Every pull request that adds or changes a result must keep the documentation up to date:** the
package's `README.md` and blueprint, its `FORMALIZATION_DIFFERENCES.md`, a row in
[RESULTS.md](RESULTS.md), an entry in [PROVENANCE.md](PROVENANCE.md), the status in
[ROADMAP.md](ROADMAP.md), and the landing page `home_page/index.md` (kept short: at most a phrase per
paper, linked to its blueprint section; the details go in the blueprint). If the landing page is not
updated in the pull request itself, open an issue to update it. Each formalized paper has a
blueprint section with a stable `\label{sec:...}` (used for links to the website); do not rename
existing labels. The [pull request template](.github/pull_request_template.md) lists these items,
together with the axiom audit.

## Releases

To make a release `vX.Y.Z`: in a pull request, update `version` and `date-released` in
[CITATION.cff](CITATION.cff) and the BibTeX entries (here and on the landing page); after merging it,
create the GitHub release `vX.Y.Z`. Zenodo archives every release automatically; then add the new
version DOI to `identifiers` in `CITATION.cff` and to the BibTeX entries. The concept DOI
(`10.5281/zenodo.23265329`) never changes.

## License

Leanamics is released under the [MIT License](LICENSE). By contributing, you agree that your
contributions are released under the same license.
