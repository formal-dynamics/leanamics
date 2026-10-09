---
# Feel free to add content and custom Front Matter to this file.
# To modify the layout, see https://jekyllrb.com/docs/themes/#overriding-theme-defaults

layout: default
usemathjax: true
---

**Leanamics** is a collection of Lean 4 + Mathlib formalizations of classical
results on opinion dynamics and related distributed processes, each paired
with a [leanblueprint](https://github.com/PatrickMassot/leanblueprint) page
connecting the paper proof to the Lean code statement-by-statement. The
developments are `sorry`-free. Probability is finite: randomness lives on finite types and
expectations are finite sums (no measure theory, no `PMF`/`ENNReal`), and the concentration
bounds and martingale arguments are proved within this layer.

This page gives a short overview of each area; the blueprint of each package has the precise statements, the proofs and the links to the Lean code.
[RESULTS.md](https://github.com/formal-dynamics/leanamics/blob/main/RESULTS.md) lists every
formalized result with its scope, source, main Lean theorems and roadmap ID;
[ROADMAP.md](https://github.com/formal-dynamics/leanamics/blob/main/ROADMAP.md) lists what we
would like to formalize next; and
[PROVENANCE.md](https://github.com/formal-dynamics/leanamics/blob/main/PROVENANCE.md) records
proof routes, explicit constants and authorship. Where a statement deviates from its source, the
package's `FORMALIZATION_DIFFERENCES.md` lists the deviations. Many statements make "for
sufficiently large $n$" explicit, with thresholds that can be astronomically large.

## Majority dynamics: 3-Majority and plurality consensus
{: #majority}

Every round, each node adopts the majority colour among three random nodes. Formalized: consensus
from a 3/5 majority in $O(\log n)$ rounds ([proof]({{ '/3-majority/blueprint/' | relative_url }}#sec:main-statement)); plurality
consensus with $k$ colours from a bias of order $\sqrt{\lambda n \log n}$ ([Becchetti et al., SPAA
2014]({{ '/plurality/blueprint/' | relative_url }}#sec:upper)) and its [lower bounds]({{ '/plurality/blueprint/' | relative_url }}#sec:lower); with two colours,
consensus from any start, even a balanced one ([details]({{ '/plurality/blueprint/' | relative_url }}#sec:any_start)).

**Plurality:** [Blueprint]({{ '/plurality/blueprint/' | relative_url }}) · [PDF]({{ '/plurality/blueprint.pdf' | relative_url }}) · [Dependency graph]({{ '/plurality/blueprint/dep_graph_document.html' | relative_url }}) · [API docs]({{ '/plurality/docs/' | relative_url }}) · [Source](https://github.com/formal-dynamics/leanamics/tree/main/plurality)  
**Two opinions:** [Blueprint]({{ '/3-majority/blueprint/' | relative_url }}) · [PDF]({{ '/3-majority/blueprint.pdf' | relative_url }}) · [Dependency graph]({{ '/3-majority/blueprint/dep_graph_document.html' | relative_url }}) · [API docs]({{ '/3-majority/docs/' | relative_url }}) · [Source](https://github.com/formal-dynamics/leanamics/tree/main/3-majority)

## Median dynamics and 2-Choices
{: #median}

Every round, each node adopts the median of its own value and two random values; with two values
this is 2-Choices. Formalized: consensus within $O(\log n)$ rounds from any configuration and
almost stable consensus against an adaptive adversary ([Doerr et al., SPAA 2011]({{ '/median/blueprint/' | relative_url }}#sec:dgmss-median));
two-sample voting on expanders ([Cooper, Elsässer and Radzik, ICALP 2014]({{ '/median/blueprint/' | relative_url }}#sec:cer-two-choices));
and, for 2-Choices with any number of colours, plurality consensus ([Elsässer et al.]({{ '/median/blueprint/' | relative_url }}#sec:efkmt-plurality))
and an $\Omega(n/\log n)$ lower bound ([Berenbrink et al., PODC 2017]({{ '/median/blueprint/' | relative_url }}#sec:bcekmn-lower)).

[Blueprint]({{ '/median/blueprint/' | relative_url }}) · [PDF]({{ '/median/blueprint.pdf' | relative_url }}) · [Dependency graph]({{ '/median/blueprint/dep_graph_document.html' | relative_url }}) · [API docs]({{ '/median/docs/' | relative_url }}) · [Source](https://github.com/formal-dynamics/leanamics/tree/main/median)

## Undecided-state dynamics
{: #undecided}

A node that sees the other opinion becomes undecided; an undecided node adopts the opinion it
sees. Formalized: majority consensus from a bias of order $\sqrt{n \log n}$ within $O(\log n)$
rounds ([Clementi et al., MFCS 2018]({{ '/undecided/blueprint/' | relative_url }}#sec:cggnps-majority)); plurality consensus with $k$
colours ([Becchetti et al., SODA 2015]({{ '/undecided/blueprint/' | relative_url }}#sec:bcnps-plurality)) and its [lower bound]({{ '/undecided/blueprint/' | relative_url }}#sec:bcnps-lower-bound); and the sequential
approximate-majority protocol ([Angluin, Aspnes and Eisenstat, 2008]({{ '/undecided/blueprint/' | relative_url }}#sec:aae-approx-majority)).

[Blueprint]({{ '/undecided/blueprint/' | relative_url }}) · [PDF]({{ '/undecided/blueprint.pdf' | relative_url }}) · [Dependency graph]({{ '/undecided/blueprint/dep_graph_document.html' | relative_url }}) · [API docs]({{ '/undecided/docs/' | relative_url }}) · [Source](https://github.com/formal-dynamics/leanamics/tree/main/undecided)

## Voter model
{: #voter}

Every round, each node copies the opinion of a random neighbour. Formalized: the consensus
probabilities on connected graphs and neutral Wright–Fisher fixation ([Hassin and
Peleg]({{ '/voter/blueprint/' | relative_url }}#sec:hassin-peleg)); consensus within $O(n^3 \log n)$ rounds on every connected graph
([details]({{ '/voter/blueprint/' | relative_url }}#sec:kms-meeting-time)), also without laziness on
non-bipartite graphs ([Hassin and Peleg]({{ '/voter/blueprint/' | relative_url }}#sec:hp-plain-walk)); and consensus times via conductance, also on dynamic
graphs ([Berenbrink et al., ICALP 2016]({{ '/voter/blueprint/' | relative_url }}#sec:bgkm-conductance)).

[Blueprint]({{ '/voter/blueprint/' | relative_url }}) · [PDF]({{ '/voter/blueprint.pdf' | relative_url }}) · [Dependency graph]({{ '/voter/blueprint/dep_graph_document.html' | relative_url }}) · [API docs]({{ '/voter/docs/' | relative_url }}) · [Source](https://github.com/formal-dynamics/leanamics/tree/main/voter)

## The Moran process and the isothermal theorem
{: #moran}

An individual chosen proportionally to its fitness places a copy of itself on a random neighbour.
Formalized: the isothermal theorem on regular graphs ([Lieberman, Hauert and Nowak,
2005]({{ '/moran/blueprint/' | relative_url }}#sec:lhn-isothermal)); neutral fixation of push and pull processes on every graph
([details]({{ '/moran/blueprint/' | relative_url }}#sec:ars-push-pull)); and exact fixation on the star, which amplifies selection
([Broom and Rychtář, 2008]({{ '/moran/blueprint/' | relative_url }}#sec:broom-rychtar)).

[Blueprint]({{ '/moran/blueprint/' | relative_url }}) · [PDF]({{ '/moran/blueprint.pdf' | relative_url }}) · [Dependency graph]({{ '/moran/blueprint/dep_graph_document.html' | relative_url }}) · [API docs]({{ '/moran/docs/' | relative_url }}) · [Source](https://github.com/formal-dynamics/leanamics/tree/main/moran)

## Epidemics and rumor spreading
{: #epidemics}

Formalized: push, pull and push–pull rumor spreading on $K_n$ inform all nodes within $O(\log n)$
rounds ([push]({{ '/rumor_spread/blueprint/' | relative_url }}#sec:main-statement), [pull and push–pull]({{ '/rumor_spread/blueprint/' | relative_url }}#sec:pull)), with
sharp upper bounds from a general analysis ([Doerr and Kostrygin, ICALP 2017]({{ '/epidemics/blueprint/' | relative_url }}#sec:doerr-kostrygin));
Reed–Frost epidemics as percolation, with small outbreaks below the threshold, also on small-world
networks ([Becchetti et al.]({{ '/epidemics/blueprint/' | relative_url }}#sec:bcdptz-small-world)), and a giant component above it
([Krivelevich and Sudakov, 2013]({{ '/epidemics/blueprint/' | relative_url }}#sec:krivelevich-sudakov)); the COBRA–BIPS duality
([Cooper, Radzik and Rivera, PODC 2016]({{ '/epidemics/blueprint/' | relative_url }}#sec:crr-cobra-bips)); and the SIR equations
([Kermack–McKendrick]({{ '/epidemics/blueprint/' | relative_url }}#sec:kermack-mckendrick)) with their law of large numbers
([Kurtz]({{ '/epidemics/blueprint/' | relative_url }}#sec:kurtz)).

**Rumor spreading:** [Blueprint]({{ '/rumor_spread/blueprint/' | relative_url }}) · [PDF]({{ '/rumor_spread/blueprint.pdf' | relative_url }}) · [Dependency graph]({{ '/rumor_spread/blueprint/dep_graph_document.html' | relative_url }}) · [API docs]({{ '/rumor_spread/docs/' | relative_url }}) · [Source](https://github.com/formal-dynamics/leanamics/tree/main/rumor_spread)  
**Epidemics:** [Blueprint]({{ '/epidemics/blueprint/' | relative_url }}) · [PDF]({{ '/epidemics/blueprint.pdf' | relative_url }}) · [Dependency graph]({{ '/epidemics/blueprint/dep_graph_document.html' | relative_url }}) · [API docs]({{ '/epidemics/docs/' | relative_url }}) · [Source](https://github.com/formal-dynamics/leanamics/tree/main/epidemics)

## Chemical reaction networks and population protocols
{: #crn}

Formalized: the stochastic mass-action kinetics of a bimolecular network has the same jump
chain as the population protocol on the same reactions, and population protocols stably compute every
threshold and remainder predicate and their Boolean combinations ([Angluin et al.,
2006]({{ '/crn/blueprint/' | relative_url }}#sec:aadfp-stable)).

[Blueprint]({{ '/crn/blueprint/' | relative_url }}) · [PDF]({{ '/crn/blueprint.pdf' | relative_url }}) · [Dependency graph]({{ '/crn/blueprint/dep_graph_document.html' | relative_url }}) · [API docs]({{ '/crn/docs/' | relative_url }}) · [Source](https://github.com/formal-dynamics/leanamics/tree/main/crn)

## Averaging dynamics
{: #averaging}

Every round, each node replaces its value by the average of its neighbours' values. Formalized:
convergence and its spectral rate ([after Lovász]({{ '/averaging/blueprint/' | relative_url }}#sec:lovasz)), sequential averaging
([details]({{ '/averaging/blueprint/' | relative_url }}#sec:bgps-gossip)), and community detection by averaging
([Becchetti et al., SODA 2017]({{ '/averaging/blueprint/' | relative_url }}#sec:bcnpt-reconstruction); [ESA
2018]({{ '/averaging/blueprint/' | relative_url }}#sec:bcmnprt-opportunistic)).

[Blueprint]({{ '/averaging/blueprint/' | relative_url }}) · [PDF]({{ '/averaging/blueprint.pdf' | relative_url }}) · [Dependency graph]({{ '/averaging/blueprint/dep_graph_document.html' | relative_url }}) · [API docs]({{ '/averaging/docs/' | relative_url }}) · [Source](https://github.com/formal-dynamics/leanamics/tree/main/averaging)

## Shared finite dynamics library
{: #dynamics}

Finite probability (expectations that agree with Mathlib's `Finset.expect`, kernels, absorption)
and the tools the dynamics share: Chernoff, Hoeffding and Bernstein bounds, optional stopping,
drift theorems and a [hitting-time lemma]({{ '/dynamics/blueprint/' | relative_url }}#sec:dgmss-hitting).

[Blueprint]({{ '/dynamics/blueprint/' | relative_url }}) · [PDF]({{ '/dynamics/blueprint.pdf' | relative_url }}) · [Dependency graph]({{ '/dynamics/blueprint/dep_graph_document.html' | relative_url }}) · [API docs]({{ '/dynamics/docs/' | relative_url }}) · [Source](https://github.com/formal-dynamics/leanamics/tree/main/dynamics)

## How to cite
{: #cite}

If you use Leanamics, please cite it. Every release is archived on [Zenodo](https://zenodo.org/)
with its own DOI, and [10.5281/zenodo.23265329](https://doi.org/10.5281/zenodo.23265329) always resolves to the latest release; the
metadata are in
[CITATION.cff](https://github.com/formal-dynamics/leanamics/blob/main/CITATION.cff). Please cite
the version you used (here v0.1.0):

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

---

Each project is a separate Lean package (its own `lakefile.toml` and toolchain) living in its own
subdirectory of the repository. The shared `dynamics/` package is used by every other package:
`rumor_spread/`, `3-majority/`, `plurality/` (which also requires `3-majority/`), `median/`,
`undecided/`, `voter/`, `moran/`, `epidemics/`, `crn/` and `averaging/`. This page is the shared
landing page linking to each development; see each subdirectory's own `README.md` for build
instructions.
