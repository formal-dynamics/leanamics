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
developments below are complete and `sorry`-free, and are built on a
minimal finite-probability layer — no measure theory, no `PMF`/`ENNReal`, no
martingales. More protocols are expected to join over time.

## Rumor spreading (uniform push)

In the uniform *push* model on the complete graph $K_n$, every informed node
sends the rumor to a uniformly random other node each round. Starting from a
single informed node, after $O(\log n)$ rounds **all** nodes are informed
with high probability. The main theorem is `RumorPush.push_informs_all_whp`.

* [Blueprint]({{ '/rumor_spread/blueprint/' | relative_url }}) · [as pdf]({{ '/rumor_spread/blueprint.pdf' | relative_url }}) ·
  [dependency graph]({{ '/rumor_spread/blueprint/dep_graph_document.html' | relative_url }})
* [API docs]({{ '/rumor_spread/docs/' | relative_url }})
* [Source](https://github.com/formal-dynamics/leanamics/tree/main/rumor_spread)
   
## Majority dynamics: 3-Majority and plurality consensus

In the *3-majority* dynamics every node holds one of $k$ colors and, every round, adopts the
majority color among three nodes sampled uniformly at random (the first one if all three differ).
If the plurality color $m$ has at least $n/\lambda$ nodes and leads every other color by at least
$22\sqrt{\lambda n \log n}$, then after $O(\lambda \log n)$ rounds **all** nodes support $m$ with
high probability (`Plurality.theorem_3_8`), formalizing the upper bound of
Becchetti–Clementi–Natale–Pasquale–Silvestri–Trevisan, *Simple Dynamics for Plurality Consensus*
(SPAA 2014). With two opinions this is consensus from a vanishing imbalance: a gap of
$22\sqrt{3 n \log n}$, i.e. a fraction $1/2 + O(\sqrt{\log n / n})$, suffices for consensus within
$390 \log n$ rounds with probability $1 - O(\log n / n)$ (`Plurality.majority3_vanishing_bias`).
The package also proves the paper's lower bounds: $\Omega(k \log n)$ rounds from balanced starts,
the characterization of 3-input rules that solve plurality consensus, and $\Omega(k/h^2)$ rounds for
$h$-plurality.

* Plurality: [Blueprint]({{ '/plurality/blueprint/' | relative_url }}) · [as pdf]({{ '/plurality/blueprint.pdf' | relative_url }}) ·
  [dependency graph]({{ '/plurality/blueprint/dep_graph_document.html' | relative_url }}) ·
  [API docs]({{ '/plurality/docs/' | relative_url }}) · [Source](https://github.com/formal-dynamics/leanamics/tree/main/plurality)
* Two opinions (`3-majority/`): [Blueprint]({{ '/3-majority/blueprint/' | relative_url }}) · [as pdf]({{ '/3-majority/blueprint.pdf' | relative_url }}) ·
  [dependency graph]({{ '/3-majority/blueprint/dep_graph_document.html' | relative_url }}) ·
  [API docs]({{ '/3-majority/docs/' | relative_url }}) · [Source](https://github.com/formal-dynamics/leanamics/tree/main/3-majority)

## Weighted synchronous voter dynamics

For a finite connected nonbipartite undirected graph, each vertex independently
samples a neighbor according to a stochastic matrix (self-loops allowed) and
copies its previous color. The eventual probability of consensus in a color equals the initial
stationary weight of vertices with that color. Uniform neighbor sampling gives
degree weights, and regular graphs give the initial color fraction.
The main theorem is `Voter.consensus_probability`, formalizing Hassin–Peleg
Sections 2.1–2.3. On the complete graph, a duality with coalescing random walks gives
consensus within $2n\log n$ rounds with probability at least $1 - 1/n$
(`Voter.voter_consensus_whp`).

* [Blueprint]({{ '/voter/blueprint/' | relative_url }}) · [as pdf]({{ '/voter/blueprint.pdf' | relative_url }}) ·
  [dependency graph]({{ '/voter/blueprint/dep_graph_document.html' | relative_url }})
* [API docs]({{ '/voter/docs/' | relative_url }})
* [Source](https://github.com/formal-dynamics/leanamics/tree/main/voter)

## The Moran process and the isothermal theorem

In the Birth–death Moran process, an individual chosen with probability proportional to its
fitness (mutants $r$, residents $1$) places a copy of itself on a uniformly random neighbour.
On a connected regular graph, $k$ mutants take over with probability
$(1 - r^{-k})/(1 - r^{-n})$ ($k/n$ when $r = 1$): the "if" direction of the isothermal theorem of
Lieberman, Hauert and Nowak. The main
theorem is `Moran.isothermal`; `Moran.moran_formula` is Moran's 1958 formula on the complete graph.
On an arbitrary connected graph, the neutral push (Birth–death) and pull (death–Birth) processes
fix a mutant set $S$ with probabilities proportional to $\sum_{v \in S} 1/\deg v$ and to
$\sum_{v \in S} \deg v$ respectively (`Moran.push_fixation`, `Moran.pull_fixation`).

* [Blueprint]({{ '/moran/blueprint/' | relative_url }}) · [as pdf]({{ '/moran/blueprint.pdf' | relative_url }}) ·
  [dependency graph]({{ '/moran/blueprint/dep_graph_document.html' | relative_url }})
* [API docs]({{ '/moran/docs/' | relative_url }})
* [Source](https://github.com/formal-dynamics/leanamics/tree/main/moran)

## Reed–Frost epidemics and bond percolation

In the Reed–Frost (Independent Cascade) epidemic, each infected node infects each susceptible
neighbour across an open edge and then recovers. With one coin per edge, the nodes infected in
round $t$ are exactly those at distance $t$ from the initial set in the graph of open edges
(`Epidemics.infected_iff`), so the final outbreak is the set of nodes connected to the initial set,
and with independent Bernoulli($p$) coins the probability of eventual infection is a bond-percolation
connection probability (`Epidemics.prob_infected_eq_prob_connected`).

* [Blueprint]({{ '/epidemics/blueprint/' | relative_url }}) · [as pdf]({{ '/epidemics/blueprint.pdf' | relative_url }}) ·
  [dependency graph]({{ '/epidemics/blueprint/dep_graph_document.html' | relative_url }})
* [API docs]({{ '/epidemics/docs/' | relative_url }})
* [Source](https://github.com/formal-dynamics/leanamics/tree/main/epidemics)

## Undecided-state dynamics

Each node holds opinion $a$, opinion $b$, or is undecided; every round it samples a uniformly random
node, adopts the sampled opinion if undecided, and becomes undecided if it sees the other opinion.
With $q$ undecided nodes, the bias between the two opinions grows in expectation by the factor
$1 + q/n$ in one round (`Undecided.expected_bias`), and every run is eventually absorbed in a
monochromatic configuration (`Undecided.absorbed`).

* [Blueprint]({{ '/undecided/blueprint/' | relative_url }}) · [as pdf]({{ '/undecided/blueprint.pdf' | relative_url }}) ·
  [dependency graph]({{ '/undecided/blueprint/dep_graph_document.html' | relative_url }})
* [API docs]({{ '/undecided/docs/' | relative_url }})
* [Source](https://github.com/formal-dynamics/leanamics/tree/main/undecided)

## Averaging dynamics

Every node replaces its value by the average of its neighbours' values. On a connected graph with
an odd closed walk all values converge to the degree-weighted average of the initial values
(`Averaging.tendsto_degAvg`); on a connected bipartite graph the values of a 2-colouring flip sign
forever (`Averaging.not_tendsto_of_colorable`).

* [Blueprint]({{ '/averaging/blueprint/' | relative_url }}) · [as pdf]({{ '/averaging/blueprint.pdf' | relative_url }}) ·
  [dependency graph]({{ '/averaging/blueprint/dep_graph_document.html' | relative_url }})
* [API docs]({{ '/averaging/docs/' | relative_url }})
* [Source](https://github.com/formal-dynamics/leanamics/tree/main/averaging)

## Median dynamics and 2-Choices

Every node holds a value from a linearly ordered set and, every round, adopts the median of its
own value and the values of two nodes sampled uniformly at random. Thresholding the process at any
value gives the binary median process, i.e. 2-Choices, driven by the same samples
(`Median.threshold_run`). With two values, a gap of $128\sqrt{n \log n}$ between them gives
consensus on the majority within $\lceil 128 \log n \rceil$ rounds with probability $1 - 128/n$
(`Median.consensus_whp`).

* [Blueprint]({{ '/median/blueprint/' | relative_url }}) · [as pdf]({{ '/median/blueprint.pdf' | relative_url }}) ·
  [dependency graph]({{ '/median/blueprint/dep_graph_document.html' | relative_url }})
* [API docs]({{ '/median/docs/' | relative_url }})
* [Source](https://github.com/formal-dynamics/leanamics/tree/main/median)

## Chemical reaction networks and population protocols

In a count-conserving bimolecular chemical reaction network ($A + B \to C + D$) with a common rate
constant, the jump chain of stochastic mass-action kinetics fires reaction $r$ with probability
proportional to its propensity. If $a$ and $b$ agents hold species $A \ne B$, a uniformly random
ordered pair of distinct agents holds one of each with probability $ab / \binom{n}{2}$ (and two $A$
with probability $\binom{a}{2} / \binom{n}{2}$), which is the propensity up to a common factor. So the
population protocol that draws such a pair, conditioned on the pair reacting, is exactly the jump
chain, as kernels on count vectors (`Crn.jumpKernel_eq_ppKernel`). The worked
instance is the approximate-majority network (`Crn.ApproxMajority.network_jumpKernel_eq_ppKernel`).

* [Blueprint]({{ '/crn/blueprint/' | relative_url }}) · [as pdf]({{ '/crn/blueprint.pdf' | relative_url }}) ·
  [dependency graph]({{ '/crn/blueprint/dep_graph_document.html' | relative_url }})
* [API docs]({{ '/crn/docs/' | relative_url }})
* [Source](https://github.com/formal-dynamics/leanamics/tree/main/crn)

## Shared finite dynamics library

`Dynamics` supplies uniform and weighted finite expectations, independent
products, pushforward, kernels, stationary distributions, and geometric
absorption. It is shared by voter dynamics, the Moran process, 3-majority and plurality consensus.

* [Blueprint]({{ '/dynamics/blueprint/' | relative_url }}) · [as pdf]({{ '/dynamics/blueprint.pdf' | relative_url }}) ·
  [dependency graph]({{ '/dynamics/blueprint/dep_graph_document.html' | relative_url }})
* [API docs]({{ '/dynamics/docs/' | relative_url }})
* [Source](https://github.com/formal-dynamics/leanamics/tree/main/dynamics)

---

Each project is a separate Lean package (its own `lakefile.toml` and
toolchain) living in its own subdirectory of the repository, with `dynamics/`
shared by `3-majority/`, `voter/`, `moran/`, `epidemics/`, `undecided/`, `averaging/`, `median/`, `crn/` and `plurality/`; this page is the
shared landing page linking to each development. See each subdirectory's own
`README.md` for build instructions.
