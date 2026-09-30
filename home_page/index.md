---
# Feel free to add content and custom Front Matter to this file.
# To modify the layout, see https://jekyllrb.com/docs/themes/#overriding-theme-defaults

layout: default
usemathjax: true
---

**Leanamycs** is a collection of Lean 4 + Mathlib formalizations of classical
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
* [Source](https://github.com/formal-dynamics/leanamycs/tree/main/rumor_spread)
   
## 3-majority dynamics

In the *3-majority* model on $n$ fully-mixing agents, each agent holds one of
two opinions and every round adopts the majority opinion among three agents
sampled uniformly at random. Starting from an imbalance of at least $60\%$
vs. $40\%$, after $O(\log n)$ rounds **all** agents hold the initial majority
opinion with probability $1 - O(1/n)$. The main theorem is
`ThreeMajority.majority3_consensus_whp`.

* [Blueprint]({{ '/3-majority/blueprint/' | relative_url }}) · [as pdf]({{ '/3-majority/blueprint.pdf' | relative_url }}) ·
  [dependency graph]({{ '/3-majority/blueprint/dep_graph_document.html' | relative_url }})
* [API docs]({{ '/3-majority/docs/' | relative_url }})
* [Source](https://github.com/formal-dynamics/leanamycs/tree/main/3-majority)

## Plurality consensus with $k$ colors

The *3-majority* dynamics with $k$ colors: every round, each node adopts the
majority color among three nodes sampled uniformly at random (the first one if
all three differ). If the plurality color $m$ has at least $n/\lambda$ nodes
and leads every other color by at least $22\sqrt{\lambda n \log n}$, then after
$O(\lambda \log n)$ rounds **all** nodes support $m$ with high probability.
The main theorem is `Plurality.theorem_3_8`, formalizing the upper bound of
Becchetti–Clementi–Natale–Pasquale–Silvestri–Trevisan, *Simple Dynamics for
Plurality Consensus* (SPAA 2014), together with its lower bounds: $\Omega(k \log n)$
rounds from balanced starts, the characterization of 3-input rules that solve
plurality consensus, and $\Omega(k/h^2)$ rounds for $h$-plurality.

* [Blueprint]({{ '/plurality/blueprint/' | relative_url }}) · [as pdf]({{ '/plurality/blueprint.pdf' | relative_url }}) ·
  [dependency graph]({{ '/plurality/blueprint/dep_graph_document.html' | relative_url }})
* [API docs]({{ '/plurality/docs/' | relative_url }})
* [Source](https://github.com/formal-dynamics/leanamycs/tree/main/plurality)

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
* [Source](https://github.com/formal-dynamics/leanamycs/tree/main/voter)

## The Moran process and the isothermal theorem

In the Birth–death Moran process, an individual chosen with probability proportional to its
fitness (mutants $r$, residents $1$) places a copy of itself on a uniformly random neighbour.
On a connected regular graph, $k$ mutants take over with probability
$(1 - r^{-k})/(1 - r^{-n})$ ($k/n$ when $r = 1$): the "if" direction of the isothermal theorem of
Lieberman, Hauert and Nowak, whose widely quoted "if and only if" form is false. The main
theorem is `Moran.isothermal`; `Moran.moran_formula` is Moran's 1958 formula on the complete graph.

* [Blueprint]({{ '/moran/blueprint/' | relative_url }}) · [as pdf]({{ '/moran/blueprint.pdf' | relative_url }}) ·
  [dependency graph]({{ '/moran/blueprint/dep_graph_document.html' | relative_url }})
* [API docs]({{ '/moran/docs/' | relative_url }})
* [Source](https://github.com/formal-dynamics/leanamycs/tree/main/moran)

## Shared finite dynamics library

`Dynamics` supplies uniform and weighted finite expectations, independent
products, pushforward, kernels, stationary distributions, and geometric
absorption. It is shared by voter dynamics, the Moran process, 3-majority and plurality consensus.

* [Blueprint]({{ '/dynamics/blueprint/' | relative_url }}) · [as pdf]({{ '/dynamics/blueprint.pdf' | relative_url }}) ·
  [dependency graph]({{ '/dynamics/blueprint/dep_graph_document.html' | relative_url }})
* [API docs]({{ '/dynamics/docs/' | relative_url }})
* [Source](https://github.com/formal-dynamics/leanamycs/tree/main/dynamics)

---

Each project is a separate Lean package (its own `lakefile.toml` and
toolchain) living in its own subdirectory of the repository, with `dynamics/`
shared by `3-majority/`, `voter/`, `moran/` and `plurality/`; this page is the
shared landing page linking to each development. See each subdirectory's own
`README.md` for build instructions.
