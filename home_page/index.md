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

This page gives a short overview of each area.
[RESULTS.md](https://github.com/formal-dynamics/leanamics/blob/main/RESULTS.md) lists every
formalized result with its scope, source, main Lean theorems and roadmap ID;
[ROADMAP.md](https://github.com/formal-dynamics/leanamics/blob/main/ROADMAP.md) lists what we
would like to formalize next; and
[PROVENANCE.md](https://github.com/formal-dynamics/leanamics/blob/main/PROVENANCE.md) records
proof routes, explicit constants and authorship. Where a statement deviates from its source, the
package's `FORMALIZATION_DIFFERENCES.md` lists the deviations. Many statements make "for
sufficiently large $n$" explicit, with thresholds that can be astronomically large.

## Majority dynamics: 3-Majority and plurality consensus

In the *3-majority* dynamics every node holds one of $k$ colors and, every round, adopts the
majority color among three nodes sampled uniformly at random (the first one if all three differ).
With two opinions, a 3/5 share gives consensus within $O(\log n)$ rounds with probability
$1 - O(1/n)$, by an elementary proof (`ThreeMajority.majority3_consensus_whp`). With $k$ colors,
if the plurality color has at least $n/\lambda$ nodes and leads every other color by at least
$22\sqrt{\lambda n \log n}$, then after $O(\lambda \log n)$ rounds **all** nodes support it with
high probability (`Plurality.theorem_3_8`), formalizing the upper bound of
Becchetti, Clementi, Natale, Pasquale, Silvestri and Trevisan, *Simple Dynamics for Plurality
Consensus* (SPAA 2014), whose proof needs a minor correction (small repairs), together with its
Corollaries 3.10 to 3.12. With two opinions this is consensus from a vanishing imbalance: a gap of
$22\sqrt{3 n \log n}$, i.e. a fraction $1/2 + O(\sqrt{\log n / n})$, suffices for consensus within
$390 \log n$ rounds with probability $1 - O(\log n / n)$ (`Plurality.majority3_vanishing_bias`).
The package also proves the paper's lower bounds ($\Omega(k \log n)$ rounds from balanced starts,
and $\Omega(k/h^2)$ rounds for $h$-plurality) and its characterization of the 3-input rules that
solve plurality consensus, except for one family of rules that remains open.

* Plurality: [Blueprint]({{ '/plurality/blueprint/' | relative_url }}) · [as pdf]({{ '/plurality/blueprint.pdf' | relative_url }}) ·
  [dependency graph]({{ '/plurality/blueprint/dep_graph_document.html' | relative_url }}) ·
  [API docs]({{ '/plurality/docs/' | relative_url }}) · [Source and README](https://github.com/formal-dynamics/leanamics/tree/main/plurality)
* Two opinions (`3-majority/`): [Blueprint]({{ '/3-majority/blueprint/' | relative_url }}) · [as pdf]({{ '/3-majority/blueprint.pdf' | relative_url }}) ·
  [dependency graph]({{ '/3-majority/blueprint/dep_graph_document.html' | relative_url }}) ·
  [API docs]({{ '/3-majority/docs/' | relative_url }}) · [Source and README](https://github.com/formal-dynamics/leanamics/tree/main/3-majority)

## Median dynamics and 2-Choices

Every node holds a value from a linearly ordered set and, every round, adopts the median of its
own value and the values of two nodes sampled uniformly at random (Doerr, Goldberg, Minder,
Sauerwald and Scheideler, *Stabilizing consensus with the power of two choices*, SPAA 2011).
Thresholding the process at any value gives the binary median process, i.e. 2-Choices, driven by
the same samples (`Median.threshold_run`). With two values, a gap of $128\sqrt{n \log n}$ gives
consensus on the majority within $\lceil 128 \log n \rceil$ rounds with probability $1 - 128/n$
(`Median.consensus_whp`), and a gap $\Delta$ of at least that size gives consensus within
$O(\log(n/\Delta) + \log \log n)$ rounds (`Median.binary_consensus_fast`). From any
configuration, with any number of values and even from a perfectly balanced start, consensus
follows within $O(\log n)$ rounds with probability $1 - O(1/n)$ (`Median.median_consensus_any`,
the paper's Theorem 1 without its adversary). The odd case of the paper's Theorem 21 is
formalized for exactly equal supports (`Median.odd_split_consensus`).

* [Blueprint]({{ '/median/blueprint/' | relative_url }}) · [as pdf]({{ '/median/blueprint.pdf' | relative_url }}) ·
  [dependency graph]({{ '/median/blueprint/dep_graph_document.html' | relative_url }})
* [API docs]({{ '/median/docs/' | relative_url }})
* [Source and README](https://github.com/formal-dynamics/leanamics/tree/main/median)

## Undecided-state dynamics

Each node holds opinion $a$, opinion $b$, or is undecided; every round it samples a uniformly random
node, adopts the sampled opinion if undecided, and becomes undecided if it sees the other opinion.
With $q$ undecided nodes, the bias between the two opinions grows in expectation by the factor
$1 + q/n$ in one round (`Undecided.expected_bias`), and every run is eventually absorbed in a
monochromatic configuration (`Undecided.absorbed`). In the sequential version, the
approximate-majority population protocol of Angluin, Aspnes and Eisenstat (Distributed Computing,
2008), one random pair of agents interacts per step: from any configuration with a decided agent,
consensus is reached within $O(n \log n)$ interactions, and from a gap of order
$\sqrt{n} \log n$ the initial majority wins, each with probability $1 - O(n^{-c})$ for every $c$
(`Undecided.Sequential.consensus_whp`, `Undecided.Sequential.majority_whp`).

* [Blueprint]({{ '/undecided/blueprint/' | relative_url }}) · [as pdf]({{ '/undecided/blueprint.pdf' | relative_url }}) ·
  [dependency graph]({{ '/undecided/blueprint/dep_graph_document.html' | relative_url }})
* [API docs]({{ '/undecided/docs/' | relative_url }})
* [Source and README](https://github.com/formal-dynamics/leanamics/tree/main/undecided)

## Voter model

For a finite connected nonbipartite undirected graph, each vertex independently
samples a neighbor according to a stochastic matrix (self-loops allowed) and
copies its previous color. The eventual probability of consensus in a color equals the initial
stationary weight of vertices with that color. Uniform neighbor sampling gives
degree weights, and regular graphs give the initial color fraction
(`Voter.consensus_probability`, formalizing Hassin and Peleg, Sections 2.1 to 2.3). One self-loop
removes the nonbipartiteness hypothesis, which covers the lazy voter on every connected graph and
neutral Wright–Fisher, where an allele held by $c$ of the $n$ individuals fixes with probability
$c/n$ (`Voter.wrightFisher_fixation`). On the complete graph, a duality with coalescing random
walks gives consensus within $2n\log n$ rounds with probability at least $1 - 1/n$
(`Voter.voter_consensus_whp`). The lazy voter reaches consensus on every connected graph within
$O(n^3 \log n)$ rounds with probability at least $1 - 1/n$ (`Voter.lazy_voter_consensus_whp`,
Hassin and Peleg's Theorem 2.5), and within $O(m/(d\varphi))$ rounds with probability at least
$1/2$, where $m$ is the number of edges, $d$ the minimum degree and $\varphi$ the conductance,
also on dynamic graphs and with any number of opinions (`Voter.lazy_consensus_conductance`,
after Berenbrink, Giakkoupis, Kermarrec and Mallmann-Trenn, ICALP 2016).

* [Blueprint]({{ '/voter/blueprint/' | relative_url }}) · [as pdf]({{ '/voter/blueprint.pdf' | relative_url }}) ·
  [dependency graph]({{ '/voter/blueprint/dep_graph_document.html' | relative_url }})
* [API docs]({{ '/voter/docs/' | relative_url }})
* [Source and README](https://github.com/formal-dynamics/leanamics/tree/main/voter)

## The Moran process and the isothermal theorem

In the Birth–death Moran process, an individual chosen with probability proportional to its
fitness (mutants $r$, residents $1$) places a copy of itself on a uniformly random neighbour.
On a connected regular graph, $k$ mutants take over with probability
$(1 - r^{-k})/(1 - r^{-n})$ ($k/n$ when $r = 1$): the "if" direction of the isothermal theorem of
Lieberman, Hauert and Nowak. The main
theorem is `Moran.isothermal`; `Moran.moran_formula` is Moran's 1958 formula on the complete graph.
On an arbitrary connected graph, the neutral push (Birth–death) and pull (death–Birth) processes
fix a mutant set $S$ with probabilities proportional to $\sum_{v \in S} 1/\deg v$ and to
$\sum_{v \in S} \deg v$ respectively (`Moran.push_fixation`, `Moran.pull_fixation`). On the star,
the fixation probability is exact from every configuration (after Broom and Rychtář, 2008), the
star amplifies selection whenever it has at least two leaves, and from a uniformly random initial mutant
the fixation probability tends to $1 - 1/r^2$ (`Moran.star_fixation`, `Moran.star_amplifier`,
`Moran.star_fixation_uniform_tendsto`).

* [Blueprint]({{ '/moran/blueprint/' | relative_url }}) · [as pdf]({{ '/moran/blueprint.pdf' | relative_url }}) ·
  [dependency graph]({{ '/moran/blueprint/dep_graph_document.html' | relative_url }})
* [API docs]({{ '/moran/docs/' | relative_url }})
* [Source and README](https://github.com/formal-dynamics/leanamics/tree/main/moran)

## Epidemics and rumor spreading

**Rumor spreading.** In the uniform *push* model on the complete graph $K_n$, every informed node
sends the rumor to a uniformly random other node each round; starting from a single informed node,
after $O(\log n)$ rounds **all** nodes are informed with high probability
(`RumorPush.push_informs_all_whp`). With the same random calls, *pull* and *push–pull* inform all
nodes within $\lceil 160 \ln n \rceil$ rounds with probability at least $1 - 2/n$
(`RumorPush.pull_informs_all_whp`, `RumorPush.pushPull_informs_all_whp`). For general
rumor-spreading processes, the upper bounds of Doerr and Kostrygin, *Randomized rumor spreading
revisited* (ICALP 2017), are formalized: exponential growth, exponential shrinking and the total
spreading time, with exponential tails (`Epidemics.Revisited.spreading_upper_tail`). Lemma 20 of
the paper needs a major correction, and the lower bounds and the concrete protocols are not
formalized.

**Reed–Frost and percolation.** In the Reed–Frost (Independent Cascade) epidemic, each infected
node infects each susceptible neighbour across an open edge and then recovers. With one coin per
edge, the nodes infected in round $t$ are exactly those at distance $t$ from the initial set in the
graph of open edges (`Epidemics.infected_iff`), so the final outbreak is the set of nodes connected
to the initial set, and with independent Bernoulli($p$) coins the probability of eventual infection
is a bond-percolation connection probability (`Epidemics.prob_infected_eq_prob_connected`). Below
the threshold (maximum degree $d$ and $p(d-1) \le 1 - \varepsilon$), every component of the
percolated graph has $O(\log n / \varepsilon^2)$ vertices with probability at least $1 - 1/n$, so
outbreaks are small and short (`Epidemics.reedFrost_subcritical`, after Becchetti, Clementi,
Denni, Pasquale, Trevisan and Ziccardi). Above it, $G(n, (1+\varepsilon)/n)$ has a linear-size
component, and Reed–Frost on $K_n$ with basic reproduction number above $1$ infects a linear number
of nodes with constant probability (`Epidemics.exists_giant_component`,
`Epidemics.reedFrost_large_outbreak`, after Krivelevich and Sudakov, 2013).

**COBRA and BIPS.** The coalescing-branching random walk and the BIPS epidemic are dual: on every
finite graph, the probability that COBRA started from a set $C$ has not visited $v$ by time $t$
equals the probability that BIPS with source $v$ infects no vertex of $C$ at time $t$
(`Epidemics.cobra_bips_duality`, Theorem 4 of Cooper, Radzik and Rivera, PODC 2016).

**SIR: the ODE and its law of large numbers.** For every solution of the Kermack–McKendrick SIR
equations (solutions are assumed, not constructed), the infected fraction initially grows if and
only if the basic reproduction number times the initial susceptible fraction exceeds $1$, and the
final susceptible fraction is the unique root of the final-size equation
(`Epidemics.KermackMcKendrick.IsSolution.final_size`). Kurtz's law of large numbers connects it to
the stochastic SIR epidemic: in discrete time, the scaled counts stay close to the solution up to
any fixed time, except with probability exponentially small in the population size
(`Epidemics.Kurtz.law_of_large_numbers`, with a maximal Azuma–Hoeffding inequality).

* Rumor spreading: [Blueprint]({{ '/rumor_spread/blueprint/' | relative_url }}) · [as pdf]({{ '/rumor_spread/blueprint.pdf' | relative_url }}) ·
  [dependency graph]({{ '/rumor_spread/blueprint/dep_graph_document.html' | relative_url }}) ·
  [API docs]({{ '/rumor_spread/docs/' | relative_url }}) · [Source and README](https://github.com/formal-dynamics/leanamics/tree/main/rumor_spread)
* Epidemics: [Blueprint]({{ '/epidemics/blueprint/' | relative_url }}) · [as pdf]({{ '/epidemics/blueprint.pdf' | relative_url }}) ·
  [dependency graph]({{ '/epidemics/blueprint/dep_graph_document.html' | relative_url }}) ·
  [API docs]({{ '/epidemics/docs/' | relative_url }}) · [Source and README](https://github.com/formal-dynamics/leanamics/tree/main/epidemics)

## Chemical reaction networks and population protocols

In a count-conserving bimolecular chemical reaction network ($A + B \to C + D$) with a common rate
constant, the jump chain of stochastic mass-action kinetics fires reaction $r$ with probability
proportional to its propensity. If $a$ and $b$ agents hold species $A \ne B$, a uniformly random
ordered pair of distinct agents holds one of each with probability $ab / \binom{n}{2}$ (and two $A$
with probability $\binom{a}{2} / \binom{n}{2}$), which is the propensity up to a common factor. So the
population protocol that draws such a pair, conditioned on the pair reacting, is exactly the jump
chain, as kernels on count vectors (`Crn.jumpKernel_eq_ppKernel`). The worked
instance is the approximate-majority network (`Crn.ApproxMajority.network_jumpKernel_eq_ppKernel`).

Population protocols with input and output stably compute every threshold predicate (an
integer linear combination of the input counts is below $c$) and every remainder predicate (it is
congruent to $c$ modulo $m$), and the stably computable predicates are closed under Boolean operations
(`Crn.IsSemilinearPred.stablyComputable`, the easy direction of Angluin, Aspnes, Diamadi, Fischer
and Peralta, 2006). Since every protocol is a count-conserving bimolecular network, every Boolean
combination of threshold and remainder predicates is stably decided by such a network
(`Crn.IsSemilinearPred.exists_network`).

* [Blueprint]({{ '/crn/blueprint/' | relative_url }}) · [as pdf]({{ '/crn/blueprint.pdf' | relative_url }}) ·
  [dependency graph]({{ '/crn/blueprint/dep_graph_document.html' | relative_url }})
* [API docs]({{ '/crn/docs/' | relative_url }})
* [Source and README](https://github.com/formal-dynamics/leanamics/tree/main/crn)

## Averaging dynamics

Every node replaces its value by the average of its neighbours' values. On a connected graph with
an odd closed walk all values converge to the degree-weighted average of the initial values
(`Averaging.tendsto_degAvg`); on a connected bipartite graph the values of a 2-colouring flip sign
forever (`Averaging.not_tendsto_of_colorable`). The convergence is exponential, at a rate given by
the second largest eigenvalue in absolute value of the random-walk matrix
(`Averaging.abs_walkMatrix_pow_sub_walkStationary_le`, Theorem 33 of the Becchetti, Clementi,
Natale survey, after Lovász), and the random sequential version, where one uniformly random edge
averages its endpoints, has expected step matrix $I - L/2m$ (`Averaging.Sequential.avg_edgeMatrix`).
On a regular graph made of two clusters with a spectral gap, starting from uniformly random
$\pm 1$ values, the sign of the change of a node's value in one round recovers the two clusters
after $O(\log n / \delta)$ rounds with probability at least $1 - 1/\sqrt{\pi n}$
(`Averaging.strong_reconstruction`, after Becchetti, Clementi, Natale, Pasquale and Trevisan,
*Find your place*, SODA 2017).

* [Blueprint]({{ '/averaging/blueprint/' | relative_url }}) · [as pdf]({{ '/averaging/blueprint.pdf' | relative_url }}) ·
  [dependency graph]({{ '/averaging/blueprint/dep_graph_document.html' | relative_url }})
* [API docs]({{ '/averaging/docs/' | relative_url }})
* [Source and README](https://github.com/formal-dynamics/leanamics/tree/main/averaging)

## Shared finite dynamics library

`Dynamics` supplies uniform and weighted finite expectations (which agree with Mathlib's
`Finset.expect`), independent products, pushforward, kernels, stationary distributions and
geometric absorption, together with the tools the dynamics share: Chernoff, Hoeffding and
Bernstein bounds, finite-horizon optional stopping, time reversal of independent rounds, drift
theorems, a hitting-time lemma for processes with multiplicative drift, progress through nested
phases, and round types on graphs.

* [Blueprint]({{ '/dynamics/blueprint/' | relative_url }}) · [as pdf]({{ '/dynamics/blueprint.pdf' | relative_url }}) ·
  [dependency graph]({{ '/dynamics/blueprint/dep_graph_document.html' | relative_url }})
* [API docs]({{ '/dynamics/docs/' | relative_url }})
* [Source and README](https://github.com/formal-dynamics/leanamics/tree/main/dynamics)

---

Each project is a separate Lean package (its own `lakefile.toml` and toolchain) living in its own
subdirectory of the repository. The shared `dynamics/` package is used by every other package:
`rumor_spread/`, `3-majority/`, `plurality/` (which also requires `3-majority/`), `median/`,
`undecided/`, `voter/`, `moran/`, `epidemics/`, `crn/` and `averaging/`. This page is the shared
landing page linking to each development; see each subdirectory's own `README.md` for build
instructions.
