# Formalized results

Everything listed here is proved on `main`, without `sorry`. One table per area: what is
proved (with its scope), the source, the main Lean theorems and the roadmap ID
([ROADMAP.md](ROADMAP.md)). [PROVENANCE.md](PROVENANCE.md) gives, for each result, the full
source, the proof route, the explicit constants and who produced it. Where a statement deviates
from its source (explicit constants, other hypotheses, corrections), the deviations are listed
in the package's `FORMALIZATION_DIFFERENCES.md`, linked under each heading.

Conventions: "w.p." means "with probability", `log` is the natural logarithm, and the Lean names
after the first one in a cell are in the same namespace. Size hypotheses such as `log n ≥ 40`
make "for sufficiently large `n`" explicit and can mean astronomically large populations (see
the table of explicit constants in [PROVENANCE.md](PROVENANCE.md)). Short citations: "Survey" is
Becchetti, Clementi, Natale, *Consensus dynamics: an overview*, SIGACT News 2020; BCNPST is
Becchetti, Clementi, Natale, Pasquale, Silvestri, Trevisan, *Simple dynamics for plurality
consensus*; "Doerr et al. 2011" is Doerr, Goldberg, Minder, Sauerwald, Scheideler, *Stabilizing
consensus with the power of two choices*, SPAA 2011; BCDPTZ is Becchetti, Clementi, Denni,
Pasquale, Trevisan, Ziccardi. Full references are in [ROADMAP.md](ROADMAP.md) and the package
READMEs.

## Shared probability layer (`dynamics/`)

[README](dynamics/README.md) · [differences from the sources](dynamics/FORMALIZATION_DIFFERENCES.md)

| Result | Source | Main theorems | Roadmap |
| --- | --- | --- | --- |
| A finite stochastic kernel from which a target is reachable from every state is absorbed geometrically fast, and every finite kernel has a stationary distribution. | Standard | `Dynamics.Kernel.finite_absorption`, `exists_stationary` | FND-1, FND-2 |
| The layer's expectations (`avg`, and `expList` over i.i.d. uniform rounds) are Mathlib's `Finset.expect`. | Standard | `Dynamics.avg_eq_expect`, `expList_eq_expect`, `expList_eq_independent_expect` | – |
| Multiplicative Chernoff bounds for independent, non-identical Bernoulli trials (upper and lower tails, with the mean replaced by any bound). | Mitzenmacher–Upfal, Thms 4.4, 4.5, Ex. 4.7 | `Dynamics.Distribution.chernoff_upper`, `chernoff_lower` | FND-3 |
| Hoeffding's and Bernstein's inequalities for sums of independent coordinates, Chernoff tails for one uniform round, and Markov's inequality: the concentration and tail bounds used by `3-majority/`, `plurality/` and `median/`, stated once here. | Standard (Dubhashi–Panconesi, Thm 1.1; Mitzenmacher–Upfal, Thms 4.4, 4.5) | `Dynamics.avg_hoeffding`, `avg_bernstein`, `avg_chernoff_upper_of_mgf`, `avg_chernoff_lower_of_mgf`, `avg_markov_one` | – |
| Finite-horizon optional stopping: an observable conserved in expectation and constant on two target events gives the absorption probability `(φ(x₀) − φB)/(φA − φB)`. | Standard | `Dynamics.Kernel.event_error_of_invariant`, `tendsto_event_of_invariant`, `iSup_event_of_invariant` | FND-4 |
| Time reversal of i.i.d. rounds: a functional of the rounds has the same expectation on the reversed rounds. | Standard | `Dynamics.expList_comp_reverse`, `Kernel.iterate_ofStep_foldr` | FND-6 |
| Progress through nested phases, without the paper's hypothesis `ε ≤ ν`. | BCNPST, SPAA 2014, Lemma A.4 (stated without proof) | `Dynamics.Kernel.nested_phases` | – |
| Drift theorems for a generic potential: drift `c_t/Ψ` gives absorption w.p. `≥ 1/2` once `∑ c_t ≥ 4Ψ₀²`, and multiplicative drift bounds the survival probability; also for time-dependent chains. | Berenbrink et al., ICALP 2016, Lemmas 2.2, 2.4 | `Dynamics.Kernel.drift_absorption`, `multiplicative_drift` | FND-5 |
| Round types on a graph: every vertex samples a uniform neighbour, or one uniform oriented edge per step, with their independence and averaging lemmas. | – | `Dynamics.NeighborRound`, `EdgeRound` | FND-7 |
| Hitting-time lemma for a finite kernel with an observable `X ≤ q` that grows geometrically except with exponentially small probability and leaves `0` with constant probability: `X ≥ c₄ log q` within `O(log q)` steps w.p. `≥ 1 − q^{−c₆}`, with the added hypothesis `c₄ log q ≤ q` that a non-asymptotic statement needs. | Doerr et al. 2011, Claim 2.9 | `Dynamics.Kernel.drift_hitting`, `drift_hitting_log` | MAJ-8 (the lemma) |

## Majority and plurality (`3-majority/`, `plurality/`)

[3-majority README](3-majority/README.md) · [plurality README](plurality/README.md) ·
[plurality: differences from the sources](plurality/FORMALIZATION_DIFFERENCES.md)

| Result | Source | Main theorems | Roadmap |
| --- | --- | --- | --- |
| 3-Majority with two opinions: from a 3/5 share, consensus within `10 + ⌈6 log n⌉ + 2` rounds w.p. `≥ 1 − 500/n`, for `log n ≥ 30`; the same for `k = 2` colors in `plurality/`. | No specific paper (own elementary proof) | `ThreeMajority.majority3_consensus_whp`, `Plurality.binary_consensus_whp` | – |
| 3-Majority with `k ≥ 2` colors: if the plurality color has `≥ n/λ` nodes and a bias `≥ 22√(λ n log n)`, all nodes adopt it within `130 λ log n` rounds w.p. `≥ 1 − 143 λ log n / n`, for `log n ≥ 40`. | BCNPST, SPAA 2014, Thm 3.8, whose proof needs a minor correction (small repairs) | `Plurality.theorem_3_8`, `theorem_3_8_bigO` | MAJ-7 |
| Corollaries of Theorem 3.8, including the `O(min{k, (n/log n)^{1/3}} log n)` bound. | BCNPST, SPAA 2014, Cors 3.10–3.12 | `Plurality.corollary_3_10`, `corollary_3_11`, `corollary_3_12` | MAJ-7 |
| Two opinions from a vanishing bias: a gap `22√(3 n log n)` (a fraction `1/2 + O(√(log n / n))`) gives consensus within `390 log n` rounds w.p. `≥ 1 − 429 log n / n`, for `log n ≥ 40`. | BCNPST, SPAA 2014, Thm 3.8 with `k = 2` | `Plurality.majority3_vanishing_bias` | MAJ-2 |
| 3-Majority with two opinions from **any** configuration, even perfectly balanced: consensus after any `T ≥ C log n` rounds w.p. `≥ 1 − C log n / n` for `log n ≥ 40`, and w.p. `≥ 1 − 1/n` for `log n ≥ C` (`C` exists but is not explicit); the gap first reaches `22√(3 n log n)` through the hitting-time lemma. | Survey §4 Case 3 (the symmetry breaking of Doerr et al. 2011 for 2-Choices), carried out for 3-Majority | `Plurality.majority3_any_start`, `majority3_any_start_whp`, `majority3_symmetry_breaking` | MAJ-8 |
| Lower bounds from a balanced start: 3-majority needs `Ω(k log n)` rounds for `k ≤ n^{1/4−δ}` (a narrower range than the paper's), and `h`-plurality needs `Ω(k/h²)` rounds. | BCNPST, SPAA 2014, Thms 4.2, 4.12, Lemma 4.11 | `Plurality.theorem_4_2_log`, `lemma_4_11`, `theorem_4_12_log` | MAJ-10 |
| Classification of 3-input rules: a rule that solves plurality consensus from a clear majority is uniform (part b), and follows the clear majority on every pair (part a) except for rules with `Δ_r, Δ_b ≤ 1`, which remain open. | BCNPST, SPAA 2014, Thm 4.8 | `Plurality.theorem_4_8_a`, `theorem_4_8_b` | MAJ-9 (partial) |

## Median and 2-Choices (`median/`)

[README](median/README.md) · [differences from the sources](median/FORMALIZATION_DIFFERENCES.md)

Theorem numbers of Doerr et al. 2011 follow its 2009 version (Dagstuhl Seminar Proceedings 09371); other rows use their own paper's numbering.

| Result | Source | Main theorems | Roadmap |
| --- | --- | --- | --- |
| Thresholding the median dynamics at any value gives the binary median process (2-Choices) with the same samples; validity, the binary one-round expectation `n(3p² − 2p³)`, almost-sure consensus. | Doerr et al. 2011 | `Median.threshold_run`, `step_mem`, `expected_ones`, `absorbed` | – |
| 2-Choices from a gap `128√(n log n)`: consensus on the majority within `⌈128 log n⌉` rounds w.p. `≥ 1 − 128/n`, for `log n ≥ 128`. | Doerr et al. 2011, two values | `Median.consensus_whp` | MAJ-1 |
| From any configuration (two values, even perfectly balanced, or any number of values), consensus within `⌈C log n⌉` rounds w.p. `≥ 1 − C/n` for `log n ≥ C` (`C = 2¹⁸` for two values, `3·2¹⁸ + 3` in general); the adversary of Theorem 1 is in the next row. | Doerr et al. 2011, Thm 1 | `Median.binary_any_start`, `consensus_of_binary`, `median_consensus_any` | MAJ-8 (2-Choices) |
| Theorem 1 with its adaptive adversary: against an adversary that recolours at most `F ≤ √n/2²⁰` nodes per round as a function of the history, from any configuration, all but `2²⁰ (F + log n)` nodes hold one value at every time from `⌈2²⁰ log n⌉` to `⌈2²⁰ log n⌉ + H`, except w.p. `≤ (2²⁰ log n + H)/n²`, for `log n ≥ 2²⁰`; with `m` legal values the failure probability is multiplied by `m − 1`. | Doerr et al. 2011, Thms 2, 3, 10, 20 (SPAA 2011: Thm 1.1) | `Median.binary_almost_stable`, `median_almost_stable`, `binary_almost_stable_of_isAdvRun` | MAJ-3 |
| Faster consensus from a gap `Δ ≥ 128√(n log n)`: within `⌈128 (log(n/Δ) + log log n)⌉` rounds w.p. `≥ 1 − 128/n` for 2-Choices, and with a margin `Δ` on both sides of a value `v` for many values. | Doerr et al. 2011 | `Median.binary_consensus_fast`, `median_consensus_fast` | MAJ-1 |
| Odd case of Theorem 21 for exactly equal supports: when `2k + 1` values are held by `n/(2k+1)` nodes each, the middle one wins within `⌈256 (log(2k+1) + log log n)⌉` rounds w.p. `≥ 1 − 256/n` (the random start and the even case are not formalized). | Doerr et al. 2011, Thm 21 | `Median.odd_split_consensus` | – |
| Two-sample voting on a `d`-regular expander with `λ_G = max{λ₂, \|λₙ\|} ≤ 3/5 − ε`: from a minority of at most `(ε/5) n`, every vertex holds the majority after `⌈25000 log n⌉` rounds except w.p. `1/n + (25000 log n + 1) e^{−εn/25000}`; the expander mixing lemma on every `d`-regular graph (the paper's Theorem 2, from an imbalance `K λ_G n`, is not formalized). | Cooper, Elsässer, Radzik, ICALP 2014, Thm 4, Lemmas 3, 5 | `Median.two_choices_expander`, `two_choices_expander_explicit`, `expander_mixing` | MAJ-5 (a) |
| k-party 2-Choices with any number `k` of colours (no bound such as `k = O(n^ε)`): if the plurality colour leads every other colour by `128√(n log n)`, all nodes hold it within `⌈384 (n/c₁) log n⌉` rounds (hence within `⌈384 k log n⌉`) w.p. `≥ 1 − 384/n`, for `log n ≥ 384`; the coupling lemma as a stochastic domination (the adversary and the lower bounds of the paper are not formalized). | Elsässer, Friedetzky, Kaaser, Mallmann-Trenn, Trinker, arXiv:1602.04667 (arXiv v5 numbering), Thm 1.2, Lemmas 2.2, 2.3; the proofs of Thm 1.2 and Lemma 2.3 need a minor correction | `Median.TwoChoices.plurality_whp`, `plurality_whp_k`, `distance_increases`, `count_stochDom` | MAJ-4 |
| Lower bound for k-party 2-Choices: if every colour has at most `ℓ` nodes, no colour exceeds `max {2ℓ, γ log n}` nodes for `n/(γ max {2ℓ, γ log n})` rounds w.p. `≥ 1 − 1/n` (every `γ ≥ 8`); hence from colours of `O(log n)` nodes, consensus needs `Ω(n/log n)` rounds w.p. `≥ 1 − 1/n`. | Berenbrink, Clementi, Elsässer, Kling, Mallmann-Trenn, Natale, PODC 2017; Thms 1 (Simplified) and 5 of arXiv:1702.04921 (v1); a constant in the proof of Thm 5 needs a minor correction | `Median.TwoChoices.lower_bound_strong`, `consensus_time_lower`, `colour_escape_le` | MAJ-6 (a) |

## Undecided-state dynamics (`undecided/`)

[README](undecided/README.md) · [differences from the sources](undecided/FORMALIZATION_DIFFERENCES.md)

| Result | Source | Main theorems | Roadmap |
| --- | --- | --- | --- |
| Synchronous, two opinions, complete graph: exact one-round expectations, so the bias grows in expectation by the factor `1 + q/n` (`q` undecided nodes), and almost-sure absorption in a monochromatic configuration. | Survey §6 (basic laws) | `Undecided.expected_bias`, `absorbed` | UND-0 |
| Synchronous, two opinions, complete graph, majority phase: from any configuration (any number of undecided nodes) with bias `≥ 10⁴ √(n log n)`, all nodes hold the majority after `⌈10⁴ log n⌉` rounds w.p. `≥ 1 − 2/n`, for `log n ≥ 10⁴`; also the SODA 2015 form, without undecided nodes and with a multiplicative bias `1 + α`. | Clementi, Ghaffari, Gualà, Natale, Pasquale, Scornavacca, MFCS 2018, Thm 3.2; Becchetti, Clementi, Natale, Pasquale, Silvestri, SODA 2015, Thm 11 with `k = 2` | `Undecided.majority_whp`, `majority_explicit`, `majority_whp_abs`, `majority_whp_of_ratio` | UND-1 |
| Synchronous, `k` colours, complete graph: from a configuration without undecided nodes in which the plurality colour leads every other colour by a factor `1 + α`, all nodes hold it after `⌈C md(c) log n⌉` rounds w.p. `≥ 1 − C/n` (`md` the monochromatic distance, `C = 10⁵ ((1 + α)²/α)²`), for `log n ≥ C` and `C k ≤ (n/log n)^{1/3}`. | Becchetti, Clementi, Natale, Pasquale, Silvestri, SODA 2015, Thm 11, whose range of `k` needs a minor correction | `Undecided.Plurality.plurality_whp`, `plurality_explicit`, `expected_count_some`, `md_le_card` | UND-3 |
| Synchronous, `k` colours, complete graph, lower bound: from any configuration without undecided nodes (no bias assumed), for every `T ≤ md(c)/C` no colour has more than `C n/md(c)` nodes after `T` rounds w.p. `≥ 1 − C/n`, and all nodes hold the same colour after `T` rounds w.p. `≤ C/n` when `C (T + 1) ≤ md(c)`; so the convergence time is `Ω(md(c))`. For `log n ≥ C` and `C k ≤ (n/log n)^{1/6}` (the proof gives `C = 1017429`, twice that for the consensus form). | Becchetti, Clementi, Natale, Pasquale, Silvestri, SODA 2015, Thm 8 with Lemmas 3, 6, 7, of which Lemmas 6 and 7 need minor corrections | `Undecided.Plurality.lower_bound_whp`, `lower_bound_consensus`, `first_round`, `descent`, `plateau` | UND-3 |
| Sequential 3-state approximate majority (one random ordered pair per step): from any non-blank configuration, consensus within `C n log n` interactions w.p. `≥ 1 − C/n^c`, and from a gap `C √n log n` the initial majority wins (the sharper gap `√(n log n)` is not formalized). | Angluin, Aspnes, Eisenstat, Distrib. Comput. 2008, Thms 1, 2 | `Undecided.Sequential.consensus_whp`, `majority_whp`, `approximate_majority` | UND-2 |

## Voter model (`voter/`)

[README](voter/README.md) · [differences from the sources](voter/FORMALIZATION_DIFFERENCES.md)

| Result | Source | Main theorems | Roadmap |
| --- | --- | --- | --- |
| Weighted synchronous voter on a connected non-bipartite graph: each color wins with probability equal to its initial stationary mass (`∑ d(v)/2m` for uniform neighbours, the initial fraction on regular graphs, any number of colors). | Hassin–Peleg 2001, §2.1–2.3 | `Voter.consensus_probability`, `uniform_consensus_probability`, `regular_consensus_probability`, `color_consensus_probability` | VOT-1 |
| The same on every connected graph with one self-loop, hence for the lazy voter `(I + D⁻¹A)/2` on bipartite graphs too, and neutral Wright–Fisher fixes allele `a` w.p. `c_a/n`. | Hassin–Peleg 2001, Remark p. 254; classical | `Voter.consensus_probability_of_selfLoop`, `lazyNeighbor_consensus_probability`, `wrightFisher_fixation` | VOT-2 |
| On the complete graph with self-loops: duality with coalescing random walks, and consensus within `2 n log n` rounds w.p. `≥ 1 − 1/n`. | Hassin–Peleg 2001, §2.4; Survey Thms 6–7 | `Voter.voter_consensus_whp` | VOT-3 |
| For the lazy voter on every connected graph: consensus within `A n³ log n` rounds w.p. `≥ 1 − 1/n` (the proof gives `A = 255`); duality with two coalescing tokens for every sampling kernel. | Hassin–Peleg 2001, Thm 2.5; Survey Thm 8, which needs a minor correction for the plain synchronous voter | `Voter.lazy_voter_consensus_whp`, `iterate_disagreement_le_of_meeting` | VOT-6 |
| For the plain voter (copy a uniformly random neighbour) on every connected non-bipartite graph: two plain walks meet within `16 n³` steps w.p. `≥ 1/2`, and consensus within `A n³ log n` rounds w.p. `≥ 1 − 1/n` (the proof gives `A = 80`). | Hassin–Peleg 2001, Lemma 2.4 (via the bipartite double cover; its proof needs a minor correction) and Thm 2.5; Survey Thm 8 with the nonbipartiteness hypothesis | `Voter.plain_voter_consensus_whp`, `plain_disagreement_le`, `plain_meeting_le_half`, `doubleCover_connected`, `plainPotential_drift` | VOT-6 |
| For the lazy voter on a graph with conductance `φ`: consensus within `128 m/(d_min φ)` rounds w.p. `≥ 1/2` and in expected time at most twice that, also on dynamic graphs with fixed degrees and for any number of opinions (the bound `n log n/φ²` is in the next row). | Berenbrink, Giakkoupis, Kermarrec, Mallmann-Trenn, ICALP 2016, Thm 1.1 (i); its Lemma 2.1 needs a minor correction | `Voter.lazy_consensus_conductance`, `lazy_expected_consensus_time`, `dynamic_consensus_conductance`, `lazy_consensus_conductance_many` | VOT-5 |
| For the lazy voter on a graph with conductance `φ`: consensus within `96 n ln n/φ²` rounds w.p. `≥ 1 − 1/n²` (two opinions) and `≥ 1 − 1/n` (any number of opinions), also on dynamic graphs with fixed degrees, expected time at most twice that, and both bounds together: consensus within `min{τ, τ'}` rounds w.p. `≥ 1/2`. | Berenbrink, Giakkoupis, Kermarrec, Mallmann-Trenn, ICALP 2016, Thm 1.1 (ii); its Lemma 2.4 needs a minor correction | `Voter.lazy_consensus_conductance_sq`, `dynamic_consensus_conductance_sq`, `lazy_consensus_conductance_sq_many`, `dynamic_consensus_conductance_sq_many`, `lazy_expected_consensus_time_sq`, `lazy_consensus_conductance_min` | VOT-5 |

## Moran process (`moran/`)

[README](moran/README.md) · [differences from the sources](moran/FORMALIZATION_DIFFERENCES.md)

| Result | Source | Main theorems | Roadmap |
| --- | --- | --- | --- |
| Birth–death Moran process on a connected regular graph: `k` mutants of fitness `r` fix w.p. `(1 − r^{−k})/(1 − r^{−n})` (`k/n` if `r = 1`), the "if" direction of the isothermal theorem; Moran's formula on the complete graph. | Lieberman, Hauert, Nowak, Nature 2005; Moran 1958 | `Moran.isothermal`, `isothermal_neutral`, `moran_formula` | MOR-1, MOR-2 |
| Neutral push (Birth–death) and pull (death–Birth) on any connected graph: a mutant set `S` fixes w.p. `∑_{v∈S} 1/deg v / ∑_v 1/deg v` (push) and `∑_{v∈S} deg v / 2m` (pull). | Antal, Redner, Sood, PRL 2006 (by approximation there) | `Moran.push_fixation`, `pull_fixation` | VOT-4 |
| The star: exact fixation probability from every configuration, amplification of selection for every `n ≥ 2`, and uniform-start fixation tending to `1 − 1/r²`. | Broom, Rychtář, Proc. R. Soc. A 2008; Lieberman, Hauert, Nowak 2005 | `Moran.star_fixation`, `star_fixation_uniform_sum`, `star_amplifier`, `star_amplifier_deleterious`, `star_fixation_uniform_tendsto` | MOR-3 (the star) |

## Epidemics and rumor spreading (`epidemics/`, `rumor_spread/`)

[rumor_spread README](rumor_spread/README.md) ·
[rumor_spread: differences from the sources](rumor_spread/FORMALIZATION_DIFFERENCES.md) ·
[epidemics README](epidemics/README.md) ·
[epidemics: differences from the sources](epidemics/FORMALIZATION_DIFFERENCES.md)

| Result | Source | Main theorems | Roadmap |
| --- | --- | --- | --- |
| PUSH on the complete graph from one informed node: all nodes informed within `(⌈117 log n⌉ + 23) + ⌈6 log n⌉` rounds w.p. `≥ 1 − 2/n` (not the sharp `log₂ n + ln n`, whose upper bound is in the EPI-8 (c) row below). | Classical (own elementary proof) | `RumorPush.push_informs_all_whp` | – |
| PULL and PUSH–PULL on the complete graph: all nodes informed within `⌈160 log n⌉` rounds w.p. `≥ 1 − 2/n`. | Karp, Schindelhauer, Shenker, Vöcking, FOCS 2000 | `RumorPush.pull_informs_all_whp`, `pushPull_informs_all_whp` | EPI-5 |
| General rumor-spreading processes, upper bounds only: exponential growth in `log_{1+γ} n + O(1)` rounds, exponential shrinking in `(1/ρ) ln n + O(1)` rounds, and the total time, with exponential tails (the lower bounds are not formalized; the instances push, pull, push–pull are in the next row). | Doerr, Kostrygin, ICALP 2017; its Lemma 20 needs a major correction | `Epidemics.Revisited.growth_upper_tail`, `shrinking_upper_tail`, `spreading_upper_tail`, `jumpProb_le` | EPI-8 |
| Push, pull and push–pull on the complete graph (self-calls allowed), from any nonempty informed set: all nodes informed within `log₂ n + ln n`, `log₂ n + log₂ ln n` and `log₃ n + log₂ ln n` rounds plus `O(1)`, with exponential tails and in expectation, for `n` beyond some `N` (upper bounds only; for push, the sharp bound of Frieze–Grimmett and Pittel); the double exponential shrinking regime behind pull and push–pull. | Doerr, Kostrygin, ICALP 2017, Thms 43, 51–53; the proof of Theorem 43 and the paper's parameters of the instances need a minor correction | `Epidemics.Revisited.push_spreading_tail`, `push_spreading_expect`, `pull_spreading_tail`, `pushPull_spreading_tail`, `double_shrinking_upper_tail` | EPI-8 (c), EPI-5 (sharp PUSH upper bound) |
| Reed–Frost (Independent Cascade) with one coin per edge, pathwise: the nodes infected in round `t` are those at distance `t` from the initial set in the graph of open edges, so with i.i.d. Bernoulli(`p`) coins the infection probability is a bond-percolation connection probability. | Kempe, Kleinberg, Tardos 2003; BCDPTZ, arXiv:2103.16398, Thm A.3 | `Epidemics.infected_iff`, `final_recovered_iff`, `prob_infected_eq_prob_connected` | EPI-1 |
| Subcritical percolation (maximum degree `d`, `p(d − 1) ≤ 1 − ε`): every component has at most `(10/ε²) log n` vertices w.p. `≥ 1 − 1/n`; hence small and short subcritical Reed–Frost outbreaks, and the same for `G(n, c/n)` with `c ≤ 1 − ε`. | BCDPTZ, arXiv:2103.16398, Thms 2.3, E.1 | `Epidemics.prob_components_small`, `reedFrost_subcritical`, `erdosRenyi_subcritical` | EPI-2 |
| Small-world networks below the percolation threshold: in `SWG(n, c/n)` (the cycle plus `G(n, c/n)`) with `p < p* − ε`, `p* = (√(c² + 6c + 1) − c − 1)/(2c)`, and in `3-SWG(n)` (the cycle plus a uniform perfect matching) with `p < 1/2 − ε`, every component of the percolated graph has `O(log n)` vertices w.p. `≥ 1 − C/n`, so Reed–Frost is over within `O(log n)` rounds with `O(\|I₀\| log n)` recovered nodes (the supercritical half is not formalized). | BCDPTZ, arXiv:2103.16398, claim 2 of Thms 2.1, 2.2, 2.4, 2.5 (Thm 2.5 needs a minor correction), Lemma C.1 | `Epidemics.swg_subcritical`, `swg3_subcritical`, `swg_reedFrost_subcritical`, `swg3_reedFrost_subcritical`, `swg_components_small` | EPI-6 (subcritical half) |
| Supercritical `G(n, (1+ε)/n)`: a path of `≥ ε² n/5` edges and a component of `≥ ε n/2` vertices w.p. `≥ 1 − C/n` for small `ε`, and a linear component for every `ε > 0`; Reed–Frost on the complete graph with `R₀ > 1` infects `Ω(n)` nodes w.p. `Ω(1)`. | Krivelevich, Sudakov, RSA 2013, Thms 1(2), 2 | `Epidemics.exists_long_path`, `exists_giant_component`, `exists_linear_component`, `reedFrost_large_outbreak` | EPI-3 |
| COBRA–BIPS duality, on every finite graph and for every `k`: COBRA from `C` has not hit `v` by time `t` with the same probability as BIPS from `{v}` avoids `C` at time `t`, also pathwise along reversed rounds (the cover-time bound is not formalized). | Cooper, Radzik, Rivera, PODC 2016, Thm 4 | `Epidemics.cobra_bips_duality`, `cobra_bips_duality_singleton`, `cobra_hit_iff_bips_reverse` | EPI-4 |
| Kermack–McKendrick SIR model with constant rates, for every solution on `[0, ∞)` (solutions are assumed, not constructed): `s = s₀ exp(−R₀ r)`, `i` initially increases iff `R₀ s₀ > 1`, the final-size equation and the uniqueness of its root, the peak. | Kermack–McKendrick 1927; Hethcote, SIAM Review 2000, Thm 2.1 | `Epidemics.KermackMcKendrick.IsSolution.s_eq_mul_exp`, `initially_increasing_iff`, `final_size`, `final_size_unique`, `exists_peak` | EPI-7 |
| Kurtz's law of large numbers for the stochastic SIR model in discrete time (uniformized chain, natural-number rates): up to time `T` the scaled counts stay within `L·dist(initial points) + ε` of the Kermack–McKendrick solution except w.p. `C exp(−c ε² N)`; along the way, a maximal Azuma–Hoeffding inequality. | Kurtz, J. Appl. Probab. 1970; Wormald 1999, Thm 5.1 | `Epidemics.Kurtz.law_of_large_numbers`, `tendsto_deviationProb`, `expList_azuma` | CRN-2 |

## Chemical reaction networks (`crn/`)

[README](crn/README.md) · [differences from the sources](crn/FORMALIZATION_DIFFERENCES.md)

| Result | Source | Main theorems | Roadmap |
| --- | --- | --- | --- |
| A count-conserving bimolecular CRN with a common rate constant has the same jump chain, on count vectors, as the population protocol that draws a uniformly random ordered pair of distinct agents conditioned on the pair reacting; worked instance: approximate majority (unequal rate constants are not formalized). | Anderson, Kurtz 2011; Gillespie 1977; Doty, SODA 2014 | `Crn.jumpKernel_eq_ppKernel`, `Crn.ApproxMajority.network_jumpKernel_eq_ppKernel` | CRN-1 |
| Easy direction of stable computation: Boolean combinations of threshold and remainder predicates are stably computable by population protocols, hence stably decided by such CRNs; the class is shown to be contained in Mathlib's semilinear sets, not equal to them, and the converse is not formalized. | Angluin, Aspnes, Diamadi, Fischer, Peralta, Distrib. Comput. 2006, whose Lemma 5 needs a minor correction for a single agent | `Crn.IsSemilinearPred.stablyComputable`, `exists_network`, `isSemilinearSet` | CRN-3 |
| Majority on connected interaction graphs: the 4-state ambassador protocol stably computes the initial majority on every connected graph (ties excluded); no protocol with at most 3 states does, already on complete graphs, so 4 states are optimal; the 3-state approximate-majority protocol, with a uniformly random oriented edge per step and a uniformly random placement, converges to the minority with probability at most that of converging to the majority (at every finite time), hence to the majority with probability at least `1/2` on connected graphs (undirected graphs only). | Mertzios, Nikoletseas, Raptopoulos, Spirakis, ICALP 2014 (arXiv:1404.7671), Thms 1, 2 and 4, whose proofs need minor corrections; Angluin, Aspnes, Eisenstat, Distrib. Comput. 2008 | `Crn.ambassador_graphStablyComputes`, `not_stablyComputesOnGraph_top_majority`, `rank_majority_eq_four`, `Crn.ApproxMajority.winProb_minority_le_majority`, `half_le_absorbProb_majority` | CRN-4 |

## Averaging dynamics (`averaging/`)

[README](averaging/README.md) · [differences from the sources](averaging/FORMALIZATION_DIFFERENCES.md)

| Result | Source | Main theorems | Roadmap |
| --- | --- | --- | --- |
| On a connected graph with an odd closed walk, the values converge to the degree-weighted average of the initial values; on a connected bipartite graph they do not converge for some initial values. | Classical (Survey §7.2) | `Averaging.tendsto_degAvg`, `not_tendsto_of_colorable` | AVG-1 |
| Rate of convergence: `\|Pᵗ(u,v) − π(v)\| ≤ √(d(v)/d(u)) λᵗ`, with `λ < 1` on connected non-bipartite graphs. | Survey Thm 33, whose `√(d(v)/d(v))` needs a minor correction to `√(d(v)/d(u))`; Lovász 1993, Thm 5.1 | `Averaging.abs_walkMatrix_pow_sub_walkStationary_le`, `walkLambda_lt_one`, `abs_avgIter_sub_walkStationary_le` | AVG-1 |
| Random sequential averaging: the expected step matrix (`I − L/2m` for a uniform edge, and equations (4)–(5)) and the first moment `𝔼[x⁽ᵗ⁾] = W̄ᵗ x⁽⁰⁾`. | Survey §7.2–7.3; Boyd, Ghosh, Prabhakar, Shah 2006 | `Averaging.Sequential.avg_expect_edgeMatrix`, `avg_edgeMatrix`, `expList_seqRun` | AVG-1 |
| Strong reconstruction: on a connected `(2n, d, b)`-clustered regular graph with `1 − 2b/d > (1+δ)λ`, from uniformly random `±1` values the sign of `x⁽ᵗ⁻¹⁾(u) − x⁽ᵗ⁾(u)` recovers the two clusters at every `t ≥ ⌈log(4n³)/log(1+δ)⌉ + 1`, w.p. `≥ 1 − 1/√(πn)`. | Becchetti, Clementi, Natale, Pasquale, Trevisan, SODA 2017 / SIAM J. Comput. 2020, Thm 3.2 | `Averaging.strong_reconstruction` | AVG-2 |
| Averaging whenever you meet: one uniformly random edge averages its endpoints per round, and a node starts from a uniform `±1` at its first activation. On an `(n, d, b)`-clustered regular graph with `λ₂/λ₃ ≤ λ₃ ε⁴/(c log² n)` (`c = 10⁶`), over the phase `6 (n/λ₃) log n ≤ t ≤ 12 (n/λ₃) log n`, at least `(1 − 3ε) n` nodes are `ε`-good at every round w.p. `≥ 1 − ε`, so the signs recover the communities (weak reconstruction w.p. `≥ 1/2 − 6ε`); also the second moment bound of Thm 4.1. | Becchetti, Clementi, Manurangsi, Natale, Pasquale, Raghavendra, Trevisan, ESA 2018, Thms 3.1 (clustered regular graphs), 4.1 (whose proof needs a minor correction), Lemma 4.2 | `Averaging.Opportunistic.nonEphemeral_good`, `sign_phase`, `weakReconstruction_phase`, `secondMoment_bound`, `oppRun_getD` | AVG-3 |
