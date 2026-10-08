# Epidemics: Reed–Frost and bond percolation; subcritical percolation; small-world networks below the threshold; the giant component; the COBRA–BIPS duality; the Kermack–McKendrick SIR model; Kurtz's law of large numbers; rumor spreading revisited

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
([`SubcriticalExploration.lean`](Epidemics/SubcriticalExploration.lean)). The tail bound
([`SubcriticalChernoff.lean`](Epidemics/SubcriticalChernoff.lean)) is the Chernoff bound of
`dynamics/` (`Distribution.prob_ge_le_exp`) at the paper's tilt `ε`. Deviations from the paper
(explicit constants, the threshold written as `p (d - 1) ≤ 1 - ε`) are listed in
[FORMALIZATION_DIFFERENCES.md](FORMALIZATION_DIFFERENCES.md).

## The supercritical giant component (EPI-3)

The random graph `G(n, p)` is bond percolation on the complete graph (`perc ⊤ ω`, `ω ~ coins p`).
Following M. Krivelevich and B. Sudakov, *The phase transition in random graphs: a simple proof*
(Random Structures & Algorithms 43, 2013, arXiv:1201.6529), a depth-first search fed with the edge
coins gives, with `p n = 1 + ε` and "with high probability" made quantitative as "with probability
at least `1 - C / n`":

| Result | Lean declaration |
| --- | --- |
| Theorem 1(2): a path of length `≥ ε² n / 5`, for small `ε` | `exists_long_path` |
| Theorem 2: a component with `≥ ε n / 2` vertices, for small `ε` | `exists_giant_component` |
| Every `ε > 0`: a component with `≥ c n` vertices | `exists_linear_component` |
| Reed–Frost on `K_n`, `R₀ = 1 + ε`: outbreak `≥ ε n / 2` w.p. `≥ ε/2 - C/n` | `reedFrost_large_outbreak_explicit` |
| Reed–Frost on `K_n`, any `R₀ > 1`: outbreak `≥ c n` w.p. `≥ q > 0` | `reedFrost_large_outbreak` |

Reusable pieces: the principle of deferred decisions for adaptive queries to independent coins
(`prob_queryAnswers`, [`Epidemics/GiantCoins.lean`](Epidemics/GiantCoins.lean)); the search
itself and its invariant ([`Epidemics/GiantDFS.lean`](Epidemics/GiantDFS.lean)); the
deterministic analysis ([`Epidemics/GiantAnalysis.lean`](Epidemics/GiantAnalysis.lean)); Lemma 1(2)
with the Chernoff bounds of `dynamics/` ([`Epidemics/GiantProb.lean`](Epidemics/GiantProb.lean));
parametric versions of both theorems (`core_path`, `core_component`,
[`Epidemics/Giant.lean`](Epidemics/Giant.lean)); the epidemic reading
([`Epidemics/GiantEpidemic.lean`](Epidemics/GiantEpidemic.lean)). Deviations from the paper are
listed in [FORMALIZATION_DIFFERENCES.md](FORMALIZATION_DIFFERENCES.md).

## Small-world networks below the percolation threshold (EPI-6)

After L. Becchetti, A. Clementi, R. Denni, F. Pasquale, L. Trevisan, I. Ziccardi, *Percolation and
epidemic processes in one-dimensional small-world networks* (arXiv:2103.16398).
`SWG(n, q)` is the cycle `C_n` plus the edges of an Erdős–Rényi graph `G(n, q)` (`swg n b`,
`b ~ coins q`); `3-SWG(n)` is the cycle plus a uniformly random perfect matching (`swg3 n M`,
`M ~ uniformMatching n`). Probabilities are over the graph and the bond percolation `ω ~ coins p`
(equivalently, the Reed–Frost epidemic with transmission probability `p`). The critical value for
`SWG(n, c/n)` is `p* = (√(c² + 6c + 1) - c - 1) / (2c)` (`swgThreshold c`), the root of
`c p (1 + p) = 1 - p`; for `3-SWG(n)` it is `1/2`. "W.h.p." is made explicit as "with probability
at least `1 - C/n`" (results in [`Epidemics/SmallWorld.lean`](Epidemics/SmallWorld.lean) and
[`Epidemics/SmallWorldEpidemic.lean`](Epidemics/SmallWorldEpidemic.lean)):

| Result | Lean declaration |
| --- | --- |
| Theorem 2.1, claim 2: `SWG(n, c/n)`, `p < p* - ε`: all components have `O(log n)` nodes w.h.p. | `swg_subcritical` |
| Lemma C.1 with explicit constants: `≤ (64/δ²) log n` nodes with probability `≥ 1 - 2/n`, `δ = 1 - p₀ - c p₀ (1 + p₀)` | `swg_components_small` |
| Theorem 2.2, claim 2: `3-SWG(n)`, `p < 1/2 - ε`: all components have `O(log n)` nodes w.h.p. | `swg3_subcritical` |
| Theorem 2.4, claim 2: Reed–Frost on `SWG(n, c/n)` below `p*` stops within `O(log n)` rounds with `O(|I₀| log n)` recovered nodes w.h.p. | `swg_reedFrost_subcritical` |
| Theorem 2.5, claim 2 (threshold `1/2`): the same on `3-SWG(n)` | `swg3_reedFrost_subcritical` |
| The threshold: `c p* (1 + p*) = 1 - p*`, `p < p* ↔ c p (1 + p) < 1 - p`, `p* = √2 - 1` for `c = 1` | `swgThreshold_spec`, `lt_swgThreshold_iff`, `swgThreshold_one` |

The proof of Lemma C.1 first collapses the two independent coin families into one percolation of
the complete graph with independent coins, of probability `p` on cycle edges and `p c / n` on
the other pairs ([`SmallWorldCollapse.lean`](Epidemics/SmallWorldCollapse.lean)). A
breadth-first exploration of a cluster gives each node the weight `1` if it was discovered through
a cycle edge and `1 + p₀` otherwise, a left eigenvector of the two-type mean matrix behind the
paper's Galton–Watson comparison; below the threshold the expected discovered weight shrinks by a
factor `1 - δ/2` per processed node, so an exponential of the weight balance is a supermartingale
([`SmallWorldMart.lean`](Epidemics/SmallWorldMart.lean): products of factors along adaptive
observations of fresh independent coordinates, the principle of deferred decisions;
[`SmallWorldExplore.lean`](Epidemics/SmallWorldExplore.lean): the exploration and the tail bound
`Explore.prob_cluster_gt_le`). Markov's inequality and a union bound over the nodes conclude
([`SmallWorldSubcritical.lean`](Epidemics/SmallWorldSubcritical.lean)). Theorem 2.2, claim 2 is
EPI-2's Theorem 2.3 (`prob_components_small`) applied to the maximum degree `3` of `3-SWG(n)`,
and the Reed–Frost claims follow from the component bounds by EPI-2's deterministic lemmas.
The supercritical claims (claim 1 of Theorems 2.1, 2.2, 2.4 and 2.5) are not formalized yet.
Deviations from the paper are listed in [FORMALIZATION_DIFFERENCES.md](FORMALIZATION_DIFFERENCES.md).

## The Kermack–McKendrick SIR model (EPI-7)

The deterministic SIR epidemic (Kermack and McKendrick 1927), in the normalized form of Hethcote,
*The mathematics of infectious diseases*, SIAM Review 2000, system (2.2) and Theorem 2.1:
`s' = -β s i`, `i' = β s i - γ i`, `r' = γ i` with `β, γ > 0` and `R₀ = β / γ`. A solution on
`[0, ∞)` is taken as a hypothesis, `IsSolution β γ s i r`: `t ↦ (s t, i t, r t)` is an
`IsIntegralCurveOn` of `sirField β γ` on `Set.Ici 0`, with `s(0), i(0) > 0`, `r(0) = 0` and
`s(0) + i(0) + r(0) = 1`. Every result holds for every such solution (namespace
`Epidemics.KermackMcKendrick`; files `Epidemics/KermackMcKendrick*.lean`):

| Result | Lean declaration |
| --- | --- |
| `s + i + r = 1`; `s, i > 0`, `r ≥ 0` on `[0, ∞)` | `IsSolution.sum_eq_one`, `s_pos`, `i_pos`, `r_nonneg` |
| `s` strictly decreasing, `r` strictly increasing | `IsSolution.strictAntiOn_s`, `strictMonoOn_r` |
| First integral `s(t) = s(0) exp(-R₀ r(t))` | `IsSolution.s_eq_mul_exp` |
| `R₀ s(0) ≤ 1` ⇒ `i` strictly decreasing | `IsSolution.strictAntiOn_i` |
| `i` initially increases iff `R₀ s(0) > 1` | `IsSolution.initially_increasing_iff` |
| `i → 0`, `s → s∞`, `r → 1 - s∞` | `IsSolution.tendsto_i`, `exists_tendsto_s`, `tendsto_r` |
| Final size `s∞ = s(0) exp(-R₀ (1 - s∞))`, `0 < s∞ < 1/R₀` | `IsSolution.final_size`, `limit_pos`, `R₀_mul_limit_lt_one` |
| `s∞` is the unique root in `(0, 1/R₀]` and in `(0, 1]` | `IsSolution.final_size_unique`, `final_size_unique_of_le_one` |
| Peak at `s = 1/R₀`, `i_max = i₀ + s₀ - 1/R₀ - log(R₀ s₀)/R₀` | `IsSolution.exists_peak` |

Positivity of `i` uses a barrier argument (`i ≥ i(0) e^{-γ t} / 2`) instead of integrals or
Gronwall; uniqueness of the final size uses the monotonicity of `x ↦ log x - R₀ x` on either side
of `1/R₀`.

Where the statements deviate from their sources (special constant-rate case, solution taken as a
hypothesis, fixed initial data, the precise form of the limits and of the uniqueness statements),
see [FORMALIZATION_DIFFERENCES.md](FORMALIZATION_DIFFERENCES.md).

## Kurtz's law of large numbers for SIR, in discrete time (CRN-2)

The stochastic SIR epidemic on `N` agents (`S + I → 2I` at rate `β S I / N`, `I → R` at rate
`γ I`), uniformized at rate `(β + γ) N`: each step draws an ordered pair of agents with replacement
and one of `β + γ` equally likely clocks (`β` infection clocks, `γ` recovery clocks, so
`β, γ ∈ ℕ`); an infected `u` infects a susceptible `v`, or an infected `u` recovers. Step `k` is
compared with the Kermack–McKendrick solution at time `k / ((β + γ) N)`, in the sup distance on
`ℝ³`. Namespace `Epidemics.Kurtz`; files `Epidemics/Kurtz*.lean`.

| Result | Lean declaration |
| --- | --- |
| Drift identity: expected one-step change of `(S, I, R)/N` is `sirField β γ / ((β + γ) N)` | `drift_susceptible`, `drift_infected`, `drift_recovered` |
| Bounded increments: one step moves `(S, I, R)/N` by at most `1/N` | `dist_scaled_step_le` |
| The kernel `Kernel.ofStep` iterates as `expList` over i.i.d. rounds | `iterate_chain` |
| Maximal Azuma–Hoeffding: `P(∃ k ≤ n, M_k ≥ λ) ≤ exp(-λ²/(2 n c²))` | `expList_azuma` |
| LLN with exponential bound: `P(∃ k ≤ T(β+γ)N, dist > L·dist(initial points) + ε) ≤ C exp(-c ε² N)` | `law_of_large_numbers` |
| Convergence in probability, uniformly on `[0, T]`, to a fixed solution | `tendsto_deviationProb` |

The constants `C, c, L` depend only on `β, γ, T` (in the proof, `L = exp((2β + γ) T)` and
`c = 1 / (32 L² T (β + γ))`). The proof: the drift identity makes each coordinate of
`X_k - X_0 - h ∑_{j<k} F(X_j)` a martingale with increments at most `2/N`; Ville's maximal
inequality for the exponential supermartingale gives the maximal Azuma bound; on the good event,
the invariance of the simplex under the ODE, the Lipschitz bound of the field, the Euler error
`O(h²)` and Mathlib's `discrete_gronwall` keep the chain close to the solution. Deviations from
the sources (discrete time, natural-number rates, sampling with replacement, time scale, initial
condition, the integral-curve hypothesis) are listed in
[FORMALIZATION_DIFFERENCES.md](FORMALIZATION_DIFFERENCES.md).

## Randomized rumor spreading revisited (EPI-8)

Doerr and Kostrygin, *Randomized rumor spreading revisited*, ICALP 2017 (long version
arXiv:2303.11150), analyze any rumor-spreading process through two numbers per round: the
probability `p_k` that an uninformed node becomes informed in a round starting with `k` informed
nodes, and a bound `c_k` on the covariance of two such events. A process is a Markov kernel on the
set of informed nodes under which informed nodes stay informed (`RumorProcess`); `notYet m t S` is
the probability that fewer than `m` nodes are informed after `t` rounds from `S`, i.e. the tail
`P[T > t]` of the spreading time. Namespace `Epidemics.Revisited`; files `Epidemics/Revisited/`.

| Result | Paper | Lean declaration |
| --- | --- | --- |
| Variance of the number of informed nodes after one round | Lemma 9 | `variance_card_le` |
| Crossing a range where every uninformed node is informed w.p. `≥ p`: tail and expectation | Lemma 19 | `connect_tail`, `connect_expect` |
| Exponential growth regime: `f n` nodes informed after `log_{1+γ} n + O(1)` rounds, exponential tail | Theorem 21 (Theorem 1, upper bounds) | `growth_upper_tail`, `growth_upper_expect` |
| One round from `< f n` informed nodes overshoots `f' n` w.p. `O(1/n)` | Lemma 20 (its proof) | `overshoot_round` |
| Jumping over `[f n, f' n[` has probability `O(E[T(|S|, f n)] / n)` (corrected Lemma 20) | Lemma 20 | `jumpProb_le` |
| Exponential shrinking regime: from `≤ g n` uninformed nodes, all informed after `(1/ρ) ln n + O(1)` rounds, exponential tail | Theorem 31 (Theorem 2, upper bounds) | `shrinking_upper_tail`, `shrinking_upper_expect` |
| Total spreading time `log_{1+γ} n + (1/ρ) ln n + O(1)`, exponential tail | Theorems 21 and 31 with Lemma 19 | `spreading_upper_tail`, `spreading_upper_expect` |

**Lemma 20 of the paper is false as stated** (a process can stay below `f n` for many rounds,
with a chance to jump over `[f n, f' n]` in each); the one-round estimate of its proof and a
corrected path statement are formalized instead. The counterexample and the other deviations
(conditions for every state instead of homogeneity, arbitrary starting sets, a uniform side
condition in Definition 11, the composed total-time theorems) are listed in
[FORMALIZATION_DIFFERENCES.md](FORMALIZATION_DIFFERENCES.md). Theorem 31 is proved with a
quadratic potential instead of the paper's phase calculus.

## COBRA ⇔ BIPS duality (EPI-4)

After Cooper, Radzik and Rivera, *The coalescing-branching random walk on expanders and the dual
epidemic process*, PODC 2016 ([arXiv:1602.05768](https://arxiv.org/abs/1602.05768)), Theorem 4.

**Model.** In every round each vertex samples `k` uniform neighbours with replacement (a uniform
element of `Choices G k`). COBRA: every vertex of the current set pushes to its sampled neighbours,
and the next set is the set of chosen vertices. BIPS with persistent source `v`: `v` is always
infected, and any other vertex is infected next iff one of its sampled neighbours is infected now.

**Main results** (in [`Epidemics/CobraDuality.lean`](Epidemics/CobraDuality.lean)):

| Result | Lean declaration |
| --- | --- |
| Pathwise: COBRA from `C` visits `v` within the rounds iff BIPS from `{v}` along the reversed rounds infects a vertex of `C` | `cobra_hit_iff_bips_reverse` |
| Theorem 4: `P(Hit_C(v) > t ∣ C₀ = C) = P(C ∩ A_t = ∅ ∣ A₀ = {v})` | `cobra_bips_duality` |
| Equation (2): `P(Hit_u(v) > t) = P(u ∉ A_t ∣ A₀ = {v})` | `cobra_bips_duality_singleton` |

The paper assumes `G` connected and regular and `k ≥ 1`; the duality holds for every finite graph
and every `k`. On a connected graph with at least two vertices the rounds exist
(`choices_nonempty`), so both sides are genuine probabilities. The proof combines the pathwise
identity with time reversal of i.i.d. rounds, the core's `Dynamics.expList_comp_reverse` (FND-6).
Deviations from the paper are listed in [FORMALIZATION_DIFFERENCES.md](FORMALIZATION_DIFFERENCES.md).
The statements were pinned and then proved by a Claude agent under the fixed-statement protocol and
checks of the provenance note below.

**Provenance.** Reed–Frost: the statements were written and pinned by hand; the proofs were produced
by a Grok agent under a fixed-statement protocol and verified mechanically (statements unchanged, no
placeholders, warning-free build, axiom audit). Kermack–McKendrick: the statements were pinned and
then proved by a Claude agent under the same protocol and checks; the statements were reviewed by
hand against the source. Kurtz (CRN-2): the statements were pinned and then proved by a Claude agent
under the same protocol and checks; the statements were reviewed by hand against the source
(Wormald's Theorem 5.1). Rumor spreading revisited (EPI-8): the statements were pinned and then
proved under the same protocol and checks, the growth regime (Lemma 9, Lemma 19, Theorem 21) by a
Grok agent and the rest (Lemma 20, Theorem 31, total time) by a Claude agent. Supercritical giant
component (EPI-3): the statements were pinned and then proved by a Claude agent under the same
protocol and checks; the statements were reviewed by hand against the source. Subcritical
percolation (EPI-2): statements and proofs were written by a Claude agent under the same protocol
and checks; the statements were reviewed by hand against the paper. Small-world networks below
the threshold (EPI-6): the statements were pinned by a Claude agent and reviewed by a second
agent against the paper; the proofs are by a Claude agent under the fixed-statement protocol and
the same checks.

Build and audit:

```bash
lake exe cache get
lake build
python3 ../scripts/check_axioms.py
```

This package requires the sibling `dynamics/` package and shares its Lean 4.32.0 toolchain and exact
Mathlib pin. The [blueprint](blueprint/src/content.tex) maps the results to declarations.
