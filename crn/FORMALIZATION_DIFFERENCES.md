# Formalization differences

Where the statements of `crn/` deviate from their sources, and why.

## CRNs are population protocols (`Basic`, `Protocol`, `ApproximateMajority`, CRN-1)

Sources: Anderson and Kurtz, *Continuous time Markov chain models for chemical reaction networks*
(2011), for CRNs as continuous-time Markov chains; Gillespie (1977) and Doty, *Timing in chemical
reaction networks* (SODA 2014, §2), for the combinatorial mass-action propensity;
Angluin, Aspnes and Eisenstat (2008) and Cardelli and Csikász-Nagy (2012) for approximate
majority.

1. **Mass-action convention.** The propensity of `A + A → ⋯` is `k·C(#A, 2)` (Gillespie; Doty
   §2), not Anderson and Kurtz's `κ·#A(#A − 1)` (their `λₖ(x) = κₖ ∏ xᵢ!/(xᵢ − yᵢₖ)!`). With a
   common rate constant, the uniformly-random-pair protocol matches Gillespie's form only. With
   Anderson and Kurtz's form the correspondence holds when every `A + A` reaction has half the
   rate constant of the others, and fails otherwise (checked numerically).
2. **Only count-conserving bimolecular CRNs.** `Reaction` is `A + B → C + D` by construction
   (two unordered pairs, `Sym2`), rather than general stoichiometry restricted by a predicate. A
   network is a `Finset` of reactions (no duplicates), required to be nonempty (the empty
   network is trivial: both chains are constant) and nontrivial (no reaction whose products
   equal its reactants; such a reaction does not change the continuous-time chain, and excluding
   it makes `jumpKernel` the embedded jump chain, see `jumpKernel_weight_self`).
3. **Randomized protocol.** Besides a uniformly random ordered pair of distinct agents, the
   protocol draws a uniformly random reaction, and "the pair reacts" means that the pair's
   species are that reaction's reactants. Several reactions may share their reactants (the two
   `X + Y` reactions of approximate majority), and then a protocol whose transition depends only
   on the pair cannot match a common rate constant. For example, the protocol that fires a
   uniformly random *applicable* reaction for the drawn pair gives, for approximate majority from
   counts `(#X, #Y, #B) = (2, 1, 1)`, the probabilities `1/5, 1/5, 2/5, 1/5` for the four
   reactions, while the jump chain gives `2/7, 2/7, 2/7, 1/7`. The deterministic one-way
   approximate-majority protocol of Angluin, Aspnes and Eisenstat has the same count chain; it is
   formalized on interaction graphs for CRN-4 (`ApproxMajority.rule`, whose effective transitions
   are exactly the reactions of `network`), but its count chain is not compared with the jump
   chain.
4. **Observed on count vectors.** `ppStep` and `condStep` record the counts after an
   interaction, not the agents' new species: which agent receives which product does not matter
   for the counts and is not canonical for unordered reactions. `ppKernel` starts from a chosen
   configuration with the given counts; `condStep_eq_jumpKernel` shows that the choice does not
   matter (lumpability).
5. **Ordered pairs.** The protocol draws ordered pairs (initiator, responder); the pair-species
   probabilities (`pair_prob_of_ne`, `pair_prob_of_eq`) are those of unordered pairs.
6. **Jump chain only, terminal states absorbing.** Holding times of the continuous-time chain are
   not modelled. The jump chain is undefined at terminal states (zero total propensity), which
   are made absorbing here. `ppStep_expect` relates the unconditioned protocol, a lazy version of
   the jump chain, to the jump chain.
7. **Common rate constant only.** `k > 0` is a parameter of `jumpKernel` and the theorems hold
   for every `k`. Unequal rate constants (which would correspond to a weighted draw of the
   reaction) are not formalized.
8. **Conditioning lives in `crn/`.** `Crn.normalize` and `Crn.condition` (and the lemmas of
   `Crn/DistLemmas.lean`) are general operations on `Dynamics.Distribution` and are candidates to
   move to `dynamics/`.

## Semilinear predicates are stably computable (`Stable*`, CRN-3, easy direction)

Sources: Angluin, Aspnes, Diamadi, Fischer and Peralta, *Computation in networks of passively
mobile finite-state sensors*, Distributed Computing 18 (2006) [AADFP06], §3 (model) and §4
(Lemma 3 and Corollary 2: Boolean closure; Lemma 5: threshold and remainder predicates, Lemma 11
in the authors' 2005 journal manuscript;
Theorem 5: Presburger-definable predicates); Angluin, Aspnes, Eisenstat and Ruppert (2007)
[AAER07] for the reachability form of stable computation; Chen, Doty and Soloveichik,
*Deterministic function computation with chemical reaction networks*, Natural Computing 13 (2014)
[CDS14], §§2.1–2.2, for chemical reaction deciders, with the "every species votes" convention of
Angluin, Aspnes and Eisenstat (PODC 2006) [AAE06].

1. **Stable computation in reachability form**, not with fair executions [AADFP06, §3.2]: every
   configuration reachable from the initial one can reach an output-stable configuration with the
   right output (the form of [AAER07] and [CDS14, §2.2]). For finite populations the two are
   equivalent (by AADFP06 Lemma 1, the configurations occurring infinitely often in a fair
   execution form a final strongly connected component); this equivalence is not formalized.
2. **Populations of every size `n ≥ 1`, and a minor correction to AADFP06 Lemma 5 for `n = 1`.** AADFP06 do
   not state a lower bound on the population size, but the protocols of their Lemma 5 start every
   agent with output bit `0` (input map `σᵢ ↦ (1, 0, aᵢ)`). With a single agent no encounter ever
   happens: under AADFP06's definitions this case is degenerate (no interaction, hence no
   computation), and under the natural convention that a lone agent keeps its state, the output
   stays `0` even when the predicate holds (for example `a = (1)`, `c = 3`,
   one agent: `1 < 3` holds but the output is `0`); the protocols are correct for `n ≥ 2`. The
   theorems here are existential in the protocol, so this is harmless: the protocols used here
   start an agent with input `i` with output bit equal to the single-agent value (`[aᵢ < c]`,
   resp. `[aᵢ ≡ c (mod m)]`). The empty population `n = 0` is excluded, as usual (no agent, no
   output).
3. **Scope.** Predicates only (output alphabet `Bool`, all-agents predicate output convention),
   standard populations (complete interaction graph on `Fin n`), symbol-count input convention.
   Not covered: general interaction graphs (stable computation on graphs is defined for CRN-4,
   below, and used there for majority only), input-output relations and functions, other output
   conventions (AADFP06 Theorem 2), the integer-based input convention (Corollary 3).
4. **Threshold direction.** AADFP06 Lemma 5(1) is `∑ aᵢ xᵢ < c` (`stablyComputable_threshold`,
   and the atom of `IsSemilinearPred`); the form `∑ aᵢ xᵢ ≥ c` is its negation, stated separately
   as `stablyComputable_le_sum`.
5. **Remainder modulus `0 < m`** instead of AADFP06's `m ≥ 2` (a slight strengthening: `m = 1`
   gives the constant `true`), the natural hypothesis for `Int.ModEq`.
6. **Theorem 5 for an inductive class.** AADFP06 Theorem 5 concerns Presburger-definable
   predicates; its proof reduces them, by Presburger's quantifier elimination (their Theorem 4,
   cited without proof), to Boolean combinations of threshold, equality and remainder predicates.
   Here `IsSemilinearPred` is defined as the Boolean combinations of threshold and remainder
   predicates (equalities are conjunctions of two thresholds, as in the paper's proof). That this
   class equals the semilinear (Presburger-definable) predicates is not proved; instead,
   `IsSemilinearPred.isSemilinearSet` proves the inclusion into Mathlib's `IsSemilinearSet`
   (Mathlib proves `presburger.definable_iff_isSemilinearSet`), which shows that the class is
   not too large. The converse inclusion is Presburger's quantifier elimination.
7. **Agent-level configurations** (`Fin n → Q`, as AADFP06's `C : A → Q` and the configurations of
   CRN-1), not multisets. Count vectors enter through `counts`, in the predicate and in the
   transfer, where `Protocol.exists_network` shows that the induced dynamics on count vectors is
   that of a CRN.
8. **Transfer hypothesis.** CRN-1's networks are nonempty and have no reaction whose products
   equal its reactants, so `Protocol.exists_network` assumes a transition that changes the
   multiset of states of the two agents (otherwise the counts never change and there is no such
   network). It holds for every protocol (stable computation plays no role), with the reaction set
   characterized exactly. `StablyComputable.exists_network` provides such a transition by tagging
   the input states, which also makes the input map injective.
9. **Stable decision by CRNs.** `Network.StablyComputes` is the chemical reaction decider of
   [CDS14, §2.2] with every species voting (the convention of [AAE06]), no initial context
   (leaderless) and input species given by an injective map `X ↪ S`; the zero input is excluded
   (with no molecule the output is undefined in [CDS14]).
10. **Sanity check of the definition.** `Protocol.StablyComputes.unique` shows that stable
    computation determines the predicate on nonzero inputs, so the definition is not vacuous.

## Majority on graphs with very small local memory (`GraphMajority*`, CRN-4)

Sources: G. B. Mertzios, S. E. Nikoletseas, C. L. Raptopoulos, P. G. Spirakis, *Determining
majority in networks with local interactions and very small local memory*, ICALP 2014,
arXiv:1404.7671 (we use the numbering of the arXiv version) [MNRS14]; journal version in
Distributed Computing 30 (2017). The 3-state protocol is that of D. Angluin, J. Aspnes,
D. Eisenstat, *A simple population protocol for fast robust approximate majority*, Distributed
Computing 21 (2008) [AAE08].

### The statements

| File | Content |
| --- | --- |
| `Crn/GraphMajorityBasic.lean` | protocols on an interaction graph, stable computation on graphs, majority |
| `Crn/GraphMajorityAmbassador.lean` | the 4-state ambassador protocol, [MNRS14, Theorem 2] |
| `Crn/GraphMajorityLowerBound.lean` | at least 4 states are needed, [MNRS14, Theorem 1] |
| `Crn/GraphMajorityRandom.lean` | the 3-state protocol of [AAE08] on a graph, [MNRS14, Theorem 4] |

**Graph setting** (`GraphMajorityBasic`).

* `dartPair d`: the (initiator, responder) pair of an oriented edge `d : G.Dart`.
* `GraphStep P G`, `GraphReaches`, `GraphOutputStable`: one encounter along an oriented edge of
  `G : SimpleGraph (Fin n)` (via the existing `Protocol.interact`), reachability, and output
  stability on `G` ([MNRS14, §2 and §2.2, "directly reachable"]).
* `StablyComputesOnGraph P G D φ`: for every input whose count vector lies in the domain `D`,
  every configuration reachable on `G` from the initial configuration can reach an output-stable
  configuration with output `φ`. Same reachability form as `Protocol.StablyComputes` (CRN-3),
  with a domain because majority is a partial function ([MNRS14, §2]).
  `GraphStablyComputes P D φ`: the above for every connected graph on `Fin n`, for every `n`.
* `majority x = decide (x false < x true)` (`true` is the paper's red `r`, `false` its green
  `g`) and `HasMajority x : x true ≠ x false` (no tie).
* On the complete graph `⊤` these are the notions of CRN-3: `graphStep_top`,
  `graphReaches_top`, `graphOutputStable_top`, and `stablyComputesOnGraph_top_iff` (stable
  computation on the complete graphs of all nonempty populations with the trivial domain is
  exactly `Protocol.StablyComputes`); `GraphStablyComputes.stablyComputes`,
  `GraphStablyComputes.top`.
* `GraphReaches.extend`: reachability transfers along an injective, edge-preserving embedding of
  populations, the other agents being frozen (the step "ignoring agents `v` and `u`" of the proof
  of Theorem 1).

**(a) The ambassador protocol, [MNRS14, Theorem 2]** (`GraphMajorityAmbassador`).

* `ambassador : Protocol Bool AmbState` with `AmbState = Bool × Bool` (color, ambassador),
  `card_ambState` (4 states), `ambassador_table` and `ambassador_table_rest` (the table of
  Figure 1, all 16 entries), `ambassador_symm` (the protocol is symmetric).
* `ambCount b c`: the number of ambassadors of color `b`. Invariants: `ambCount_input` (it starts
  at the input counts), `ambCount_interact_le` (it never increases), `ambCount_sub_interact` (the
  difference red minus green never changes).
* `exists_reaches_annihilate`: on a connected graph, while both colors have ambassadors, one
  ambassador of each color can be annihilated (the step `𝒞_{k,ℓ} → 𝒞_{k−1,ℓ−1}`).
* `exists_reaches_allColor`: on a connected graph, if all ambassadors have color `b` and there is
  one, the all-`b` coloring is reachable; `graphOutputStable_of_allColor`: an all-`b` coloring is
  output-stable.
* **`ambassador_graphStablyComputes`**: the ambassador protocol stably computes majority on every
  connected graph, for every input with a majority; `ambassador_stablyComputesOnGraph_top` on
  complete graphs.
* `ambassador_tie_stuck`: with one red and one green agent, a configuration is reachable from
  which no output-stable configuration is reachable (why the tie is excluded).

**(b) The lower bound, [MNRS14, Theorem 1]** (`GraphMajorityLowerBound`).

* **`not_stablyComputesOnGraph_top_majority`**: no protocol with at most 3 states (any
  `Fintype Q` with `card Q ≤ 3`) stably computes majority, ties excluded, on the complete graphs of
  all nonempty populations.
* `not_graphStablyComputes_majority`: the same on all connected graphs, the paper's
  `R(𝒫_majority) > 3`; `rank_majority_eq_four`: with Theorem 2, the minimal number of states is 4.

**(c) The protocol of [AAE08] on a graph, [MNRS14, Theorem 4]** (`GraphMajorityRandom`,
namespace `Crn.ApproxMajority`).

* `rule`: the one-way rule of [MNRS14, eq. (1)] on the species `X`, `Y`, `B` of CRN-1, and
  `protocol` the corresponding population protocol. `rule_mem_network` and
  `exists_rule_of_mem_network`: the effective transitions of `rule` are exactly the four
  reactions of the CRN-1 network `ApproxMajority.network`.
* `graphStep G c d`, `graphKernel G = Kernel.ofStep (graphStep G)` over `EdgeRound G = G.Dart`:
  the probabilistic scheduler (a uniform edge with a uniform orientation).
* `Unanimous s c`, `placement S` (`Y` on `S`, `X` elsewhere), `winProb G m s t` (the probability,
  over a uniform `m`-subset `S` and the scheduler, that every agent is `s` at time `t`), and
  `absorbProb G m s = ⨆ t, winProb G m s t`.
* Coupling: `rank` (the order `Y < B < X`), `rule_mono`, `graphStep_mono`, and
  `event_allX_mono` (the probability of all `X` at time `t` is monotone in the initial
  configuration). Symmetry: `swap`, `rule_swap`, `graphStep_swap`, `event_swap`.
* `prob_unanimous_of_unanimous`, `winProb_monotone`, `winProb_mem_Icc`, `tendsto_winProb`.
* `exists_injective_of_regular`: [MNRS14, Corollary 1] (systems of distinct representatives for
  regular families, from Hall's theorem); `exists_injective_subset`: the instance used in the
  proof (an injective choice of an `(n − m)`-subset `A_S ⊆ S` of every `m`-set `S`).
* **`winProb_minority_le_majority`**: on every graph with an edge, if `n ≤ 2m`, at every time `t`
  the probability that the minority has won is at most the probability that the majority has
  won; the limit form `absorbProb_minority_le_majority`.
* `tendsto_event_unanimous`: on a connected graph, from every configuration with a non-blank
  agent, the protocol is absorbed in all-`X` or all-`Y` with probability tending to 1.
* **`half_le_absorbProb_majority`**: on a connected graph, if `n ≤ 2m` and `m ≤ n`, the
  probability of converging to the majority is at least `1/2` (the theorem as stated).

| [MNRS14] | Lean |
| --- | --- |
| §2, model; "directly reachable" (§2.2) | `GraphStep`, `GraphReaches`, `GraphOutputStable`, `dartPair` |
| §2, stably computes (partial function) | `StablyComputesOnGraph`, `GraphStablyComputes` |
| §2.1, eq. (1) | `ApproxMajority.rule`, `ApproxMajority.protocol` |
| Definition 1 and Theorem 1 | `not_stablyComputesOnGraph_top_majority`, `not_graphStablyComputes_majority`, `rank_majority_eq_four` |
| §4, Figure 1 | `ambassadorδ`, `ambassador`, `ambassador_table`, `ambassador_table_rest`, `ambassador_symm` |
| Theorem 2 (and its proof's invariant and steps) | `ambassador_graphStablyComputes`; `ambCount_*`, `exists_reaches_annihilate`, `exists_reaches_allColor`, `graphOutputStable_of_allColor` |
| Corollary 1 | `exists_injective_of_regular`, `exists_injective_subset` |
| Theorem 4, eqs. (18) to (23) | `winProb`, `absorbProb`, `event_allX_mono` (eq. (19)), `event_swap` (eq. (20)), `winProb_minority_le_majority`, `absorbProb_minority_le_majority`, `half_le_absorbProb_majority` |

### Differences in the statements

1. **Undirected graphs only.** The paper allows directed or undirected graphs (Theorem 2:
   "(un)directed"; Theorem 4: strongly connected directed graphs). We use `SimpleGraph (Fin n)`,
   where an interaction is an oriented edge (`G.Dart`) and the probabilistic scheduler draws a
   uniform oriented edge, which is the paper's scheduler on undirected graphs. Directed graphs are
   not covered.
2. **Stable computation in reachability form.** The paper defines stable computation through fair
   schedulers; we use the reachability form of `Protocol.StablyComputes` (see the CRN-3 section,
   item 1), generalized to graphs, with a domain `D` for partial predicates. Agreement with the
   existing notion on the complete graph is proved (`stablyComputesOnGraph_top_iff`).
3. **The tie case** is excluded from the domain (`HasMajority`), exactly as in Theorem 2 ("if there
   exists initially a majority"); `ambassador_tie_stuck` shows that no output convention could
   include it.
4. **Theorem 1 in a stronger form.** The paper's proof only uses complete graphs, so the
   impossibility is stated on complete graphs (the standard populations of CRN-3); the statement on
   all connected graphs follows. The proof works with `|V| = 3` (the paper takes `|V| = 2k + 1`,
   `k ≥ 2`). The protocol may have any finite state type with at most 3 elements and any input map
   (the paper assumes the two input states distinct, which is the only non-trivial case).
5. **Theorem 4 in finite time.** Convergence is formalized in the finite probability layer:
   `winProb G m s t` is the probability that the configuration at time `t` is unanimous `s`;
   unanimity is absorbing, so it is nondecreasing and its supremum (the limit) `absorbProb` is the
   convergence probability, as for `Dynamics.Kernel.iSup_event_of_invariant`. The main inequality
   is stated at every finite time (stronger than the limit) and on every graph with an edge (the
   paper assumes strong connectivity). The paper's "probability at least `1/2`" needs convergence
   with probability 1, which is stated separately (`tendsto_event_unanimous`,
   `half_le_absorbProb_majority`) on connected graphs.
6. **The rule of [AAE08].** Eq. (1) of the paper does not list the case of a blank initiator and a
   non-blank responder; as in [AAE08] it leaves both states unchanged. The CRN-1 model
   `ApproxMajority.network` draws a uniform reaction and is observed on counts, so it cannot be
   run on a graph agentwise; we use the one-way rule on its species and prove that its effective
   transitions are exactly the reactions of `network`.
7. **Placement.** The random initial placement is a uniform `m`-subset `S` of agents of the
   majority type `Y` (the paper's eq. (18)), with `X` on the complement; `Y` plays the paper's
   green majority `g` and `X` its red minority `r`.

### Corrections to the source

* **Theorem 1** needs a minor correction in its proof: "agents `v` and `u` remain of type `r`"
  should read type `g`, and "`|G_1| = k − 1`" for `C_2` should read `|G_2| = k − 1`.
* **Theorem 2** needs a minor correction in its proof: "for every configuration in `𝒞_{k,ℓ}` there
  exists a chain of transitions that lead to `𝒞_{k−1,ℓ−1}`" does not address ambassadors blocking
  each other (an ambassador cannot move onto a vertex holding an ambassador of the same color).
  Choosing a closest pair of ambassadors of opposite colors fixes this (see the proof route
  below).
* **Theorem 4** needs a minor correction in its proof: the monotonicity claim "increasing the
  initial number of agents of type `r` increases the probability that agents of type `r` win" is
  stated without proof (it holds by the monotone coupling below, the rule being monotone for
  `g < b < r`), and the conclusion "with probability at least `1/2`" additionally needs absorption
  with probability 1, which is not argued (it holds on connected graphs,
  `tendsto_event_unanimous`).

### Proof route

* **`GraphReaches.extend`**: induction on `ReflTransGen`; a step along `d` is simulated by the dart
  `(f d.fst, f d.snd)` of `G'`; on the range of `f` both sides agree by injectivity, off the range
  both are frozen.
* **Theorem 2.** Counting through `ambInd` and `ambCount_interact_add` with the table facts (by
  `decide` over the 16 pairs) gives the invariants. `exists_reaches_annihilate_of_dist`: strong
  induction on the distance from a red ambassador `u` to a green ambassador `w`; the red
  ambassador walks along a shortest path, moving onto free vertices and handing over to red
  ambassadors it meets, until it meets a green one. `exists_reaches_spread_of_dist` (strong
  induction on the distance from a `b`-ambassador to a vertex of color `!b`) reaches a
  configuration with strictly fewer `!b`-colored vertices, and `exists_reaches_allColor` iterates
  it. Iterated annihilation (`𝒞_{k,ℓ} → 𝒞_{k−ℓ,0}`) and the invariant give
  `ambassador_graphStablyComputes`. Configurations without ambassadors are frozen
  (`graphReaches_eq_of_noAmb`), which gives `ambassador_tie_stuck`.
* **Theorem 1.** One agent has no partner, so both outputs occur on `Fin 1`. If `q₁` is the only
  state with output `b`, the inputs `(b, b, !b)` and `(b, b, b)` on `Fin 3` reach "all `q₁`", and
  embedding them into `Fin 5` with two extra `!b` agents (`GraphReaches.extend` along
  `Fin.castLE`) gives a common configuration reachable from inputs with majorities `!b` and `b`
  (`not_stablyComputesOnGraph_top_majority_of_unique`, once for both colors). The main theorem
  counts the two output classes of `Q`.
* **Theorem 4.** Coupling and symmetry: `iterate_graphKernel_mono` (monotone observables stay
  monotone at every time) and `iterate_graphKernel_swap`. Hall: `exists_injective_of_regular` by
  `Finset.all_card_le_biUnion_card_iff_exists_injective` and double counting;
  `exists_injective_subset` applies it to `T S = {A ⊆ S, #A = n − m}` with `r = d = C(m, n − m)`.
  `winProb_minority_le_majority` follows eqs. (18) to (23), with `τ S = (σ S)ᶜ` a bijection of the
  `m`-sets, so the final inequality (23) is an equality. Absorption (section `Absorption`): an
  initiator `s ≠ B` activated twice on the same responder makes it `s`, so an opinion present
  spreads to all agents along boundary darts (`graphReaches_const`, using
  `SimpleGraph.Walk.exists_boundary_dart`); `tendsto_event_unanimous` follows by
  `Kernel.finite_absorption` on the indicator of "not unanimous", and
  `half_le_absorbProb_majority` from the limits and `absorbProb_minority_le_majority`.

### Numerical checks of the statements

* Theorem 1: an exhaustive search over all protocols with at most 3 states (all `9^9` transition
  tables and both output maps; on one agent the two input states must differ, so they are fixed up
  to renaming) finds 650 tables per output map that stably compute majority on the complete graph
  of 3 agents and none that also does so on 5 agents, as in the proof route (populations of 1, 3
  and 5 agents).
* Theorem 2: reachability-form stable computation of the ambassador protocol on all connected
  graphs with at most 4 vertices and all non-tie inputs.
* Theorem 4: the finite-time inequality on paths, stars, cycles and lollipops (exact rational
  arithmetic, `t ≤ 25`, including a graph with an isolated vertex); exact absorption probabilities
  (linear solve) on paths, stars, cycles, complete graphs and a lollipop with at most 6 vertices:
  the convergence probabilities to the majority and to the minority sum to 1, the former is at
  least `1/2`, with equality exactly at ties; from every configuration with a non-blank agent,
  all-blank is unreachable and all-`s` is reachable for every opinion `s` present.

### Not covered

* Theorem 3: expected convergence time `O(n⁶)` on any connected graph and
  `O(n² log n / |k − ℓ|)` on the clique, under the probabilistic scheduler (meeting and cover
  times of random walks).
* Lemmas 1 and 2 (birth-death absorption probabilities and times; partly covered by
  `Dynamics.Kernel.iSup_event_of_invariant`).
* Theorem 5 (robustness on the clique: failure probability `e^{−Θ(n)}` for a minority below
  `n/7`), Lemmas 3 to 5, and Lemma 6 (the path `L_m`, absorption probability `1/(2(m − 1))`,
  checked numerically for `m ≤ 6`).
* The failure families: Theorem 6 (lollipop graphs, where the protocol of [AAE08] converges to the
  minority with high probability although the majority is `n − Θ(log n)`) and Theorem 7 (two
  cliques joined by an edge, expected exponential convergence time), with Lemmas 7 to 11.
* Directed interaction graphs and Observation 1.

## Deterministic exact majority and plurality (`ExactMajority*`, CRN-5)

Source: L. Gąsieniec, D. Hamilton, R. Martin, P. G. Spirakis, G. Stachowiak, *Deterministic
population protocols for exact majority and plurality*, OPODIS 2016, LIPIcs 70, paper 14,
doi:10.4230/LIPIcs.OPODIS.2016.14 [GHMSS16]. No longer version with more detailed proofs was
found; the conference version is the reference.

### The statements

| File | Content |
| --- | --- |
| `Crn/ExactMajorityOutput.lean` | stable computation with outputs in any type, and marking (`StablyMarks`) |
| `Crn/ExactMajorityStatic.lean` | Section 2: the static protocol `P₁`, Lemmas 1 and 2, Theorem 3 |
| `Crn/ExactMajorityDynamic.lean` | Section 3: the dynamic protocol `P₂`, its invariants, Lemmas 4 and 5, stabilization |
| `Crn/ExactMajorityCompose.lean` | the composition step: `P₂` driven by another protocol (`Protocol.drive`) |
| `Crn/ExactMajorityAbsolute.lean` | Section 4: Absolute-Majority, Theorem 6 |
| `Crn/ExactMajorityRelative.lean` | Section 5.1: Relative-Majority, Theorem 7 |

Notation: colours are `k`-bit labels `L : Fin k → Bool` (`Label k`), bits read as `±1`
(`bitSign`); `x : Label k → ℕ` is the input count vector; the scheduler is fair, in the
reachability form of `StableBasic.lean` (CRN-3). `StablyMarks P O g`: for every nonempty population,
from every configuration reachable from the initial one, a configuration is reachable from which
every agent `v` forever outputs `O(state) = g x (ι v)` (`ι v` its input); `StablyComputesWith P O f`
is the case `g x _ = f x`.

**Outputs** (`ExactMajorityOutput`).

* `Protocol.OutputStableAt`, `Protocol.StablyMarks`, `Protocol.StablyComputesWith`: stable
  computation with outputs in any type `Y`, read through a map `O : Q → Y`, and possibly depending
  on the agent's own input.
* `stablyComputesWith_output_iff`: with the protocol's own `Bool` output, `StablyComputesWith` is
  CRN-3's `StablyComputes`.

**The static protocol, [GHMSS16, Section 2]** (`ExactMajorityStatic`).

* `StaticState`, `StaticState.δ`, `staticMajority`: the 6-state protocol `P₁` (Figs. 1 and 2),
  `card_staticState`.
* `StaticState.weight_sum_eq` (Lemma 1): the weight sum equals the colour sum along every
  execution.
* `StaticState.absWeight_sum_step_le`, `StaticState.exists_reaches_absWeight_sum_eq` (Lemma 2):
  `R = ∑ |w|` does not increase, and `R = |∑ colours|` is reachable.
* **`staticMajority_stablyComputes`** (Theorem 3): `P₁` stably computes `sign(#1 − #(−1))`, with
  output `0` for a tie.

**The dynamic protocol, [GHMSS16, Section 3]** (`ExactMajorityDynamic`).

* `DynState`, `DynState.δ`, `DynState.recolour`, `dynamicMajority`: the 8-state protocol `P₂`
  (Figs. 3 and 4) and the state change forced by a colour change, `card_dynState`.
* `Protocol.GStep`, `Protocol.GReaches`: steps between agents of the same group (for Section 5).
* `DynInv`: per group, the colour sum equals the weight sum (Invariant 1); `|w − c| ≤ 1`
  (Invariant 2); every group contains a strong state (a third invariant, see the corrections).
  `DynInv.input`: the initial configuration `[c_a]` satisfies it.
* `DynInv.gstep`, `DynInv.recolour` (Lemma 4): interactions inside groups and colour changes with
  `recolour` preserve `DynInv`.
* `DynState.absWeight_sum_gstep_le`, `DynState.exists_greaches_noOpposite` (Lemma 5): `R` does not
  increase, and a configuration without opposite weights in a group is reachable.
* `DynInv.exists_stable` (the conclusion of Section 3): from `DynInv`, a configuration is reachable
  from which every agent forever outputs the sign of its group's colour sum.
* **`dynamicMajority_stabilizes`**: after any finite interleaving of interactions and colour
  changes (`DynExtStep`), `P₂` stabilizes on the sign of the final colour sum;
  `dynamicMajority_stablyComputes`: without the external force, `P₂` stably computes
  `sign(#1 − #(−1))`.

**Composition, [GHMSS16, Sections 4 and 5]** (`ExactMajorityCompose`).

* `Protocol.drive D col grp`: `P₂` driven by a protocol `D` through colours `col : Q → SignType`,
  inside groups `grp`, with the recolouring in the same encounter.
* `Protocol.drive_dynInv` (Lemma 4 for the composition): along every execution of `D.drive`,
  `DynInv` holds for the derived colours.
* **`Protocol.drive_stablyMarks`**: if `D` stably marks the agents with their eventual colours,
  `D.drive` stably marks them with the sign of their group's eventual colour sum.

**Absolute majority, [GHMSS16, Section 4]** (`ExactMajorityAbsolute`).

* `bitsProtocol`, `majBit`, `bitsProtocol_stablyMarks`: `k` copies of `P₁` on the bits stably
  compute the `k` majority bits (memory (1) and (2) of Section 4).
* `absColour`, `absoluteMajority`, `absOutput` (Algorithm Absolute-Majority, Section 4.1) and the
  specification `IsAbsMajority`, `absMajority`, `absTarget`; `absMajority_eq_some_iff`:
  `absMajority x = some L ↔ 2·x_L > n`.
* `absTarget_sum_sign_eq_one_iff`, `majBit_eq_of_isAbsMajority`: the combinatorial part of the
  proof of Theorem 6.
* **`absoluteMajority_stablyComputes`** (Theorem 6): all agents eventually and forever output
  `some L` (`L` held by more than half of the agents) or `none` if there is no such colour.
* `card_absState` (Theorem 6, space): `2^k · 6^k · 8 ≤ 2^(4k+3)` states.

**Relative majority (plurality), [GHMSS16, Section 5.1]** (`ExactMajorityRelative`).

* `RelState`, `RelState.label`, `RelState.won`, `stageColour`, `relativeMajorityLevel`,
  `relativeMajority`: Algorithm Relative-Majority as `k` nested `drive`s.
* `IsGroupWinner`, `IsPlurality`, `duelColour`, `wins`, `bitAt`, `prefixMask`: the specification
  (the most frequent colour, ties to the lexicographically largest label).
* `duel_wins_iff` (one stage of the proof of Theorem 7): the stage-`i` duel selects the winner of
  the prefix group; `isGroupWinner_zero_iff`: the winner of the whole population is the plurality
  colour.
* `relativeMajority_level_stablyMarks` (the induction of the proof of Theorem 7): level `m ≤ k`
  stably marks each agent with whether it wins its group of prefix length `k − m`.
* **`relativeMajority_stablyMarks`** (Theorem 7, as formalized): eventually and forever, every
  agent outputs whether its own colour is the plurality colour. The agents learn whether they hold
  the winning colour, not the winner's label (difference 6 below).
* `card_relState_level`, `card_relState` (Theorem 7, space): `2^k · 8^k = 2^(4k)` states.

| [GHMSS16] | Lean |
| --- | --- |
| Section 1, model (stable computation, outputs) | `Protocol.StablyMarks`, `Protocol.StablyComputesWith`, `stablyComputesWith_output_iff` |
| Section 2, Figs. 1 and 2 | `StaticState`, `StaticState.δ`, `staticMajority` |
| Lemma 1 | `StaticState.weight_sum_eq` |
| Lemma 2 | `StaticState.absWeight_sum_step_le`, `StaticState.exists_reaches_absWeight_sum_eq` |
| Theorem 3 | `staticMajority_stablyComputes` |
| Section 3, Figs. 3 and 4 | `DynState`, `DynState.δ`, `DynState.recolour`, `dynamicMajority` |
| Section 3, invariants 1 and 2 | `DynInv`, `DynInv.input` |
| Lemma 4 | `DynInv.gstep`, `DynInv.recolour`, `Protocol.drive_dynInv` |
| Lemma 5 | `DynState.absWeight_sum_gstep_le`, `DynState.exists_greaches_noOpposite` |
| Section 3, after Lemma 5 | `DynInv.exists_stable`, `dynamicMajority_stabilizes`, `dynamicMajority_stablyComputes` |
| Sections 4 and 5, composition | `Protocol.drive`, `Protocol.drive_stablyMarks` |
| Section 4.1, Algorithm Absolute-Majority | `bitsProtocol`, `absColour`, `absoluteMajority`, `absOutput` |
| Theorem 6 | `absoluteMajority_stablyComputes`, `card_absState` |
| Section 5.1, Algorithm Relative-Majority | `RelState`, `stageColour`, `relativeMajorityLevel`, `relativeMajority` |
| Theorem 7 | `duel_wins_iff`, `relativeMajority_level_stablyMarks`, `relativeMajority_stablyMarks`, `card_relState` |

### Differences in the statements

1. **Outputs.** CRN-3's `StablyComputes` has `Bool` outputs, read through the protocol's `output`
   field. Theorem 3 outputs a sign, Theorem 6 a colour or none, and the protocol of Theorem 7
   *marks* the agents (each agent learns whether its own colour wins). `StablyMarks` reads the
   outputs through a separate map and allows targets depending on the agent's input; for the
   `Bool` output it is `StablyComputes` (`stablyComputesWith_output_iff`). The transitions and
   reachability are CRN-3's.
2. **Colours.** The `C ≤ 2^k` colours are the `k`-bit labels (`Label k`); a population with fewer
   colours leaves some labels unused (count `0`). The paper's `±1` reading of bits is `bitSign`.
3. **Dynamic inputs.** The external force of Section 3 is modelled without changing the protocol
   framework: since the interaction table of `P₂` does not read the colours, the colours are a
   separate assignment `col` linked to the states by the invariants (`DynInv`); a colour change is a
   separate step (`DynExtStep`), and `dynamicMajority_stabilizes` covers every finite interleaving
   of interactions and changes. In the compositions the force is internal: the colour is a
   function of the driver's state, and the recolouring happens in the encounter that changes it
   (`Protocol.drive`), as the paper assumes that a colour does not change during an interaction of
   `P₂`. The hypothesis `0 < n` of `dynamicMajority_stabilizes` is not used (the statement is
   trivial for the empty population).
4. **Absolute-Majority.** The colour of an agent for `P₂` is `1` iff every copy `P₁(i)` currently
   reports the agent's own bit `l[i]` (the paper: "the contents of `s[i]` and `l[i]` reflect the
   initial setting"); a reported tie (`0`) counts as inconsistent. The output is `some L*` (the
   reported majority bits) if `P₂` reports `1`, and `none` otherwise; a colour held by exactly half
   of the agents is not an absolute majority (`P₂` then reports a tie).
5. **Relative-Majority.** The colours `c[i]` are derived from the label and the states of the
   stages `> i` instead of being stored, so that a change propagates to all lower stages within the
   same encounter (Stabilisation Stage 2). This saves the `k` bits of `c`: `2^k · 8^k = 2^(4k)`
   states. The protocol is the `k`-fold iteration of `Protocol.drive` (level `m` holds the stages
   `k − 1, …, k − m`), so that the proof of Theorem 7 is an induction on levels, each step being the
   composition theorem plus the duel lemma. Stage `k − 1` uses `P₂` with constant colours (the paper
   writes `P₁(k − 1)` in Stabilisation Stage 1 and `P₂(k − 1)` in the proof; both work). Ties are
   broken in favour of the lexicographically largest label, bit `0` first and `−1 < 1`: this is the
   paper's own specification (Section 5: "the colour with the latest in the lexicographical order
   label") and what its protocol does (Stabilisation Stage 2: on a tie the agents with `c[i] = 1`
   win); only the reading of `l[0]` as the most significant bit is implicit in the paper.
6. **What Theorem 7 delivers.** Theorem 7 is formalized in the sense of Section 5: the protocol of
   Section 5.1 *marks* the agents of the winning colour, i.e. eventually and forever every agent
   outputs whether its own colour is the winner (the most frequent colour, the lexicographically
   largest among several). It is not plurality consensus in the sense of all agents outputting the
   winner's label: Section 1.2's "all nodes learn about the most frequent colour with the largest
   label" needs an additional dissemination layer, which the paper does not give and which is not
   formalized. Section 1.2's "all most frequent colours eventually become aware of their dominance"
   is not what Section 5.1 does either: among several most frequent colours only the
   lexicographically largest is marked, the others lose a tie at some stage.
7. **Space.** The paper claims `O(k)` bits; the formal bounds are exact state counts:
   `2^k · 6^k · 8 ≤ 2^(4k+3)` (Absolute-Majority, `card_absState`) and `2^(4k)`
   (Relative-Majority, `card_relState`).

### Corrections to the source

* **Fig. 4 needs a minor correction.** The prose rules of Section 3 are formalized. The table of
  Fig. 4 differs from them in five entries. Four are harmless (`[2]` meeting `[−1]` gives
  `[1], ⟨1⟩` instead of `[1], [0]`, symmetrically for `[−2]`, `[1]`: same weights). The entry for
  the initiator `[1]` meeting the responder `[0]`, printed `(⟨1⟩, [1])`, moves the weight to the
  `[0]` agent and breaks Invariant 2 (`|w(s_a) − c_a| ≤ 1`): an agent of colour `−1` in state `[0]`
  (reachable, e.g. after `[−1]` meets `[1]`) gets `[1]`, and a later change of its colour to `1`
  asks for the nonexistent state `[3]`. With the printed table, Absolute-Majority reaches this
  situation already for `k = 2` and the four colours `00, 00, 01, 01`. The text's `([1], ⟨1⟩)` is
  used.
* **The final argument of Section 3 needs a minor correction.** It uses, in the tie case ("the
  last entity that reached state `[0]`"), that every group contains a strong state, an invariant
  the paper does not state; Invariants 1 and 2 alone do not suffice (colours all `0` with states
  `⟨1⟩, ⟨−1⟩` satisfy them and never change). `DynInv` adds this third invariant: it holds
  initially and is preserved (an interaction never removes the last strong state, and a colour
  change makes a state strong), so the conclusion stands.
* **Section 5.2 (uniqueness) needs a major correction and is not formalized.** Section 5.2 adds a
  bit `c'` meant to inform all agents whether the most frequent colour is unique. Rule (2) sets the
  bit `c'` of a potential winner to `1` when it sees a tie, and only losers can reset it (rule (4)).
  A tie seen before the stages stabilize then persists: for `k = 1` and colours `1, 1, −1`, the
  `−1`-agent must eventually annihilate with one of the `1`-agents, which then reports `[0]` (a
  tie) and keeps `c' = 1` forever, while the other `1`-agent stays in `[1]` and keeps `c' = 0`; the
  loser's bit then changes forever (rules (3) and (4)). So the mechanism of Section 5.2 never
  stabilizes on this input, in any execution (checked by exhaustive search: none of the 25
  reachable configurations is output-stable for `c'`), and the claim that all entities are
  eventually informed does not hold as stated. A repaired rule, in which a potential winner
  recomputes `c'` from its current stage reports (`1` iff one of the stages it currently wins is a
  tie) and losers copy `c'` from potential winners, was checked by exhaustive search for
  `k = 1, n ≤ 5` and `k = 2, n ≤ 4`; it is not proved. Section 5.1 and Theorem 7 do not depend on
  Section 5.2.
* **Typos.** In the proof of Theorem 7, "let `i > k − 1`" should read `i < k − 1`; in the proof of
  Theorem 6, "instances of `P`" and "`P(2)`" should read `P₁` and `P₂`, and "`l(i)`" should read
  `l[i]`.

### Proof route

* **Generic tools** (end of `ExactMajorityOutput.lean`): `Protocol.outputStableAt_of_invariant`,
  `Protocol.sum_interact` (sums over agents across an encounter), `Protocol.forall_step` and
  `Protocol.exists_step` (closure of "all agents" and "some agent" properties under steps),
  `exists_reflTransGen_of_measure` (strong induction on a potential), `exists_recruit` (moving every
  agent into its target set, one agent per step), `Protocol.StablyMarks.congr`.
* **Per-encounter facts** are proved by `decide` over the finite state types: e.g.
  `StaticState.absWeight_δ_le`, `StaticState.δ_recruit`, `StaticState.δ_out`,
  `DynState.close_δ_fst` and `close_δ_snd` (Invariant 2 under interactions), `DynState.δ_strong`
  (a strong state survives), `DynState.natAbs_δ_lt` (opposite weights decrease `R`),
  `DynState.δ_recruit`, `DynState.δ_out`.
* **Theorem 3.** Reach `R = |S|`; then every weight is `0` or `s = sign S`, a strong agent `[s]`
  exists (for `s = 0` it is the strong agent that is never lost), and it recruits every agent into
  `{q | out q = s}`, which is closed under `δ`.
* **Section 3.** `sum_group_interact` (group sums across an encounter inside a group),
  `sum_eq_add_of_eq_off` (for the recolouring), `DynInv.greaches`. In `DynInv.exists_stable` the
  target of agent `v` is `s v`, the sign of its group's colour sum; after Lemma 5 every nonzero
  weight in a group has sign `s v`, a strong agent of weight sign `s v` exists in each group (the
  third invariant gives it in the tie case), and it recruits its group into `{q | out q = s v}`.
* **Composition.** `drive_interact_fst`, `drive_reaches_fst`, `drive_lift_fst`, `drive_grp`
  (groups are constant along paths), `drive_interact_snd` (if `D` does not change the colours, the
  `P₂`-part of an encounter is a `P₂` encounter in a group, or nothing), `drive_lift_snd`,
  `drive_greaches_snd`, `drive_dynInv_interact` (one encounter is a group interaction followed by
  two recolourings, i.e. `DynInv.gstep` then `DynInv.recolour` twice).
* **Theorem 6.** `bitsProtocol_interact_snd`, `bitsProtocol_reaches_snd`, `bitsProtocol_lift`
  (the `k` copies of `P₁` are stabilized one at a time by induction on a `Finset` of indices),
  `sign_counts_bit_eq_majBit`; `majBit_eq_bitSign_of_isAbsMajority`, `sum_mul_absTarget_of`; then
  `Protocol.drive_stablyMarks` with a single group.
* **Theorem 7.** `winKey` (the ranking `(count, label)` in the lexicographic product, a linear
  order), `exists_groupWinner_bit`, `groupWinner_unique`, `toLex_lt_of_bit`, `duel_sum_eq` (the
  colour sum of a group is `x W₊ − x W₋`); `relativeMajorityLevel_δ_label`,
  `relativeMajorityLevel_input_label`, `relativeMajorityLevel_zero_reaches`; the level induction
  applies `Protocol.drive_stablyMarks` and `duel_wins_iff` at each level. `duel_wins_iff` needs no
  positivity of the counts.

### Numerical checks of the statements

* The transition functions of the Lean definitions (`P₁`, `P₂`, the recolouring, Absolute-Majority
  for `k = 1` with its outputs, Relative-Majority for `k = 2` with its outputs; 74,894 table
  entries) were evaluated and compared with an independent model, on which stable computation was
  checked by exhaustive reachability on multisets of states: `P₁` for all inputs with `n ≤ 7`;
  `P₂` with arbitrary interleavings of interactions and colour changes for `n ≤ 6`;
  Absolute-Majority for `k = 1, n ≤ 5` and `k = 2, n ≤ 4`; Relative-Majority for `k = 1, n ≤ 5`,
  `k = 2, n ≤ 5` and `k = 3, n ≤ 3`.
* The duel lemma (`duel_wins_iff`) for all count vectors with entries `≤ 2` (`k ≤ 2`) and `≤ 1`
  (`k = 3`).
* The table of Fig. 2 against the rules of Section 2 (all entries agree).

### Not covered

* Section 5.2 (informing all agents whether the most frequent colour is unique), which needs a
  major correction (see above).
* Dissemination of the winner's label to all agents (plurality consensus in the sense of
  Section 1.2), which the paper does not give.
