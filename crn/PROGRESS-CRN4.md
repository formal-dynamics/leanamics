# CRN-4: majority on graphs with very small local memory (progress)

Source: G. B. Mertzios, S. E. Nikoletseas, C. L. Raptopoulos, P. G. Spirakis, *Determining
majority in networks with local interactions and very small local memory*, ICALP 2014,
arXiv:1404.7671 (numbering of the arXiv version, cited as [MNRS14]); journal version in
Distributed Computing 30 (2017). The 3-state protocol is that of D. Angluin, J. Aspnes,
D. Eisenstat, *A simple population protocol for fast robust approximate majority*, Distributed
Computing 21 (2008) [AAE08].

Status: **all pinned statements proved** (phase 2). `lake build Crn` succeeds without
warnings, there is no `sorry` left in the four files, and `python3 ../scripts/check_axioms.py`
reports only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`) for every audited
declaration, including all CRN-4 pins. No pinned statement, definition body or section `variable`
was changed; the proofs only add helper lemmas (and one new section, `Absorption`).

| File | Content | Lines |
| --- | --- | --- |
| `Crn/GraphMajorityBasic.lean` | protocols on an interaction graph, stable computation on graphs, majority | 184 |
| `Crn/GraphMajorityAmbassador.lean` | the 4-state ambassador protocol, [MNRS14, Theorem 2] | 451 |
| `Crn/GraphMajorityLowerBound.lean` | at least 4 states are needed, [MNRS14, Theorem 1] | 165 |
| `Crn/GraphMajorityRandom.lean` | the 3-state protocol of [AAE08] on a graph, [MNRS14, Theorem 4] | 678 |

The pinned declarations are listed in `PINNED.txt` at the repository root. Proved at the pin
commit: the agreement with `Protocol.StablyComputes` on the complete graph, the transition tables,
the closure lemmas `graphOutputStable_of_allColor` and `prob_unanimous_of_unanimous`, the
one-step coupling and symmetry `graphStep_mono`, `graphStep_swap`, the bounds
`winProb_mem_Icc`, and the corollaries `not_graphStablyComputes_majority`,
`rank_majority_eq_four`, `tendsto_winProb`, `absorbProb_minority_le_majority`,
`ambassador_stablyComputesOnGraph_top`. The 17 remaining `sorry`s are now proved (see
"Proofs" below). Remaining: none.

## Proofs (phase 2)

### `GraphMajorityBasic`

* `GraphReaches.extend`: induction on `ReflTransGen`; a step along `d` is simulated by the dart
  `(f d.fst, f d.snd)` of `G'`; on the range of `f` both sides agree by injectivity, off the
  range both are frozen (`Function.extend_apply'`).

### `GraphMajorityAmbassador` (Theorem 2)

* Counting: `ambInd`, `ambCount_eq_sum`, `ambCount_interact_add` (`sum_add_pair` over one
  encounter) and the table facts `ambInd_δ_le`, `ambInd_δ_sub` (by `decide` over the 16 pairs)
  give `ambCount_interact_le` and `ambCount_sub_interact`; `ambCount_input` by `simp`.
* One-step facts: `interact_move` (an ambassador moves onto a vertex without ambassador and
  paints it), `ambCount_interact_move` (a move changes no count), `ambCount_interact_annihilate`
  (both counts drop by one); `card_filter_add_pair` (counting a state predicate when two agents
  change); `exists_adj_dist_lt` (on a connected graph, a neighbour strictly closer to `w`).
* `exists_reaches_annihilate_of_dist`: strong induction on the distance from a red ambassador
  `u` to a green ambassador `w`; the red ambassador walks along a shortest path, moving onto free
  vertices and handing over to red ambassadors it meets, until it meets a green one. This is the
  fix of the "blocking" gap noted below.
* `exists_reaches_spread_of_dist` (strong induction on the distance from a `b`-ambassador to a
  vertex of color `!b`, no `!b`-ambassadors): reaches a configuration with strictly fewer
  `!b`-colored vertices; `exists_reaches_allColor` iterates it (strong induction on that number).
* `ambCount_sub_reaches` (the invariant along reachability), `exists_reaches_ambCount_eq_zero`
  (iterated annihilation, `𝒞_{k,ℓ} → 𝒞_{k−ℓ,0}`), then `ambassador_graphStablyComputes`.
* `graphReaches_eq_of_noAmb` (configurations without ambassadors are frozen) for
  `ambassador_tie_stuck`.

### `GraphMajorityLowerBound` (Theorem 1)

* `Protocol.GraphReaches.eq_of_fin_one` (one agent has no partner),
  `output_input_of_stablyComputesOnGraph_top_majority` (both outputs occur, on `Fin 1`),
  `not_stablyComputesOnGraph_top_majority_of_unique` (the core argument, once for both colors:
  if `q₁` is the only state with output `b`, the inputs `(b, b, !b)` and `(b, b, b)` on `Fin 3`
  reach "all `q₁`", and embedding them into `Fin 5` with two extra `!b` agents
  (`GraphReaches.extend` along `Fin.castLE`) gives a common configuration reachable from inputs
  with majorities `!b` and `b`). The main theorem counts the two output classes of `Q`.

### `GraphMajorityRandom` (Theorem 4)

* Coupling and symmetry: `graphKernel_apply`, `iterate_graphKernel_mono` (monotone observables
  stay monotone at every time), `iterate_graphKernel_swap`, `unanimous_swap_iff`; then
  `event_allX_mono`, `event_swap`, `winProb_monotone`.
* Hall: `exists_injective_of_regular` by `Finset.all_card_le_biUnion_card_iff_exists_injective`
  and double counting (`card_mul_eq_card_mul`, `card_mul_le_card_mul`);
  `exists_injective_subset` applies it to `T S = {A ⊆ S, #A = n − m}` with
  `r = d = C(m, n − m)` (bijections with `S.powersetCard (n − m)` and, via complements, with
  `Aᶜ.powersetCard (n − m)`).
* `winProb_minority_le_majority`: as in eqs. (18) to (23), with `τ S = (σ S)ᶜ` a bijection of
  the `m`-sets, so the final inequality (23) is an equality (`avg_equiv`).
* Absorption (section `Absorption`): `rule_fst`, `rule_blank_snd`, `rule_snd_rule_snd` (an
  initiator `s ≠ B` activated twice on the same responder makes it `s`), `graphStep_fst`,
  `graphStep_snd`, `graphStep_of_ne`, `graphStep_of_unanimous`, `graphStep_eq_of_fst`,
  `graphStep_not_unanimous_blank`, `graphReaches_const` (spreading an opinion to all agents,
  using a boundary dart `SimpleGraph.Walk.exists_boundary_dart`), `exists_iterate_lt_one`
  (reachability of a state where `g < 1` gives `K^k g < 1`), `iterate_unanimous_blank`. Then
  `tendsto_event_unanimous` by `Kernel.finite_absorption` on the indicator of "not unanimous",
  and `half_le_absorbProb_majority` from the limits and `absorbProb_minority_le_majority`.

## Pinned statements in words

### Graph setting (`GraphMajorityBasic`)

* `dartPair d`: the (initiator, responder) pair of an oriented edge `d : G.Dart`.
* `Protocol.GraphStep P G`, `GraphReaches`, `GraphOutputStable`: one encounter along an
  oriented edge of `G : SimpleGraph (Fin n)` (via the existing `Protocol.interact`),
  reachability, and output stability on `G` ([MNRS14, §2 and §2.2, "directly reachable"]).
* `Protocol.StablyComputesOnGraph P G D φ`: for every input whose count vector lies in the
  domain `D`, every configuration reachable on `G` from the initial configuration can reach an
  output-stable configuration with output `φ`. Same reachability form as the existing
  `Protocol.StablyComputes`, with a domain because majority is a partial function ([MNRS14,
  §2]).
* `Protocol.GraphStablyComputes P D φ`: the above for every connected graph on `Fin n`, every
  `n`.
* `majority x = decide (x false < x true)` (`true` is red) and `HasMajority x : x true ≠
  x false` (no tie).
* Proved: `graphStep_top`, `graphReaches_top`, `graphOutputStable_top` (on the complete graph
  `⊤` these are `Step`, `Reaches`, `OutputStable`), `stablyComputesOnGraph_top_iff`
  (stable computation on the complete graphs of all nonempty populations with the trivial domain
  is exactly `Protocol.StablyComputes`), `GraphStablyComputes.stablyComputes`,
  `GraphStablyComputes.top`.
* `GraphReaches.extend`: reachability transfers along an injective, edge-preserving embedding
  of populations, the other agents being frozen (the step "ignoring agents `v` and `u`" of the
  proof of Theorem 1).

### (a) The ambassador protocol, [MNRS14, Theorem 2] (`GraphMajorityAmbassador`)

* `ambassador : Protocol Bool AmbState` with `AmbState = Bool × Bool` (color, ambassador),
  `card_ambState` (4 states), `ambassador_table` and `ambassador_table_rest` (the table of
  Figure 1, all 16 entries), `ambassador_symm` (the protocol is symmetric).
* `ambCount b c`: the number of ambassadors of color `b`. Invariants: `ambCount_input` (it starts
  at the input counts), `ambCount_interact_le` (never increases), `ambCount_sub_interact` (the
  difference red minus green never changes).
* `exists_reaches_annihilate`: on a connected graph, while both colors have ambassadors, one
  ambassador of each color can be annihilated (the step `𝒞_{k,ℓ} → 𝒞_{k−1,ℓ−1}`).
* `exists_reaches_allColor`: on a connected graph, if there are ambassadors of color `b` only,
  the all-`b` coloring is reachable.
* `graphOutputStable_of_allColor` (proved): an all-`b` coloring is output-stable.
* **`ambassador_graphStablyComputes`**: the ambassador protocol stably computes majority on
  every connected graph, for every input with a majority. Corollary (proved):
  `ambassador_stablyComputesOnGraph_top` on complete graphs.
* `ambassador_tie_stuck`: with one red and one green agent, a configuration is reachable from
  which no output-stable configuration is reachable (why the tie is excluded).

### (b) Lower bound, [MNRS14, Theorem 1] (`GraphMajorityLowerBound`)

* **`not_stablyComputesOnGraph_top_majority`**: no protocol with at most 3 states (any
  `Fintype Q` with `card Q ≤ 3`) stably computes majority (ties excluded) on the complete graphs
  of all nonempty populations.
* `not_graphStablyComputes_majority` (proved from it): the same on all connected graphs, the
  paper's `R(𝒫_majority) > 3`.
* `rank_majority_eq_four` (proved from the above and Theorem 2): the minimal number of states is 4.

### (c) The protocol of [AAE08] on a graph, [MNRS14, Theorem 4] (`GraphMajorityRandom`)

* `rule`: the one-way rule of [MNRS14, eq. (1)] on `ApproxMajority.Species` (`X`, `Y`, `B`),
  `protocol` the corresponding population protocol. `rule_mem_network` and
  `exists_rule_of_mem_network` (proved): the effective transitions of `rule` are exactly the four
  reactions of the CRN-1 network `ApproxMajority.network`.
* `graphStep G c d`, `graphKernel G = Kernel.ofStep (graphStep G)` over `EdgeRound G = G.Dart`:
  the probabilistic scheduler (uniform edge, uniform orientation).
* `Unanimous s c`, `placement S` (`Y` on `S`, `X` elsewhere), `winProb G m s t` (probability,
  over a uniform `m`-subset `S` and the scheduler, that every agent is `s` at time `t`),
  `absorbProb G m s = ⨆ t, winProb G m s t`.
* Coupling: `rank` (order `Y < B < X`), `rule_mono` and `graphStep_mono` (proved),
  `event_allX_mono` (the probability of all `X` at time `t` is monotone in the initial
  configuration).
* Symmetry: `swap`, `rule_swap` and `graphStep_swap` (proved), `event_swap`.
* `prob_unanimous_of_unanimous` (proved), `winProb_monotone`, `winProb_mem_Icc` (proved),
  `tendsto_winProb` (proved from the previous two).
* `exists_injective_of_regular`: [MNRS14, Corollary 1] (systems of distinct representatives for
  regular families, from Hall's theorem); `exists_injective_subset`: its instance used in the
  proof (injective choice of an `(n − m)`-subset `A_S ⊆ S` of every `m`-set `S`).
* **`winProb_minority_le_majority`**: on every graph with an edge, if `n ≤ 2m`, at every time
  `t` the probability that the minority has won is at most the probability that the majority
  has won. Limit form (proved from it): `absorbProb_minority_le_majority`.
* `tendsto_event_unanimous`: on a connected graph, from every configuration with a non-blank
  agent, the protocol is absorbed in all-`X` or all-`Y` with probability tending to 1.
* **`half_le_absorbProb_majority`**: on a connected graph, if `n ≤ 2m` and `m ≤ n`, the
  probability of converging to the majority is at least `1/2` (the theorem as stated).

## Correspondence with [MNRS14]

| Paper | Lean |
| --- | --- |
| §2, model; "directly reachable" (§2.2) | `GraphStep`, `GraphReaches`, `GraphOutputStable`, `dartPair` |
| §2, stably computes (partial function) | `StablyComputesOnGraph`, `GraphStablyComputes` |
| §2.1, eq. (1) | `ApproxMajority.rule`, `ApproxMajority.protocol` |
| Definition 1 and Theorem 1 | `not_stablyComputesOnGraph_top_majority`, `not_graphStablyComputes_majority`, `rank_majority_eq_four` |
| §4, Figure 1 | `ambassadorδ`, `ambassador`, `ambassador_table`, `ambassador_table_rest`, `ambassador_symm` |
| Theorem 2 (and its proof's invariant and steps) | `ambassador_graphStablyComputes`; `ambCount_*`, `exists_reaches_annihilate`, `exists_reaches_allColor`, `graphOutputStable_of_allColor` |
| Corollary 1 | `exists_injective_of_regular`, `exists_injective_subset` |
| Theorem 4, eqs. (18) to (23) | `winProb`, `absorbProb`, `event_allX_mono` (eq. (19)), `event_swap` (eq. (20)), `winProb_minority_le_majority`, `absorbProb_minority_le_majority`, `half_le_absorbProb_majority` |

## Deviations from the source

1. **Undirected graphs only.** The paper allows directed or undirected graphs (Theorem 2:
   "(un)directed"; Theorem 4: strongly connected directed graphs). We use
   `SimpleGraph (Fin n)`, where an interaction is an oriented edge (`G.Dart`) and the
   probabilistic scheduler draws a uniform oriented edge, which is the paper's scheduler on
   undirected graphs. Directed graphs are not covered.
2. **Stable computation in reachability form.** The paper defines stable computation through
   fair schedulers; we use the reachability form of the existing `Protocol.StablyComputes`
   (equivalent for finite populations, see `FORMALIZATION_DIFFERENCES.md`, CRN-3), generalized
   to graphs, with a domain `D` for partial predicates. Agreement with the existing notion on the
   complete graph is proved.
3. **The tie case** is excluded from the domain (`HasMajority`), exactly as in Theorem 2 ("if
   there exists initially a majority"); `ambassador_tie_stuck` shows that no output convention
   could include it.
4. **Theorem 1 in a stronger form.** The paper's proof only uses complete graphs, so we state the
   impossibility on complete graphs (the existing standard populations); the statement on all
   connected graphs follows. The proof works with `|V| = 3` (the paper takes `|V| = 2k + 1`,
   `k ≥ 2`). The protocol may have any finite state type with at most 3 elements and any input
   map (the paper assumes the two input states distinct, which is the only non-trivial case).
5. **Theorem 4 in finite time.** Convergence is formalized in the finite probability layer:
   `winProb G m s t` is the probability that the configuration at time `t` is unanimous `s`;
   unanimity is absorbing, so it is nondecreasing and its supremum (the limit) `absorbProb` is
   the convergence probability, as for `Dynamics.Kernel.iSup_event_of_invariant`. The main
   inequality is pinned at every finite time (stronger than the limit) and on every graph with
   an edge (the paper assumes strong connectivity). The paper's "probability at least `1/2`" needs
   convergence with probability 1, a step the paper leaves implicit; it is pinned separately
   (`tendsto_event_unanimous`, `half_le_absorbProb_majority`) on connected graphs.
6. **The rule of [AAE08].** Eq. (1) of the paper does not list the case of a blank initiator and
   a non-blank responder; as in [AAE08] it leaves both states unchanged. The existing CRN-1 model
   `ApproxMajority.network` draws a uniform reaction and is observed on counts, so it cannot be
   run on a graph agentwise; we use the one-way rule on its species and prove that its effective
   transitions are exactly the reactions of `network`.
7. **Placement.** The random initial placement is a uniform `m`-subset `S` of agents of the
   majority type `Y` (the paper's eq. (18)), with `X` on the complement; `Y` plays the paper's
   green majority `g` and `X` its red minority `r`.

## Errors and gaps found in the source

* Theorem 1, proof: "agents `v` and `u` remain of type `r`" needs a minor correction (they are
  of type `g`), and "`|G_1| = k − 1`" for `C_2` should read `|G_2| = k − 1`.
* Theorem 4, proof: the monotonicity claim "increasing the initial number of agents of type `r`
  increases the probability that agents of type `r` win" is stated without proof; it holds by
  the monotone coupling above (the rule is monotone for `g < b < r`). The conclusion "with
  probability at least `1/2`" additionally needs absorption with probability 1, which is not
  argued (minor correction: add it; true on connected graphs).
* Theorem 2, proof: "for every configuration in `𝒞_{k,ℓ}` there exists a chain of transitions
  that lead to `𝒞_{k−1,ℓ−1}`" does not address ambassadors blocking each other (an ambassador
  cannot move onto a vertex holding an ambassador of the same color); choosing a closest pair of
  opposite ambassadors fixes this (minor correction).
* Lemma 6 (path `L_m`, absorption probability `1/(2(m − 1))`) was checked numerically for
  `m ≤ 6` and is not formalized here.

## Numerical checks of the pinned statements

* Theorem 1 (`not_stablyComputesOnGraph_top_majority`): an exhaustive search over all protocols
  with at most 3 states (all `9^9` transition tables and both output maps; on one agent the two
  input states must differ, so they are fixed up to renaming) finds 650 tables per output map
  that stably compute majority on the complete graph of 3 agents and none that also does so on
  5 agents, as in the proof route (populations of 1, 3 and 5 agents).
* Theorem 2: reachability-form stable computation of the ambassador protocol on all connected
  graphs with at most 4 vertices and all non-tie inputs.
* Theorem 4: the finite-time inequality on paths, stars, cycles and lollipops (exact rational
  arithmetic, `t ≤ 25`, including a graph with an isolated vertex); exact absorption
  probabilities (linear solve) on paths, stars, cycles, complete graphs and a lollipop with at
  most 6 vertices: the convergence probabilities to the majority and to the minority sum to 1,
  the former is at least `1/2`, with equality exactly at ties; from every configuration with a
  non-blank agent, all-blank is unreachable and all-`s` is reachable for every opinion `s`
  present.

## Remaining (not pinned)

* Theorem 3: expected convergence time `O(n⁶)` on any connected graph and
  `O(n² log n / |k − ℓ|)` on the clique, under the probabilistic scheduler (needs meeting and
  cover times of random walks, [TW91]).
* Lemmas 1 and 2 (birth-death absorption probabilities and times; partly covered by
  `Dynamics.Kernel.iSup_event_of_invariant`).
* Theorem 5 (robustness on the clique: failure probability `e^{−Θ(n)}` for a minority below
  `n/7`), Lemmas 3 to 5, Lemma 6.
* The failure families: Theorem 6 (lollipop graphs, where the protocol of [AAE08] converges to the
  minority with high probability although the majority is `n − Θ(log n)`) and Theorem 7 (two
  cliques joined by an edge, expected exponential convergence time), with Lemmas 7 to 11. They
  build on Theorem 5 and are not cheap.
* Directed interaction graphs and Observation 1.

## Draft roadmap row

| ID | Result | Source | Needs | Size | Status |
| --- | --- | --- | --- | --- | --- |
| CRN-4 | **Majority on arbitrary graphs with very small local memory.** Population protocols on a connected interaction graph `G` (interactions along edges), two input types. (a) The 4-state *ambassador protocol* stably computes the initial majority on every connected graph (ties excluded), in the reachability form of CRN-3 generalized to graphs; (b) no protocol with at most 3 states does, already on complete graphs, so 4 states are optimal; (c) the 3-state approximate-majority protocol (CRN-1) on any graph, with a uniformly random oriented edge per step and a uniformly random placement of the two types, converges to the majority with probability at least that of converging to the minority (at every finite time, by a monotone coupling, the colour symmetry and Hall's theorem), hence with probability at least 1/2 on connected graphs. Remaining: expected convergence times (`O(n⁶)`, clique `O(n² log n / gap)`), robustness on the clique (minority below `n/7` wins with probability `e^{−Θ(n)}`) and the failure families (lollipop graphs: the minority wins w.h.p.; two cliques joined by an edge: exponential time). | Mertzios–Nikoletseas–Raptopoulos–Spirakis, ICALP 2014 (arXiv:1404.7671; Distributed Computing 2017); Angluin–Aspnes–Eisenstat 2008 | CRN-1, CRN-3, FND-2, FND-7 | M (a–c) / L (times, failure families) | (a–c) proved |
