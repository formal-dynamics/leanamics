# Comparison: Hassin–Peleg (2001) vs. Lean 4 Formalization

This document provides a detailed comparison between the paper:
> Yehuda Hassin and David Peleg, **Distributed Probabilistic Polling and Applications to Proportionate Agreement**, *Information and Computation* 171 (2001), 248–268.

and its Lean 4 formalization in the `voter` package (`leanamics/voter`).

---

## 1. Scope & Formalization Status

### 1.1 Formalized Results (Sections 2.1–2.3 + Section 4.3.1)

| Paper Result | Informal Content | Lean 4 Declaration | File |
| :--- | :--- | :--- | :--- |
| **Section 2.1** | Synchronous copying round | [`Voter.step`](Voter/Model.lean#L17) | [Voter/Model.lean](Voter/Model.lean) |
| **Section 2.1** | Configuration transition kernel | [`Voter.transition`](Voter/Model.lean#L32) | [Voter/Model.lean](Voter/Model.lean) |
| **Section 2.1** | Transition probability formula ($P_{ab}$) | [`Voter.transition_product`](Voter/Model.lean#L52), [`Voter.transition_product_bool`](Voter/Model.lean#L72) | [Voter/Model.lean](Voter/Model.lean) |
| **Preamble to Lemma 2.2** | Stationary distribution existence | [`Dynamics.Kernel.exists_stationary`](../dynamics/Dynamics/Stationary.lean#L53) | [Dynamics/Stationary.lean](../dynamics/Dynamics/Stationary.lean) |
| **Lemma 2.1** | Monochromatic edge in nonbipartite graph | [`Voter.monochromatic_edge`](Voter/Graph.lean#L18) | [Voter/Graph.lean](Voter/Graph.lean) |
| **Lemma 2.1** | Monochromatic region propagation | [`Voter.propagate_region`](Voter/Graph.lean#L46), [`Voter.possible_consensus`](Voter/Graph.lean#L90) | [Voter/Graph.lean](Voter/Graph.lean) |
| **Lemma 2.1** | Consensus states absorbing & nonconsensus survival vanishes | [`Voter.transition_constant`](Voter/Absorption.lean#L52), [`Voter.consensus_tendsto`](Voter/Absorption.lean#L109) | [Voter/Absorption.lean](Voter/Absorption.lean) |
| **Lemma 2.3** | Expected stationary weight invariance (martingale) | [`Voter.round_mass`](Voter/Model.lean#L101), [`Voter.iterate_mass`](Voter/Model.lean#L115) | [Voter/Model.lean](Voter/Model.lean) |
| **Lemma 2.2** | Finite-time discrepancy bound & limit of white probability | [`Voter.whiteMass_bounds`](Voter/Main.lean#L117), [`Voter.whiteProbability_error`](Voter/Main.lean#L133), [`Voter.whiteProbability_tendsto`](Voter/Main.lean#L150) | [Voter/Main.lean](Voter/Main.lean) |
| **Theorem 2.1** | Eventual all-white absorption probability $\rho_{s1} = \sum_{i \in W_s} \pi_H(i)$ | [`Voter.consensus_probability`](Voter/Main.lean#L162) | [Voter/Main.lean](Voter/Main.lean) |
| **Corollary 2.2** | Degree weights are stationary; uniform consensus probability $\sum_{i \in W_s} \frac{d_i}{2m}$ | [`Voter.degree_stationary`](Voter/Uniform.lean#L43), [`Voter.uniform_consensus_probability`](Voter/Corollaries.lean#L26) | [Voter/Uniform.lean](Voter/Uniform.lean), [Voter/Corollaries.lean](Voter/Corollaries.lean) |
| **Section 4.3.1** | Consensus on $d$-regular graph equals initial white fraction $x/n$ | [`Voter.regular_consensus_probability`](Voter/Corollaries.lean#L36) | [Voter/Corollaries.lean](Voter/Corollaries.lean) |
| **Section 2.3** | Many colors: projections commute with dynamics | [`Voter.step_project`](Voter/Model.lean#L24), [`Voter.iterate_project`](Voter/Colors.lean#L10), [`Voter.colorProbability_project`](Voter/Colors.lean#L37) | [Voter/Model.lean](Voter/Model.lean), [Voter/Colors.lean](Voter/Colors.lean) |
| **Section 2.3** | Many colors: consensus probability $\rho_{sc} = \sum_{i \in A_c^s} \pi_H(i)$ | [`Voter.color_consensus_probability`](Voter/Colors.lean#L51), [`Voter.sum_color_consensus_probability`](Voter/Colors.lean#L61) | [Voter/Colors.lean](Voter/Colors.lean) |
| **Figure 1** | Bipartite 2-cycle alternating coloring flips and cycles without consensus | [`Voter.Examples.twoVertex_flip`](Voter/Examples.lean#L65), [`Voter.Examples.twoVertex_cycle`](Voter/Examples.lean#L68), [`Voter.Examples.twoVertex_never_consensus`](Voter/Examples.lean#L72) | [Voter/Examples.lean](Voter/Examples.lean) |

---

### 1.2 Unformalized Results

The following portions of the paper were not formalized:
1. **Section 2.4: Time Bounds** (formalized since VOT-3 and VOT-6, with the deviations of
   §4; only the plain walk on nonbipartite graphs remains open)
   - Dual coalescing random walks: on the complete graph with self-loops in
     [`Coalescence.lean`](Voter/Coalescence.lean); for every sampling kernel
     [`iterate_disagreement_le_pairWalk`](Voter/Meeting.lean) (two coalescing tokens, union bound).
   - Fact 2.3 (lazy uniform case): commute bound $Z_{x,y} + Z_{y,x} \le 4\,\mathrm{vol}\,(n-1)$ for
     hitting times defined by their Laplacian system,
     [`hitting_add_hitting_le`](Voter/MeetingHitting.lean).
   - Lemma 2.4 (lazy walks, tail form): meeting within $51 n^3$ steps with probability
     $\ge 1/2$, [`lazy_meeting_le_half`](Voter/MeetingTime.lean), via the comparison of
     synchronous and sequential walks of Kanade, Mallmann-Trenn, Sauerwald instead of
     $M = O(n Z_{\max})$.
   - Theorem 2.4 (tail form, no Chernoff bound needed): consensus fails after $k T_0$ rounds with
     probability $\le (n-1)2^{-k}$ if tokens meet within $T_0$ steps with probability $\ge 1/2$,
     [`iterate_disagreement_le_of_meeting`](Voter/Meeting.lean), for every kernel.
   - Theorem 2.5 (lazy uniform walk, high-probability form): consensus within
     $255 n^3 \log n$ rounds with probability $\ge 1 - 1/n$ on every connected graph,
     [`lazy_voter_consensus_whp`](Voter/MeetingConsensus.lean). The plain walk on connected
     nonbipartite graphs (the paper's setting) is covered only conditionally on a meeting bound.
2. **Section 3: Application to Distributed Consensus & Dynamic Networks**
   - Section 3.1: Formal specification of the consensus problem (Agreement, Validity, Stopping) and Proportionate Consensus.
   - Section 3.2: Algorithm `PropCon` (choice of degree-to-reliability factor $k = \max_i \lceil d_i / R_i \rceil$, normalized weights $\tilde{R}_i$, and weight matrix $H$ with self-loops $H_{ii} = 1 - d_i/\tilde{R}_i$).
   - Theorem 3.1: `PropCon` solves proportionate consensus.
   - Theorem 3.2 & Corollary 3.3: Convergence time bounds for `PropCon` ($O(kn \log n)$ and $O(n^2 \Delta \log n)$).
   - Section 3.3: Stabilizing dynamic network model $\text{DynNet}(G, T_0, A)$ and dynamic process $M_{pc}$.
   - Lemma 3.1 & Theorem 3.4: Dynamic martingale property and preservation of consensus probability under transient link failures.
3. **Section 4: Extremal Combinatorial Results (except Section 4.3.1)**
   - Section 4.1: Theorem 4.1 (characterization of pairs $(G, W_s)$ maximizing $f(x, n)$ via white clique, black independent set, and $|E(B_s, W_s)| = n - x$).
   - Corollary 4.2: Formula $f(x, n) = \frac{x^2 - 2x + n}{x^2 - 3x + 2n}$.
   - Section 4.2: Extremal monopoly threshold $\Psi(G, \alpha)$; Proposition 4.1 ($\Psi(G, 1/2) \ge 2$ and tight); Proposition 4.2 ($\Psi(G, 1-\epsilon) = \Theta(\sqrt{n/\epsilon})$).
   - Section 4.3.2: Planar graph bound $f_P(x, n)$ and Corollary 4.3 ($\Psi(G, 1-\epsilon) = \Omega(n)$).
   - Section 4.4: Theorem 4.4 (relation to deterministic majority model: admissible 2-colorings have $\rho_{s1} > 1/2$, tight).

---

## 2. Key Differences, Adaptations, and Mathematical Nuances

### 2.1 Correction of the "W.L.O.G. White" Handwave in Lemma 2.1 Proof
* **Paper text (page 252)**:
  > *"Under this state, there must be two neighbors with the same color. This must happen because $G$ is nonbipartite, so it must contain an odd cycle, and any 2-coloring on this cycle must assign the same color to two neighbors. Let $i$ and $j$ be two such neighboring nodes, and **w.l.o.g assume that they are colored white**. We prove by induction that there is a positive probability that at time $k$ all nodes of distance $k$ from $i$ or $j$ are colored white. Hence at time step $\text{Diam}(V)$, $s$ can be absorbed to the all-white state..."*
* **The issue**:
  Assuming "without loss of generality" that the monochromatic edge is white is invalid when analyzing an arbitrary non-monochromatic state $s$. An initial state $s$ could contain monochromatic *black* edges but *no* monochromatic white edges (e.g. if the white vertices form an independent set). From such an edge, the region propagation argument can only guarantee reaching the *all-black* state in $\text{Diam}(V)$ steps, not necessarily the all-white state directly.
* **Lean's rigorous treatment**:
  [`Voter.possible_consensus`](Voter/Graph.lean#L90) explicitly proves:
  ```lean
  ∃ c, Relation.ReflTransGen (Possible G) s (fun _ => c)
  ```
  That is, consensus is reachable in **some** color $c \in \{\text{true}, \text{false}\}$ (the color of the monochromatic edge found by [`Nonemonochromatic_edge`](Voter/Graph.lean#L18)). This suffices to prove that the probability of staying in non-consensus states decays to 0 ([`Noneconsensus_tendsto`](Voter/Absorption.lean#L109)), fixing the paper's informal leap.

---

### 2.2 Formalization of Absorption Probability ($\rho_{s1}$)
* **Paper approach**:
  The paper introduces $\rho_{s1}$ as the absorption probability into state $\mathbf{1}$, implicitly appealing to the underlying infinite-horizon Markov chain path measure $\mathbb{P}_s(\exists t \ge 0, S_t = \mathbf{1})$.
* **Lean approach**:
  Rather than formalizing an infinite trajectory measure space, Lean defines the finite-time consensus probability:
  ```lean
  noncomputable def colorProbability [Fintype C] (H : Kernel V) (c : C) (n : ℕ)
      (s : Config V C) : ℝ := (transition H).iterate n (allColor c) s
  ```
  and defines eventual consensus probability as its supremum:
  ```lean
  noncomputable def eventualColor [Fintype C] (H : Kernel V) (c : C)
      (s : Config V C) : ℝ := ⨆ n, colorProbability H c n s
  ```
  Since consensus states are absorbing fixed points ([`Nonetransition_constant`](Voter/Absorption.lean#L52)), $n \mapsto \text{colorProbability } H\ c\ n\ s$ is monotone increasing ([`NonecolorProbability_mono`](Voter/Main.lean#L47)) and converges to its supremum ([`NonecolorProbability_tendsto`](Voter/Main.lean#L66)). This gives a fully constructive and rigorous definition using only standard real analysis.

---

### 2.3 Reordering of Lemma 2.2 and Lemma 2.3
* **Paper structure**:
  1. **Lemma 2.2** is stated first: $\lim_{t \to \infty} \mathbb{E}_s(\pi_H(S_t)) = \rho_{s1}$. Its proof decomposes the expectation over the state space $\mathcal{S} = \{0, 1\}^n$:
     $$\mathbb{E}_s(\pi_H(S_t)) = \sum_{a \notin \{0, 1\}} \pi_H(a) \mathbb{P}_s(S_t = a) + 0 \cdot \mathbb{P}_s(S_t = 0) + 1 \cdot \mathbb{P}_s(S_t = 1)$$
     and relies on transient state probabilities tending to 0 while $\mathbb{P}_s(S_t = 1) \to \rho_{s1}$.
  2. **Lemma 2.3** is proved second: $\forall t \ge 0, \mathbb{E}_s(\pi_H(S_t)) = \sum_{i \in W_s} \pi_H(i)$ (martingale property).
  3. **Theorem 2.1** equates the two limits.
* **Lean structure**:
  1. **Lemma 2.3** ([`Noneround_mass`](Voter/Model.lean#L101), [`Noneiterate_mass`](Voter/Model.lean#L115)) is proved **first** in `Model.lean`.
  2. **Lemma 2.2** is then formalized in `Main.lean` through explicit error bounds:
     - [`NonewhiteMass_bounds`](Voter/Main.lean#L117): $\mathbf{1}_{\{s=\mathbf{1}\}} \le \text{whiteMass } p\ s \le \mathbf{1}_{\{s=\mathbf{1}\}} + \text{survival } s$.
     - [`NonewhiteProbability_error`](Voter/Main.lean#L133): sandwiching the difference:
       $$0 \le \text{whiteMass } p\ s - \text{colorProbability } H\ \text{true } n\ s \le (transition\ H)^n (\text{survival})(s)$$
       This is an instance of the shared finite-horizon optional stopping theorem
       `Dynamics.Kernel.event_error_of_invariant` (roadmap FND-4): the targets are the two
       consensus configurations, the invariant is the white mass, and `whiteMass_bounds`
       bounds it between `0` and `1` off the targets.
     - [`NonewhiteProbability_tendsto`](Voter/Main.lean#L150): by squeezing with [`Noneconsensus_tendsto`](Voter/Absorption.lean#L109), $\text{colorProbability } n \to \text{whiteMass}$.
  3. **Theorem 2.1** ([`Noneconsensus_probability`](Voter/Main.lean#L162)) identifies the limit with `eventualColor`.
* **Rationale**:
  This rearrangement avoids summing over the exponential state space $\mathcal{S}$ and avoids having to classify recurrent/transient states in full generality.

---

### 2.4 Generalization of Lemma 2.3 (No Graph Assumptions)
* **In the paper**:
  Lemma 2.3 is stated under the standing hypotheses of Section 2.1 (connected, nonbipartite, undirected graph).
* **In Lean**:
  [`Noneround_mass`](Voter/Model.lean#L101) and [`Noneiterate_mass`](Voter/Model.lean#L115) are generalized:
  - They require **no graph structure** at all, holding for any stochastic transition kernel `H : Kernel V`.
  - They require no connectivity, nonbipartiteness, or symmetry.
  - They hold for any real-valued observable $f : C \to \mathbb{R}$ on any finite color palette $C$, not just Boolean indicators.

---

### 2.5 Stationary Distribution: Existence vs. Uniqueness
* **In the paper (page 253)**:
  The authors cite Motwani & Raghavan [MR95] asserting that for a strongly connected graph, there exists a *unique* stationary distribution $\pi_H$.
* **In Lean**:
  - **Uniqueness is not needed**: Theorem 2.1 ([`Noneconsensus_probability`](Voter/Main.lean#L162)) is parameterized by *any* stationary distribution `p` (`hp : H.Stationary p`). Because the LHS (`eventualColor`) does not depend on `p`, any stationary distribution must yield identical mass on Boolean indicators.
  - **Constructive existence**: Existence is proved from scratch in the generic library ([`Dynamics.Kernel.exists_stationary`](../dynamics/Dynamics/Stationary.lean#L53)) using Cesàro averages of iterated distributions and compactness of the probability simplex in $\mathbb{R}^{|V|}$, requiring no black-box citations.

---

### 2.6 Strict Absence of Self-Loops vs Section 2.2 Remark
* **In the paper (page 251 & page 254 Remark)**:
  - Page 251: *"For simplicity it is assumed (at this stage) that the graph contains no self loops."*
  - Page 254 Remark: *"Given an initial bipartite graph, one can always add self-loops, with arbitrary chosen weights (even to a single node), hence converting the graph into a nonbipartite one. In this case Theorem 2.1 holds without the requirement that the graph is nonbipartite."*
* **In Lean**:
  - $G$ is modeled as a Mathlib `SimpleGraph V`, which is irreflexive by definition ($\neg G.\text{Adj } i\ i$).
  - The support condition is `hsupport : ∀ i j, G.Adj i j → 0 < (H i).weight j`: every edge has positive weight, and `H` may put additional weight elsewhere, in particular on self-loops ($(H i).\text{weight } i > 0$). This covers lazy chains and Wright–Fisher sampling ([`wrightFisher_one_third`](Voter/Examples.lean)).
  - The main theorem `consensus_probability` keeps the nonbipartite hypothesis, because its propagation argument starts from a monochromatic *edge* of `G`.
  - The Remark itself is formalized (VOT-2) as [`consensus_probability_of_selfLoop`](Voter/LazyLoop.lean) and [`color_consensus_probability_of_selfLoop`](Voter/LazyLoop.lean): on any connected `G`, bipartite or not, it suffices that `H` charges every edge and that `0 < (H v).weight v` for a single vertex `v`. The propagation ([`propagate_kernel_region`](Voter/LazyPropagation.lean)) takes rounds in the support of `H`, so the region `{v}` is monochromatic with `v` as its own internal neighbour. As in the main theorem, `H` may also charge non-edges, which is slightly more general than the Remark. Corollaries: the lazy voter `(I + D⁻¹A)/2` on any connected graph ([`lazyNeighbor_consensus_probability`](Voter/Lazy.lean)) and Wright–Fisher fixation `c_a / n` for every population size ([`wrightFisher_fixation`](Voter/WrightFisher.lean)).

---

### 2.7 Section 2.3 (Many Colors): Commuting Projections
* **In the paper**:
  The paper reduces $k > 2$ colors to two colors by considering a chosen color $c$ as white and all other colors as black. It asserts:
  $$\rho_{sc} = \sum_{i \in A_c^s} \pi_H(i) = \sum_{i \in A_c^s} \frac{d_i}{2m}$$
* **In Lean**:
  - Lean establishes a general projection commutativity lemma:
    [`Voter.iterate_project`](Voter/Colors.lean#L10): for any color map $g : C \to D$,
    $$(transition\ H)^n f (g \circ s) = (transition\ H)^n (f \circ (g \circ \cdot))(s)$$
  - Using $g = \text{colorIndicator } c$, this cleanly reduces consensus in color $c$ to Theorem 2.1 without duplicating the absorption analysis ([`Voter.color_consensus_probability`](Voter/Colors.lean#L51)).
  - Lean additionally proves that the color probabilities form a complete distribution over colors:
    [`Voter.sum_color_consensus_probability`](Voter/Colors.lean#L61): $\sum_{c \in C} \text{eventualColor } H\ c\ s = 1$.
  - *Note*: The uniform degree-weight corollary ($\sum_{i \in A_c^s} d_i / 2m$) was formalized for Boolean colors in `uniform_consensus_probability`, but not explicitly restated as a separate lemma for the general $C$ case.

---

## 3. Self-loops, the Lazy Voter and Neutral Wright–Fisher

This section covers the extension of Theorem 2.1 to graphs with self-loops (the Remark on
page 254, see §2.6), the lazy voter with kernel `(I + D⁻¹A)/2` (the kernel used by
Berenbrink, Giakkoupis, Kermarrec and Mallmann-Trenn, ICALP 2016) and neutral Wright–Fisher
fixation. Files: [`LazyPropagation.lean`](Voter/LazyPropagation.lean),
[`LazyLoop.lean`](Voter/LazyLoop.lean), [`Lazy.lean`](Voter/Lazy.lean),
[`WrightFisher.lean`](Voter/WrightFisher.lean).

### 3.1 Wright–Fisher with labelled individuals
* The classical neutral Wright–Fisher model is the count chain `X_{t+1} ~ Bin(n, X_t / n)`.
  Lean models it with labelled individuals: the synchronous voter with kernel `wfKernel V`,
  where each offspring picks a uniformly random parent with replacement. The count chain is
  the lumping of this chain and has the same fixation event; working with labelled
  configurations is what makes fixation a corollary of the voter theorem.
* The population is an arbitrary finite type `V` with `n = Fintype.card V`, rather than
  `Fin n` (a special case).
* Two versions are proved: [`wrightFisher_fixation_of_three_le`](Voter/WrightFisher.lean)
  (`3 ≤ n`) follows from the original `color_consensus_probability` on the complete graph,
  which is nonbipartite once `n ≥ 3`; [`wrightFisher_fixation`](Voter/WrightFisher.lean)
  holds for every `n ≥ 1` and goes through the self-loop extension.

### 3.2 The lazy voter on bipartite graphs needs the Remark
* `consensus_probability` assumes `¬ G.Colorable 2`. For the lazy kernel on a bipartite `G`
  this cannot be repaired by choosing another graph: every loopless graph `G'` whose edges are
  charged by `(I + D⁻¹A)/2` is a subgraph of `G`, hence bipartite. The lazy results are
  therefore proved through the self-loop extension
  ([`consensus_probability_of_selfLoop`](Voter/LazyLoop.lean),
  [`color_consensus_probability_of_selfLoop`](Voter/LazyLoop.lean)).
* The extension is slightly more general than the Remark: as in the main theorem, `H` may
  charge non-edges (only `G.Adj i j → 0 < H i j` is assumed), and one positive diagonal
  entry suffices ("even to a single node", as the Remark says).
* The generic step [`eventualColor_eq_whiteMass_of_tendsto`](Voter/LazyLoop.lean) is
  Lemma 2.2 in graph-free form: if the probability of not having reached consensus vanishes,
  the eventual white probability equals the stationary white mass.

### 3.3 Lazy voter hypotheses and forms
* [`lazyNeighbor`](Voter/Lazy.lean) needs `hd : ∀ i, 0 < G.degree i` (every vertex has a
  neighbour to sample), as `uniformNeighbor` does. For a connected graph this only excludes
  the one-vertex graph, where the statement is trivial. The holding probability is fixed at
  `1/2`.
* Only the many-colour forms are stated for the lazy voter
  ([`lazy_consensus_probability`](Voter/Lazy.lean),
  [`lazyNeighbor_consensus_probability`](Voter/Lazy.lean), with consensus probability
  `∑ i with s i = c, deg i / (2 |E|)`); the Boolean form is the instance `C = Bool`,
  `c = true`. This also supplies the many-colour degree-weight corollary missing in §2.7,
  for the lazy kernel.
* `eventualColor` is, as elsewhere in the package, the supremum of the finite-time consensus
  probabilities (§2.2).

---

## 4. Time Bounds on Connected Graphs (Section 2.4)

Files: [`MeetingRounds.lean`](Voter/MeetingRounds.lean), [`Meeting.lean`](Voter/Meeting.lean),
[`MeetingDrift.lean`](Voter/MeetingDrift.lean), [`MeetingHitting.lean`](Voter/MeetingHitting.lean),
[`MeetingTime.lean`](Voter/MeetingTime.lean), [`MeetingConsensus.lean`](Voter/MeetingConsensus.lean).
Further sources: Becchetti, Clementi, Natale, *Consensus dynamics: an overview*, SIGACT News
51(1), 2020 (the "survey"); Kanade, Mallmann-Trenn, Sauerwald, *On coalescence time in graphs*,
SODA 2019 (arXiv:1611.02460); Cooper, Elsässer, Ono, Radzik, SIAM J. Discrete Math. 2013.

### 4.1 Survey Theorem 8 is false as stated; the lazy walk is formalized
* Theorem 8 of the survey states: "Let G be any connected undirected graph. Starting from an
  arbitrary initial configuration c on G, the Voter dynamics reaches consensus w.h.p. in
  O(n³ log n) rounds." For the synchronous voter with plain uniform-neighbour sampling this
  **fails on bipartite graphs**: two tokens on opposite sides of a bipartite graph never meet,
  and an alternating colouring never reaches consensus
  (cf. [`twoVertex_never_consensus`](Voter/Examples.lean)). Hassin and Peleg's standing
  hypotheses (§2.1) do require a nonbipartite graph, and their Theorem 2.5 is the uniform case
  `H_ij = 1/d_i`.
* We formalize the **lazy** version, which makes "every connected graph" true: every vertex
  keeps its colour with probability `1/2` and otherwise copies a uniformly random neighbour,
  i.e. the kernel [`lazyNeighbor`](Voter/Lazy.lean) `= (I + D⁻¹A)/2` of §3. This kernel lies
  within Hassin and Peleg's weighted-polling framework with self-loops (the Remark on p. 254;
  it is also their PropCon weighting `H_ii = 1 − d_i/R̃_i` with `R̃_i = 2 d_i`, taking
  `H_ij = 1/R̃_i` on edges as the row sums require), and it is the setting of Cooper,
  Elsässer, Ono and Radzik and of Kanade, Mallmann-Trenn and Sauerwald, whose Proposition B.9
  (`t_meet ≤ 4 t_hit`) gives a clean meeting-time argument
  ([`iterate_outside_succ_le`](Voter/MeetingDrift.lean)). The main theorem is
  [`lazy_voter_consensus_whp`](Voter/MeetingConsensus.lean).
* Hassin and Peleg's own setting (plain walk on a connected nonbipartite graph) is covered
  only **conditionally** on a meeting bound:
  [`iterate_disagreement_le_of_meeting`](Voter/Meeting.lean) holds for every sampling kernel.
* The complete-graph model of [`Coalescence.lean`](Voter/Coalescence.lean) (uniform sampling
  over all vertices, i.e. Wright–Fisher) is not a special case: `lazyNeighbor ⊤ ≠ wfKernel`.
  The self-loop generalization (uniform over the closed neighbourhood) would contain it, but
  its holding probability `1/(d+1)` breaks the constant-factor coupling of Proposition B.9.

### 4.2 Form of the statements
* **High-probability form instead of expected time.** Hassin and Peleg's Theorems 2.4 and 2.5
  bound the expected consensus time (`O(M log n)`, `O(n³ log n)`). We prove
  `P(no consensus at T) ≤ 1/n` for `T ≥ A n³ log n`, the "w.h.p." form of the survey. The
  meeting time is likewise a tail bound (apart after `A n³` steps with probability `≤ 1/2`,
  [`lazy_meeting_le_half`](Voter/MeetingTime.lean), and `≤ 2^{-k}` after `k A n³` steps,
  [`lazy_meeting_le_pow`](Voter/MeetingTime.lean)) instead of an expected meeting time
  `M = O(n³)`; the two agree up to constants (Markov's inequality and geometric trials).
  Theorem 2.4 in tail form needs no Chernoff bound (Proposition 2.1): the diagonal of the
  two-token walk is absorbing, so being apart is submultiplicative in blocks.
* **Existential constants.** `O(·)` is rendered as `∃ A > 0`, uniform over all graphs, vertex
  types of a fixed universe and palettes. The proofs give `A = 51` (meeting) and `A = 255`
  (consensus); the literature route gives `A = 16` for the meeting bound (our commute bound
  loses a factor `2` over darts, and the `3/4`-per-block step loses more).
* **Two coalescing tokens driven by common rounds** ([`pairWalk`](Voter/Meeting.lean), the
  survey's Definition 5 with two tokens) instead of two independent walks with the path event
  "never met up to `T`". Before meeting the tokens are independent (distinct coordinates of
  `Distribution.independent H`), and the diagonal is absorbing, so "apart at time `T`" is
  exactly "not met within `T` steps".
* **Hitting times** are defined as the solution of their Laplacian system (it exists by the
  maximum principle: the system is injective, hence surjective), not as expectations of a
  path-space stopping time. The commute bound is
  `Z_{x,y} + Z_{y,x} ≤ 4 vol (n − 1) ≤ 4 n³`
  ([`hitting_add_hitting_le`](Voter/MeetingHitting.lean)), the lazy uniform case of Fact 2.3.
  Lemma 2.4 (`M = O(n Z_max)`) is replaced by the potential argument of Kanade,
  Mallmann-Trenn and Sauerwald ([`lazy_meeting_core`](Voter/MeetingTime.lean)).
* **Positive degrees** `hd : ∀ i, 0 < G.degree i` are assumed, as for `uniformNeighbor`; for a
  connected graph this only excludes `n = 1`, where consensus is trivial.
* **Arbitrary finite palette** (the survey uses `n` colours; Hassin and Peleg two colours,
  reduced from `k`).

---

## 5. Consensus Time via Conductance (Berenbrink–Giakkoupis–Kermarrec–Mallmann-Trenn)

Source: Berenbrink, Giakkoupis, Kermarrec, Mallmann-Trenn, *Bounds on the voter model in
dynamic networks*, ICALP 2016, arXiv:1603.01895 (BGKM16). Numbering: Theorem 1.1 (upper
bound), Lemma 2.1 (potential drop), Lemma 2.2 (drift implies time), Lemma 2.3 (phases for
`κ` opinions), Lemma 2.4 (the bound `n log n / φ²`). Files: `Conductance*.lean`. The
dynamics is the lazy voter [`lazyNeighbor`](Voter/Lazy.lean) `= (I + D⁻¹A)/2` of §3.

### 5.1 Lemma 2.1 of BGKM16 is false as printed
* The paper states
  `𝔼[Ψ(S_{t+1}) | S_t = s_t] ≤ Ψ(s_t) - ∑_{u ∈ V} λ_{u,t} d_u / (32 Ψ(s_t)³)`,
  with the sum over **all** vertices, where `Ψ(s) = √(vol(minority))` and `λ_u` is the
  number of neighbours of `u` with the other opinion. This is false. Counterexample: the star
  `K_{1,k}` with `k ≥ 15` and a single leaf in the minority (`Ψ = 1`). Only the leaf and the
  hub can change opinion, and exactly
  `𝔼[Ψ'] = ½ (1 - 1/(2k)) + (√(k-1) + √k)/(4k)`; for `k = 15` this is `0.6102`, while the
  printed bound is `1 - (1 + 15)/32 = 0.5` (the hub contributes `λ d = 15`); for `k = 40` it is
  `0.5723` against `-0.2812`.
* The paper's proof only yields the sum over the **minority side** `v^(0)`, and Lemma 2.2 only
  uses that sum. [`potential_drift`](Voter/ConductanceDrift.lean) formalizes this corrected
  form, with the paper's constant `32`:
  `𝔼 Ψ' ≤ Ψ - ∑_{u ∈ minority} λ_u d_u / (32 Ψ³)`. The conductance form
  ([`potential_drift_conductance`](Voter/ConductanceDrift.lean), `𝔼 Ψ' ≤ Ψ - d_min φ / (32 Ψ)`)
  is the display at the start of the proof of Lemma 2.2.
* The definition of `λ_u` in the paper has typos ("neighbours of `u` in `V ∖ v^1(t)`" for
  `u ∈ v^(0)`); the intended meaning, used in the proof, is the number of neighbours with the
  other opinion ([`discordant`](Voter/Conductance.lean)).
* In the replacement lemma (Lemma A.1) the printed proof drops a factor `1/2` that cancels;
  the formalized version is [`independent_expect_comp_sum_le`](Voter/ConductanceIndep.lean).
* Lemma 2.3 says "with probability 1/2 by Markov's inequality"; the reverse Markov argument
  gives `1/3`, which is what is used ([`phase_step`](Voter/ConductanceManyAux.lean)).

### 5.2 Form of the statements
* **Constant `128` instead of `129`** (Lemma 2.2 uses
  `τ* = min{t' : ∑ φ_i ≥ 129 vol(s_t̂)/d_min}`): the shared drift lemma
  `Dynamics.Kernel.drift_absorption` gives `4 · 32 = 128`, which is stronger. The statements
  read "for every `T` with `128 vol ≤ d_min φ T`, `P(no consensus at time T) ≤ 1/2`", which is
  `P(T_cons ≤ T) ≥ 1/2` because consensus is absorbing; no stopping times or path space are
  used. The paper's "with a probability of 1/2" is read as "at least 1/2".
* **Theorem 1.1 (i), static graph, two opinions, explicit constant:** `128 m / (d_min φ)`
  ([`lazy_consensus_conductance`](Voter/ConductanceTime.lean), from `vol(minority) ≤ m`). The
  alternative bound `n log n / φ²` (part (ii), Lemma 2.4) is in §5.5.
* **Expected time** ([`lazy_expected_consensus_time`](Voter/ConductanceTime.lean)) is stated
  as `∑_{t < N} P(T_cons > t) ≤ 2 T₀` for every horizon `N`, i.e. `𝔼[min(T_cons, N)] ≤ 2 T₀`,
  which gives `𝔼[T_cons] ≤ 2 T₀` by monotone convergence. A `tsum` statement would be vacuous
  for non-summable series (`∑' = 0` in Mathlib).
* **No connectivity hypothesis; `hd : ∀ v, 0 < G.degree v` instead.** `hd` is needed to define
  the lazy voter, as in §3. Connectivity is not needed: a disconnected graph without isolated
  vertices has `φ = 0` (a component of volume `≤ m` has an empty cut), so the hypotheses force
  `m = 0` and the statements are vacuous.
* **Conductance** ([`conductance`](Voter/Conductance.lean)) is the paper's formula, with
  `∑_{u ∈ U} λ_u` written as `#(G.interedges U Uᶜ)` (Mathlib's ordered pairs `(u, w)` with
  `u ∈ U`, `w ∉ U` adjacent: one per cut edge). Convention `φ = 0` when no `U` has
  `0 < vol U ≤ m` (only for graphs without edges).
* **Two opinions** are `Bool`, `false` being the paper's opinion `0`, which wins ties in
  [`minority`](Voter/Conductance.lean).

### 5.3 Dynamic graphs
* [`dynamic_consensus_conductance`](Voter/ConductanceTime.lean) (Lemma 2.2 on dynamic graphs)
  is stated for two opinions (the generality of Lemma 2.2, not of Theorem 1.1's `κ`).
* The adversary chooses the graph `G t x` from the time and the **current** configuration,
  not from the whole history as in the paper: a history-dependent adversary is not a kernel on
  configurations. The kernel is [`dynamicLazy`](Voter/Conductance.lean).
* The degrees are fixed (`hdeg`, relative to the first graph `G 0 s`; the paper fixes a degree
  sequence `d_1, …, d_n`), and `φ t` must bound the conductance of every graph the adversary
  may use at time `t` (the paper fixes the sequence `φ_t` in advance). `vol(s_0)` and `d_min`
  are computed in `G 0 s` (they only depend on the degrees). In
  `dynamic_consensus_conductance`, `φ t` may be negative, which only weakens the hypothesis; the
  statements of §5.5 square `φ t` and require `0 ≤ φ t` (the paper's `φ_t` is a conductance).
* The start time is `t̂ = 0`; a later start is the same statement for the shifted family
  `fun t => G (t̂ + t)`.

### 5.4 Many opinions
* [`lazy_expected_consensus_time_many`](Voter/ConductanceMany.lean) and
  [`lazy_consensus_conductance_many`](Voter/ConductanceMany.lean) (Theorem 1.1 (i) for any
  number of opinions) are for static graphs, with an existential constant `∃ b` (the paper:
  "`b > 0` a suitably chosen constant"); the proofs give `b = 7000` (expectation) and
  `b = 14000` (probability `1/2`). The expectation form corresponds to the paper's
  `𝔼[T] ≤ b m / (4 d_min)` (in phases) in the proof of part (i).
* `[Nonempty V]` is assumed: with `V` and the colour type both empty, the empty configuration
  has no consensus colour in the convention of `disagreement`, while the hypothesis `b · 0 ≤ 0`
  holds. The paper's "`κ ≤ n` opinions" is automatic (any finite colour type; only the
  opinions present matter).
* The phase argument of Lemma 2.3 is organized by levels `θ_j = n (5/6)^j` of the number of
  opinions present, with an occupation-time bound per level
  ([`sum_iterate_le_of_block`](Voter/ConductanceLevels.lean)) instead of expected numbers of
  phases.

### 5.5 The bound `n log n / φ²` (Theorem 1.1 (ii), Lemma 2.4)
Files: [`ConductanceSq.lean`](Voter/ConductanceSq.lean),
[`ConductanceSqAux.lean`](Voter/ConductanceSqAux.lean).
* **The multiplicative drift** ([`potential_drift_mul`](Voter/ConductanceSq.lean),
  `𝔼 Ψ' ≤ (1 - φ²/(32n)) Ψ` from every two-opinion configuration) is derived from the corrected
  Lemma 2.1 of §5.1 (sum over the minority side). The proof of Lemma 2.4 starts from the printed
  form of Lemma 2.1 (sum over all of `V`) but immediately restricts the sum to the minority side
  `v^(0)`, so the corrected form is exactly what it needs. Cauchy–Schwarz is applied over the
  minority side, which has at most `n` vertices, as in the paper.
* **Lemma 2.4 needs a minor correction to its statement:** it prints
  `Pr(T ≤ τ') ≥ 1/n²`, while its proof and its own static special case give
  `Pr(T ≤ τ') ≥ 1 - 1/n²`. The formalized statements
  ([`lazy_consensus_conductance_sq`](Voter/ConductanceSq.lean),
  [`dynamic_consensus_conductance_sq`](Voter/ConductanceSq.lean)) read: for every `T` with
  `96 n ln n ≤ φ² T` (static) or `96 n ln n ≤ ∑_{t < T} φ_t²` (dynamic), the opinions still
  disagree at time `T` with probability at most `1/n²`.
* **A minor correction to the proof of Lemma 2.4:** the recursion display ends with
  `Ψ_0 exp(+∑ φ_i² / (32n))`; the sign of the exponent must be negative. The formal proof uses
  `1 - x ≤ e^{-x}` factor by factor ([`prod_one_sub_le`](Voter/ConductanceSqAux.lean)) instead of
  the arithmetic–geometric mean step, and the multiplicative drift lemma of the shared library
  (`Dynamics.Kernel.multiplicative_drift_seq`) for `P(Ψ_T > 0) ≤ 𝔼 Ψ_T` (using `Ψ ≥ 1` before
  consensus, [`one_le_potential`](Voter/ConductanceSqAux.lean)).
* **Constants:** `b = 96` and the natural logarithm, as in the static statement of Lemma 2.4
  ("`96 n log n / φ²`"); the computation `Ψ_0 e^{-3 ln n} ≤ n · n^{-3}` uses the natural
  logarithm (`Ψ_0 ≤ √m ≤ n`, [`potential_le_card`](Voter/ConductanceSqAux.lean)). Rounds are
  `t < T`, as in §5.2.
* **Any number of opinions** ([`lazy_consensus_conductance_sq_many`](Voter/ConductanceSq.lean),
  [`dynamic_consensus_conductance_sq_many`](Voter/ConductanceSq.lean)): probability at most `1/n`
  of disagreement, the paper's `Pr(T(κ) ≤ τ') ≥ 1 - 1/n`, by the paper's union bound over the
  projections "`i` against the rest". Unlike part (i) (§5.4), this covers dynamic graphs too. There
  the adversary sees the whole configuration, so the projected process is not itself a dynamic
  two-opinion voter of §5.3; the proof therefore runs the multiplicative drift on the full process
  with the observable `Ψ(projection)`, using that one round commutes with the projection on
  whatever graph the adversary chooses. The union bound is over all colours, those absent at time
  `0` contributing nothing, so at most `n` terms count. `[Nonempty V]` is assumed for the reason
  of §5.4.
* **Expected time** ([`lazy_expected_consensus_time_sq`](Voter/ConductanceSq.lean), static
  graphs, any number of opinions): `∑_{t < N} P(T_cons > t) ≤ 2 T₀` when
  `96 n ln n ≤ φ² T₀`, by restarting, as in §5.2.
* **Theorem 1.1 with both parts** ("`T ≤ min{τ, τ'}` with probability `1/2`") is stated as: if
  `T` satisfies the threshold of part (i) or that of part (ii), the opinions disagree at time `T`
  with probability at most `1/2`; since both sums are nondecreasing in `T`, this is the paper's
  `min`. On static graphs, for any number of opinions and with an existential constant `b`
  ([`lazy_consensus_conductance_min`](Voter/ConductanceSq.lean); the proof gives
  `b = max(b₁, 96)` with `b₁` the constant of part (i)). On dynamic graphs only for two opinions
  ([`dynamic_consensus_conductance_min`](Voter/ConductanceSq.lean), constants `128` and `96`),
  since part (i) with many opinions is formalized for static graphs only (§5.4); its hypothesis
  `0 ≤ φ t` is needed by part (ii) and also restricts the part (i) branch.
