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
| **Lemma 2.1** | Consensus states absorbing & nonconsensus survival vanishes | [`Voter.transition_constant`](Voter/Absorption.lean#L34), [`Voter.consensus_tendsto`](Voter/Absorption.lean#L91) | [Voter/Absorption.lean](Voter/Absorption.lean) |
| **Lemma 2.3** | Expected stationary weight invariance (martingale) | [`Voter.round_mass`](Voter/Model.lean#L101), [`Voter.iterate_mass`](Voter/Model.lean#L115) | [Voter/Model.lean](Voter/Model.lean) |
| **Lemma 2.2** | Finite-time discrepancy bound & limit of white probability | [`Voter.whiteMass_bounds`](Voter/Main.lean#L101), [`Voter.whiteProbability_error`](Voter/Main.lean#L117), [`Voter.whiteProbability_tendsto`](Voter/Main.lean#L132) | [Voter/Main.lean](Voter/Main.lean) |
| **Theorem 2.1** | Eventual all-white absorption probability $\rho_{s1} = \sum_{i \in W_s} \pi_H(i)$ | [`Voter.consensus_probability`](Voter/Main.lean#L144) | [Voter/Main.lean](Voter/Main.lean) |
| **Corollary 2.2** | Degree weights are stationary; uniform consensus probability $\sum_{i \in W_s} \frac{d_i}{2m}$ | [`Voter.degree_stationary`](Voter/Uniform.lean#L43), [`Voter.uniform_consensus_probability`](Voter/Corollaries.lean#L26) | [Voter/Uniform.lean](Voter/Uniform.lean), [Voter/Corollaries.lean](Voter/Corollaries.lean) |
| **Section 4.3.1** | Consensus on $d$-regular graph equals initial white fraction $x/n$ | [`Voter.regular_consensus_probability`](Voter/Corollaries.lean#L36) | [Voter/Corollaries.lean](Voter/Corollaries.lean) |
| **Section 2.3** | Many colors: projections commute with dynamics | [`Voter.step_project`](Voter/Model.lean#L24), [`Voter.iterate_project`](Voter/Colors.lean#L10), [`Voter.colorProbability_project`](Voter/Colors.lean#L37) | [Voter/Model.lean](Voter/Model.lean), [Voter/Colors.lean](Voter/Colors.lean) |
| **Section 2.3** | Many colors: consensus probability $\rho_{sc} = \sum_{i \in A_c^s} \pi_H(i)$ | [`Voter.color_consensus_probability`](Voter/Colors.lean#L51), [`Voter.sum_color_consensus_probability`](Voter/Colors.lean#L61) | [Voter/Colors.lean](Voter/Colors.lean) |
| **Figure 1** | Bipartite 2-cycle alternating coloring flips and cycles without consensus | [`Voter.Examples.twoVertex_flip`](Voter/Examples.lean#L65), [`Voter.Examples.twoVertex_cycle`](Voter/Examples.lean#L68), [`Voter.Examples.twoVertex_never_consensus`](Voter/Examples.lean#L72) | [Voter/Examples.lean](Voter/Examples.lean) |

---

### 1.2 Unformalized Results

The following portions of the paper were not formalized:
1. **Section 2.4: Time Bounds** (partially formalized since VOT-3: on the complete graph with
   self-loops, the backward coalescing-walk duality [`runRounds_eq_comp`](Voter/Coalescence.lean) and
   consensus within `2 n log n` rounds with probability `≥ 1 - 1/n`
   [`voter_consensus_whp`](Voter/Coalescence.lean); the general-graph bounds below remain open)
   - Dual coalescing random walks backward in time on general graphs (the complete graph with self-loops is formalized in [`Coalescence.lean`](Voter/Coalescence.lean)).
   - Lemma 2.4: Bound on meeting time $M = O(n Z_{\max})$.
   - Fact 2.3: Hitting time sum $Z_{i,j} + Z_{j,i} \le 1 / (\pi_H(i) h_{ij})$ for reversible Markov chains.
   - Theorem 2.4: Expected time to monochromatic absorption $O(M \log n)$ via Chernoff bounds (Proposition 2.1).
   - Theorem 2.5: Convergence time $O(n^3 \log n)$ in the uniform case.
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
  That is, consensus is reachable in **some** color $c \in \{\text{true}, \text{false}\}$ (the color of the monochromatic edge found by [`monochromatic_edge`](Voter/Graph.lean#L18)). This suffices to prove that the probability of staying in non-consensus states decays to 0 ([`consensus_tendsto`](Voter/Absorption.lean#L91)), fixing the paper's informal leap.

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
  Since consensus states are absorbing fixed points ([`transition_constant`](Voter/Absorption.lean#L34)), $n \mapsto \text{colorProbability } H\ c\ n\ s$ is monotone increasing ([`colorProbability_mono`](Voter/Main.lean#L46)) and converges to its supremum ([`colorProbability_tendsto`](Voter/Main.lean#L65)). This gives a fully constructive and rigorous definition using only standard real analysis.

---

### 2.3 Reordering of Lemma 2.2 and Lemma 2.3
* **Paper structure**:
  1. **Lemma 2.2** is stated first: $\lim_{t \to \infty} \mathbb{E}_s(\pi_H(S_t)) = \rho_{s1}$. Its proof decomposes the expectation over the state space $\mathcal{S} = \{0, 1\}^n$:
     $$\mathbb{E}_s(\pi_H(S_t)) = \sum_{a \notin \{0, 1\}} \pi_H(a) \mathbb{P}_s(S_t = a) + 0 \cdot \mathbb{P}_s(S_t = 0) + 1 \cdot \mathbb{P}_s(S_t = 1)$$
     and relies on transient state probabilities tending to 0 while $\mathbb{P}_s(S_t = 1) \to \rho_{s1}$.
  2. **Lemma 2.3** is proved second: $\forall t \ge 0, \mathbb{E}_s(\pi_H(S_t)) = \sum_{i \in W_s} \pi_H(i)$ (martingale property).
  3. **Theorem 2.1** equates the two limits.
* **Lean structure**:
  1. **Lemma 2.3** ([`round_mass`](Voter/Model.lean#L101), [`iterate_mass`](Voter/Model.lean#L115)) is proved **first** in `Model.lean`.
  2. **Lemma 2.2** is then formalized in `Main.lean` through explicit error bounds:
     - [`whiteMass_bounds`](Voter/Main.lean#L101): $\mathbf{1}_{\{s=\mathbf{1}\}} \le \text{whiteMass } p\ s \le \mathbf{1}_{\{s=\mathbf{1}\}} + \text{survival } s$.
     - [`whiteProbability_error`](Voter/Main.lean#L117): sandwiching the difference:
       $$0 \le \text{whiteMass } p\ s - \text{colorProbability } H\ \text{true } n\ s \le (transition\ H)^n (\text{survival})(s)$$
     - [`whiteProbability_tendsto`](Voter/Main.lean#L132): by squeezing with [`consensus_tendsto`](Voter/Absorption.lean#L91), $\text{colorProbability } n \to \text{whiteMass}$.
  3. **Theorem 2.1** ([`consensus_probability`](Voter/Main.lean#L144)) identifies the limit with `eventualColor`.
* **Rationale**:
  This rearrangement avoids summing over the exponential state space $\mathcal{S}$ and avoids having to classify recurrent/transient states in full generality.

---

### 2.4 Generalization of Lemma 2.3 (No Graph Assumptions)
* **In the paper**:
  Lemma 2.3 is stated under the standing hypotheses of Section 2.1 (connected, nonbipartite, undirected graph).
* **In Lean**:
  [`round_mass`](Voter/Model.lean#L101) and [`iterate_mass`](Voter/Model.lean#L115) are generalized:
  - They require **no graph structure** at all, holding for any stochastic transition kernel `H : Kernel V`.
  - They require no connectivity, nonbipartiteness, or symmetry.
  - They hold for any real-valued observable $f : C \to \mathbb{R}$ on any finite color palette $C$, not just Boolean indicators.

---

### 2.5 Stationary Distribution: Existence vs. Uniqueness
* **In the paper (page 253)**:
  The authors cite Motwani & Raghavan [MR95] asserting that for a strongly connected graph, there exists a *unique* stationary distribution $\pi_H$.
* **In Lean**:
  - **Uniqueness is not needed**: Theorem 2.1 ([`consensus_probability`](Voter/Main.lean#L144)) is parameterized by *any* stationary distribution `p` (`hp : H.Stationary p`). Because the LHS (`eventualColor`) does not depend on `p`, any stationary distribution must yield identical mass on Boolean indicators.
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
