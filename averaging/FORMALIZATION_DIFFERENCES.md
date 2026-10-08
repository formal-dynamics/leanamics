# Formalization differences

Where the statements of `averaging/` deviate from their sources, and why.

## Strong reconstruction by averaging (`Reconstruction`, AVG-2)

Source: Becchetti, Clementi, Natale, Pasquale, Trevisan, *Find your place: simple distributed
algorithms for community detection*, SODA 2017; SIAM J. Comput. 49(4), 2020
([arXiv:1511.03927](https://arxiv.org/abs/1511.03927)): Section 2 (protocol, `P`, `χ`, `λ`),
Definition 3.1, Theorem 3.2 and its proof (inequality (3)), Observation A.3, Lemma B.1, Lemma C.1.

1. **Simple graphs.** `G : SimpleGraph V` (no multi-edges or self-loops; the paper's Section 2
   allows them), to reuse the package's `avgStep`/`avgIter` (`Averaging.Basic`) and Mathlib's
   `adjMatrix`.
2. **Clusters as finsets** `V₁ V₂ : Finset V` of a finite vertex type with an
   `IsBalancedPartition` hypothesis, instead of the vertex set `V₁ ∪ V₂`.
3. **Transition matrix** `P = (1/d) A` with `d` a parameter (Section 3's form); it equals
   Section 2's `D⁻¹A` for `d`-regular graphs, the only case used.
4. **`λ`** is defined from Mathlib's sorted spectrum `eigenvalues₀` (`λ₁ ≥ λ₂ ≥ ⋯`, with
   multiplicity) as the supremum of `|λᵢ|`, `i ≥ 3`, and is `0` when `2n ≤ 2` (the paper's maximum
   over an empty set is undefined). The proofs only use `|λᵢ| ≤ λ` for `i ≥ 3`, not the full
   sortedness.
5. **Explicit number of rounds**, uniform in `x`: `T(n, δ) = ⌈log(4n³)/log(1+δ)⌉ + 1` instead of
   the paper's per-instance `t - 1 ≥ log(2√(2n)/(|α₂|(1-λ₂))) / log(λ₂/λ)` and "`O(log n)`
   rounds". It follows from the paper's condition with `|α₂| ≥ 1/n` (`⟨x,χ⟩` even and nonzero),
   `1 - λ₂ = 2b/d` with `b ≥ 1` (connectivity), `d < 2n`, and `λ₂/λ > 1 + δ`; the paper's form is
   also undefined when `λ = 0`. The order `O(log n / δ)` is the separate `reconstructionTime_le`.
6. **"w.h.p." made explicit**: probability at least `1 - 1/√(πn)`, from the exact count
   `P(⟨x,χ⟩ = 0) = C(2n,n)/4ⁿ`, instead of the paper's Lemma B.1
   (`P(|⟨w,x⟩|/√(2n) ≤ δ) ≤ O(δ)`, used for `|α₂| ≥ n^{-γ}`). Only `⟨x,χ⟩ ≠ 0` is needed because
   nonzero values are automatically at least `2` in absolute value. So "w.h.p." here means
   `1 - O(n^{-1/2})`.
7. **Rademacher initialization** as `Dynamics.Distribution.uniform (V → ℤˣ)` (`ℤˣ = {-1, 1}`, cast
   to `ℝ`): the uniform distribution on `{-1,1}^{2n}`, i.e. independent uniform signs.
8. **Lemma C.1 and Observation A.3** carry the hypothesis `0 < d`, implicit in the paper
   (`P = (1/d)A`); both are false in Lean for `d = 0`, where `P = 0`. Lemma C.1 names
   `α₁ = ⟨x,𝟙⟩/2n`, `α₂ = ⟨x,χ⟩/2n` explicitly (the paper says "there are reals" and defines them
   in the proof) and is stated pointwise (`‖e⁽ᵗ⁾‖_∞` as a bound at every node).
9. **Strong reconstruction** is defined directly as `f(V₁) ∩ f(V₂) = ∅`, the paper's `ε`-weak
   reconstruction with `ε = 0` (which forces `Wᵢ = Vᵢ`); it is proved at every round `t ≥ T`
   (the paper: "within `O(log n)` rounds").
10. **Colors** are `Bool`, `true` = blue (`x⁽ᵗ⁾(v) ≥ x⁽ᵗ⁻¹⁾(v)`), `false` = red.
11. **Deterministic core** is stated as `sgn(x⁽ᵗ⁻¹⁾(u) - x⁽ᵗ⁾(u)) = sgn(⟨x,χ⟩ χ(u))`, the
    paper's `sgn(α₂ χ(u))` (same sign, `α₂ = ⟨x,χ⟩/2n`), plus cluster and coloring forms; the
    paper's `x⁽ᵗ⁾ = Pᵗx` (Section 2) is a separate bridge lemma,
    `avgIter_eq_transitionMatrix_pow_mulVec`, between `avgIter` and the matrix form.
12. **Proof of Lemma C.1** uses equality in Bessel's inequality instead of a dimension argument:
    with `K = {j : |νⱼ| > λ}` (at most 2 elements), every eigenvector `wⱼ`, `j ∉ K`, is orthogonal
    to `𝟙` and `χ` (distinct eigenvalues), so Parseval gives
    `∑_{j∈K} (⟨wⱼ,𝟙⟩² + ⟨wⱼ,χ⟩²) = 4n` while Bessel bounds each term by `2n`; hence each `wⱼ`,
    `j ∈ K`, lies in `span {𝟙, χ}` and is orthogonal to `x - α₁𝟙 - α₂χ`.

## Rate bound and sequential averaging (`Rate`, `Sequential`, AVG-1)

Sources: Becchetti, Clementi, Natale, *Consensus Dynamics: An Overview*, ACM SIGACT News 51(1),
2020 (the Survey; open copy hal-02507613), Section 7.1 (Definitions 30, 31), Section 7.2
(footnote 24, Theorems 32 and 33, equations (2) to (5)), Section 7.3.2 (first moment); Lovász,
*Random walks on graphs: a survey*, 1993, Theorem 5.1 (the source of the Survey's Theorem 33);
Boyd, Ghosh, Prabhakar, Shah, *Randomized gossip algorithms*, IEEE Trans. Inf. Theory 52(6),
2006 (BGPS06; the source of equations (4) and (5)).

1. **Simple graphs.** `G : SimpleGraph V` on a finite type (no multi-edges or self-loops, which
   footnote 24 allows), to reuse `avgIter`/`transW` of `Averaging.Basic` and Mathlib's
   `adjMatrix`, `degMatrix`, `lapMatrix`.
2. **Typo in the Survey.** Its Theorem 33 prints `√(d(v)/d(v)) λᵗ`; the correct factor, as in
   Lovász's Theorem 5.1, is `√(d(v)/d(u)) λᵗ`, which is what `abs_walkMatrix_pow_sub_walkStationary_le`
   states. We take `λ = max {|λ₂|, |λₙ|}` as in the Survey: with `min` instead of `max` the bound
   would fail, e.g. on a connected bipartite graph, where `λₙ = -1` and `Pᵗ(u, v)` does not converge.
3. **Theorem 33 under a weaker hypothesis.** Every degree positive (`∀ v, 0 < G.degree v`)
   instead of "connected" (with at least one edge, implicit for a random walk). Connected graphs
   with at least two nodes satisfy it (`Connected.preconnected.degree_pos_of_nontrivial`), so the
   Lean statement implies the source's; the spectral proof does not use connectivity (on a
   disconnected graph without isolated nodes `λ = 1` and the bound is trivial). The same applies
   to `charpoly_walkMatrix` and the averaging corollary. Positive degrees are needed: on one
   isolated node `|P⁰ - π| = 1` but the right-hand side is `0`. (`charpoly_walkMatrix` would also
   hold without this hypothesis, since isolated nodes give zero rows and columns in both `P` and
   `N`; it is kept because every use has it.)
4. **`λ` via the symmetric matrix `N = D^{-1/2} A D^{-1/2}`.** `P = D⁻¹A` is not symmetric, and
   Mathlib's sorted real spectrum `eigenvalues₀` is for Hermitian matrices. `N` is similar to `P`
   (`charpoly_walkMatrix`), so its sorted eigenvalues are those of `P` with multiplicity. `λ` is
   `0` by convention when `n < 2` (there is no `λ₂`).
5. **`m` is the number of edges.** The Survey's notation paragraph (Section 7.1) says
   `m = ∑ᵥ d(v)`, inconsistent with `π(v) = d(v)/2m` summing to `1`; we use `m = |E|`
   (`#G.edgeFinset`), as Lovász does.
6. **"Unless `G` is bipartite, `λ < 1`"** (a sentence after Theorem 33) is stated for connected
   graphs with a closed walk of odd length (that is, non-bipartite), the hypotheses of
   `tendsto_degAvg`. Connectivity is needed: a disconnected graph without isolated nodes (e.g. two
   disjoint triangles) has `λ₂ = 1`.
7. **Averaging corollary.** The Survey has no displayed bound for `Pᵗx`; we state the direct
   consequence of Theorem 33, `|x⁽ᵗ⁾(u) - ∑ᵥ π(v)x(v)| ≤ λᵗ ∑ᵥ √(d(v)/d(u)) |x(v)|`, for every real
   initial vector (Definition 30's `±1` initialization plays no role in this deterministic
   bound). `∑ᵥ π(v)x(v)` equals `degAvg G x` of `Averaging.Basic`.
8. **Bridges.** `walkMatrix_pow_apply` and `avgIter_eq_walkMatrix_pow_mulVec` are the Survey's
   sentences "`Pᵗᵤᵥ` is the probability that a random walk started at `u` is at `v` after `t`
   steps" and "`x⁽ᵗ⁾ = Pᵗ x⁽⁰⁾`", connecting the matrix to `transW`/`avgIter`.
9. **Two edge laws for equations (4) and (5).** The Survey's random sequential model selects one
   oriented edge uniformly at random (Sections 2 and 6.1), for which `𝔼[W] = I - L/(2m)`. Its
   equation (4), taken from BGPS06, is the expected matrix of a different law: a uniformly random
   node `i` contacts `j` with probability `Pᵢⱼ`. The two coincide on regular graphs, which is
   where (5) lives. We state (4) for BGPS06's law with an arbitrary stochastic `P`, given as a
   `Dynamics.Kernel` (`avg_expect_edgeMatrix`; self-loops allowed, `W(i,i) = I`), (5) as its
   specialization to `P = D⁻¹A` on a regular graph (`gossipMeanMatrix_of_isRegular`), and the
   uniform-edge identity with its own form of (5) (`avg_edgeMatrix`, `meanMatrix_of_isRegular`).
10. **Uniform oriented edge = uniform dart**; matrix expectations are entrywise, because
    `Dynamics.avg` and `Distribution.expect` are real-valued. `[Nonempty G.Dart]` (at least one
    edge) is assumed, since the average over an empty type is `0` by the `dynamics/` convention.
    The rounds are i.i.d. via `Dynamics.expList G.Dart`, and `seqRun` applies the first step at the
    head of the list.
11. **Only `δ = 1/2`** (Survey footnote 28, the case of Section 7.2); `Averaging(δ)` for other `δ`
    and the first-activation `±1` initialization of Definition 31 are not modelled: the
    identities hold for every state `x`.
12. **Second-moment identity** (not displayed in the Survey): `𝔼[WᵀW] = 𝔼[W]` (BGPS06, since `W`
    is a symmetric projection), stated in matrix and vector (`𝔼‖Wx‖² = xᵀW̄x`) forms for the
    uniform-edge law, together with the projection identity itself.
13. **First moment for every graph.** Section 7.3.2 states `𝔼[x⁽ᵗ⁾] = W̄ᵗ x` for regular graphs
    with `W̄` from (5); we state it for every graph with an edge, with `W̄ = I - L/(2m)`. On regular
    graphs this is (5) by `meanMatrix_of_isRegular`, which needs `d > 0` (for `d = 0` there are no
    edges and `meanMatrix = 1` in Lean).

## Averaging whenever you meet (`Opportunistic*`, AVG-3)

Source: Becchetti, Clementi, Manurangsi, Natale, Pasquale, Raghavendra, Trevisan, *Average
whenever you meet: opportunistic protocols for community detection*, ESA 2018
([arXiv:1703.05045](https://arxiv.org/abs/1703.05045), numbering of v3): Algorithm 1, equations
(1), (2), (7), (15), Definitions 2.2, 2.3, 4.1, Theorems 3.1 and 4.1, Lemma 4.2, Observation A.2,
Lemma A.1, Lemmas B.1, B.3, B.4, C.1 to C.4.

1. **Uniform edge as a uniform dart.** Each round draws a dart of `G` uniformly (`G.Dart`, the
   core's `EdgeRound`); every edge carries two darts, so this is a uniform edge (`avg_dart_edge`).
   Rounds are i.i.d., with expectations through `Dynamics.expList G.Dart`.
2. **First-activation coins drawn in advance.** The coins `σ : V → ℤˣ` are uniform and
   independent of the edges, as in the paper's deferred-decision argument (Section 3). The protocol
   with first activations is modelled (`oppStep`, `oppRun`: a node holds no value before its first
   activation) and shown to agree with the averaging process started from `σ` at every activated
   node (`oppRun_getD`, `oppRun_isSome_iff`); all later statements are about this averaging
   process `avgRun G (signVec σ)`.
3. **Only `Averaging(1/2)`.** The lazy variant `Averaging(δ)` of Section 5 is not modelled.
4. **`λ₃` as a Rayleigh-quotient lower bound.** `ThirdEigenvalueLB G V₁ d lam3` says
   `zᵀ L z ≥ lam3 · d · ‖z‖²` for `z ⟂ 𝟙, χ`, instead of naming the third eigenvalue of
   `𝓛 = L/d`. On a clustered regular graph `χ` is an eigenvector (eigenvalue `2b/d`), so the
   orthogonal complement of `span{𝟙, χ}` is invariant and the largest admissible `lam3` is the
   least eigenvalue on it, which is the paper's `λ₃` when `λ₃ > 2b/d`. Taking `lam3 = λ₃` gives the
   paper's statements. A smaller admissible `lam3` is also allowed: the hypotheses become stronger
   and the phase moves later and becomes longer, and the theorems still hold. `λ₂` is written as
   `2b/d`, as in the paper.
5. **Explicit constants.** "`λ₂ = o(λ₃/log n)`" (Theorem 4.1) becomes `c λ₂ log n ≤ λ₃`, and "a
   large enough constant `c`" (Lemma 4.2) becomes an existential `c`; the `O(ε)` terms have an
   existential constant `C`. The constants are chosen before the graph, and the theorems are stated
   on `Fin n`. The proofs give `c = 100` for Theorem 4.1, `c = 10⁶` for Lemma 4.2 and the sign
   theorems, `C = 4` for `sign_phase` and `C = 6` for `weakReconstruction_phase`; general versions
   on any finite vertex type are `IsClusteredRegular.secondMoment_bound_aux`, `prob_good_window`,
   `prob_sign_window`, `prob_weakReconstruction_window`. Logarithms are natural.
6. **Theorem 4.1.** The statement is the paper's, `E‖y⁽ᵗ⁾ + z⁽ᵗ⁾ - y⁽⁰⁾‖² ≤ 3λ₂t/n` for
   `3 (n/λ₃) log n ≤ t ≤ n/(4λ₂)`, the expectation being over the initial signs and the edges; the
   proof does not use the upper bound `t ≤ n/(4λ₂)`. The paper's proof needs a minor correction:
   its last step uses `E‖z⁽⁰⁾‖² ≤ 1/n`, while for uniform signs `E‖z⁽⁰⁾‖² = n - 2` (since
   `‖x⁽⁰⁾‖² = n` and `E‖x_∥‖² = E‖y⁽⁰⁾‖² = 1`); the conclusion still holds. Our bookkeeping, for fixed
   signs and with `L = λ₂t/n`, `r = λ₂/λ₃`, `s₀ = ‖y⁽⁰⁾‖²`, is
   `E‖y⁽ᵗ⁾ + z⁽ᵗ⁾ - y⁽⁰⁾‖² ≤ (1 + 2r)(L (1 + 8/n) s₀ + 4r + 4Lr) + n (1 - λ₃/n)ᵗ + 2r s₀`
   (`expList_sum_sq_dev_signVec_le`), from the one-round bounds
   `E‖z'‖² ≤ (1 - λ₃/n)‖z‖² + λ₂β²` (Lemma C.3, via `E‖Wx‖² = xᵀW̄x` and Jensen) and
   `E n(β' - γ)² ≤ (1 - λ₂/n) n(β - γ)² + λ₂γ² + (4λ₂/n²)(nβ² + ‖z‖²)` for every reference `γ`
   (the form of Lemma C.2 used here; `β = ⟨x, χ⟩/n`).
7. **Lemma 4.2 in its non-ephemeral form.** The displayed formula reads "`|B_t| ≤ 3εn` for all `t`
   in the phase"; we state the stronger form that the proof establishes and that the name refers
   to: at least `(1 - 3ε)n` nodes are `ε`-good at *every* round of the phase. The hypotheses
   `ε > 0` and `λ₃ > 0` are explicit. The proof follows the idea of Appendix C.3 (good nodes
   averaged only with good nodes of their own community stay good) with a different accounting.
   The deviation `x_v - (x_∥,v + y⁽⁰⁾_v)` splits into the drift of the cut component up to the start
   `t₁` of the phase, which is the same at every node, and a remainder `r⁽ᵗ⁾` measured from the
   state at `t₁`. A node is good throughout if its remainder is small at `t₁` and every round that
   touches it during the phase is internal with both endpoints small. The expected number of
   other rounds is bounded through the second-moment bounds restarted at `t₁`, and the failure
   probability through Markov's inequality and the anti-concentration of `‖y⁽⁰⁾‖² = (S₁ - S₂)²/n`
   (`avg_le_of_mul_le`, from `P(S = 0) ≤ 1/√(m+1)` and `E[1/|S|; S ≠ 0] ≤ 2(1 + log m)/√(m+1)`).
   This handles the term of order `λ₂/λ₃` in the second moment that is not proportional to
   `‖y⁽⁰⁾‖²` (it comes from `z⁽⁰⁾`), in place of the step (39) of the paper.
8. **Phase and number of rounds.** The phase `6 (n/λ₃) log n ≤ t ≤ 12 (n/λ₃) log n` is stated with
   real inequalities on `t : ℕ`; the process runs for `⌊12 (n/λ₃) log n⌋₊` rounds and `x⁽ᵗ⁾` is the
   state after the first `t` of them.
9. **Sign recovery and weak reconstruction.** The paper has no single numbered statement of the
   form "the sign of the values recovers the communities over the phase"; `sign_phase` and
   `weakReconstruction_phase` state this consequence of Lemma 4.2 and Lemma A.1, as used in
   Section 4.2 and in the proof of Lemma C.7. An `ε`-good node has the sign of its community's
   initial average `2S_h/n` (`S_h` the sum of the signs in community `h`) unless
   `2|S_h| ≤ ε|S₁ - S₂|`, which forces `|S₁| ≤ ε|S₂|` or `|S₂| ≤ ε|S₁|`, each of probability at most
   `ε + 1/√(n/2 + 1)` by independence of the two blocks (the form of Lemma A.1 used here). The two
   averages have opposite signs with probability at least `1/2 - 1/√(n/2 + 1)`, hence the `1/2`.
   Definition 2.3 is stated with labels in `{±1}` (`ℤˣ`); the labelling is `+1` for a positive
   value and `-1` otherwise (a value `0` gets `-1`; good nodes never have value `0` on the event
   considered). The same sets `W₁`, `W₂` work at every round of the phase.
10. **Theorem 3.1 only on clustered regular graphs**, through its finite core: Lemma B.1
    (decomposition, exact since `f_⊥ = 0`), Lemma B.3, Lemma B.4. There the bad set `B_ε` is empty
    and the `ε` of B.3 and B.4 is not needed (we state the `ε → 0` versions, which are stronger).
    The time conditions are in power form (`n³λ̄₃ᵗ ≤ λ̄₂ᵗ`; `nλ̄₃ᵗ ≤ |α₁|` and `2|α₁| < |α₂|λ̄₂ᵗ` for
    the window of B.4), equivalent to the paper's logarithmic form; like the paper's window
    `log(n/|α₁|)`, `sign_criterion` is vacuous when `α₁ = 0`. Not formalized: the almost-regular
    version of Theorem 3.1 (it needs sorted eigenvalues, a chosen second eigenvector of `W̄` and the
    asymptotic notation `o(m)`, `Ω(1)`, `Θ(n log n)`) and Lemma B.5 (only sketched in the paper).
11. **Not formalized:** Theorem 4.3 and Corollary 4.2 (Sign-Labeling with `ℓ` copies and local
    activation counters) and Section 5 (dense cuts, Theorems 5.1 and 5.3, Jump-Labeling).
