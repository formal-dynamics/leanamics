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
