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
