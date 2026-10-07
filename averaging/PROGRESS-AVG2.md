# PROGRESS: AVG-2, strong reconstruction by averaging

Source: Becchetti, Clementi, Natale, Pasquale, Trevisan, *Find your place: simple distributed
algorithms for community detection*, SODA 2017; SIAM J. Comput. 49(4), 2020 (arXiv:1511.03927,
v-latest fetched 2026-10-07). Relevant parts: Section 2 (protocol, `P`, `χ`, `λ`), Definition 3.1,
Theorem 3.2 and its proof (inequality (3)), Observation A.3, Lemma B.1, Lemma C.1.

## Status

**Phase 1 (pin statements): done. Phase 2 (proofs): done (2026-10-07).** All 10 pinned theorems
are proved; `lake build Averaging` is warning-free; `#print axioms` on every pinned declaration
(scratch file under `/tmp`, and `python3 ../scripts/check_axioms.py` on the extended `Audit.lean`)
gives only `propext`, `Classical.choice`, `Quot.sound`. No pinned statement turned out to be false.

## Pinned (see `PINNED.txt` at the repository root)

`Averaging/ReconstructionDefs.lean` (definitions; no `sorry`):
* `IsBalancedPartition V₁ V₂ n`: `V₁`, `V₂` partition the nodes and `|V₁| = |V₂| = n`.
* `IsClusteredRegular G V₁ V₂ n d b` (Definition 3.1): extends the above; `G` is `d`-regular,
  each node of `V₁` has exactly `b` neighbours in `V₂` and vice versa.
* `clusterIndicator V₁ V₂ = 𝟙_{V₁} - 𝟙_{V₂}` (`χ`).
* `transitionMatrix G d = (d : ℝ)⁻¹ • G.adjMatrix ℝ` (`P`) and `transitionMatrix_isHermitian`
  (proved; needed to define `λ`).
* `maxAbsOtherEigenvalue G d = ⨆ i : {i : Fin (card V) // 2 ≤ i}, |eigenvalues₀ i|` (`λ`), with
  Mathlib's decreasingly sorted `Matrix.IsHermitian.eigenvalues₀`.
* `color G x t v = decide (x⁽ᵗ⁻¹⁾ v ≤ x⁽ᵗ⁾ v)` (blue = `true`), `x⁽ᵗ⁾ = avgIter G t x` (AVG-1).
* `IsStrongReconstruction V₁ V₂ f := Disjoint (V₁.image f) (V₂.image f)`.
* `reconstructionTime n δ = ⌈log (4 n³) / log (1 + δ)⌉₊ + 1` (`T(n, δ)`).

`Averaging/Reconstruction.lean` (theorems, all `sorry`):
1. `avgIter_eq_transitionMatrix_pow_mulVec`: `d`-regular ⇒ `avgIter G t x = Pᵗ *ᵥ x`.
2. `transitionMatrix_mulVec_clusterIndicator` (Obs. A.3): `0 < d` ⇒ `P χ = (1 - 2b/d) χ`.
3. `abs_avgIter_sub_le` (Lemma C.1): `0 < d`, `λ < 1 - 2b/d`, `x ∈ {±1}^V` ⇒
   `|x⁽ᵗ⁾(v) - (⟨x,𝟙⟩/2n + ⟨x,χ⟩/2n · (1-2b/d)ᵗ · χ(v))| ≤ λᵗ √(2n)`.
4. `sign_avgIter_sub_eq` (Thm 3.2, deterministic core): connected, `0 < δ`,
   `(1+δ)λ < 1 - 2b/d`, `x ∈ {±1}^V`, `⟨x,χ⟩ ≠ 0`, `T(n,δ) ≤ t` ⇒
   `sign (x⁽ᵗ⁻¹⁾ u - x⁽ᵗ⁾ u) = sign (⟨x,χ⟩ · χ u)`.
5. `exists_sign_avgIter_sub_clusters`: same hypotheses ⇒ `∃ s ≠ 0`, for all `t ≥ T`, the sign is
   `s` on `V₁` and `-s` on `V₂`.
6. `isStrongReconstruction_color`: same hypotheses ⇒ `color G x t` is a strong reconstruction.
7. `reconstructionTime_le`: `2 ≤ n`, `0 < δ ≤ 1` ⇒ `T(n, δ) ≤ 10 log n / δ + 2`.
8. `prob_dotProduct_clusterIndicator_eq_zero` (Lemma B.1, exact): for `σ` uniform on `V → ℤˣ`,
   `P(⟨σ, χ⟩ = 0) = C(2n, n) / 4ⁿ`.
9. `choose_div_four_pow_le`: `0 < n` ⇒ `C(2n, n) / 4ⁿ ≤ 1 / √(π n)`.
10. `strong_reconstruction` (Thm 3.2): connected, `0 < δ`, `(1+δ)λ < 1 - 2b/d` ⇒
    `1 - 1/√(π n) ≤ P(∀ t ≥ T(n, δ), color is a strong reconstruction)`.

## Proved

Everything. Pinned theorems in `Reconstruction.lean` are one-line applications of helpers:

| Pinned theorem | Helper (file) |
| --- | --- |
| `avgIter_eq_transitionMatrix_pow_mulVec` | `avgIter_eq_pow_mulVec` (Matrix) |
| `transitionMatrix_mulVec_clusterIndicator` | `transitionMatrix_mulVec_clusterIndicator_aux` (Matrix) |
| `abs_avgIter_sub_le` | `abs_avgIter_sub_le_aux` (Decomp) |
| `sign_avgIter_sub_eq` | `sign_avgIter_sub_eq_aux` (Sign) |
| `exists_sign_avgIter_sub_clusters` | `exists_sign_avgIter_sub_clusters_aux` (Sign) |
| `isStrongReconstruction_color` | `isStrongReconstruction_color_aux` (Sign) |
| `reconstructionTime_le` | `reconstructionTime_le_aux` (Count) |
| `prob_dotProduct_clusterIndicator_eq_zero` | `prob_dotProduct_clusterIndicator_eq_zero_aux` (Count) |
| `choose_div_four_pow_le` | `choose_div_four_pow_le_aux` (Count) |
| `strong_reconstruction` | `strong_reconstruction_aux` (Count) |

Files (import chain Defs → Spectral, Matrix → Decomp → Sign → Count → Reconstruction):
* `ReconstructionDefs.lean` (84 lines, pinned definitions).
* `ReconstructionSpectral.lean` (208 lines), generic, reusable for any real symmetric matrix:
  `eigvec` (Mathlib's `eigenvectorBasis` as plain vectors), `eigvec_dotProduct_eigvec`,
  `sum_dotProduct_smul_eigvec` (expansion), `sum_dotProduct_mul_dotProduct` (Parseval),
  `eigvec_dotProduct_pow_mulVec`, `pow_mulVec_dotProduct_self_le` (contraction),
  `card_filter_lt_abs_eigenvalues_le_two`, `eigvec_dotProduct_eq_zero_of_mulVec_eq_smul`,
  projection residual and Bessel (in)equality on `span {u₁, u₂}`, and the key
  `pow_mulVec_dotProduct_self_le_of_orthogonal`.
* `ReconstructionMatrix.lean` (147 lines): `IsBalancedPartition` API (`card_eq`, `mem_or`, values
  of `χ`, `⟨𝟙,𝟙⟩ = ⟨χ,χ⟩ = 2n`, `⟨𝟙,χ⟩ = 0`), `avgStep_eq_transitionMatrix_mulVec`,
  `avgIter_eq_pow_mulVec`, `transitionMatrix_mulVec_one`, Obs. A.3,
  `pow_mulVec_of_mulVec_eq_smul`, `maxAbsOtherEigenvalue_nonneg`,
  `abs_eigenvalues₀_le_maxAbsOtherEigenvalue`.
* `ReconstructionDecomp.lean` (100 lines): Lemma C.1.
* `ReconstructionSign.lean` (263 lines): `one_le_cross` (connectivity ⇒ `b ≥ 1`),
  `cross_le_degree`, `degree_lt_two_mul`, `dotProduct_clusterIndicator_eq` (`⟨x,χ⟩ = 2(k - n)`),
  `two_le_abs_dotProduct`, `four_mul_cube_le_one_add_pow`, `sign_add_eq_of_abs_lt`,
  `sign_sub_eq_of_bounds` (real-arithmetic core of (3)), the three deterministic forms.
* `ReconstructionCount.lean` (217 lines): `card_filter_dotProduct_eq_zero` (bijection with
  `powersetCard n univ`), exact probability, Wallis bound, time bound, `one_sub_prob_le_prob`
  (reusable: `¬s ⇒ s'` gives `1 - P(s) ≤ P(s')` for `Dynamics.Distribution`), final theorem.
* `Reconstruction.lean` (131 lines): the pinned statements.

Also updated: `Audit.lean` (+11 `#print axioms`), `README.md` (AVG-2 section and paper ↔ Lean
table), `blueprint/src/content.tex` (section "Strong reconstruction").

## Remaining

Nothing for AVG-2. Possible follow-ups: move the generic spectral lemmas and
`one_sub_prob_le_prob` to `dynamics/` (not allowed in this job: only `averaging/` may change);
update the AVG-2 row of `ROADMAP.md` (outside `averaging/`).

## Errors / blockers

None.

## Sanity checks done in phase 1 (outside the repository, not part of the build)

Exact rational arithmetic (Python, integer vectors `Aᵗ x`) on two `K₅` joined by a perfect matching
(`n = d = 5`, `b = 1`, `λ = 2/5`, `δ = 0.4`, `T = 20`, all 1024 inputs) and on four random connected
clustered regular graphs (`n` up to 20): the Lemma C.1 bound holds (worst ratio 0.51), the sign
claim holds for all `t ≥ T` (in fact already from round 8–9). Numerically,
`C(2n,n)/4ⁿ ≤ 1/√(πn)` for `n < 3000` and `T(n,δ) ≤ 10 log n/δ + 2` on a sweep. In Lean:
`0 ≤ λ` and `|eigenvalues₀ i| ≤ λ` for `i ≥ 2` follow from `Real.iSup_nonneg`, `le_ciSup`.

## Proof notes (phase 2)

The plan of phase 1 worked as written, with one simplification for Lemma C.1: instead of a
dimension argument, Bessel's equality. With `K = {j : |νⱼ| > λ}` (at most 2 elements by the sorted
spectrum), every eigenvector `wⱼ`, `j ∉ K`, is orthogonal to `𝟙` and `χ` (distinct eigenvalues), so
Parseval gives `∑_{j∈K} (⟨wⱼ,𝟙⟩² + ⟨wⱼ,χ⟩²) = 4n`, while Bessel gives each term `≤ 2n`; hence each
`wⱼ`, `j ∈ K`, lies in `span {𝟙, χ}` and is orthogonal to `y = x - α₁𝟙 - α₂χ`. Only the bound
`|eigenvalues₀ i| ≤ λ` for `i ≥ 2` is used, not the full sortedness.

## Deviations from the paper

1. **Simple graphs.** `G : SimpleGraph V` (no multi-edges or self-loops; the paper's Section 2
   allows them), to reuse AVG-1's `avgStep`/`avgIter` and Mathlib's `adjMatrix`.
2. **Clusters as finsets** `V₁ V₂ : Finset V` of a finite vertex type with an
   `IsBalancedPartition` hypothesis, instead of the vertex set `V₁ ∪ V₂`.
3. **Transition matrix** `P = (1/d) A` with `d` a parameter (Section 3's form); it equals
   Section 2's `D⁻¹A` for `d`-regular graphs, the only case used.
4. **`λ`** is defined from Mathlib's sorted spectrum `eigenvalues₀` (`λ₁ ≥ λ₂ ≥ ⋯`, with
   multiplicity) as the supremum of `|λᵢ|`, `i ≥ 3`, and is `0` when `2n ≤ 2` (the paper's maximum
   over an empty set is undefined).
5. **Explicit number of rounds**, uniform in `x`: `T(n, δ) = ⌈log(4n³)/log(1+δ)⌉ + 1` instead of
   the paper's per-instance `t - 1 ≥ log(2√(2n)/(|α₂|(1-λ₂))) / log(λ₂/λ)` and "`O(log n)`
   rounds". It follows from the paper's condition with `|α₂| ≥ 1/n` (`⟨x,χ⟩` even and nonzero),
   `1 - λ₂ = 2b/d` with `b ≥ 1`, `d < 2n`, and `λ₂/λ > 1 + δ`; the paper's form is also undefined
   when `λ = 0`. The order `O(log n / δ)` is the separate `reconstructionTime_le`.
6. **"w.h.p." made explicit**: probability at least `1 - 1/√(πn)`, from the exact count
   `P(⟨x,χ⟩ = 0) = C(2n,n)/4ⁿ` (the roadmap hint), instead of the paper's Lemma B.1
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
    paper's `x⁽ᵗ⁾ = Pᵗx` (Section 2) is pinned as a bridge to AVG-1.
