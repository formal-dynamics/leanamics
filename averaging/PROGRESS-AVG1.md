# PROGRESS: AVG-1, rate bound and the random sequential version

Sources:
* **Survey**: Becchetti, Clementi, Natale, *Consensus Dynamics: An Overview*, ACM SIGACT News
  51(1):58–104, 2020, open copy hal-02507613 (fetched 2026-10-07). Section 7.1 (Definitions 30,
  31), Section 7.2 (footnote 24, Theorems 32–33, equations (2)–(5)), Section 7.3.2 (first moment).
* **Lovász**, *Random walks on graphs: a survey*, 1993, Theorem 5.1 (source of Survey Thm 33).
* **BGPS06**: Boyd, Ghosh, Prabhakar, Shah, *Randomized gossip algorithms*, IEEE Trans. Inf.
  Theory 52(6), 2006 (source of equations (4)–(5); `W` a projection, `𝔼[WᵀW] = 𝔼[W]`).

Already done before this job (`Averaging/Basic.lean`): convergence on connected non-bipartite
graphs (`tendsto_degAvg`) and the bipartite counterexample (`not_tendsto_of_colorable`).

## Status

**Phase 1 (pin statements): done. Phase 2 (proofs): done (2026-10-07).** All 26 pinned
declarations are proved; `lake build Averaging` is warning-free and `#print axioms` on every pinned
declaration gives only `propext`, `Classical.choice`, `Quot.sound`. The plan below is kept as a
record of the proof route.

## Pinned (see `PINNED.txt` at the repository root)

`Averaging/RateDefs.lean` (namespace `Averaging`; definitions, no `sorry`):
* `walkMatrix G = diagonal (d⁻¹) * A`: `P = D⁻¹A` (footnote 24).
* `normAdjMatrix G = diagonal (1/√d) * A * diagonal (1/√d)`: `N = D^{-1/2} A D^{-1/2}`, and
  `normAdjMatrix_isHermitian` (proved; needed to define `λ`).
* `walkLambda G = max |eigenvalues₀ 1| |eigenvalues₀ (n-1)|` of `N` (`0` if `n < 2`):
  `λ = max {|λ₂(P)|, |λₙ(P)|}` with Mathlib's decreasingly sorted `eigenvalues₀`.
* `walkStationary G v = d(v) / (2 · #edges)`: `π` (Theorem 32).

`Averaging/Rate.lean` (theorems, all `sorry`):
1. `walkMatrix_pow_apply`: `(Pᵗ) u v = transW G t u v` (the `t`-step walk probability of
   `Basic.lean`).
2. `avgIter_eq_walkMatrix_pow_mulVec`: `avgIter G t x = Pᵗ *ᵥ x` (`x⁽ᵗ⁾ = Pᵗx⁽⁰⁾`).
3. `charpoly_walkMatrix`: all degrees positive ⇒ `charpoly P = charpoly N` (so `walkLambda` is
   computed from the spectrum of `P`, via `sort_roots_charpoly_eq_eigenvalues₀`).
4. `abs_walkMatrix_pow_sub_walkStationary_le` (**Theorem 33**): all degrees positive ⇒
   `|Pᵗ(u,v) - π(v)| ≤ √(d(v)/d(u)) · λᵗ` for all `u, v, t`.
5. `walkLambda_lt_one`: connected and an odd closed walk (non-bipartite) ⇒ `λ < 1`.
6. `abs_avgIter_sub_walkStationary_le` (corollary for averaging): all degrees positive ⇒
   `|x⁽ᵗ⁾(u) - ∑ᵥ π(v) x(v)| ≤ λᵗ · ∑ᵥ √(d(v)/d(u)) |x(v)|`.

`Averaging/SequentialDefs.lean` (namespace `Averaging.Sequential`; definitions, no `sorry`):
* `edgeMatrix i j = 1 - (1/2) • vecMulVec (eᵢ - eⱼ) (eᵢ - eⱼ)`: `W` of equation (2).
* `kernelMatrix K = of fun i j => (K i).weight j`: the stochastic matrix of a `Dynamics.Kernel`.
* `gossipMeanMatrix K = 1 - (2n)⁻¹ • diagonal (∑ⱼ (Pᵢⱼ + Pⱼᵢ)) + (2n)⁻¹ • (P + Pᵀ)`: the
  right-hand side of (4).
* `seqRun G x l = l.foldl (fun y d => edgeMatrix d.fst d.snd *ᵥ y) x`: equation (3), first step
  at the head of the list (as in `expList`).
* `meanMatrix G = 1 - (2m)⁻¹ • L`: `W̄ = I - L/(2m)`.

`Averaging/Sequential.lean` (theorems, all `sorry`):
1. `edgeMatrix_mulVec`: `W x` averages the endpoints `i, j` and keeps the other values.
2. `edgeMatrix_mem_doublyStochastic`: `W ∈ doublyStochastic ℝ V` (remark ii after (3)).
3. `transpose_edgeMatrix_mul_self`: `WᵀW = W`.
4. `avg_expect_edgeMatrix` (**equation (4)**): for every kernel `K` (stochastic `P`),
   `avg_i (K i).expect (j ↦ W(i,j) a b) = gossipMeanMatrix K a b`.
5. `gossipMeanMatrix_of_isRegular` (**equation (5)** from (4)): `kernelMatrix K = P`, `G`
   regular ⇒ `gossipMeanMatrix K = (1 - 1/n) • 1 + (1/n) • P`.
6. `avg_edgeMatrix`: uniform dart (`[Nonempty G.Dart]`) ⇒ `𝔼[W] a b = (I - L/2m) a b`.
7. `meanMatrix_of_isRegular` (**equation (5)**, uniform edge): `d`-regular, `0 < d` ⇒
   `I - L/2m = (1 - 1/n) • 1 + (1/n) • P`.
8. `avg_transpose_edgeMatrix_mul_self` (second moment): `𝔼[WᵀW] a b = (I - L/2m) a b`.
9. `avg_sum_sq_edgeMatrix_mulVec` (second moment on a state): `𝔼 ‖W x‖² = x ⬝ᵥ (W̄ *ᵥ x)`.
10. `expList_seqRun` (first moment, §7.3.2): `expList G.Dart t (seqRun G x · v) = (W̄ᵗ *ᵥ x) v`.

## Proved

* `normAdjMatrix_isHermitian` (`isHermitian_conjTranspose_mul_mul`, `diagonal_conjTranspose`).
* Phase 2: all 10 theorems of `Sequential.lean` (helpers in `Averaging/SequentialMatrix.lean`:
  `edgeMatrix_apply`, `edgeMatrix_transpose`, `edgeMatrix_mul_self`, the weighted sum
  `sum_mul_edgeMatrix_apply` behind both (4) and the uniform-edge identity, `sum_dart`,
  `sum_dart_edgeMatrix_apply`, `sum_sq_edgeMatrix_mulVec`, `avg_edgeMatrix_mulVec_apply`).

## Remaining

All 6 theorems of `Rate.lean` (in progress; helpers in `Averaging/RateMatrix.lean`).

## Errors / blockers

None.

## Sanity checks done in phase 1 (outside the repository, not part of the build)

* Numerically (numpy, script in `/tmp/avg1-check/check.py`, not committed) on 38 graphs (path,
  star, `K₂`, triangle with a tail, two disjoint triangles, `K₄`, `C₅`, Petersen, 30 random graphs
  without isolated nodes): Theorem 33 for `t ≤ 24` and all `u, v` (worst ratio 0.96, attained;
  holds on bipartite and on disconnected graphs too), the averaging corollary, `λ < 1` on
  connected non-bipartite graphs, equal spectra of `P` and `N`, (4) for `P = D⁻¹A` and for a
  random dense stochastic matrix with self-loops, `𝔼[W] = 𝔼[WᵀW] = I - L/2m` for uniform darts,
  (5) for both laws on regular graphs, `𝔼‖Wx‖² = xᵀW̄x`, and `𝔼[x⁽ᵗ⁾] = W̄ᵗx` by exact
  enumeration of all dart sequences for `t ≤ 2`, `W` doubly stochastic.
* In Lean (scratch file, deleted): `edgeMatrix_mulVec`, `walkMatrix_pow_apply`,
  `∑ᵥ walkStationary G v = 1` when there is an edge, and the `n ≥ 2` branch of `walkLambda` all
  proved quickly, so the definitions mean what the docstrings say (proofs below).

* Independent adversarial review (subagent, 2026-10-07): no false, vacuous or unfaithful
  statement; re-checked Theorem 33 numerically on 191 graphs (`t ≤ 29`, worst ratio 0.967),
  (4) on 50 random kernels with self-loops, the first moment for `t ≤ 3`, and the elaborated
  casts and `seqRun` unfolding in Lean. Its three minor doc findings are fixed above. It notes
  that `charpoly_walkMatrix` also holds without `hdeg` (isolated nodes give zero rows and
  columns in both `P` and `N`); the hypothesis is kept, since every use has it and the
  similarity proof needs it.

## Plan (phase 2: proofs; helpers in new `Averaging/Rate*.lean`, `Averaging/Sequential*.lean`)

Proofs already checked in the scratch file (paste them):
```lean
-- edgeMatrix_mulVec
  ext w
  simp only [edgeMatrix, sub_mulVec, one_mulVec, smul_mulVec, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [vecMulVec_mulVec]
  simp only [Pi.smul_apply, sub_dotProduct, single_one_dotProduct, Pi.sub_apply,
    Pi.single_apply]
  by_cases hi : w = i <;> by_cases hj : w = j <;> subst_vars <;> simp_all <;> ring
-- walkMatrix_pow_apply
  induction t generalizing u with
  | zero => simp [transW, one_apply]
  | succ t ih =>
    rw [pow_succ', mul_apply]
    simp_rw [ih]
    simp only [transW, walkMatrix, diagonal_mul, SimpleGraph.adjMatrix_apply, mul_ite, mul_one,
      mul_zero, ite_mul, zero_mul]
    rw [← sum_filter, div_eq_inv_mul, mul_sum, SimpleGraph.neighborFinset_eq_filter]
```

Rate:
1. `avgIter_eq_walkMatrix_pow_mulVec`: `funext`, `avgIter_eq_sum_transW`, `mulVec`,
   `dotProduct`, `walkMatrix_pow_apply`.
2. `charpoly_walkMatrix`: with `S = diagonal (1/√d)`, `S' = diagonal √d`, `S' * S = 1` (hdeg),
   `P = S * N * S'`; `charpoly_mul_comm` gives `charpoly (S * (N * S')) = charpoly (N * S' * S)`.
3. Theorem 33 (spectral proof, no connectivity needed): `s = √π` (`s v = √(d v / 2m)`) is a unit
   vector with `N s = s`; `Pᵗ = S Nᵗ S'` so `Pᵗ(u,v) = √(d v/d u) Nᵗ(u,v)` and
   `π(v) = √(d v/d u) s(u) s(v)`; reduce to `|Nᵗ(u,v) - s(u)s(v)| ≤ λᵗ`. Write
   `Nᵗ - ssᵀ = Nᵗ Q` with `Q = I - ssᵀ` (`N` commutes with `Q`), so the entry is
   `⟨Q eᵤ, Nᵗ Q eᵥ⟩ ≤ ‖Q eᵤ‖ ‖Nᵗ Q eᵥ‖ ≤ λᵗ`, using `‖N y‖ ≤ λ ‖y‖` for `y ⊥ s` and `N(s⊥) ⊆ s⊥`.
   Key lemma, via `eigenvectorBasis` (`eigenvalues = eigenvalues₀ ∘ e`, `eigenvalues₀_antitone`):
   every index with `|μₖ| > λ` has sorted position `0`, so there is at most one such `k₀`; all
   `|μ| ≤ 1` (an `N`-eigenvector `w` gives the `P`-eigenvector `S w`, and `P` is stochastic, so
   a max-norm argument); if `|μₖ₀| > λ` then `μₖ₀ = 1` (else `s`, an eigenvector for `1`, lies in
   the span of eigenvectors with `μ = 1` at positions `≥ 1`, forcing `λ ≥ 1 ≥ |μₖ₀|`), and then
   `s ∥ wₖ₀`, so `⟨y, wₖ₀⟩ = 0`; Parseval gives `‖N y‖² = ∑ μₖ² ⟨y,wₖ⟩² ≤ λ² ‖y‖²`.
4. `walkLambda_lt_one`: reuse `tendsto_degAvg`. An `N`-eigenvector `w` with eigenvalue `μ`,
   `|μ| = 1`, gives `y = S w` with `avgIter G t y = μᵗ y` (bridge 2). If `μ = -1`, `(-1)ᵗ y(v)`
   converges, so `y = 0`. If `μ = 1`, `y` is constant (`= degAvg`), so `w ∥ √d`. Hence `-1` is
   not an eigenvalue and the eigenvalue `1` is simple; with `|μ| ≤ 1` and sorting, every sorted
   index `≥ 1` has `|λᵢ| < 1` (`n ≥ 3` from the odd cycle, so `walkLambda` is the max).
5. Corollary: bridges 1–2, `∑ᵥ π(v) x(v)` subtracted inside the sum, `abs_sum_le_sum_abs`,
   `abs_mul`, Theorem 33, `mul_sum`.

Sequential:
1. Doubly stochastic: entries are `1`, `1/2` or `0`; row/column sums from `edgeMatrix_mulVec` on
   `𝟙` and symmetry (`edgeMatrix i j` is symmetric).
2. Projection: `u = eᵢ - eⱼ`, `(uuᵀ)(uuᵀ) = (u ⬝ᵥ u) uuᵀ` (`vecMulVec_mul_vecMulVec`?), and
   `u ⬝ᵥ u = 2` if `i ≠ j`, `u = 0` if `i = j`.
3. (4): entrywise expansion of `W(i,j) a b = δ_ab - (δ_ia - δ_ja)(δ_ib - δ_jb)/2`;
   `Distribution.expect` is `∑ⱼ Pᵢⱼ ·`; `(K i).sum_one`; `avg` over `V` is `/ n`.
4. Uniform darts: `avg` over `G.Dart` is `/ (2m)` (`SimpleGraph.dart_card_eq_twice_card_edges`);
   count darts with `fst = a` (`G.dart_fst_fiber_card_eq_degree`) and the darts `(a,b)`, `(b,a)`.
5. (5): `IsRegularOfDegree`, `2m = n d` (`sum_degrees_eq_twice_card_edges`), `L = dI - A`,
   `P = d⁻¹ A`; for (4) also `Pᵀ = P` and `D̄ = 2I`.
6. Second moment: (3) of this list + `avg_edgeMatrix`; vector form by `dotProduct_mulVec`,
   `mulVec_mulVec` and linearity of `avg` (`avg_sum`, `avg_const_mul`).
7. First moment: induction on `t` with `expList_succ`, `seqRun` on `d :: l`, linearity
   (`expList_sum`, `expList_const_mul`) and `avg_edgeMatrix`; `W̄ᵗ⁺¹ = W̄ᵗ W̄`.
8. Afterwards: `#print axioms` lines in `Audit.lean` (only once sorry-free), README and blueprint
   entries, ROADMAP status of AVG-1, PROVENANCE entry.

## Deviations from the paper

1. **Simple graphs.** `G : SimpleGraph V` on a finite type (no multi-edges or self-loops, which
   footnote 24 allows), to reuse `avgIter`/`transW` of `Basic.lean` and Mathlib's `adjMatrix`,
   `degMatrix`, `lapMatrix`.
2. **Theorem 33 under a weaker hypothesis.** Every degree positive (`∀ v, 0 < G.degree v`)
   instead of "connected" (with at least one edge, implicit for a random walk). Connected graphs
   with at least two nodes satisfy it (`Connected.preconnected.degree_pos_of_nontrivial`), so the
   pinned statement implies the source's; the spectral proof does not use connectivity (on a
   disconnected graph without isolated nodes `λ = 1`), as the numerical checks confirm. The
   same applies to `charpoly_walkMatrix` and the averaging corollary. Positive degrees are
   needed: on one isolated node `|P⁰ - π| = 1` but the right-hand side is `0`.
3. **Typo fixed.** The Survey prints `√(d(v)/d(v)) λᵗ`; we state `√(d(v)/d(u)) λᵗ` (Lovász,
   Theorem 5.1; ROADMAP errata). According to the ROADMAP errata, Lovász's text writes
   `λ = min{|λ₂|, |λₙ|}`, a slip for `max` (not re-checked against the original in this job);
   we follow the Survey's `max`.
4. **`λ` via the symmetric matrix `N = D^{-1/2} A D^{-1/2}`.** `P = D⁻¹A` is not symmetric and
   Mathlib's sorted real spectrum `eigenvalues₀` is for Hermitian matrices. `N` is similar to `P`
   (`charpoly_walkMatrix`), so its sorted eigenvalues are those of `P` with multiplicity. `λ` is
   `0` by convention when `n < 2` (no `λ₂`).
5. **`m` is the number of edges.** The Survey's notation paragraph (Section 7.1) says
   `m = ∑ᵥ d(v)`, inconsistent with `π(v) = d(v)/2m` summing to `1`; we use `m = |E|`
   (`#G.edgeFinset`), as Lovász does.
6. **"Unless `G` is bipartite, `λ < 1`"** (a sentence after Theorem 33) is pinned for connected
   graphs with a closed walk of odd length (= non-bipartite), the hypotheses of `tendsto_degAvg`.
   Connectivity is needed: a disconnected graph without isolated nodes (e.g. two disjoint
   triangles) has `λ₂ = 1`. (With isolated nodes `walkLambda` can be `< 1`, e.g. a triangle plus
   an isolated node gives `½`; no pinned statement involves that case.)
7. **Averaging corollary.** The Survey has no displayed bound for `Pᵗx`; we pin the direct
   consequence of Theorem 33, `|x⁽ᵗ⁾(u) - ∑ᵥ π(v)x(v)| ≤ λᵗ ∑ᵥ √(d(v)/d(u)) |x(v)|`, for every real
   initial vector (Definition 30's `±1` initialization plays no role in this deterministic
   bound). `∑ᵥ π(v)x(v)` equals `degAvg G x` of `Basic.lean`.
8. **Bridges.** `walkMatrix_pow_apply` and `avgIter_eq_walkMatrix_pow_mulVec` are the Survey's
   sentences "`Pᵗᵤᵥ` is the probability that a random walk started at `u` is at `v` after `t`
   steps" and "`x⁽ᵗ⁾ = Pᵗ x⁽⁰⁾`", connecting the matrix to `transW`/`avgIter`.
9. **Two edge laws for (4)–(5).** The Survey's random sequential model selects one oriented edge
   uniformly at random (Section 2, Section 6.1), for which `𝔼[W] = I - L/(2m)`. Its equation (4),
   taken from BGPS06, is the expected matrix of a different law: a uniformly random node `i`
   contacts `j` with probability `Pᵢⱼ`. The two coincide on regular graphs, which is where (5)
   lives. We pin (4) for BGPS06's law with an arbitrary stochastic `P`, given as a
   `Dynamics.Kernel` (`avg_expect_edgeMatrix`; self-loops allowed, `W(i,i) = I`), (5) as its
   specialization to `P = D⁻¹A` on a regular graph (`gossipMeanMatrix_of_isRegular`), and the
   uniform-edge identity with its own form of (5) (`avg_edgeMatrix`, `meanMatrix_of_isRegular`).
10. **Uniform oriented edge = uniform dart**; matrix expectations are entrywise, because
    `Dynamics.avg` and `Distribution.expect` are real-valued. `[Nonempty G.Dart]` (at least one
    edge) is assumed, since the average over an empty type is `0` by the `dynamics/` convention.
    The rounds are i.i.d. via `Dynamics.expList G.Dart`.
11. **Only `δ = 1/2`** (Survey footnote 28, the case of Section 7.2); `Averaging(δ)` for other `δ`
    and the first-activation `±1` initialization of Definition 31 are not modelled: the
    identities hold for every state `x` (AVG-3 models first activation).
12. **Second-moment identity** (not displayed in the Survey): `𝔼[WᵀW] = 𝔼[W]` (BGPS06, since `W`
    is a symmetric projection), pinned in matrix and vector (`𝔼‖Wx‖² = xᵀW̄x`) forms for the
    uniform-edge law, with the projection identity itself.
13. **First moment for every graph.** Section 7.3.2 states `𝔼[x⁽ᵗ⁾] = W̄ᵗ x` for regular graphs
    with `W̄` from (5); we state it for every graph with an edge, with `W̄ = I - L/(2m)`. On regular
    graphs this is (5) by `meanMatrix_of_isRegular`, which needs `d > 0` (for `d = 0` there are no
    edges and `meanMatrix = 1` in Lean).

## Coordination with sibling branches (not merged into this one)

`avg2-reconstruction` pins `Averaging.transitionMatrix G d = d⁻¹ • A` (regular graphs; equals
`walkMatrix G` when `G` is `d`-regular) and `Averaging.abs_avgIter_sub_le`; `avg3-opportunistic`
pins `Averaging.Opportunistic.stepMatrix`/`meanStepMatrix` (entrywise `W` and `I - L/(2m)`),
`avg_stepMatrix`, `avg_sum_sq_edgeAvg`, `expList_avgRun`. All AVG-1 names were chosen not to
clash (`walk*`, namespace `Averaging.Sequential`); after merging, those statements could be
derived from the AVG-1 ones.
