# Formalization differences

Where the statements of `epidemics/` deviate from their sources, and why.

## The supercritical giant component (`Giant*`, EPI-3)

Source: M. Krivelevich, B. Sudakov, *The phase transition in random graphs: a simple proof*,
Random Structures & Algorithms 43 (2013) 131–138, arXiv:1201.6529 (numbering of arXiv v4:
Lemma 1, Theorem 1, Theorem 2 in Discussion item 3).

1. **Finite, quantitative "whp".** The paper's "with high probability" (probability → 1) is
   stated as "probability at least `1 - C / n`" with `∃ C` depending on `ε`. The proofs actually
   give exponentially small failure probabilities (paper's Discussion, item 1), turned into
   `C / n`.
2. **"`ε > 0` a small enough constant"** is `∃ ε₀ > 0, ∀ ε ∈ (0, ε₀]`, with `C` chosen after `ε`;
   the proofs take `ε₀ = 1/100` (Theorem 1(2)) and `ε₀ = 1/10` (Theorem 2).
3. **`G(n, p)` as bond percolation on `K_n`**: `perc ⊤ ω`, `ω ~ coins p`, one coin per element
   of `Sym2 V` (the diagonal coins are ignored since `⊤` has no loops); the vertex set is any
   finite type `V` with `n = |V|` rather than `[n]`.
4. **`p = (1 + ε)/n` is written `p * n = 1 + ε`** (with `0 ≤ p ≤ 1` as hypotheses, required by
   `coins`). Equivalent for `n ≥ 1`; it excludes `n = 0`, where Lean's `C / 0 = 0` would make
   `1 - C / n ≤ P(…)` false for the empty graph. `p ≤ 1` forces `n ≥ 1 + ε`.
5. **Path length in edges.** Theorem 1(2) is stated as "a path (`Walk.IsPath`) with
   `Walk.length ≥ ε² n / 5` edges"; the proof shows `|U| ≥ ε² n / 5 + 1` vertices (slightly
   stronger than the paper's `|U| ≥ ε² n / 5`), using the slack of the paper's final inequality.
6. **Lemma 1(2) by Chernoff (FND-3) instead of Chebyshev**, with a relative deviation `δ N₀ p`
   instead of `n^{2/3}` (paper's Discussion, item 1).
7. **Theorem 2's windows.** The paper uses `t ∈ [n^{7/4}, N₀]` with deviations `n^{2/3}`,
   `n^{5/6}`; the formalization uses `t ∈ [⌊η n²⌋, N₀]` with relative deviations `δ t p` (union
   bound over `≤ N₀ + 1` times, each exponentially small in `n`). The contradiction "an epoch
   starting at time `τ` in the window" is the paper's `t ≥ |S|(n - |S|)` computation.
8. **"`|S| < n/3` at time `N₀`"**: the paper looks at the moment when `|S| = n/3` exactly; with
   queries as time steps `S` can jump, so the formal argument takes the first query time at
   which `3 |S ∪ U| ≥ n` (`|S ∪ U|` grows by at most `2` per query) and concludes `3 |S ∪ U| < n`
   at `N₀`.
9. **Floors and ceilings**, omitted in the paper, are explicit (`N₀ = ⌊θ n²⌋`, `t₁ = ⌊η n²⌋`).
10. **DFS details.** (a) The fixed order `σ` is replaced by an arbitrary deterministic choice
    (`DFS.pick`, `Classical.choose`); the analysis never uses `σ`. (b) The coupling goes the
    other way: the coins on the pairs come first and the search reads them adaptively; the
    paper's "fed with i.i.d. `X̄`, the graph is distributed as `G(n, p)`" becomes the principle
    of deferred decisions (`prob_queryAnswers`). (c) Each query is one step of `ofAnswers`;
    moves without query are grouped by `settle`. (d) The completion phase is kept, so the
    strategy is fresh for all `n(n-1)/2` pairs.
11. **Additions.** `exists_linear_component` covers every `ε > 0` (the paper proves only small
    `ε`); it is obtained by the same DFS argument with `N₀ = ⌊θ n²⌋`, `θ` small in terms of `ε`
    (parametric cores `core_path`, `core_component`). The epidemic corollaries are the Reed–Frost
    reading via the percolation coupling (`final_recovered_iff`): the final outbreak from `{v}`
    is the component of `v`, and vertex symmetry of `K_n` (`coins_prob_perm`,
    `prob_component_ge`) gives `P(|C(v)| ≥ k) ≥ (k/n) P(∃ component ≥ k)`. `R₀ = p n` (the mean
    number of secondary infections caused by the first case is `p (n - 1)`).
12. **Not formalized**: Theorem 1(1) and Lemma 1(1) (the subcritical regime), Theorems 3–6
    (digraphs, minimum-degree hosts, pseudo-random hosts, Maker–Breaker).
13. **Local probability lemmas.** `prob_congr`, `prob_not`, `prob_or_le`, `prob_exists_le_sum`
    and `one_sub_le_prob` (`GiantCoins.lean`) are elementary event bounds not yet in
    `dynamics/`; their move to the core is tracked in issue #42. Monotonicity and the
    expectation form of `prob` are the core's.
