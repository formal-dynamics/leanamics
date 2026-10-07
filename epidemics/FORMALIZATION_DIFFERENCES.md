# Formalization differences

Where the statements of `epidemics/` deviate from their sources, and why.

## The Kermack–McKendrick SIR model (`KermackMcKendrick*`, EPI-7)

Sources: W. O. Kermack, A. G. McKendrick, *A contribution to the mathematical theory of
epidemics*, Proc. R. Soc. Lond. A 115 (1927) 700–721; H. W. Hethcote, *The mathematics of
infectious diseases*, SIAM Review 42 (2000) 599–653, §2.3, system (2.2) and Theorem 2.1.

1. **Special case of Kermack–McKendrick 1927.** Their model has infectivity and removal rates
   depending on the age of infection; as in Hethcote §2.3, we formalize the constant-rate
   special case (the SIR ODE). Docstrings cite Hethcote 2000 (system (2.2), Theorem 2.1) for
   numbering, since the 1927 paper has no numbered theorems.
2. **Solution as hypothesis, on `[0, ∞)`.** Hethcote states existence, uniqueness and positive
   invariance of the triangle `T`; we do not construct solutions. The ODE is Mathlib's
   `IsIntegralCurveOn` of `fun _ ↦ sirField β γ` on `Set.Ici 0`, i.e. derivatives within
   `[0, ∞)` (one-sided at `0`); values for `t < 0` are irrelevant. Positivity of `s` and `i` is
   proved, not assumed.
3. **`ℝ³` as `ℝ × ℝ × ℝ`, components as three functions.** The curve is
   `fun t ↦ (s t, i t, r t)`; the theorems speak about `s`, `i`, `r` directly. We keep `r` in
   the state with `r' = γ i` (Hethcote eliminates it by `r = 1 - s - i`; here conservation is a
   theorem, `IsSolution.sum_eq_one`).
4. **Initial data.** Hethcote allows `s₀, i₀ ≥ 0` and `r(0) = 1 - s₀ - i₀ ≥ 0`; we fix
   `r(0) = 0` and `s(0), i(0) > 0`. Hence `i₀ + s₀ = 1`, and his equation
   `i₀ + s₀ - s∞ + ln(s∞/s₀)/σ = 0` becomes `s∞ = s₀ exp(-R₀(1 - s∞))`. The peak value is
   stated verbatim as `i₀ + s₀ - 1/R₀ - log(R₀ s₀)/R₀`.
5. **"Initially increases"** is formalized as `∃ ε > 0, StrictMonoOn i (Set.Icc 0 ε)` (a
   statement about `i`, not merely the sign of `i'(0)`, which would be a tautology).
6. **Threshold, subcritical case.** Hethcote's "if `σ s₀ ≤ 1`, `i(t)` decreases to zero" is
   split into `strictAntiOn_i` (strictly decreasing on `[0, ∞)`) and `tendsto_i` (which holds
   for every solution).
7. **Limits.** "`s∞` exists" is `∃ sInfty, Tendsto s atTop (𝓝 sInfty)`; the properties of `s∞`
   are stated for any limit (hypothesis `Tendsto s atTop (𝓝 sInfty)`), avoiding a `limUnder`
   definition. `i∞ = 0` is `Tendsto i atTop (𝓝 0)`; `r∞ = 1 - s∞` is `tendsto_r`.
8. **Uniqueness of the final size.** Hethcote's "unique root in `(0, 1/σ)`" is stated on the
   slightly larger `(0, 1/R₀]` (`R₀ x ≤ 1`), together with `0 < s∞` and `R₀ s∞ < 1`; we also add
   uniqueness on `(0, 1]` (`final_size_unique_of_le_one`), the physically meaningful range.
9. **Additions**, all from Hethcote's Theorem 2.1: `strictAntiOn_s`, `strictMonoOn_r`,
   `strictAntiOn_i`, `tendsto_r`, `limit_pos`, `R₀_mul_limit_lt_one`, the two uniqueness
   statements and `exists_peak`.
10. **Proof route.** Positivity of `i` uses the barrier `i(t) ≥ i(0) e^{-γ t}/2` (via
    `image_le_of_deriv_right_lt_deriv_boundary'`) instead of integrating `β s - γ` or Gronwall.
    The model-independent calculus lemmas (constancy and strict monotonicity from the sign of a
    derivative within `[0, ∞)`, limits of monotone functions) are in
    `KermackMcKendrickCalculus.lean`.

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
