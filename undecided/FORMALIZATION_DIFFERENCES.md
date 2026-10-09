# Formalization differences

Where the statements of `undecided/` deviate from their sources, and why.

## Majority phase of the binary dynamics (`Majority*`, roadmap UND-1)

Sources: L. Becchetti, A. Clementi, E. Natale, F. Pasquale, R. Silvestri, *Plurality consensus in
the gossip model*, SODA 2015, arXiv:1407.2565 [BCNPS15]; A. Clementi, M. Ghaffari, L. Gualà,
E. Natale, F. Pasquale, G. Scornavacca, *A tight analysis of the parallel undecided-state
dynamics with two colors*, MFCS 2018, arXiv:1707.05135 [CGGNPS18].

### The statements

`Undecided/Majority.lean` (namespace `Undecided`) reuses `Config`, `Op`, `count` and `step` from
`Undecided/Basic.lean`; probabilities are `Dynamics.expList (Fin n → Fin n) T` expectations of
the indicator that `l.foldl step x` is the all-`a` (or all-`b`) configuration.

* `majority_whp`: there is `C > 0` such that for every `n` with `log n ≥ C` and every
  configuration with `count a - count b ≥ C √(n log n)` (any number of undecided nodes), all
  nodes hold `a` after `⌈C log n⌉` rounds with probability at least `1 - C/n`. Proved with
  `C = 10⁴`; the explicit form is `majority_explicit` (failure probability at most `2/n`).
* `majority_whp_abs`: the same with `|count a - count b|`, the target being the initial majority
  opinion.
* `majority_whp_of_ratio (hα : 0 < α)`: [BCNPS15, Theorem 11] for two colours. Without undecided
  nodes and with `count a ≥ (1 + α) count b`, the same conclusion with
  `C = 10⁴ + 3·10⁴ (2 + α)/α`.

### Differences in the statements

1. **Additive bias, undecided nodes allowed.** [BCNPS15] proves the binary case only as
   Theorem 11 with `k = 2`, from configurations without undecided nodes (`q⁽⁰⁾ = 0`, Section 2.1)
   and with a multiplicative bias `c₁ ≥ (1 + α) c₂`, that is a bias of order `n`. The main
   statement `majority_whp` is the stronger form of [CGGNPS18, Theorem 3.2]: any configuration
   with bias at least `C √(n log n)`. The form of [BCNPS15] is stated separately
   (`majority_whp_of_ratio`), with `q⁽⁰⁾ = 0` as in the paper. The hypothesis `q⁽⁰⁾ = 0` cannot
   be dropped there: with undecided nodes allowed, a ratio hypothesis alone does not give a
   high-probability statement (from `a = 2`, `b = 1` and all other nodes undecided, simulations
   show that the majority wins only in about 80% of the runs).
2. **Explicit "with high probability".** `1 - n^{-Θ(1)}` and `O(log n)` become one existential
   constant `C`: `log n ≥ C`, bias at least `C √(n log n)`, `⌈C log n⌉` rounds, probability at
   least `1 - C/n`. [CGGNPS18] allows any constant `γ > 0` in the bias `γ √(n log n)` (with a
   `γ`-dependent exponent); only the existence of a suitable (large) constant is stated here.
3. **"Within `T` rounds" is stated as "at round `T`"**, which is equivalent because the
   monochromatic configurations are absorbing (`step_of_mono`).
4. **The majority is named `a`** in `majority_whp`, following the paper's convention `c₁ ≥ c₂`;
   `majority_whp_abs` covers either opinion.
5. **Sampling model.** Every node samples one node uniformly with replacement, possibly itself
   (as in `Undecided/Basic.lean`). This is the model behind the expectations (3) and (4) of
   [BCNPS15] (`µᵢ = cᵢ (cᵢ + 2q)/n`) and (1) to (3) of [CGGNPS18].
6. **Finite probability.** Probabilities are `expList` expectations over `T` i.i.d. uniform
   rounds (equivalently `(kernel n).event`, by `Dynamics.Kernel.event_ofStep`), not events on a
   path space.
7. **`majority_whp_of_ratio`:** the constant depends on `α`, as the `O(·)` of [BCNPS15] does. The
   paper's condition `k = O((n / log n)^{1/3})` is vacuous for `k = 2`, and the monochromatic
   distance is at most `2`, so `O(md(c) log n) = O(log n)`.

### Differences in the proofs

The proof does not follow [BCNPS15] (Lemmas 1, 2, 5, 9 and 10, built on the monochromatic distance
and a multiplicative bias), which does not reach an additive `√(n log n)` bias. It follows the
phase structure of [CGGNPS18] (phases `H4`, `H5`, `H7`, then `H6`, then consensus), simplified with
large explicit constants. Only Hoeffding's inequality is used (`Dynamics.avg_hoeffding`), at
deviation `Λ = √(n log n)`: a round is *bad* if one of the counts of `a`, `b` or undecided nodes
deviates from its expectation by `Λ` in the relevant direction, which has probability at most
`4/n²` (`bad_round`, `four_exp_sqrt`). With `s = count a - count b`, `q = count u` and the
potential `Ψ = 12 count b + q` (`MajorityStages.lean`):

1. **Growth** (`growth_stage`, `T₁ + 1` rounds with `T₁ = ⌈log n / log(201/200)⌉`): from
   `s ≥ 402Λ`, one good round reaches the set where `s ≥ 400Λ` and either `q ≥ n/100` or
   `s ≥ 400Λ + n/20`; the threshold `400Λ` then grows by the factor `201/200` per good round up to
   `7n/10` (if `s ≤ 4n/5`, a good round leaves at least `n/100` undecided nodes, as in
   [CGGNPS18, (4)]; with that many undecided nodes the bias grows by the factor `1.01`).
2. **Bridge** (`bridge_stage`, `18` rounds): while `s ≥ 2n/3`, `Ψ` shrinks by `9/10` per good
   round, from `Ψ ≤ 2n` to `Ψ ≤ n/3`, and `s` loses at most `2Λ` per round.
3. **Final phase** (`fin_stage`, `T₃ ≥ 12 log n` rounds): on `{Ψ ≤ n/3}` the expectation of `Ψ`
   contracts by `5/6` per round and the set is kept after a good round, so the probability of
   not being all-`a` is at most `(5/6)^{T₃} n/3 + T₃ · 4/n²`; here `Ψ < 1` if and only if all nodes
   hold `a`. This linear potential replaces the analysis of [CGGNPS18] in the last phase.

The stages are composed by the Markov property (`missP_comp`, through `Dynamics.expList_append`),
the moving targets of the growth phase by `Dynamics.expList_escape`, and the total failure
probability is at most `⌈10⁴ log n⌉ · 4/n² + 1/(3n) ≤ 2/n`. The `b`-majority case follows by
exchanging the two opinions (`swapOp`, `MajoritySymm.lean`). Simulations (`n = 10⁵`, bias
`√(n log n)` and `2 √(n log n)`, various numbers of undecided nodes) reached consensus on the
majority within about `2 log n` rounds, far below the proved `10⁴ log n`.

## The dynamics with `k` colours (`Plurality*`, roadmap UND-3)

Source: [BCNPS15], Theorem 11 (Section 3.6), with the model of Section 2 (Table 1, equations (3)
and (4)) and the monochromatic distance of Section 2.1.

### The model and the statements

`Undecided/PluralityBasic.lean` (namespace `Undecided.Plurality`): `Config n k := Fin n →
Option (Fin k)` (`none` is the undecided state), `update` (Table 1 of the paper), `step`, `count`,
`maxCount` and `md x = ∑ᵢ (cᵢ / maxⱼ cⱼ)²`, with their defining equations (`step_apply`,
`count_def`, `maxCount_def`, `md_def`) and the facts `one_le_md`, `md_le_card` (the paper's (1)),
`md_eq_of_plurality`, `expected_count_some`, `expected_count_none` (the paper's (3) and (4)).
`Undecided/PluralityBinary.lean` shows that the binary model of `Undecided/Basic.lean` is the case
`k = 2` (`step_two`, `foldl_two`, `count_two`).

`plurality_whp` (`Undecided/Plurality.lean`): for every `α > 0` there is `C > 0` such that, for
every `n` with `log n ≥ C`, every `k` with `C k ≤ (n / log n)^{1/3}`, every configuration `x`
without undecided nodes and every colour `m` with `(1 + α) cᵢ ≤ c_m` for all `i ≠ m`, all nodes
hold `m` after `⌈C · md(x) · log n⌉` rounds with probability at least `1 - C/n`. It is proved with
`C = 10⁵ ((1 + α)²/α)²`; the explicit form is `plurality_explicit` (failure probability at most
`6/n`).

### Differences in the statements

1. **Range of `k`: `C k ≤ (n / log n)^{1/3}` with `C = C(α)`**, that is the paper's exponent with
   a sufficiently small constant, instead of `k = O((n / log n)^{1/3})` with an arbitrary
   constant. The range of `k` in [BCNPS15, Theorem 11] needs a minor correction:
   * the proof of Theorem 11 invokes Lemma 10, which assumes `k = O((n / log n)^{1/4})`, so the
     proof covers that smaller range;
   * the paper bounds the ratios `Cᵢ / C₁` (Lemma 2) round by round with high probability. When
     `c₁ ≈ n / (2 md)`, the drift of a ratio in one round is about `α / (2 md)` and its one-round
     fluctuation about `√(md log n / n)`, so the per-round argument closes if and only if
     `md^{3/2} ≲ α √(n / log n)`, that is `k ≤ ε(α) (n / log n)^{1/3}`; an arbitrary constant
     would need concentration over many rounds (martingale arguments), which neither the paper nor
     `dynamics/` provides;
   * simulations of the exact count dynamics with `n = 10⁵` and `10⁶`, `k = ⌊(n / log n)^{1/3}⌋`
     and `α = 0.05` gave consensus on the plurality colour in only 2 to 7 runs out of 20 (with
     `α = 0.2`: 12 to 20 out of 20), while with `k ≤ 10` it won in all 40 runs, always within
     `0.63 md log n` rounds.

   For large `n` the stated range contains `k = O((n / log n)^{1/4})` with any constant, the range
   that the paper's proof assumes.
2. **Explicit "with high probability"**: `log n ≥ C`, `⌈C md(x) log n⌉` rounds, probability at
   least `1 - C/n` (the paper: `O(md(c) log n)` rounds and `1 - n^{-Θ(1)}`). The error `C/n` is
   reachable because every expectation used is at least `n^{1/3}` up to logarithmic factors, and
   the end game uses an expectation contraction over `O(log n)` rounds instead of the paper's
   final Markov step (which gives `O(log² n / n)`).
3. **"Within `T` rounds" is stated as "at round `T`"**: monochromatic configurations are absorbing
   (`step_const`).
4. **The plurality colour is named `m`** instead of sorting the colours (`c₁ ≥ c₂ ≥ ⋯`); the
   hypothesis `(1 + α) cᵢ ≤ c_m` for all `i ≠ m` makes `m` the unique plurality colour.
5. **`k` is the size of the palette** (`Fin k`): colours may be absent, and `k ≥ 2` is not
   assumed (`k ≤ 1` is trivial). The paper's standing assumption `c₁ > n/k` follows from the
   bias hypothesis when there are no undecided nodes.
6. **Sampling model**: uniform with replacement, possibly oneself, which gives exactly the
   paper's (3) and (4) (`expected_count_some`, `expected_count_none`).
7. **`md`** is defined with `c₁ = maxCount x = maxᵢ cᵢ`; for a configuration without any colour
   `md = 0` (Lean's `x / 0 = 0`), which does not matter for the theorem.
8. **Finite probability**: probabilities are `expList` expectations over i.i.d. uniform rounds.
9. **Not covered**: Section 4 (expanders). The `Ω(md(c))` lower bound (Theorem 8) is in the next
   section.

### Differences in the proofs

The proof does not follow Lemmas 1 to 10 of [BCNPS15] verbatim: a single invariant with a
state-dependent slack replaces the accumulated errors of Lemma 2, and the potential
`Φ = c(c + 2q)/n` replaces the two-step use of Lemmas 1 and 9. Notation: `c = c_m`, `q` the number
of undecided nodes, `S = n - q - c = ∑_{j≠m} cⱼ`, `µᵢ = cᵢ(cᵢ + 2q)/n`, `ℓ = 3 log n`,
`dev µ = √(3ℓ(µ + 2ℓ))`, `θ = 1/(1 + α)`, `κ = 1 - θ`, `K = 1/(θκ) = (1 + α)²/α`, `B = 2 md(x₀)`.

1. **Concentration** (`PluralityConc.lean`, from `Dynamics.avg_bernstein`): for a sum of
   independent `{0, 1}` coordinates with mean `µ`, each tail beyond `dev µ` has probability at
   most `e^{-ℓ}` (`tail_up`, `tail_down`). A round is *good* if every `cᵢ` stays below
   `µᵢ + dev`, `c_m` above `µ_m - dev`, `S` below its mean plus `dev`, and `q` within `dev` of its
   mean; a bad round has probability at most `(k + 4)/n³` (`bad_le`).
2. **Invariant** (`PluralitySteps.lean`): `cᵢ + 12√(ℓc) ≤ θc` for all `i ≠ m` and
   `S + 12B√(ℓc) ≤ Bc`. A good round keeps it while `Φ ≥ n/(2k²)`; in the drift case
   (at least `n/20` decided nodes) the deterministic drift `X µ_m - µ_X c ≥ (t/2) κ c³/n` must beat
   the deviation, which needs `θ²κ²c³ ≥ 2048 n² ℓ`, i.e. `n ≥ 4.5·10⁸ K² k³ ℓ`: this is where the
   range of `k` is used.
3. **Progress** (`PluralityProgress.lean`): the identity
   `µ_m + 2µ_q = n + (n - c - 2q)²/n + 2∑ⱼ cⱼ(c - cⱼ)/n` with `∑ⱼ cⱼ(c - cⱼ) ≥ κcS` shows that,
   as long as `4S + q > n/10`, `Φ` grows by the factor `1 + κ/(8000B)` per good round.
4. **Stages** (`PluralityStages.lean`): one round from `x₀` into the invariant; then moving targets
   (`Dynamics.expList_escape`) until `4S + q ≤ n/10`; then `⌈8 log n⌉` rounds in which
   `E[4S' + q'] ≤ (3/4)(4S + q)` and `{4S + q ≤ n/10}` is kept by a good round (the pattern of
   UND-1's final phase). The total number of rounds is at most `C md(x) log n`, and the failure
   probability at most `T (k + 4)/n³ + (3/4)^{T₃} n/10 ≤ 6/n`.

## The lower bound with `k` colours (`LowerBound*`, roadmap UND-3)

Source: [BCNPS15], Theorem 8 (Section 3.5), proved from Lemma 3 (Section 3.3, the first round),
Lemma 6 (Section 3.4, the descent of the undecided nodes) and Lemma 7 (Section 3.5, the
plateau); equations (16) and (17) are in the proof of Lemma 6, (19), (20) and (23) in the proof
of Lemma 7. The paper writes `R(c) = ∑ᵢ cᵢ/c₁` and `Λ(c) = R(c)²/md(c)` (Section 2.1), where
colour `1` is the initial plurality.

### The statements

`Undecided/LowerBoundBasic.lean` (namespace `Undecided.Plurality`) defines `ratioR x = ∑ᵢ cᵢ /
maxⱼ cⱼ` and `ratioLam x = ratioR x ² / md x` and proves `md ≤ R ≤ k`, the paper's (2) `Λ ≤ k`,
`md ≤ Λ`, their values without undecided nodes (`R = n / maxᵢ cᵢ`, `Λ = n² / ∑ᵢ cᵢ²`), and the
expectations (20) `µᵢ = (1 + (2δ + cᵢ)/n) cᵢ` and (19) `E[Q' - n/2] = (2δ² - ∑ⱼ cⱼ²)/n`, with
`δ = q - n/2` (`mu_eq_half`, `muU_sub_half`). Below, `q` is the number of undecided nodes,
`miss S T y` the probability of not being in `S` after `T` rounds from `y` (as in
`PluralityStages.lean`), and every constant `C` is existential.

* `first_round` (Lemma 3; `C k ≤ (n / log n)^{1/2}`): from `x` without undecided nodes and a
  plurality colour `m`, after one round, with probability at least `1 - C/n`: `c_m ≥ n/(2R²)`,
  every colour is at most `2n/R²`, and `n(1 - 2/Λ) ≤ q ≤ n(1 - 1/(2Λ))` (`R`, `Λ` of `x`).
* `undecided_square` ((16); `C k ≤ (n / log n)^{1/6}`): if `q = (1 + δ)n/2` and
  `1 - δ ≥ 1/(2k)`, then after one round `Q' ≤ (1 + δ²) n/2` with probability at least
  `1 - C/n²`.
* `undecided_not_below` ((17), corrected; `C k ≤ (n / log n)^{1/6}`): for every `γ ≥ 1` and
  `D ∈ (0, k]`, if every colour is at most `γ n/D`, then after one round `Q' ≥ n/2 - 2γ² n/D`
  with probability at least `1 - C/n²` (`C` does not depend on `γ`).
* `descent` (Lemma 6, corrected; `C k ≤ (n / log n)^{1/6}`): there are `γ ≥ 1` and `C` such
  that, for `x` without undecided nodes with `md(x) ≥ C` and `y` satisfying the conclusion of
  Lemma 3 (every colour at most `2n/R(x)²`, `n(1 - 2/Λ(x)) ≤ q ≤ n(1 - 1/(2Λ(x)))`), there is a
  round `t ≤ C log n` such that, with probability at least `1 - C/n`, every colour is at most
  `γ n/md(x)` at each round `s ≤ t`, and at round `t` moreover `|q - n/2| ≤ 2γ² n/md(x)`.
* `plateau_step` (one round of Lemma 7, corrected; `C k ≤ (n / log n)^{1/4}`): for every
  `γ ≥ 1` there is `C` such that, if `C ≤ D ≤ k`, `|q - n/2| ≤ 2γ² n/D` and every colour is at
  most `B ∈ [γ n/D, 2γ n/D]`, then after one round, with probability at least `1 - C/n²`, every
  colour is at most `(1 + (4γ² + 2γ + 1)/D) B` and still `|q - n/2| ≤ 2γ² n/D`.
* `plateau` (Lemma 7, corrected; `C k ≤ (n / log n)^{1/4}`): for every `γ ≥ 1` there is `C`
  such that, if `C ≤ D ≤ k`, `|q - n/2| ≤ 2γ² n/D` and every colour is at most `γ n/D`, then for
  every `T ≤ D/C`, after `T` rounds, with probability at least `1 - C/n`, every colour is at
  most `2γ n/D` and `|q - n/2| ≤ 2γ² n/D`.
* `lower_bound_whp` (Theorem 8; `C k ≤ (n / log n)^{1/6}`, `log n ≥ C`): for `x` without
  undecided nodes and every `T` with `C T ≤ md(x)`, after `T` rounds, with probability at least
  `1 - C/n`, every colour is at most `C n/md(x)`.
* `lower_bound_consensus` (Theorem 8, the convergence time; same range): for `x` without
  undecided nodes and every `T` with `C(T + 1) ≤ md(x)`, the probability that all nodes hold the
  same colour after `T` rounds is at most `C/n`.

The proofs give `C = 100` for `first_round`, `C = 8` for `undecided_square` and
`undecided_not_below`, the witnesses `γ = 24` and `C = 10⁶` for `descent`, `C = 16γ²` for
`plateau_step`, `C = 30γ²` for `plateau`, and `C = 1017429` for `lower_bound_whp` (twice that
for `lower_bound_consensus`).

### Differences in the statements

1. **Explicit "w.h.p.", `O`, `Ω`, `o` and "sufficiently small `ε`"**: one existential constant
   `C` per statement, with `log n ≥ C`, `C k ≤ (n / log n)^{a}` with the paper's exponent `a`
   (`1/2` for `k = o(√(n / log n))` in Lemma 3, `1/4` in Lemma 7, `1/6` in Lemma 6 and
   Theorem 8), failure probability `C/n`, and `T ≤ md/C` rounds for `Ω(md)`. The one-round steps
   (16), (17) and the step of Lemma 7 are stated with failure probability `C/n²` (a bad round has
   probability `(k + 4)/n³` at deviation level `3 log n`), so that they can be iterated over
   `O(log n)` (respectively `O(md) ≤ n`) rounds.
2. **All colours, not only the initial plurality.** The lower bound needs that *no* colour
   reaches all nodes. Lemmas 6 and 7 bound only the initial plurality `C₁`, but their proofs use
   properties of the largest colour (`∑ⱼ cⱼ² ≤ c₁ (n - q)`, `c₁ ≥ (n - q)/k`), and without a bias
   another colour may overtake the initial plurality. This needs a minor correction: every upper
   bound is stated for `maxCount`. Lemma 3 also keeps the paper's lower bound on the plurality
   colour `m`.
3. **Theorem 8, form of the conclusion.** "The convergence time is `Ω(md(c̄))` w.h.p." becomes
   (a) `lower_bound_whp`: at every round `T ≤ md(x)/C`, w.h.p. no colour has more than
   `C n/md(x)` nodes (what the proof shows), and (b) `lower_bound_consensus`: if
   `C(T + 1) ≤ md(x)`, the probability of a monochromatic configuration after `T` rounds is at
   most `C/n`. Monochromatic configurations are absorbing (`step_const`), so this bounds the
   probability of converging within `T` rounds. The `+ 1` excludes `T = 0` with `md(x) < C` (for
   instance a monochromatic `x`). Convergence means that all nodes hold the same colour (the
   target of Section 2); the all-undecided configuration, also absorbing, is not counted as
   convergence.
4. **Initial configurations without undecided nodes** (`count x none = 0`), as in the paper
   (Section 2.1: "In the initial state we always have `q⁽⁰⁾ = 0`"). No bias is assumed, as in the
   paper.
5. **Lemma 6 and Theorem 8: `2γ² n/md(c̄)`.** The window `|Q - n/2| ≤ 2γ²/md(c̄)` in the
   statement of Lemma 6 and in the proof of Theorem 8 needs a minor correction (a typo): it
   should read `2γ² n/md(c̄)`, the interval used in the proof of Lemma 6.
6. **Lemma 6: a deterministic round, and all rounds before it.** The paper gives a round
   `t̄ = O(log n)` at which, w.h.p., `C₁ ≤ γ n/md` and `|Q - n/2| ≤ 2γ² n/md`. Here the round
   `t` is deterministic (it depends on `n`, `Λ(c̄)` and `md(c̄)`; the proof takes the first `s`
   with `(1 - 1/Λ)^{2^s} ≤ 4γ²/md`), and the bound `γ n/md` on the colours holds at every round
   `s ≤ t`, not only at `t`. This is what the proof shows, it avoids a random round (a stopping
   time) in the composition, and the per-round form `lower_bound_whp` needs it: when
   `md(c̄) ≪ log Λ(c̄)`, some rounds `T ≤ md/C` lie before `t̄`. (For the convergence time alone
   the paper's composition suffices: at `t̄` about `n/2` nodes are undecided, so the process has
   not converged before `t̄`, consensus being absorbing.) The step (16) is stated for every `δ`
   with `1 - δ ≥ 1/(2k)` (also `δ < 1/md(c̄)`, possibly negative), which contains the paper's
   range `1/md(c̄) ≤ δ ≤ 1 - 1/(2Λ(c̄))` since `Λ ≤ k`; the paper's computation holds verbatim on
   the larger range.
7. **(17) needs a minor correction.** The paper's proof writes `∑ⱼ cⱼ² = c₁² md(c̄)`, with the
   monochromatic distance of the *initial* configuration instead of the current one. The bound
   `∑ⱼ cⱼ² ≤ (maxⱼ cⱼ)(n - q) ≤ γ n²/md` gives `E[Q'] ≥ n/2 - γ n/md`, and the statement for every
   `γ ≥ 1`.
8. **Lemma 7 needs minor corrections.**
   * The growth factor is `1 + (4γ² + 2γ + 1)/md` instead of `1 + (2γ(γ + 1) + 1)/md`: with
     `|δ| ≤ 2γ² n/md`, the term `2δ/n` of (20) is at most `4γ²/md`, not `2γ²/md`. The number of
     rounds changes accordingly (still `Ω(md)`).
   * The lower bound (23), `E[Δ'] ≥ -(4/9) n/md`, uses `∑ⱼ cⱼ² ≤ k ((n - q)/k)²`, which is the
     reverse of the Cauchy–Schwarz inequality `∑ⱼ cⱼ² ≥ (n - q)²/k`. With
     `∑ⱼ cⱼ² ≤ (maxⱼ cⱼ)(n - q) ≤ (2γ n/md)(2n/3)` one gets `E[Δ'] ≥ -(4γ/3) n/md`, which stays
     inside the window `-2γ² n/md` for `γ ≥ 1`.
   * The lemma is stated for `γ ≥ 1` instead of "an arbitrary positive constant `γ`": the proof's
     invariant (the window `|Δ| ≤ 2γ² n/md`, part of the formal conclusion) is not preserved for
     `γ < 1/2`, since from `q = n/2` and `md/(4γ)` colours of size `2γ n/md` one gets
     `E[Δ'] = -γ n/md < -2γ² n/md`. Whether the paper's conclusion (which bounds only `C₁`) holds
     for small `γ` is left open; Theorem 8 needs only one large `γ`.
   * `md(c̄)` is a real parameter `D` with `C ≤ D ≤ k`; the paper assumes `md(c̄) ≥ 8γ²`, a
     "sufficiently large constant".
9. **Lemma 3** is stated with the same constant `C` in the range `C k ≤ (n / log n)^{1/2}` (the
   paper: `k = o(√(n / log n))`), which is what its Chernoff bounds need
   (`E[C_m'] = n/R² ≥ n/k² ≥ C² log n`).
10. **Lemma 4** (`R(C⁽¹⁾) ≤ md(c̄)(1 + o(1))`) is not used by the lower bound and is not
    formalized.
11. **Model**: as for `plurality_whp` (sampling with replacement, possibly oneself; finite
    probability via `expList`); `k` is the size of the palette (colours may be absent).

### Differences in the proofs

Every one-round statement follows from the good event of `PluralityRound.lean` at deviation level
`ℓ = 3 log n` (`bad_le`: a bad round has probability at most `(k + 4)/n³`; `round_le` in
`PluralityStages.lean`), by a
deterministic lemma on a good round (`LowerBoundRound.lean`: `first_of_good`, `square_of_good`,
`not_below_of_good`; `plateau_of_good`). `plateau` and `descent` iterate their steps with moving
targets (`Dynamics.expList_escape`). In `descent` (`LowerBoundDescentCore.lean`) the colour
envelope is the recursion `descentGrowth`: in a first phase the colours stay at most `8n/D`, in a
second at most `γ n/D` with `γ = 24`, while the number of undecided nodes tracks
`max((1 - 1/Λ)^{2^s}, 4γ²/D)` until this quantity reaches the window `4γ²/D`. `lower_bound_whp`
composes `first_round`, `descent` and `plateau` by the Markov property (`miss_comp`); a round `T`
up to the descent round `t` is covered by the bound at every round `s ≤ t` of `descent`.

## Sequential approximate majority (`Sequential*`, roadmap UND-2)

Source: D. Angluin, J. Aspnes, D. Eisenstat, *A simple population protocol for fast robust
approximate majority*, Distributed Computing 21(2):87–102, 2008 [AAE08]. Journal manuscript:
<https://cs.yale.edu/homes/aspnes/papers/approximate-majority-abstract.html>.

### The model and the statements

`Undecided/Sequential.lean` (namespace `Undecided.Sequential`) reuses `Undecided.Op`, `Config`,
`count` and `update` from `Undecided/Basic.lean`:

* `Interaction n`: ordered pairs `(initiator, responder)` of distinct agents (a subtype of
  `Fin n × Fin n`), drawn uniformly and independently by `Dynamics.expList (Interaction n) T`.
* `step s p`: the responder `p.1.2` takes `update (s p.1.2) (s p.1.1)`; the other agents are
  unchanged. This is exactly the transition table of [AAE08, §3] under `x ↦ .a`, `y ↦ .b`,
  blank `↦ .u`.
* `run s l := l.foldl step s` (the form used by `Dynamics.Kernel.iterate_ofStep`).

`Undecided/SequentialMain.lean` states:

* `consensus_whp` [AAE08, Thm 1]: for every `c : ℕ` there is `C` such that for all `n ≥ 2`, every
  non-blank configuration `s` (`∃ v, s v ≠ .u`) and every `T ≥ C n log n`,
  `1 - C / n ^ c ≤ P[count .a = n ∨ count .b = n after T interactions]`.
* `majority_whp` [AAE08, Thm 2 and Thm 1]: for every `c : ℕ` there is `C` such that for all
  `n ≥ 2`, every configuration `s` (blanks allowed) with `C √n log n ≤ count s .a - count s .b`
  and every `T ≥ C n log n`, `1 - C / n ^ c ≤ P[count .a = n after T interactions]`.
* `approximate_majority`: the same with error `1 - C / n` (the case `c = 1`).

The explicit forms behind them (`SequentialConsensus.lean`): for `n ≥ 16`, any `L` and
`T ≥ 256L + 34576nL + 6336n`, `P[not in consensus at T] ≤ 9n e^{-L}` from a non-blank start
(`prob_notCons_le`), and `P[not all x at T] ≤ 9n e^{-L} + exp(-(x₀-y₀)²/(2(60nL + 11n)))` if
`x₀ > y₀` (`prob_notAllX_le`). The main theorems take `L = (c+2) log n` and
`C = 40000(c+2) + 16^c` (`constC`, `SequentialWhp.lean`).

### Differences in the statements

1. **Initial gap `√n · log n`, not `√(n log n)`.** [AAE08, Thm 2 and abstract] assumes an initial
   gap `ω(√n log n)`, and its proof (a coupling with a fair walk and Azuma over `Θ(n log n)`
   steps, whose fluctuation is `√(n log n · log n)`) cannot reach `√(n log n)`. We state the
   paper's hypothesis. The `ω(√(n log n))` in the ROADMAP row UND-2 is the bound of a later
   result: A. Condon, M. Hajiaghayi, D. Kirkpatrick, J. Maňuch, *Approximate majority analyses
   using tri-molecular chemical reaction networks*, Natural Computing 2020 (their §1.4: "their
   [AAE] majority-consensus analysis assumes an initial gap of `√n lg n`, while ours is
   `√(n lg n)`"). That result is for initial configurations *without blanks* (`x + y = n`) and
   goes by a different route (emulating a tri-molecular chemical reaction network); it is not
   formalized here.
2. **`ω(·)` replaced by `C · (·)`**, with `C` existential (depending on `c`). This implies the
   paper's `ω` form (a gap that is `ω(√n log n)` eventually exceeds `C √n log n`) and is what the
   paper's proof establishes.
3. **"With high probability" means: for every `c : ℕ`, error `≤ C n^{-c}`.** [AAE08, Thm 1] says
   "for any fixed `c > 0`"; a natural `c` loses nothing (`n^{-⌈c⌉} ≤ n^{-c}`). The paper's
   explicit constants (`6769 n log n + 6773 c n log n + 2552 n`, error `5 n^{-c}`) and its
   "sufficiently large `n`" are absorbed into `C` (small `n` are vacuous, since then
   `1 - C / n^c ≤ 0`).
4. **Time bound in the correctness theorem.** [AAE08, Thm 2] concludes eventual convergence to
   the initial majority; `majority_whp` concludes convergence to the majority within `C n log n`
   interactions, that is Thm 2 together with Thm 1 (which is what the proof of Thm 2 shows).
5. **The majority is taken to be `x` (`Op.a`)**, without loss of generality by the `x ↔ y`
   symmetry of the protocol; the paper speaks of "the initial majority value".
6. **"Within `T` interactions" is stated as "at every time `T ≥ C n log n`"**: the two are
   equivalent because the consensus configurations are absorbing. The hitting time `τ*` (first
   time with `x = n` or `y = n`) is not defined.
7. **`2 ≤ n`**: an interaction needs two distinct agents (for `n ≤ 1` the interaction type is
   empty and `expList` would be `0`); the paper's statements are for sufficiently large `n`.
8. **Notation.** `Undecided.Op` is reused with `x ↦ .a`, `y ↦ .b`, blank `↦ .u` (so the letter `b`
   denotes opinion `y` in Lean but the blank state in the paper). The rules
   `B + X → X + X`, `B + Y → Y + Y` of the ROADMAP are unordered chemical-reaction-network
   notation; with the responder as the agent that changes, they are AAE's `(x, b) → (x, x)` and
   `(y, b) → (y, y)`, initiator first, which is what `step` implements.
9. **Probability model**: a finite horizon, with `T` i.i.d. uniform interactions via
   `Dynamics.expList`; the paper's filtration and stopping-time language does not appear in the
   statements.
10. **Not covered**: the epidemic-triggered start ([AAE08, §6], Thm 3, gap `Ω(n^{3/4+ε})`),
    Byzantine agents (§7), more than two values (§8).

### Differences in the proofs

The statements do not depend on these. Only some constants are needed, so the four-region
bookkeeping of [AAE08, §4] is replaced by six weighted supermartingales, all instances of one
generic lemma (`SequentialMartingale.lean`, `expList_exp_pathSum_le`): if
`avg_p exp(φ s p) · F(step s p) ≤ F s` for all `s`, then `E[exp(∑_path φ) · F(X_T)] ≤ F(X_0)`,
hence (Markov) `P[∑_path φ ≥ L] ≤ F(X_0) e^{-L} / min F`.

Notation: counts `x, y, b`, `u = x - y`, `v = x + y`; per-step indicators `I_vb` (interactions
`xb`, `yb`), `I_xy` (`xy`, `yx`), `I_ch = I_vb + I_xy`; regions (for `n ≥ 16`):
`R_b : 8v ≤ n`, `R_x : 8x ≥ 7n ∧ x < n`, `R_y` symmetric, `R_c : 8v > n ∧ 8x < 7n ∧ 8y < 7n`.

| bound | weight `φ` | potential `F` |
| --- | --- | --- |
| P1: state-changing steps ([AAE08, §4.4]; `stepSC`) | `(I_vb/5 - I_xy/6)/n` | `1/(u² + 4n)` |
| PC: central steps, `P[change] ≥ 1/128` (`stepC`) | `(R_c - 256 I_ch)/256` | `1` |
| PB: blank corner (`stepB`) | `(5/(16n))(R_b - 64 I_xy)` | `1/v` |
| PX: `x` corner (`stepX`) | `(5/(32n))(R_x - 128 I_ch)` | `3y + b + 1` |
| PY: `y` corner (`stepY`) | symmetric | `3x + b + 1` |
| PM: `u` stays positive, for Thm 2 (`stepM`) | `-(λ²/2) I_ch` | `exp(-λ max(u, 0))` |

Deterministic glue: `b_T - b_0 = S_xy - S_vb` (so `S_xy ≤ S_vb + n`); non-consensus is absorbing
backwards (not in consensus at `T` implies that all `T` steps were non-consensus steps); and
`notCons ≤ R_c + R_b + R_x + R_y`. Off the six bad events (total probability
`≤ 9n e^{-L} + e^{-u₀²/(2N)}`), `S_ch < N := 60nL + 11n` and the number of non-consensus steps is
`< 256L + 34576nL + 6336n`. Then `L = (c+2) log n` and `λ = u₀/N`.

11. **Potentials and constants.** P1 uses `1/(u² + 4n)` instead of the paper's `1/(u² + 2n)`
    (this makes the `xy`-to-`vb` ratio `5/6 < 1` with simple constants); the central region is
    handled by a Bernoulli-type supermartingale (`P[change] ≥ 1/128` there) instead of
    [AAE08, Lemma 5]; the corners use `8v ≤ n` and `8x ≥ 7n` as in [AAE08, Table 1], with our own
    weights. The constants are far larger than the paper's (`C = 40000(c+2) + 16^c`), which the
    `∃ C` statements allow; simulations suggest `≈ 4 n log n` interactions.
12. **No stopping times.** The horizon `T` is fixed; consensus is absorbing, so "not in consensus
    at `T`" means that every one of the `T` interactions happened outside consensus, and the
    counters only count interactions in non-consensus regions (`R_x` requires `x < n`).
13. **Theorem 2 via PM** instead of the coupling with a fair walk and Azuma ([AAE08, §5]): while
    `u ≥ 0`, `P[u increases] - P[u decreases] = g b u ≥ 0` with `g = 1/(n(n-1))`, and
    `cosh λ ≤ exp(λ²/2)`.
