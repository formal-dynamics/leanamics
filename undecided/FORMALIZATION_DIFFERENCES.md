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
9. **Not covered**: Theorem 8 (the `Ω(md(c))` lower bound) and Section 4 (expanders).

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
