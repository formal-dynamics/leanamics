# Formalization differences

Where the statements of `dynamics/` deviate from their sources, and why.

## The finite layer and its bridge to Mathlib (`Bridge`)

1. **`avg f = (Distribution.uniform α).expect f` is not a new declaration.** It already exists
   as `Dynamics.Distribution.uniform_expect` (`(uniform α).expect f = avg f`, the reverse
   orientation); a second, symmetric copy would be a duplicate. Use `← Distribution.uniform_expect` to rewrite `avg` into the
   distribution form.
2. **One extra bridge, `Distribution.independent_uniform_expect`**: the independent product of
   uniform laws is the uniform law on the product. Both `expList` bridges factor through it, and
   it generalizes `Voter.independent_wfKernel_expect` (where `wfKernel V = fun _ => uniform V`).
3. **Two forms of the `expList` bridge** (Mathlib `𝔼` and `Distribution.independent`), since
   `dynamics/` does have the iterated product distribution.
4. **Hypotheses.** The `Distribution` forms need `[Nonempty α]` because `Distribution.uniform`
   does (a distribution cannot live on an empty type). The Mathlib forms need nothing:
   `Finset.expect` and `avg` both vanish on an empty type.
5. **No paper numbering.** `dynamics/` is a generic library without a source paper (see the
   abstract of its blueprint); the docstrings cite the dynamics blueprint labels
   (`def:avg`, `lem:uniform-trajectory`, `lem:uniform-agreement`, `lem:weighted-product`).
6. **`RumorPush.expList_eq_avg_ofFn` is kept although it is a verbatim duplicate**, because the
   rumor_spread blueprint presents it as a theorem ("Faithfulness of the model"); it is a
   one-line alias of `Dynamics.expList_eq_avg_ofFn`.
7. **The copyright-header linter is disabled** (`weak.linter.style.header = false` in the
   lakefiles of `rumor_spread/`, `3-majority/`, `plurality/`, which enable Mathlib's standard
   linter set). It accepts only Mathlib's Apache 2.0 header, while the repository is released
   under the MIT License. A style linter does not affect kernel checking.
8. **`ThreeMajority.avg` is an `abbrev`, not an `export`.** An `export Dynamics (avg)` alias is
   not a constant, and the 3-majority blueprint's `\lean{ThreeMajority.avg}` is checked with
   `Environment.contains`; the reducible abbreviation keeps the name and removes the copy. The
   23 `ThreeMajority.avg_*`/`expList_*` wrappers stay (one-line proofs by the `Dynamics`
   lemmas, tagged in the blueprint, needed by `rw` on `ThreeMajority.avg` terms).
9. **Not yet consolidated:** a few generic lemmas re-proved in moran, voter and undecided
   (see the section on tail bounds below), and the single-copy independence lemmas
   `Plurality.avg_prod_iter`, `Plurality.avg_eval_two`.

## Chernoff bounds for independent Bernoulli trials (`Chernoff`, FND-3)

1. **`≤` instead of `<` in (4.1).** M&U state the ratio upper tail with strict `<`; it fails
   when `μ = 0` (both sides equal `1`). Exercise 4.7 itself uses `≤`. All bounds are
   non-strict.
2. **Closed upper form `exp (-δ²μH/(2+δ))` for all `δ > 0`** (as in the roadmap) instead of Theorem 4.4 (4.2), `e^{-δ²μ/3}` for `0 < δ ≤ 1`. It is stronger
   (`2 + δ ≤ 3` on that range) and is the standard consequence of (4.1) via
   `log (1+δ) ≥ 2δ/(2+δ)`. (4.2), (4.3) (`R ≥ 6μ ⇒ 2^{-R}`) and Corollary 4.6 (two-sided) are
   not stated; they are one-line corollaries.
3. **Finite model of the trials.** "Independent Poisson trials with `Pr(Xᵢ = 1) = pᵢ`" is
   modelled on the finite product `Distribution.independent P : Distribution (ι → α)` (the
   existing product of `dynamics/`) with `Xᵢ = Y i (ω i)`, `Y i` `{0,1}`-valued and
   `pᵢ = (P i).expect (Y i)`; `μ` is written `∑ᵢ pᵢ` (equal to `𝔼X`) rather than `𝔼X`. The
   coordinate type `α` is common to all trials, as in `Distribution.independent`;
   non-identical trials come from different `P i` and `Y i`. Probabilities are
   `Distribution.prob` of a `Prop` (or `avg` of an indicator in the uniform-round form).
4. **Exercise 4.7 is built in.** Every bound is stated for `μH ≥ μ` (upper) or `μL ≤ μ`
   (lower); the exact-mean statements of Theorems 4.4/4.5 are the case `le_rfl`. No sign
   condition on `μH`/`μL` is needed (as in the exercise); `μL < 0` makes the event empty.
5. **Subsets of coins.** The Bernoulli forms count heads over any `S : Finset ι`
   (`S = univ` is the textbook statement). Generalization motivated by EPI-2/EPI-3, which
   count open edges among a subset of the pairs of identical coins `Epidemics.coins`.
6. **Three settings** (general, Bernoulli coins, uniform rounds `avg` over `ι → γ`), the last
   so that packages can apply the bounds to one round (`Kernel.prob_ofStep`) and as a
   drop-in for `ThreeMajority.avg_tail_*` / `Plurality.chernoff_lower` (the latter also
   allows `δ = 0`, trivially). The `avg` forms need no `Nonempty γ`.
7. **New definition `Distribution.bernoulli`** duplicates `Epidemics.bernoulli` (identical
   signature and body, so the two are interchangeable); switching `epidemics/` to the shared
   one is left to a follow-up. No other definition is introduced
   (expectation, probability, product and averages are the existing `dynamics/` API).
8. `δ` ranges are the source's: `δ > 0` (upper), `0 < δ < 1` (lower).
9. **Proof route** is the textbook one (Markov on `e^{tX}`, `1 + x ≤ eˣ` per trial,
   `t = log (1 ± δ)`); the only non-textbook step is the series proof of
   `log (1+δ) ≥ 2δ/(2+δ)`.

## Optional stopping and time reversal (`OptionalStopping`, `Reverse`, FND-4, FND-6)

1. **Targets are events, not states.** `A`, `B : α → Prop` with `φ` constant (`φA`, `φB`) on
   each; the roadmap's `φ(A)`, `φ(B)` for states `a`, `b` is the case `A = (· = a)`,
   `B = (· = b)`. Strictly more general; matches `Kernel.event`.
2. **"Absorption probability" without path space.** The library has no hitting times, so the
   conclusion is stated (i) as the limit of `P(X_T ∈ A)` (no absorption hypothesis needed) and
   (ii) as the supremum `⨆ T, P(X_T ∈ A)` when `A` is absorbing, which is how `Moran.fixation`
   and `Voter.eventualColor` define it.
3. **Invariance hypothesis read literally:** `∀ T, K.iterate T φ x₀ = φ x₀` (only from `x₀`).
   A harmonic `K.apply φ = φ` gives it via `Kernel.iterate_invariant`.
4. **Survival → 0 is a hypothesis** on `K.event (¬A ∧ ¬B)` at `x₀`, as in the roadmap; for
   chains it is supplied by `Kernel.finite_absorption`.
5. **No boundedness or disjointness hypotheses:** `φ` is bounded since `α` is finite, and
   `A ∩ B = ∅` is implied by `φA ≠ φB` (the finite-time bound needs neither).
6. **Additions:** the quantitative finite-time bound `event_error_of_invariant` (generalizes
   `Voter.whiteProbability_error`), and the corollary `iterate_ofStep_foldr` of FND-6.
7. **FND-6 needs no `Nonempty α`:** for empty `α` both sides are `0` (`avg` convention) when
   `T > 0`, and equal `F []` when `T = 0`.
8. **Refactor (not a statement deviation):** `Moran.fixation_eq_of_invariant` changed its
   hypotheses (weaker: no sandwich bounds; the survival limit is passed directly), and 15 helper
   lemmas that only served the old argument were removed.

## Drift theorems and graph-indexed rounds (`Drift`, `DriftSeq`, `GraphRounds`, FND-5, FND-7)

FND-5:

1. **Generic potential.** The paper states Lemma 2.2 for the two-opinion voter model with
   `Ψ = √vol(minority)`, its drift coming from Lemma 2.1 and the conductance bound. We state the
   abstract drift lemma for any nonnegative `Ψ` on a finite chain with drift `c_t / Ψ`; the
   voter instance (`c_t = d_min φ_t / 32`) belongs to VOT-5.
2. **Constant 4 (the paper's 128, not 129).** The statement uses
   `∑ φ ≥ 129 vol(s)/d_min`, the proof needs only `128`, which in drift units
   `c_t = d_min φ_t/32` is `∑_{t<T} c_t ≥ 4 Ψ₀²`. We state the proof's (slightly stronger)
   threshold, non-strict.
3. **Time-dependent chains** are modelled by a family `K : ℕ → Kernel α` (new definition
   `iterateSeq`). The paper's adversary may choose `G_{t+1}` knowing the past; a family of kernels
   covers adversaries depending on the time and the current state (a kernel is a function of the
   state); a history-dependent adversary needs the relevant history in the (finite) state.
4. **Start time.** The paper starts at an arbitrary time `t̂` with `s_t̂` fixed; we start at
   time `0` from `x₀` (shift the family: `fun t => K (t̂ + t)`).
5. **Absorption is `Ψ = 0`**, as in the paper (`T` = first time `s_t = ∅`, i.e. `Ψ_t = 0`), and
   is an explicit hypothesis `habs` (`K.apply Ψ x = 0` when `Ψ x = 0`); in the paper it is
   implicit (consensus is absorbing, used as `𝔼[Ψ_t | T ≤ t] = 0`). It cannot be dropped: a
   chain alternating between `Ψ = 1` and `Ψ = 0` satisfies the drift but is absorbed at no even
   time.
6. Hypotheses are required only for the steps `t < T` (a generalization).
7. **Multiplicative drift.** The paper's Lemma 2.4 is voter-specific (`δ_t = φ_t²/(32n)`,
   `Ψ_min ≥ 1`, `Ψ₀ ≤ n`) and concludes `P(T ≤ τ') ≥ 1 − 1/n²` via AM–GM and `exp`. We state the
   generic bound `∏_{t<T}(1 − δ_t) Ψ₀ / Ψmin` (`(1 − δ)^T Ψ₀/Ψmin` for one kernel); the `exp`
   form follows from `Real.one_sub_le_exp_neg`-type lemmas. No hypothesis on `δ` is needed (if
   `1 − δ_t < 0`, `hdrift` forces `Ψ ≡ 0`). Source typos noticed: the statement of Lemma 2.4
   reads `Pr(T ≤ τ') ≥ 1/n²` (the proof gives `1 − 1/n²`), and its chain of inequalities ends
   with `exp(+∑ φ_i²/32n)` instead of `exp(−∑ φ_i²/32n)`.

FND-7:

8. **"One uniformly random edge per step" uses oriented edges** (`SimpleGraph.Dart`): a uniform
   dart is a uniform edge with a uniform orientation (`avg_edgeRound_edge`,
   `avg_edgeRound_symm`); the orientation is what asymmetric rules (push/pull,
   initiator/responder) need. The roadmap's "random node" variant is not a new type:
   `V × NeighborRound G` read at `(v, r v)` (`avg_vertex_neighborRound`).
9. `NeighborRound G` is empty when `G` has an isolated vertex (then `avg` over it is `0` by
   convention), so the marginal lemmas assume `∀ v, 0 < G.degree v`; the product lemma
   (`avg_neighborRound_prod`) holds unconditionally. Its relation to `RumorPush.Tgt n`
   (complete graph on `Fin n`) is only documented, since `dynamics/` does not import
   `rumor_spread/`.

## Hitting-time lemma (`DriftHitting`, MAJ-8, Doerr et al. SPAA 2011 Claim 2.9)

1. **General finite chain with an observable.** The paper states the claim for a Markov chain
   on `{0, …, q}`; we state it for a `Dynamics.Kernel` on any finite `α` and an observable
   `X : α → ℕ` with `X ≤ q`, the hypotheses holding from every state (i.e. conditionally on the
   whole state). The paper's chain is `α = Fin (q + 1)`, `X = Fin.val` (checked). Reason: the
   application (Lemma 2.8, survey §4 Case 3) uses `Υ = ⌊Δ/(c√n)⌋`, a function of the
   configuration that is not itself a Markov chain; CGPS17's Lemma 4.5 uses the same form.
2. **Time-homogeneous kernel.** The paper's "for any `t ∈ ℕ`" allows time dependence, and
   Lemma 2.8 applies the claim with a `√n`-bounded (adaptive) adversary. A kernel covers
   adversaries that are functions of the current state; time- or history-dependent ones need
   that information in the finite state (as FND-5 deviation 3). A `_seq` version would need a
   time-dependent `hitProb`.
3. **Added hypothesis `c₄ log q ≤ q`** (the target is a possible value of `X`). It is needed for a
   non-asymptotic statement: for `c₄ = 10`, `q = 2` the target `10 log 2 > 2` is never hit, while
   `1 - 2^{-c₆} > 0`. The paper is asymptotic in `q`, where this holds.
4. **Growth only below the target** (generalization): the first property is assumed only at
   states with `X a < c₄ log q`, since `T` depends only on the chain before hitting. This
   matters for the application: Lemma 2.7 gives growth only for `Δ ≤ c√(n log n)`.
5. "`X_{t+1} ≥ 1` with probability `c3`" is read as "with probability at least `c₃`".
6. **`c₅` depends on `c₁, c₂, c₃` too** (written `c5(c4, c6)` in the paper, where `c1, c2, c3`
   are fixed constants of the chain). Necessary: the waiting time at `0` alone is `≈ 1/c₃`
   steps, and numerically `c₅` can be `≈ 10¹²`.
7. **Natural logarithms** (`Real.log`); the paper does not fix the base. A base change is a
   constant factor absorbed by `c₄` (universally quantified) and `c₅` (existential).
   `log_{c₁}` is `Real.logb c₁`.
8. **Time origin.** The paper's chain starts at `X_1` and `T = min{t ∈ ℕ : X_t ≥ c4 log q}`;
   we start at time `0` and `hitProb … t a₀` counts the states at times `0, …, t` (`t`
   transitions). The two readings differ by one step, which `c₅` absorbs (`log q ≥ log 2` for
   `q ≥ 2`; for `q ≤ 1` the target `c₄ log q = 0` is hit at time `0`). The bound is stated for
   every integer `t ≥ c₅ log q + log_{c₁}(c₄ log q)`, equivalent to `T ≤` that real number.
9. Deterministic start `a₀`; a random start follows by averaging.
10. **Edge cases** `q ∈ {0, 1}`: Lean's `Real.log 0 = Real.log 1 = 0` makes the target `0`,
    hit at time `0`; the statements hold trivially there.
11. **Extra corollary** `drift_hitting_log` (not in the paper): the `O(log q)` form used by
    applications; `log_{c₁}(c₄ log q) ≤ c₄ log q / log c₁` is absorbed into the constant.
12. `hitProb` is a thin wrapper over the existing `Kernel.trajectory` (expectation of a path
    indicator); no new expectation, probability or distribution notion is introduced.

## Concentration and tail bounds shared by the packages (`Concentration`, `Chernoff`, `Tail`)

The tail bounds that `median/`, `plurality/` and `3-majority/` used to prove locally are stated
once here; the packages call them directly (the old package names, e.g.
`ThreeMajority.avg_tail_ge_log` or `Plurality.chernoff_lower`, are removed rather than kept as
aliases, and the package blueprints tag the `Dynamics` names).

1. **No paper numbering.** As for the rest of the library, the docstrings cite the textbook
   statements (Dubhashi–Panconesi, Theorem 1.1; Mitzenmacher–Upfal, Theorems 4.4 and 4.5) and
   the package lemmas and blueprint labels (`lem:tails`, `lem:mgf`, `lem:chernoff`,
   `lem:chernofflog`) that a statement replaces.
2. **`{0,1}`-valued coordinates.** The MGF bound and Hoeffding's inequality also hold for
   `[0,1]`-valued coordinates (convexity of `exp`), but every caller has `{0,1}` coordinates
   and `avg_hoeffding` uses the same hypothesis.
3. **Two families of uniform-round Chernoff bounds.** `avg_chernoff_upper`/`avg_chernoff_lower`
   (FND-3, above) are the optimized bounds at `(1 ± δ)μ`. The 3-majority proofs need the
   bounds before `t` is optimized and at an arbitrary threshold `k`: these are
   `avg_chernoff_upper_of_mgf`/`avg_chernoff_lower_of_mgf` (free parameter `t`) and
   `avg_chernoff_upper_log`/`avg_chernoff_lower_log` (`P(X ≥ k)`, `P(X ≤ k)` at most
   `exp(k - μ - k log(k/μ))`, with `μ` any upper, respectively lower, bound on the mean). They
   are stated for `ω : Fin n → γ`, the index type of their callers. The exact-mean forms
   (`μ = 𝔼X`) are not separate declarations.
4. **`avg_chernoff_lower_mul`** is `avg_chernoff_lower` at the exact mean, extended to `δ = 0`
   (where the bound is `1`), which is the form `Plurality.chernoff_lower` had.
5. **`avg_markov_one` assumes `0 ≤ Yᵢ`, not `Yᵢ ∈ {0,1}`**: Markov's inequality needs only
   nonnegativity.
6. **No `[Nonempty γ]`** in `avg_chernoff_mgf`, `avg_chernoff_lower_mul` and
   `variance_le_avg_of_zero_one`: the statements are true on an empty type (the averages
   vanish). `avg_hoeffding_lower` keeps it, as `avg_hoeffding` does.
7. **Predicates rather than sets** in `Distribution.prob_mono` and
   `Kernel.one_sub_avg_le_prob_ofStep`, matching `Distribution.prob` and `Kernel.prob_ofStep`.
   Since the hypothesis of `prob_mono` is strict-implicit, a set inclusion `A ⊆ B` is accepted
   for the events `(· ∈ A)`, `(· ∈ B)`.
8. **Two monotonicity statements**: `Kernel.iterate_monotone` (a subharmonic observable,
   `f ≤ K f`, has nondecreasing iterates) and its absorbing-event form
   `Kernel.event_monotone`. `Kernel.iSup_event_of_invariant` (`OptionalStopping`) proves the
   same monotonicity for its own use.
9. **Mathlib instead of new lemmas** where Mathlib states the fact: `xᵏ/k! ≤ eˣ` is
   `Real.pow_div_factorial_le_exp` and `(q - 1)/q ≤ log q` is `Real.one_sub_inv_le_log_of_pos`.
   The conversions `exp_neg_two_log` and `one_le_of_log_pos` (for `n : ℕ`) are new.
10. **Copies left in other packages**: `Moran.expect_lt_one` and `Voter.expect_lt_one` have the
    statement of `Distribution.expect_lt_one`, `Undecided.avg_lt_one` that of `avg_lt_one`, and
    `Voter.colorProbability_mono` re-proves `Kernel.iterate_monotone` for its indicator; they
    can be replaced by the shared versions.
