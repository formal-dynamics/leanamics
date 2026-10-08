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

## Kurtz's law of large numbers for SIR, in discrete time (`Kurtz*`, CRN-2)

Sources: T. G. Kurtz, *Solutions of ordinary differential equations as limits of pure jump
Markov processes*, J. Appl. Probab. 7 (1970) 49–58 (cited without a theorem number); N. Wormald,
*The differential equation method for random graph processes and greedy algorithms*, Lectures
on Approximation and Randomized Algorithms (1999) 73–155, Theorem 5.1; K. Azuma, Tôhoku Math. J.
19 (1967); W. Hoeffding, JASA 58 (1963), Theorem 2.

1. **Discrete time (uniformization) instead of the continuous-time chain.** The stochastic SIR
   chain (`S + I → 2I` at rate `β S I / N`, `I → R` at rate `γ I`) is a continuous-time Markov
   chain, outside the finite-probability layer. We formalize its uniformized jump chain at rate
   `Λ = (β + γ) N`: each step infects with probability `β S I / (N Λ)` and recovers with
   probability `γ I / Λ`. The continuous-time chain is this chain observed along an independent
   Poisson(`Λ`) clock; we replace the Poisson clock by the deterministic times `k / Λ` and do not
   formalize the time change. This is the setting of Wormald's Theorem 5.1 (discrete steps).
2. **Natural-number rates.** With i.i.d. *uniform* rounds (`Dynamics.expList`,
   `Dynamics.Kernel.ofStep`) every transition probability is rational, so the infection/recovery
   choice is one of `β + γ` equally likely clocks with `β, γ : ℕ`, `0 < β, γ`. Since
   `t ↦ x(ct)` solves the system with rates `(cβ, cγ)`, this covers every pair of real rates with
   a rational ratio `β / γ`, up to a time change; irrational ratios are not covered (they would
   need non-uniform rounds).
3. **Pair drawn with replacement.** With `(u, v)` uniform in `Fin N × Fin N` the infection
   probability is exactly `β/(β+γ) · (S/N)(I/N)`, so the drift is exactly
   `sirField / ((β + γ) N)` (with distinct agents it would carry a factor `N/(N-1)`). For `u = v`
   nothing happens.
4. **Time scale.** Step `k` is compared with the ODE at time `k / ((β + γ) N)` and the horizon
   is `k ≤ ⌊T (β + γ) N⌋₊` (the drift is `F/(β+γ)` per step); equivalently, time `k / N` for the
   rates `β/(β+γ)`, `γ/(β+γ)`.
5. **Initial condition, more general than Wormald's; integral-curve hypothesis.** Wormald takes
   the solution through `Y(0)/n`. We allow any initial configuration `x₀` and any solution
   started in the simplex and pay `L · dist (scaled x₀) (s 0, i 0, r 0)` in the tube width
   (Grönwall stability), so the exact case is `dist = 0`, and the classical Kurtz statement
   (`tendsto_deviationProb`, initial data converging to a fixed point) follows without
   constructing ODE solutions. The ODE hypothesis is the integral-curve formulation of EPI-7,
   `IsIntegralCurveOn … (fun _ ↦ sirField β γ) (Set.Ici 0)`, plus `s 0, i 0, r 0 ≥ 0` and
   `s 0 + i 0 + r 0 = 1`, rather than `IsSolution`, which would force `r(0) = 0` and
   `s(0), i(0) > 0` (every `IsSolution` satisfies these hypotheses). Solutions are assumed, not
   constructed (as in EPI-7).
6. **Explicit form of the bound.** Constants `C, c > 0` and `L` depend only on `β, γ, T`
   (uniform in `N`, `x₀`, the solution and `ε`); the bound `C exp(-c ε² N)` (Kurtz/Azuma form)
   is stronger than Wormald's `O((β/λ) exp(-nλ³/β³))` for error `O(λn)`, thanks to the exact
   drift (`λ₁ = 0`), deterministic bounded increments (`γ = 0` in Wormald's (i)) and a maximal
   martingale inequality. No domain `D` or stopping time `T_D` is needed: the chain and the
   solution stay in the simplex.
7. **Uniformity on the grid.** "Uniformly on `[0, T]`" is stated at the step times
   `k / ((β + γ) N)`, `k ≤ ⌊T (β+γ) N⌋₊` (the chain has no values in between; its
   piecewise-constant interpolation is within `O(1/N)` of these, not stated). Distances are sup
   distances on `ℝ × ℝ × ℝ` (`Prod.dist_eq`), Wormald's "for each `l`".
8. **Convergence in probability** is `Tendsto (N ↦ deviationProb …) atTop (𝓝 0)` for every
   `ε > 0`, along all `N` (with the configuration `x₀ N` of `N` agents).
9. **Azuma–Hoeffding is proved in this package** (`expList_azuma`): Mathlib's version
   (`ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF`) is measure-theoretic and not
   maximal, and `Dynamics.Concentration` has Hoeffding/Bernstein only for independent sums. It
   is stated for martingales `∑ D(X_j, ρ_j)` of a process driven by i.i.d. uniform rounds, with
   an arbitrary state type (hence for all martingales of the rounds' filtration, taking
   histories as states), in maximal form (`∃ k ≤ n`), with the classical constant
   `exp(-λ²/(2 n c²))`. Moving it (with Ville's inequality) to `dynamics/` is tracked in issue
   #51.
10. **Additions:** the kernel `chain` and `iterate_chain` (link between the
    `Dynamics.Kernel.ofStep` kernel and the `expList` path averages), and the corollary
    `tendsto_deviationProb` (the "convergence in probability" phrasing).

## Randomized rumor spreading revisited (`Revisited/`, EPI-8)

Source: B. Doerr, A. Kostrygin, *Randomized rumor spreading revisited*, ICALP 2017; long version
arXiv:2303.11150 (numbering of the long version: Lemma 9, Lemma 19, Lemma 20, Definition 11,
Theorem 21, Theorem 31).

### Lemma 20 of the paper needs a major correction

Lemma 20 (Lemma 5 of the overview) claims: if `p_k ≤ p` and `c_k ≤ c/n` for every `k < f n`,
then there is `f' ∈ ]f, 1[` such that, with probability `1 - O(1/n)`, the number of informed
nodes lies in `[f n, f' n]` at the end of some round. The proof bounds one round: from
`k < f n`, `P[k + X(k) ≥ f' n] = O(1/n)`. It then concludes that the whole process jumps over
`[f n, f' n]` with probability `O(1/n)`, but the process may spend many rounds below `f n`, with
a chance to jump in each.

**Example.** The printed statement does not hold for the following process. From every `S` with `|S| < f n`, inform all nodes with probability
`ε = c/n` and otherwise none. For `n ≥ c/p`, `p_k = ε ≤ p` and `c_k = ε(1 - ε) ≤ c/n`, but the
process started from one node jumps from `1` to `n` with probability 1. (The same process with
`ε_k = c k / n²` satisfies the lower exponential growth conditions, so the last sentence of
Theorem 1, which rests on Lemma 20 (through Theorem 27), needs another argument in general. That
sentence is a lower-bound statement, outside the scope of this formalization. The long version
also uses Lemma 20 in the proofs of Theorems 57 and 58.)

Two corrected versions are formalized instead:

* `overshoot_round`, the one-round estimate of the proof, for every `f' ∈ ]f + p(1-f), 1[`;
* `jumpProb_le`, the path statement with the union bound over rounds:
  `P[jump within t rounds] ≤ C/n · E[number of those rounds started below f n]`, that is,
  `O(E[T(|S|, f n)] / n)`.

A smaller slip in the same proof: it writes `E[X(k)] ≤ p n (1 - f)`; the correct bound is
`p (n - k)`. The threshold `f + p(1-f)` for `f'` is still right, because
`k + p(n - k) < n (f + p(1-f))` for `k < f n`.

### Statements

1. **Processes and spreading times.** A rumor-spreading process is a Markov kernel
   (`Dynamics.Kernel`) on the set of informed nodes under which informed nodes stay informed
   (`RumorProcess`). The spreading time `T(k, m)` (Definition 8) is handled through its tail
   `notYet m t S = P[fewer than m nodes informed after t rounds from S]`; expectations
   `E[T] = ∑_t P[T > t]` are bounded through every finite partial sum of this series.
2. **No homogeneity.** Homogeneity (Definition 6) is defined (`Homogeneous`) but not assumed:
   the growth and shrinking conditions (`UpperGrowth`, `UpperShrinking`) are bounds for every
   state, which every homogeneous process satisfying the paper's conditions satisfies.
3. **Starting sets.** The paper starts from one informed node (Theorem 21) or from exactly
   `n - ⌊g n⌋` informed nodes (Theorem 31). Here the growth and total-time theorems start from
   any nonempty `S`, and Theorem 31 from any `S` with `n - |S| ≤ g n`.
4. **Time convention.** Tails are `P[T > ⌈log_{1+γ} n⌉ + r]` and `P[T > ⌈(1/ρ) ln n⌉ + r]`.
   This matches the paper's `P[T > log_{1+γ} n + r]` up to replacing `A` by `A e^α`. The
   constants `A, α, B` and the threshold `N` are explicit and depend only on the parameters of
   the conditions (`N` may be enormous).
5. **Definition 11, uniform side condition.** The side condition `e^{-ρ_n} + a g < 1` is taken
   uniformly in `n`, as `e^{-ρlo} + a g < 1`. The per-`n` reading is not enough: if
   `e^{-ρ_n} + a g = 1 - δ_n` with `δ_n → 0` fast, then rounds near `g n` uninformed nodes shrink
   by a factor `1 - δ_n`, and escaping them costs `Θ(log n)` extra rounds, not `O(1)`. Lemma 19,
   which the paper uses to shrink `g`, likewise needs a uniform `p`.
6. **`ρ_n ∈ [ρlo, ρhi]` is kept**, also for the uniform constants. The upper bound matters: for
   `ρ = ln n`, the term `a u / n` makes the shrinking double exponential, which takes about
   `log₂ ln n` rounds, not `ln n / ρ + O(1) = O(1)`.
7. **Lemma 20's hypotheses.** `overshoot_round` assumes the bounds only for the one starting set,
   and does not require it to be nonempty (Chebyshev does not need it). `jumpProb_le` assumes
   them for every nonempty `S` with `|S| < f n` (the paper's `1 ≤ k < f n`) and starts from a
   nonempty set. The bad event "jumps over `[f n, f' n[`" is a path event (`JumpsOver`), and its
   probability `jumpProb` is an expectation over `Dynamics.Kernel.trajectory`.
8. **Total spreading time.** `spreading_upper_tail` and `spreading_upper_expect` are not single
   statements of the paper. They compose Theorem 21, Lemma 19 and Theorem 31 the way the paper
   does for concrete protocols (Section 3.4, Appendix C, e.g. Theorem 51). The middle-range
   hypothesis is Lemma 19's: every uninformed node becomes informed with probability at least
   `p` when `f n ≤ |S|` and `n - |S| > g n`. Like `connect_tail`, it takes `0 < p ≤ 1`; the
   paper's Lemma 19 takes `0 < p < 1`. If `f + g ≥ 1` the middle range is empty and the
   hypothesis is vacuous. The growth and shrinking conditions have separate constants `a, c`
   and `a', c'`.
9. **Unused hypotheses kept for fidelity.** Some hypotheses of the paper are not needed by the
   proofs (`0 < f`, `f < 1`, `f' < 1` in `overshoot_round`, `0 < f` in `jumpProb_le`, `g < 1` in
   the four shrinking and total-time theorems); they are kept in the statements.

### Proof routes (not statement changes)

1. **Lemma 19** does not use a dummy process. The potential is `g S = n - |S|` while
   `ℓ ≤ |S| < m`, and `0` once `|S| ≥ m`.
2. **Theorem 21.** The phase crossing does not use stochastic domination by sums of geometric
   random variables (Lemmas 10, 11, 25). It is an induction on `Kernel.iterate` with a phase
   potential. `f` is shrunk to `f' = min(f/2, 1/(8(a+1)))` only inside the phase construction,
   to keep the round target `E0(k) = E(k) - A k^{3/4}` increasing; the theorem's threshold stays
   `f n`, and Lemma 19 crosses `[k_J, f n)`. Cantelli's inequality (not Chebyshev's) bounds the
   probability of missing a round target, by `q/(1+q)`. Time is split in half between the phase
   potential and Lemma 19, which halves both exponential rates.
3. **Theorem 31** is proved with the single quadratic potential `Φ = u + (β/n) u²` of the number
   `u` of uninformed nodes, which satisfies `E[Φ'] ≤ e^{-ρ} (1 + K/n) Φ`, instead of the paper's
   phase calculus (target sequence, Chebyshev per phase and geometric domination, Lemmas 32–37).
   A first stage by Lemma 19 brings the number of uninformed nodes below a smaller `g₀ n`.
4. **Lemma 20, path form,** is proved by a union bound along `Kernel.trajectory`.
5. `Distribution.prob` and `Kernel.event` are bridged by `prob_indicator_eq`, because `prob`
   decides propositions with `Classical.propDecidable`.

### Theorem 43 and the push, pull and push–pull protocols

Source: the same paper, Definition 13, Theorem 43 (Appendix B.6) and Theorems 51, 52 and 53
(Appendix C).

1. **Definition 13 and fast finishing, one `n` at a time.** `UpperDoubleShrinking ℓ a c g α`
   asks, for every `S` with `n^{1-α} ≤ u = n - |S| ≤ g n`, that every uninformed node stays
   uninformed with probability at most `a (u/n)^{ℓ-1}` and that covariances are at most
   `c n / u²`. `FastFinishing α τ` is the second hypothesis of Theorem 43: for `u ≤ n^{1-α}`,
   the stay probability is at most `n^{-τ}`. The exponent `ℓ > 1` is real (real powers). The
   parameter ranges are the paper's (`g, α ∈ [0, 1]`, `a, c ≥ 0`, `a g^{ℓ-1} < 1`, `τ > 0`);
   no parameter depends on `n`, so the per-`n` reading loses nothing. The overview's Theorem 3
   uses Definition 5 (conditions for all `u ∈ [1, g n]`), which implies Definition 13 together
   with fast finishing for large `n`.
2. **Tail form.** The paper's `P[T ≥ log_ℓ ln n + r] ≤ O(n^{-α' r + A'})` is stated as
   `P[T > ⌈log_ℓ ln n⌉ + r] ≤ C n^{A' - α' r}`. The formal event is contained in the paper's, so
   the paper's bound implies the formal one; conversely the formal bound gives the paper's up to
   one round, absorbed in `A'`. The expectation is bounded through every partial sum of the tail
   series, as in Theorems 21 and 31.
3. **Starting sets.** Theorem 43 starts from exactly `⌈(1 - g) n⌉` informed nodes; here from any
   `S` with `n - |S| ≤ g n`. The total-time theorems and the instances start from any nonempty
   set (the paper: one informed node).
4. **The proof of Theorem 43 needs a minor correction.** The paper first reduces to a small `g`
   by Lemma 19. This gives `O(1)` expected rounds for that stage, but Lemma 19's tail
   `(g/g') (1 - p)^r` has a rate that does not depend on `n`, so the stated tail
   `O(n^{-α' r + A'})` does not follow for the whole process. The statement holds: the formal
   proof replaces Lemma 19 by geometric phase targets `g μ^j n`, `μ = (1 + a g^{ℓ-1}) / 2`, whose
   failure probability per round is `O(1/n)` by Chebyshev's inequality with the variance bound of
   Lemma 9 (or `O(n^{-τ})` by Markov's inequality below `n^{1-α}` uninformed nodes). In the
   paper's tail bound (11), `J q^{-r}` has a typo in the sign of the exponent.
5. **Proof route** (not a statement change). The double exponential targets are written in
   closed form, `ε_j = exp (-(κ + ℓ^j D₀))` with `κ (ℓ - 1) = ln (2 a₁)` and `a₁ = max a 1`, and
   the number of phases is `J = ⌊log_ℓ (β ln n / (2 D₀))⌋ ≤ log_ℓ ln n` with `β = min α (1/4)`,
   so that `n^{-β} ≤ ε_J ≤ n^{-β/(2ℓ)}`. Instead of the domination by geometric variables
   (Lemma 47), the phase potential `λ^{J - j}` with `λ = n^δ` contracts by `n^{-2δ} + n^{-δ}`
   per round (`notYet_phase_le`); its factor `2^J` is a power of `n`. The last stage uses that
   every uninformed node stays uninformed with probability at most `n^{-τ₃}` below `ε_J n`
   uninformed nodes, and Markov's inequality. The degenerate cases `g = 0` (nothing to do) and
   `α = 0` (fast finishing everywhere) are treated separately.
6. **Total time with double exponential shrinking.** `spreading_upper_tail_double` and
   `spreading_upper_expect_double` compose Theorem 21, Lemma 19 and Theorem 43 as in the proofs
   of Theorems 52 and 53, like `spreading_upper_tail` for Theorem 31. They require `g > 0` (for
   Lemma 19's prefactor `(1 - f)/g`); the unused hypotheses `g ≤ 1` and `α ≤ 1` are kept.
7. **The protocols.** Every node calls a uniformly random node, itself included (the paper's
   convention for complete graphs); the calls of a round form a uniform function
   `Fin n → Fin n`. The package `rumor_spread/` models PUSH, PULL and PUSH–PULL without
   self-calls; the two developments are independent.
8. **The parameters of the instances need a minor correction.** Definition 9 requires
   `0 < f < 1` and `a f < 1`, and Definition 13 requires `a g^{ℓ-1} < 1`. The paper takes
   `f = 1` and `a = 1` for push, `f = 1` for pull, and `g = 1`, `a = 1`, `α = 0` for the double
   exponential shrinking of pull; with `α = 0`, Theorem 43's fast finishing would also be
   required for all `u ≤ n`, which fails at `u = n/2` (the stay probability of pull is `u/n`).
   The formal instances take `f = g = 1/2` (so the middle range of Lemma 19 is empty),
   `a = 1/2` for push (the paper's own estimate `p_k ≥ k/n - k²/(2n²)`), `a = 3/4` and
   `γ = 2` for push–pull (from `p_k ≥ 2k/n - 3k²/(2n²)`), `ℓ = 2`, `a = 1`, `c = 0`,
   `α = τ = 1/2` for the double exponential shrinking of pull and push–pull, and `ρ = 1`,
   `a = 2/e`, `c = 0`, `g = 1/2` for the exponential shrinking of push, as in the paper.
9. **Statements of Theorems 51 to 53.** The paper states the expected times `± O(1)`; only the
   upper bounds are formalized, with exponential tails added. Lower bounds are out of scope.

## Subcritical percolation and small outbreaks (`Subcritical*`, EPI-2)

Source: L. Becchetti, A. Clementi, R. Denni, F. Pasquale, L. Trevisan, I. Ziccardi,
*Percolation and epidemic processes in one-dimensional small-world networks*, arXiv:2103.16398:
Theorem 2.3 (bounded-degree graphs, Section 2.1) and Theorem E.1 (Appendix E, "Regular graphs
below the threshold") with its deferred-decision proof. The Reed–Frost corollary is the one the
paper mentions but omits after Theorem 2.5; its shape follows claim 2 of Theorems 2.4 and 2.5.

1. **Threshold written multiplicatively**: `p * ((d : ℝ) - 1) ≤ 1 - ε` instead of
   `p < (1 - ε)/(d - 1)` (Theorem 2.3) or `p = (1 - ε)/(d - 1)` (Theorem E.1). It covers both
   (the results are monotone in `p`), is equivalent to `p ≤ (1 - ε)/(d - 1)` for `d ≥ 2`, and
   avoids Lean's `x / 0 = 0` at `d = 1`, where the paper's threshold is `+∞`: for `d = 1` any `p`
   is allowed and the statements stay true (components have at most 2 vertices). For `d = 0` the
   hypothesis is automatic and components are singletons.
2. **`ε < 1` assumed** (as in Theorem E.1; Theorem 2.3 says "ε > 0 arbitrary"). For `ε ≥ 1` and
   `d ≥ 2` the hypothesis forces `p = 0`, and an explicit `(C/ε²) log n` bound would be false for
   large `ε` (singletons against a bound tending to 0), so nothing is lost.
3. **"Maximum degree `d`"** is the upper bound `∀ v, G.degree v ≤ d` (equivalent to
   `G.maxDegree ≤ d`); the proof only uses the upper bound. Component sizes are measured as in
   Mathlib, by `K.supp.ncard`.
4. **Explicit tail constant**: `exp (ε - ε² t / 2) = e^ε exp (-ε² t / 2)` for Theorem E.1's
   `exp (-Ω(ε² t))`. The paper's proof claims `exp (-ε² t / 3)` "by Chernoff bounds", but the
   mean of its `t (d - 1) + 1` trials is `(1 - ε) t + p`, not `(1 - ε) t`: the extra trial at the
   source (degree `d`, not `d - 1`) is what the prefactor `e^ε ≤ e` pays for. The bound is
   Markov's inequality on `exp (ε X)`, i.e. the core's Chernoff tail before optimization
   (`Distribution.prob_ge_le_exp`) at the paper's tilt `ε`; the optimized closed forms of the
   core (`bernoulli_chernoff_upper`) do not give this constant directly. Numerically the paper's
   `exp (-ε² t / 3)` also seems to hold for the binomial tail, but it is not what the standard
   argument proves, so it is not claimed.
5. **"W.h.p." made explicit**: probability at least `1 - 1/n` with `C_ε = 10/ε²`, for every
   `n = |V|` (no "n large enough"; for `n ≤ 1` the statement is trivial, and for `n = 0` Lean's
   `1/0 = 0` makes it claim probability 1, which holds since there are no components). The
   paper's union-bound sentence ("probability … at most `1 - 1/n²`") has a typo for `1/n²`.
6. **Deferred decisions as a probability comparison**: the paper's "we have observed at most
   `t (d - 1) + 1` Bernoulli random variables with parameter `p` and found that at least `t` of
   them were 1" is stated as `P(|C(s)| > t) ≤ P(≥ t successes among t (d - 1) + 1 i.i.d.
   Bernoulli(p))`, with the product `Distribution.independent` over `Fin (t * (d - 1) + 1)`
   (natural subtraction: one trial when `d = 0`, still true). The paper's BFS (which has a stray
   `y` for `x`) is replaced by any one-vertex-at-a-time exploration.
7. **Proof route** (not a statement change). There is no BFS queue: the induction is on a budget
   `m` over exploration states `(D, X)` (discovered set, examined pairs whose coins are forced
   closed): if `frontier G D X + (k - 1)(d - 1) ≤ m` then `P(|D| + k ≤ |reach of D|) ≤
   binTail m k`. Conditioning on the coin of one frontier edge, a closed coin removes it from the
   frontier and an open one adds a vertex and at most `d - 1` frontier edges, which is exactly
   the recursion `binTail_succ_succ`. No padding of the coin sequence and no stochastic-domination
   coupling are needed.
8. **Percolation model**: EPI-1's `coins` put one coin on every element of `Sym2 V` (non-edges
   and the diagonal included); only the coins of edges of `G` matter, so `perc G ω` has the law
   of `G_p`.
9. **Reed–Frost corollary**: the paper omits its formal statement for bounded-degree graphs. We
   take the shape of claim 2 of Theorems 2.4 and 2.5 ("stops within `O_ε(log n)` steps,
   `O_ε(|I₀| log n)` recovered nodes") with explicit constants, for EPI-1's pathwise process (one
   coin per edge, equivalent in law to Reed–Frost with transmission probability `p`). The
   reproduction number is `R₀ = p (d - 1)` (an infected non-source node has at most `d - 1`
   susceptible neighbours), and "`R₀ < 1`" is quantified as `R₀ ≤ 1 - ε` with `0 < ε < 1`.
   "Stops within `T` rounds" is `(run G ω I₀ T).infected = ∅`; the total number of infected
   nodes is the final recovered set `(run G ω I₀ (Fintype.card V)).recovered`.
10. **Erdős–Rényi corollary** (an addition): `G(n, c/n)` is `perc ⊤ ω` with `coins (c/n)`; the
    hypotheses `0 ≤ c/n ≤ 1` are needed to form the coins.
11. **Local lemmas.** The binomial tail `binTail` with its recursion, the scalar inequality
    `(1 - ε) e^ε ≤ 1 - ε²/2` (`one_sub_mul_exp_le`), `prob_eq_one`, `prob_eq_zero` and the two
    conditioning lemmas for independent products (`independent_expect_update`,
    `independent_expect_fin_succ`, `coins_prob_split`) are not in `dynamics/` yet; their move is
    tracked in issues #42, #44 and #46. Monotonicity, Markov's inequality on `exp (t X)` and the
    moment-generating-function bound are the core's; congruence, complement and the union bound
    are shared with EPI-3 (`GiantCoins.lean`).

## Small-world networks below the percolation threshold (`SmallWorld*`, EPI-6)

Source: L. Becchetti, A. Clementi, R. Denni, F. Pasquale, L. Trevisan, I. Ziccardi,
*Percolation and epidemic processes in one-dimensional small-world networks*, arXiv:2103.16398
(v3): Definitions 1.1 (`SWG(n, q)`) and 1.2 (`3-SWG(n)`), claim 2 of Theorems 2.1, 2.2, 2.4 and
2.5, and Appendix C (Lemma C.1 and its proof).

1. **"W.h.p." made explicit.** The paper's "with high probability" is `≥ 1 - n^{-Ω(1)}`; the
   statements say "with probability at least `1 - C / n`" with `∃ C`, the rate the proofs give
   (Lemma C.1 states `1 - 1/n` for `n` large). The constants are explicit in the proofs:
   `β = 64 / δ²` and `C = 2` for `SWG(n, c/n)` (`swg_components_small`, valid for every `n ≥ 2`),
   where `p₀ = p* - ε` and `δ = 1 - p₀ - c p₀ (1 + p₀) > 0`; `β = 10 / (2ε)²` and `C = 1` for
   `3-SWG(n)`.
2. **Constants uniform in `p`.** The constants depend only on `c` and `ε` (resp. `ε`) and the
   statements quantify over every `p` below `p* - ε` (resp. `1/2 - ε`) afterwards, as in the
   appendix lemmas (Lemma C.1 is stated for `0 ≤ p ≤ p* - ε`). The inequalities on `p` are strict,
   as in Section 2. `0 ≤ p ≤ 1` replaces the paper's `p > 0` (the case `p = 0` is included).
3. **Bridge probability.** `q = c / n` is written `q * n = c` with `0 ≤ q ≤ 1` (needed to form the
   coins, so `n ≥ c`), as `p * n = 1 + ε` in EPI-3. `n ≥ 3` for `SWG(n, q)` (Definition 1.1) and
   `n ≥ 4` even for `3-SWG(n)` (Definition 1.2).
4. **Models.** The vertex set is `Fin n` with Mathlib's `cycleGraph n`. The bridges of
   `SWG(n, q)` are the open pairs of EPI-1's i.i.d. coins `b ~ coins q` (`perc ⊤ b`, EPI-3's
   `G(n, q)`), so `swg n b = cycleGraph n ⊔ perc ⊤ b`: a bridge on a cycle edge is the same edge,
   as in the paper's `E₁ ∪ E₂`. The coins are indexed by all of `Sym2 (Fin n)`; diagonal coins are
   unused. The matching of `3-SWG(n)` is a uniformly random element of Mathlib's perfect matchings
   of the complete graph (`Subgraph.IsPerfectMatching`), rather than a sequential sampling
   procedure; perfect matchings exist for even `n` (`PerfectMatching.nonempty`).
5. **Joint law.** "Probabilities over the randomness of `G` and of the percolation" is the iterated
   expectation `(coins q).expect fun b => (coins p).prob fun ω => …` (resp. over
   `uniformMatching n`), which is the probability under the product of the two independent laws.
6. **`O(log n)`** is `β * Real.log n` (natural logarithm). Component sizes are measured as in
   Mathlib, by `K.supp.ncard`.
7. **Reed–Frost.** EPI-1's pathwise process `run` with one coin per edge (equal in law to the
   paper's process, each edge being tried at most once; Theorem A.3). "The process stops within
   `T` steps" is `∃ t ≤ T` with no infectious node; "recovered nodes at the end" is
   `(run … n).recovered` (the epidemic is over after `n` rounds); the bounds `O(log n)` and
   `O(|I₀| log n)` share one constant `β`.
8. **Theorem 2.5, claim 2 needs a minor correction.** In v3 its hypothesis repeats the `SWG(n, c/n)`
   threshold `p < (√(c² + 6c + 1) - c - 1)/(2c) - ε`, but `3-SWG(n)` has no parameter `c`. The
   formal statement uses `p < 1/2 - ε`, the threshold of Theorem 2.2, claim 2, from which the
   paper derives it.
9. **Theorem 2.2, claim 2** is derived, as in the paper, from Theorem 2.3: EPI-2's
   `prob_components_small` with `d = 3` (`swg3_degree_le`) and `2ε` in place of `ε`
   (`2 p ≤ 1 - 2ε`). Theorem 2.3 itself is EPI-2's and is not restated.
10. **Proof route for Lemma C.1** (not a statement change). The paper dominates the size of a
    breadth-first search by a single-type Galton–Watson process with offspring
    `W = Y + ∑_{j ≤ 2Y} L_j` (`Y ~ Bin(n, pc/n)`, `L_j` geometric) and bounds `∑ W_i` by Chernoff
    bounds on `Y` and on the negative binomial. Here the two coin families are first collapsed
    into one percolation of the complete graph with independent coins (`expect_prob_swg_eq`):
    probability `p` on cycle edges, `p q` on the other pairs. The exploration then processes one
    node at a time and tracks two types of nodes: discovered through a cycle edge (weight `1`, at
    most one undiscovered cycle neighbour) or not (weight `1 + p₀`, at most two). These weights
    are a left eigenvector of the mean matrix at `p₀`. Below the threshold the expected weight
    discovered from a node of weight `w` is at most `(1 - δ/2) w`. An exponential of the weight
    balance is then a supermartingale, by deferred decisions on fresh coins, which gives
    `P(|C(s)| > t) ≤ exp (δ/4 - δ² t / 32)`. In the paper's Algorithm 3 the queue starts as `{s}`
    and only local clusters of bridge neighbours are enqueued, so the cycle neighbours of `s` (its
    local cluster) are never visited unless reached through a bridge: the claim that the
    algorithm visits the component of `s` needs a minor correction (start from the local cluster
    of `s`, which adds one more local cluster to the domination). The exploration here processes
    every discovered node, the root included, whose two cycle neighbours are covered by its
    weight `1 + p₀`.
11. **Not formalized (yet).** Claim 1 (the supercritical regime) of Theorems 2.1, 2.2, 2.4 and 2.5
    (Appendices B and D), and the extensions of Appendix F.
12. **Local lemmas.** The supermartingale lemma for adaptive observations
    (`expect_prod_hist_le_one`) and its deferred-decisions form for fresh coordinates
    (`expect_prod_hist_le_one_of_fresh`), the coordinatewise combination of independent families
    (`expect_expect_coord`, `expect_mul_of_dep`), Markov's inequality `prob_le_expect_div`, the
    moment-generating function of a weighted block of coins (`expect_exp_sum_open`) and the union
    bound over components for an arbitrary random graph (`prob_components_le_of_tail'`, the
    form of EPI-2's `prob_components_le_of_tail` for any distribution) are not in `dynamics/`
    yet; their move is tracked in issues #42, #46 and #49.

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

## COBRA ⇔ BIPS duality (`Cobra*`, EPI-4)

Source: C. Cooper, T. Radzik, N. Rivera, *The coalescing-branching random walk on expanders and
the dual epidemic process*, PODC 2016, arXiv:1602.05768: Theorem 4 (Section 2) and its case
`C = {u}`, equation (2) (Section 1). The paper's Theorem 4: for a connected regular graph and
`k ≥ 1`, `P̂(Hit_C(v) > t | C₀ = C) = P(C ∩ A_t = ∅ | A₀ = v)` for all `v`, `C ⊆ V`, `t ≥ 0`.
The cover-time bounds (Theorems 1 to 3) are not formalized.

1. **Hypotheses dropped (statement strengthened).** The paper assumes `G` connected and regular
   and `k ≥ 1`. `cobra_bips_duality`, `cobra_bips_duality_singleton` and the pathwise lemma hold
   for every finite simple graph and every `k` (including `k = 0`): the paper's proof only matches
   each vertex's choice law in the two processes and never uses regularity (exhaustive checks on
   small irregular graphs agree). The paper's hypotheses appear in `choices_nonempty`: on a
   connected graph with at least two vertices the round type is nonempty, so both sides are
   genuine probabilities. On a graph with an isolated vertex and `k ≥ 1` (where neither process
   is defined) the round type is empty and both sides are `0` for `t ≥ 1` by the `avg`
   convention, so the statement is vacuous there.
2. **Conditioning on the initial state.** `P̂(· | C₀ = C)` and `P(· | A₀ = v)` are expressed by
   starting the round-driven processes at `C` and `{v}` and averaging over `t` i.i.d. uniform
   rounds with `Dynamics.expList` (finite probability layer, no path space). A round
   (`Choices G k`) gives every vertex `k` neighbours sampled uniformly with replacement; both
   processes read the same round type, a coupling of the two per-vertex sampling laws, and each
   ignores the choices it does not use (COBRA: vertices outside `C_s`; BIPS: the source `v`), as
   in the paper's model.
3. **Hitting time as an event.** `Hit_C(v) = min {s ≥ 0 : v ∈ C_s}` is not defined as a random
   variable; `Hit_C(v) > t` is written `∀ s ≤ t, v ∉ C_s` with `C_s = cobraRun C (l.take s)`,
   time 0 included (the convention fixed by the paper's base case, "trivial if `v ∈ C`, since
   both probabilities are 0").
4. **Extra pathwise result and proof route.** The pathwise identity `cobra_hit_iff_bips_reverse`
   (COBRA from `C` along the rounds `r₁, …, r_t` visits `v` iff BIPS from `{v}` along
   `r_t, …, r₁` infects a vertex of `C`) is not stated in the paper, whose intuition paragraph
   sketches it for `k = 1`. Theorem 4 is proved from it and the time reversal of i.i.d. rounds
   (`Dynamics.expList_comp_reverse`), instead of the paper's induction on `t` with one-step
   conditioning; the statement is the same.
5. **Generalized BIPS start.** `bipsRun` takes any initial infected set `A₀`; the theorems use
   the paper's `A₀ = {v}`.
6. **Round type local to the package.** `Choices G k = (x : V) → Fin k → G.neighborSet x` is the
   `k`-sample version of the core's `NeighborRound G` (`Dynamics.GraphRounds`, one uniform
   neighbour per vertex); it is equivalent to `k` independent such rounds (`Fin k → NeighborRound
   G`, after swapping the arguments) but is kept in `epidemics/` with the statements as written.
