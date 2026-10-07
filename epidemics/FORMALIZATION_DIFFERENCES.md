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
