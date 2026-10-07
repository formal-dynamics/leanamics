# PROGRESS: CRN-2 (Kurtz's law of large numbers for SIR, discrete time)

Source: `ROADMAP.md`, row CRN-2 (depends on EPI-7, on this branch `crn2-kurtz`).

References:

* N. Wormald, *The differential equation method for random graph processes and greedy
  algorithms*, Lectures on Approximation and Randomized Algorithms (1999) 73–155, **Theorem 5.1**
  (read from the PDF): hypotheses (i) boundedness `max_l |Y_l(t+1) - Y_l(t)| ≤ β` w.p. `≥ 1 - γ`,
  (ii) trend `|E(Y_l(t+1) - Y_l(t) | H_t) - f_l(t/n, Y(t)/n)| ≤ λ₁`, (iii) Lipschitz `f_l` on a
  domain `D`; conclusion (b): with probability `1 - O(nγ + (β/λ) exp(-nλ³/β³))`,
  `Y_l(t) = n z_l(t/n) + O(λn)` uniformly for `0 ≤ t ≤ σn`, where `z` solves `z' = f(x, z)` with
  `z(0) = Y(0)/n`.
* T. G. Kurtz, *Solutions of ordinary differential equations as limits of pure jump Markov
  processes*, J. Appl. Probab. 7 (1970) 49–58 (the law of large numbers for density-dependent
  chains; theorem number not verified, so docstrings cite the paper without a number).
* K. Azuma, Tôhoku Math. J. 19 (1967); W. Hoeffding, JASA 58 (1963), Theorem 2.

## Status

* **Phase 1 (pin statements): done** (2026-10-07). `lake build Epidemics` succeeds; the only
  warnings are `declaration uses 'sorry'` (8, one per pinned theorem). `PINNED.txt` (repository
  root) lists the 17 pinned declarations (8 theorems, 9 definitions).
* **Phase 2 (proofs, docs): done** (2026-10-07). All 8 pinned theorems are proved; no `sorry`,
  `admit`, `axiom`, `native_decide`, `implemented_by`, `extern` or `set_option` in the new files.
  `lake build Epidemics` is warning-free. `#print axioms` (scratch file under `/tmp`, 16 pinned and
  helper declarations, and `python3 ../scripts/check_axioms.py` on `Audit.lean`, 33 declarations)
  reports only `propext`, `Classical.choice`, `Quot.sound`. Pinned text unchanged: a script
  comparing docstring + text up to `:=` (whole block for `inductive Compartment`) against the
  phase-1 commit `fa6b81a` reports all 17 declarations identical, `KurtzDefs.lean` (definition
  bodies) is byte-identical to phase 1, and `PINNED.txt` is unchanged.
* No pinned statement turned out false; none was weakened.

## Pinned (text up to `:=` frozen; see `PINNED.txt`)

All in namespace `Epidemics.Kurtz`. Definition bodies are part of the specification: do not change
them either, even though the gate only freezes the text up to `:=`.

| Declaration | File | Statement in words |
| --- | --- | --- |
| `incrementSum` (def) | `KurtzAzuma.lean` | `incrementSum step D x l = ∑_{j<|l|} D X_j l_j`, `X_0 = x`, `X_{j+1} = step X_j l_j` (recursion on `l`) |
| `expList_azuma` | same | `avg (D y) = 0 ∀ y`, `|D y a| ≤ c`, `0 ≤ λ` ⇒ `expList R n [∃ k ≤ n, λ ≤ incrementSum step D x (l.take k)] ≤ exp(-(λ²/(2 n c²)))` (state type `σ` arbitrary) |
| `Compartment` (inductive) | `KurtzDefs.lean` | `susceptible | infected | recovered`, `DecidableEq`, `Fintype` |
| `Config N` (abbrev) | same | `Fin N → Compartment` |
| `count c x` (def) | same | `#{v | x v = c}` (ℕ) |
| `scaled x` (def) | same | `(S/N, I/N, R/N) : ℝ × ℝ × ℝ` |
| `Round N β γ` (abbrev) | same | `Fin N × Fin N × (Fin β ⊕ Fin γ)`: ordered pair with replacement, one of `β` infection / `γ` recovery clocks |
| `step β γ x ρ` (def) | same | infection clock: `x u = I ∧ x v = S` ⇒ `v := I`; recovery clock: `x u = I` ⇒ `u := R`; else unchanged |
| `chain β γ N` (def) | same | `Dynamics.Kernel.ofStep (step β γ)`, needs `[Nonempty (Round N β γ)]` |
| `deviationProb β γ x₀ x δ n` (def) | same | `expList (Round N β γ) n [∃ k ≤ n, δ < dist (scaled ((l.take k).foldl (step β γ) x₀)) (x (k / ((β+γ) N)))]` |
| `drift_susceptible` | `KurtzDrift.lean` | `avg_ρ ((scaled (step x ρ)).1 - (scaled x).1) = (sirField β γ (scaled x)).1 / ((β+γ) N)` (no hypotheses) |
| `drift_infected` | same | same, second component |
| `drift_recovered` | same | same, third component |
| `dist_scaled_step_le` | same | `dist (scaled (step β γ x ρ)) (scaled x) ≤ 1 / N` |
| `iterate_chain` | same | `(chain β γ N).iterate n f x₀ = expList (Round N β γ) n (fun l ↦ f (l.foldl (step β γ) x₀))` |
| `law_of_large_numbers` | `Kurtz.lean` | `0 < β, γ`, `0 < T` ⇒ `∃ C c L, 0 < C ∧ 0 < c ∧ ∀ N > 0, ∀ x₀ s i r`, integral curve of `sirField β γ` on `Ici 0`, `s 0, i 0, r 0 ≥ 0`, sum `1`, `∀ ε > 0`: `deviationProb β γ x₀ (s, i, r) (L · dist (scaled x₀) (s 0, i 0, r 0) + ε) ⌊T (β+γ) N⌋₊ ≤ C exp(-(c ε² N))` |
| `tendsto_deviationProb` | same | fixed solution started in the simplex, `scaled (x₀ N) → (s 0, i 0, r 0)`, `ε > 0` ⇒ `deviationProb β γ (x₀ N) (s, i, r) ε ⌊T (β+γ) N⌋₊ → 0` |

Import chain: `KurtzDefs` (imports `Dynamics.Rounds`, `KermackMcKendrickDefs`) ← `KurtzDrift`;
`KurtzAzuma` (imports `Dynamics.Uniform`); `Kurtz` imports `KurtzAzuma`, `KurtzDrift`. All four
are imported by `Epidemics.lean`.

Checks done in phase 1 (scratch files under `/tmp`, nothing in the repo):

* elaborated types (`#check`, `pp.numericTypes`): every cast is at the leaves, in `ℝ`
  (`(↑β + ↑γ) * ↑N`, `↑k / ((↑β + ↑γ) * ↑N)`, `⌊T * (↑β + ↑γ) * ↑N⌋₊`);
* `incrementSum st D x (a :: l) = D x a + incrementSum st D (st x a) l`, `incrementSum … [] = 0`
  and `step β γ x (u, v, .inr c) = …` hold by `rfl`;
* EPI-7's `IsSolution` gives the hypotheses of the main theorems (`h.isIntegralCurveOn`,
  `h.s_zero_pos.le`, `h.i_zero_pos.le`, `h.r_zero.ge`, `h.sum_zero`);
* **drift identity and increment bound checked by exact rational enumeration** (Python, all
  configurations with `1 ≤ N ≤ 4`, `0 ≤ β, γ ≤ 3`, `β + γ ≥ 1`: 1800 configurations, 0 failures);
* **maximal Azuma checked by exact enumeration** on a state-dependent mean-zero chain with
  `R = Fin 3`, `c = 2`, `n ≤ 8`, several `λ` (worst `prob - bound = 0`, at `λ = 0`).

## Why the statements are true (proof sketch; the phase-2 plan, followed)

Differences from this plan in the executed proof: the Euler error is bounded more crudely by
`Lip · M · h²` (no factor `1/2`); the "event empty" case uses `ε ≥ 2` (sup distance of two points
of the unit ball) instead of `ε ≥ 1`; `C = 6 exp(4 c L T Lip)` instead of a `max`; Hoeffding's
lemma is used in the `|D| ≤ c` form with `Real.cosh_le_exp_half_sq`, exactly as planned.

Notation: `h = 1/((β+γ)N)`, `n = ⌊T(β+γ)N⌋₊`, `t_k = k h ≤ T` for `k ≤ n`, `X_k` the scaled
state, `x(t) = (s t, i t, r t)`, sup norm on `ℝ³`.

1. **Drift** (helper file `KurtzCount.lean`): split the sum over `Round` with
   `Fintype.sum_prod_type`, `Fintype.sum_sum_type`; count after `Function.update`
   (`count c (update x v c') = count c x - [x v = c] + [c' = c]`); the infection rounds that
   change something are `#{u | x u = I} · #{v | x v = S} · β` (for `u = v` nothing happens), the
   recovery ones `#{u | x u = I} · N · γ`; `card Round = N² (β+γ)`. Cases `N = 0` and
   `β + γ = 0`: both sides `0` (empty `avg`, `x / 0 = 0`).
2. **Bounded increments**: one `Function.update` changes each count by at most 1;
   `Prod.dist_eq`, `Real.dist_eq`.
3. **`iterate_chain`**: `Dynamics.Kernel.iterate_ofStep`.
4. **`expList_azuma`**: (a) Hoeffding's lemma for `avg (D y) = 0`, `|D| ≤ c`:
   `avg (exp (θ D y ·)) ≤ exp (θ² c² / 2)` (convexity: `e^{θd} ≤ ((c-d) e^{-θc} + (c+d) e^{θc})/(2c)`,
   average gives `cosh (θc)`, then `Real.cosh_le_exp_half_sq`; `c = 0` separately).
   (b) Ville's inequality by induction on `n`, generalizing the start `x` and the level `μ > 0`:
   for `Z_k = exp(θ M_k - k θ² c²/2)`, `expList [∃ k ≤ n, μ ≤ Z_k] ≤ 1/μ` (if `μ ≤ 1` trivial;
   else peel the first round with `expList_succ`, `Z_{k+1}(x, a :: l) = z(x,a) Z_k(step x a, l)`
   with `z = exp(θ D x a - θ²c²/2)`, IH at level `μ / z`, then `avg z ≤ 1` by (a)).
   (c) `λ ≤ M_k`, `k ≤ n` ⇒ `Z_k ≥ exp(θλ - nθ²c²/2)`; take `θ = λ/(n c²)`. Edge cases: `n = 0`
   (bound `exp 0 = 1` in Lean since `x/0 = 0`), `c = 0` (then `D = 0`), `R` empty
   (`expList (n+1) = 0`).
5. **ODE side** (helper `KurtzODE.lean`, reusing `KermackMcKendrickCalculus.lean`): component
   derivatives from `IsIntegralCurveOn` (as `IsSolution.hasDerivWithinAt_s/i/r`, but without
   `IsSolution`); conservation `s + i + r = 1` (`eq_of_hasDerivWithinAt_zero`); `s ≥ 0` from the
   first integral `s e^{R₀ r} = const` (adapt `IsSolution.s_mul_exp_eq`, which uses only the
   derivatives and `γ ≠ 0`); `i ≥ 0` by the integrating factor
   `i(t) exp(-∫₀ᵗ (β s - γ)) = i(0)` (`intervalIntegral.integral_hasDerivWithinAt_right`);
   `r` nondecreasing so `r ≥ r 0 ≥ 0`. Hence `x(t)` stays in the simplex for `t ≥ 0`.
   On the simplex `sirField` is `Lip = 2β + γ`-Lipschitz and bounded by `M = β + γ` (sup norm),
   so the Euler error is `‖x(t+h) - x(t) - h F(x(t))‖ ≤ Lip M h² / 2` (mean-value inequality,
   e.g. `norm_image_sub_le_of_norm_deriv_le_segment'`).
6. **Grönwall**: `e_k = X_k - x(t_k)` satisfies
   `‖e_k‖ ≤ ‖e_0‖ + h Lip ∑_{j<k} ‖e_j‖ + max_{j≤n} ‖M_j‖ + T h Lip M / 2`; the sum form follows
   from Mathlib's `discrete_gronwall` (`Mathlib/Analysis/ODE/DiscreteGronwall.lean`) applied to
   `B_k = A + h Lip ∑_{j<k} ‖e_j‖`, giving `‖e_k‖ ≤ L (‖e_0‖ + max ‖M‖ + T h Lip M/2)` with
   `L = exp(Lip T)`.
7. **Assembly of `law_of_large_numbers`**: martingale `M^l_k = incrementSum (step β γ) D_l x₀
   (l.take k)` with `D_l y ρ = (scaled (step y ρ))_l - (scaled y)_l - F_l(scaled y) h`
   (`|D_l| ≤ 2/N`, mean zero by 1), so `X_k - X_0 - h ∑_{j<k} F(X_j) = M_k`. Six Azuma bounds
   (three coordinates, `±D_l`) at level `ε/(2L)` give failure probability
   `≤ 6 exp(-ε² N / (32 L² T (β+γ)))` (union bound via `expList_le_expList`, `expList_add`).
   Constants: `c = 1/(32 L² T (β+γ))`; when `T h Lip M/2 > ε/(2L)` (i.e. `N < K/ε`) or
   `ε ≥ 1` use: for `ε ≥ 1` the event is empty (both points in the simplex, sup distance `≤ 1`,
   `L ≥ 1`), for `ε < 1` we have `c ε² N < c K`, so `C = max 6 (exp (c K))` makes the bound `≥ 1`.
8. **`tendsto_deviationProb`**: from 7 with `ε/2`; eventually `L · dist (scaled (x₀ N)) x(0) ≤ ε/2`;
   `deviationProb` is antitone in `δ` and nonnegative (`expList_nonneg`); squeeze.
9. Docs: `README.md` table, blueprint section with `\lean{}`, `Audit.lean` `#print axioms` lines.

## Proved

Everything (8/8 theorems). Files (`epidemics/Epidemics/`), lines, content:

| File | Lines | Content |
| --- | --- | --- |
| `KurtzDefs.lean` | 84 | pinned definitions (unchanged since phase 1) |
| `KurtzCount.lean` | 92 | counts after `Function.update` and after one `step`; total change over all rounds (`sum_count_step`); `abs_count_step_sub_le`; `card_round` |
| `KurtzDrift.lean` | 100 | pinned: three drift identities, `dist_scaled_step_le`, `iterate_chain` |
| `KurtzAzumaAux.lean` | 135 | Hoeffding's lemma `avg_exp_mul_le`; Ville's maximal inequality `expList_ville`; `expList_le_one`, `expList_le_expList_of_length`, `ite_one_zero_le_of_imp` |
| `KurtzAzuma.lean` | 120 | pinned `incrementSum`, `expList_azuma`; `incrementSum_mul_sub` |
| `KurtzODE.lean` | 256 | invariance of the simplex for any integral curve of `sirField` started in it (`sir_norm_le_one`); Lipschitz and bound of the field on the unit ball; Euler error `sir_euler_le` |
| `KurtzGronwall.lean` | 117 | sum-form Grönwall `le_mul_exp_of_le_add_sum` (from Mathlib's `discrete_gronwall`); discrete stability `norm_sub_le_of_euler` |
| `KurtzMainAux.lean` | 261 | telescoping of `incrementSum`; coordinates `coord`; martingale increments `mgIncr` (centred, `≤ 2/N`); `incrementSum_mgIncr`; `close_of_good` |
| `KurtzBound.lean` | 130 | `deviationProb_nonneg/anti`; `mgEvent`; `fail_indicator_le`; `deviationProb_le_azuma` (six Azuma bounds) |
| `Kurtz.lean` | 201 | pinned: `law_of_large_numbers`, `tendsto_deviationProb` |

Total 1496 lines. Docs: `README.md` (CRN-2 section and table, provenance), `blueprint/src/content.tex`
(new section, `\lean{}` links), `Audit.lean` (8 new `#print axioms` lines).

Constants of `law_of_large_numbers`: `Lip = 2β + γ`, `L = exp(Lip T)`, `c = 1/(32 L² T (β + γ))`,
`C = 6 exp(4 c L T Lip)`. Case analysis: `ε ≥ 2` (event empty: both points in the unit ball);
`ε N < 2 L T Lip` (bound `≥ 1`); `⌊T(β+γ)N⌋ = 0` (only `k = 0`, event empty as `L ≥ 1`); otherwise
`deviationProb_le_azuma` at level `δ = ε/(2L)` and `ε² N² /(32 L² n) ≥ c ε² N` from `n ≤ T(β+γ)N`.

Reusable pieces:

* `expList_azuma` (+ `expList_ville`, `avg_exp_mul_le`): martingale concentration for any process
  driven by i.i.d. uniform rounds (`Dynamics.expList`), arbitrary state type; candidates for
  `dynamics/Dynamics/Concentration.lean`.
* `le_mul_exp_of_le_add_sum`, `norm_sub_le_of_euler`: deterministic stability of Euler schemes
  with a perturbation (any differential-equation-method argument).
* `KurtzODE.lean`: invariance of the simplex for SIR solutions with nonnegative initial data
  (generalizes EPI-7's positivity, which assumed `IsSolution`).
* `incrementSum_telescope`, `incrementSum_take`: compensators of chains as `Finset.range` sums.

## Remaining

Nothing. Possible follow-ups (not required): move the Azuma/Ville lemmas to `dynamics/`; a
continuous-time statement (Poisson time change) or real rates (non-uniform rounds).

## Errors

No statement turned out false or unprovable. Problems met and fixed during phase 2:

* `split_ifs` also splits the indicator `if`s on the compartment; use `by_cases` and
  `rw [if_pos h, if_pos h]` for the step's condition only.
* `ring` cannot split `(N² (β + γ))⁻¹` once `simp` has expanded it into a sum; evaluate the
  indicators with `reduceCtorEq`/`↓reduceIte` only, then `generalize (β : ℝ) + γ = B`, and close
  `N · N⁻¹ = 1` with `linear_combination … * mul_inv_cancel₀ hN` after a case split on `N = 0`.
* Dot notation on `hx : IsIntegralCurveOn …` fails (the type unfolds to a `∀`): the ODE lemmas are
  plain `sir_*` lemmas taking `hx` explicitly.
* `simpa` on `HasDerivWithinAt` of a difference produced Pi-subtraction with other instance paths;
  `congr_deriv` avoids it (as in EPI-7).
* `omit [Fintype R] in` must precede the docstring.
* The first version of `law_of_large_numbers` hit the heartbeat limit (one large declaration;
  bisection located it in the final `calc` with `gcongr`/`nlinarith` over a large context): fixed
  without `maxHeartbeats` by moving the six-event bound to `KurtzBound.lean`
  (`fail_indicator_le`, `deviationProb_le_azuma`) and using explicit monotonicity lemmas.
* `push_neg` is deprecated in this Mathlib: `push Not`.

Phase-1 notes: the root module `Dynamics` is not built in `dynamics/.lake`, so scratch files
import `Dynamics.Rounds` / `Dynamics.Concentration` (built), and so do the new files. `step` and
`incrementSum` are written as `… := match …` so that the gate's "text up to `:=`" is well defined
(precedent: earlier pinned definitions all have `:=`).

## Deviations from the paper

1. **Discrete time (uniformization) instead of the continuous-time chain.** The roadmap's chain
   (`S + I → 2I` at rate `β S I / N`, `I → R` at rate `γ I`) is a continuous-time Markov chain,
   outside the finite-probability layer. We formalize its uniformized jump chain at rate
   `Λ = (β + γ) N`: each step infects with probability `β S I / (N Λ)` and recovers with
   probability `γ I / Λ`. The continuous-time chain is this chain observed along an independent
   Poisson(`Λ`) clock; we replace the Poisson clock by the deterministic times `k / Λ` and do not
   formalize the time change. This is the setting of Wormald's Theorem 5.1 (discrete steps).
2. **Natural-number rates.** With i.i.d. *uniform* rounds (`Dynamics.expList`,
   `Dynamics.Kernel.ofStep`) every transition probability is rational, so the infection/recovery
   choice is one of `β + γ` equally likely clocks with `β, γ : ℕ`, `0 < β, γ`. Since
   `t ↦ x(ct)` solves the system with rates `(cβ, cγ)`, this covers every pair of real rates with
   a rational ratio `β / γ`, up to a time change; irrational ratios are not covered (they would
   need non-uniform rounds, outside `expList`).
3. **Pair drawn with replacement** (the task suggested distinct agents): with `(u, v)` uniform in
   `Fin N × Fin N` the infection probability is exactly `β/(β+γ) · (S/N)(I/N)`, so the drift is
   exactly `sirField / ((β + γ) N)` (with distinct agents it would carry a factor `N/(N-1)`).
   For `u = v` nothing happens.
4. **Time scale.** Step `k` is compared with the ODE at time `k / ((β + γ) N)` and the horizon is
   `k ≤ ⌊T (β + γ) N⌋₊` (the drift is `F/(β+γ)` per step, as allowed by the task); equivalently,
   time `k / N` for the rates `β/(β+γ)`, `γ/(β+γ)`.
5. **Initial condition, more general than Wormald's.** Wormald takes the solution through
   `Y(0)/n`. We allow any initial configuration `x₀` and any solution started in the simplex and
   pay `L · dist (scaled x₀) (s 0, i 0, r 0)` in the tube width (Grönwall stability), so the exact
   case is `dist = 0`, and the classical Kurtz statement (`tendsto_deviationProb`, initial data
   converging to a fixed point) follows without constructing ODE solutions. The ODE hypothesis is
   EPI-7's integral-curve formulation `IsIntegralCurveOn … (fun _ ↦ sirField β γ) (Set.Ici 0)`
   plus `s 0, i 0, r 0 ≥ 0`, `s 0 + i 0 + r 0 = 1`, rather than `IsSolution`, which would force
   `r(0) = 0` and `s(0), i(0) > 0` (every `IsSolution` satisfies these hypotheses). Solutions are
   assumed, not constructed (as in EPI-7).
6. **Explicit form of the bound.** Constants `C, c > 0` and `L` depend only on `β, γ, T`
   (uniform in `N`, `x₀`, the solution and `ε`); the bound `C exp(-c ε² N)` (Kurtz/Azuma form) is
   stronger than Wormald's `O((β/λ) exp(-nλ³/β³))` for error `O(λn)`, thanks to the exact drift
   (`λ₁ = 0`), deterministic bounded increments (`γ = 0` in Wormald's (i)) and a maximal
   martingale inequality. No domain `D` / stopping time `T_D` is needed: the chain and the
   solution stay in the simplex.
7. **Uniformity on the grid.** "Uniformly on `[0, T]`" is stated at the step times
   `k / ((β + γ) N)`, `k ≤ ⌊T (β+γ) N⌋₊` (the chain has no values in between; its piecewise-constant
   interpolation is within `O(1/N)` of these, not stated). Distances are sup distances on
   `ℝ × ℝ × ℝ` (`Prod.dist_eq`), Wormald's "for each `l`".
8. **Convergence in probability** is `Tendsto (N ↦ deviationProb …) atTop (𝓝 0)` for every
   `ε > 0`, along all `N` (with the configuration `x₀ N` of `N` agents).
9. **Azuma–Hoeffding pinned in this package** (`expList_azuma`): Mathlib's version
   (`ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF`) is measure-theoretic and not
   maximal; `Dynamics.Concentration` has Hoeffding/Bernstein only for independent sums. It is
   stated for martingales `∑ D(X_j, ρ_j)` of a process driven by i.i.d. uniform rounds, with an
   arbitrary state type (hence for all martingales of the rounds' filtration, taking histories as
   states), in maximal form (`∃ k ≤ n`), with the classical constant `exp(-λ²/(2 n c²))`.
10. **Extras beyond the task list:** the kernel `chain` and `iterate_chain` (link between the
    `Dynamics.Kernel.ofStep` kernel and the `expList` path averages), and the corollary
    `tendsto_deviationProb` (the roadmap's "convergence in probability" phrasing).
