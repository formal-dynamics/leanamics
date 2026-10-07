# Epidemics: Reed–Frost and bond percolation; the Kermack–McKendrick SIR model; Kurtz's law of large numbers

A Lean formalization of the pathwise correspondence between the Reed–Frost (Independent Cascade)
epidemic and bond percolation (after Kempe, Kleinberg and Tardos, KDD 2003; see also Becchetti et
al., arXiv:2103.16398, Theorem A.3).

**Model.** Every edge of a finite graph `G` carries one coin `ω e : Bool`; the open edges form the
percolated graph `perc G ω`. In each round, a susceptible node with an infected neighbour across an
open edge becomes infected, and every infected node recovers for good.

**Main results** (in [`Epidemics/ReedFrost.lean`](Epidemics/ReedFrost.lean), namespace `Epidemics`):

| Result | Lean declaration |
| --- | --- |
| Nodes infected in round `t` = nodes at distance `t` from `I₀` in `perc G ω` | `infected_iff` |
| Nodes recovered by round `t` = nodes at distance `< t` | `recovered_iff` |
| The epidemic is over after `card V` rounds, and as soon as all finite distances are `< t` | `extinct`, `extinct_of_dist_lt` |
| Final outbreak = nodes connected to `I₀` by open edges | `final_recovered_iff` |
| With i.i.d. Bernoulli(`p`) coins, P(`v` eventually infected) = P(`v` connected to `I₀`) | `coins_prob_open`, `prob_infected_eq_prob_connected` |

The coupling holds for every coin assignment, which is stronger than the distributional
equivalence usually stated (with fresh coins in each round); that distributional version is not
formalized here.

## The Kermack–McKendrick SIR model (EPI-7)

The deterministic SIR epidemic (Kermack and McKendrick 1927), in the normalized form of Hethcote,
*The mathematics of infectious diseases*, SIAM Review 2000, system (2.2) and Theorem 2.1:
`s' = -β s i`, `i' = β s i - γ i`, `r' = γ i` with `β, γ > 0` and `R₀ = β / γ`. A solution on
`[0, ∞)` is taken as a hypothesis, `IsSolution β γ s i r`: `t ↦ (s t, i t, r t)` is an
`IsIntegralCurveOn` of `sirField β γ` on `Set.Ici 0`, with `s(0), i(0) > 0`, `r(0) = 0` and
`s(0) + i(0) + r(0) = 1`. Every result holds for every such solution (namespace
`Epidemics.KermackMcKendrick`; files `Epidemics/KermackMcKendrick*.lean`):

| Result | Lean declaration |
| --- | --- |
| `s + i + r = 1`; `s, i > 0`, `r ≥ 0` on `[0, ∞)` | `IsSolution.sum_eq_one`, `s_pos`, `i_pos`, `r_nonneg` |
| `s` strictly decreasing, `r` strictly increasing | `IsSolution.strictAntiOn_s`, `strictMonoOn_r` |
| First integral `s(t) = s(0) exp(-R₀ r(t))` | `IsSolution.s_eq_mul_exp` |
| `R₀ s(0) ≤ 1` ⇒ `i` strictly decreasing | `IsSolution.strictAntiOn_i` |
| `i` initially increases iff `R₀ s(0) > 1` | `IsSolution.initially_increasing_iff` |
| `i → 0`, `s → s∞`, `r → 1 - s∞` | `IsSolution.tendsto_i`, `exists_tendsto_s`, `tendsto_r` |
| Final size `s∞ = s(0) exp(-R₀ (1 - s∞))`, `0 < s∞ < 1/R₀` | `IsSolution.final_size`, `limit_pos`, `R₀_mul_limit_lt_one` |
| `s∞` is the unique root in `(0, 1/R₀]` and in `(0, 1]` | `IsSolution.final_size_unique`, `final_size_unique_of_le_one` |
| Peak at `s = 1/R₀`, `i_max = i₀ + s₀ - 1/R₀ - log(R₀ s₀)/R₀` | `IsSolution.exists_peak` |

Positivity of `i` uses a barrier argument (`i ≥ i(0) e^{-γ t} / 2`) instead of integrals or
Gronwall; uniqueness of the final size uses the monotonicity of `x ↦ log x - R₀ x` on either side
of `1/R₀`.

## Kurtz's law of large numbers for SIR, in discrete time (CRN-2)

The stochastic SIR epidemic on `N` agents (`S + I → 2I` at rate `β S I / N`, `I → R` at rate
`γ I`), uniformized at rate `(β + γ) N`: each step draws an ordered pair of agents with replacement
and one of `β + γ` equally likely clocks (`β` infection clocks, `γ` recovery clocks, so
`β, γ ∈ ℕ`); an infected `u` infects a susceptible `v`, or an infected `u` recovers. Step `k` is
compared with the Kermack–McKendrick solution at time `k / ((β + γ) N)`, in the sup distance on
`ℝ³`. Namespace `Epidemics.Kurtz`; files `Epidemics/Kurtz*.lean`.

| Result | Lean declaration |
| --- | --- |
| Drift identity: expected one-step change of `(S, I, R)/N` is `sirField β γ / ((β + γ) N)` | `drift_susceptible`, `drift_infected`, `drift_recovered` |
| Bounded increments: one step moves `(S, I, R)/N` by at most `1/N` | `dist_scaled_step_le` |
| The kernel `Kernel.ofStep` iterates as `expList` over i.i.d. rounds | `iterate_chain` |
| Maximal Azuma–Hoeffding: `P(∃ k ≤ n, M_k ≥ λ) ≤ exp(-λ²/(2 n c²))` | `expList_azuma` |
| LLN with exponential bound: `P(∃ k ≤ T(β+γ)N, dist > L·dist(initial points) + ε) ≤ C exp(-c ε² N)` | `law_of_large_numbers` |
| Convergence in probability, uniformly on `[0, T]`, to a fixed solution | `tendsto_deviationProb` |

The constants `C, c, L` depend only on `β, γ, T` (in the proof, `L = exp((2β + γ) T)` and
`c = 1 / (32 L² T (β + γ))`). The proof: the drift identity makes each coordinate of
`X_k - X_0 - h ∑_{j<k} F(X_j)` a martingale with increments at most `2/N`; Ville's maximal
inequality for the exponential supermartingale gives the maximal Azuma bound; on the good event,
the invariance of the simplex under the ODE, the Lipschitz bound of the field, the Euler error
`O(h²)` and Mathlib's `discrete_gronwall` keep the chain close to the solution. Deviations from
the sources (discrete time, natural-number rates, sampling with replacement, time scale, initial
condition) are listed in [`PROGRESS-CRN2.md`](PROGRESS-CRN2.md).

**Provenance.** Reed–Frost: the statements were written and pinned by hand; the proofs were
produced by a Grok agent under a fixed-statement protocol and verified mechanically (statements
unchanged, no placeholders, warning-free build, axiom audit). Kermack–McKendrick: the statements
were pinned and then proved by a Claude agent under the same protocol and checks; the statements
were reviewed by hand against the source. Kurtz (CRN-2): the statements were pinned and then
proved by a Claude agent under the same protocol and checks; the statements were reviewed by hand
against the source (Wormald's Theorem 5.1).

Build and audit:

```bash
lake exe cache get
lake build
python3 ../scripts/check_axioms.py
```

This package requires the sibling `dynamics/` package and shares its Lean 4.32.0 toolchain and exact
Mathlib pin. The [blueprint](blueprint/src/content.tex) maps the results to declarations.
