# 3-Majority and plurality consensus

A Lean 4 + Mathlib formalization of the **3-majority** dynamics: `n` nodes each support one of
`k` colors; every round, each node samples three nodes uniformly at random (with repetition,
possibly itself) and adopts the majority color among them, or the first one if all three differ.
The package has two libraries:

* `Plurality`: plurality consensus after Becchetti, Clementi, Natale, Pasquale, Silvestri and
  Trevisan (SPAA 2014), its upper and lower bounds, and two opinions from a vanishing bias and
  from any configuration ([below](#plurality-consensus-library-plurality));
* `ThreeMajority`: two opinions from a `3/5` majority, with its own elementary proof
  ([below](#two-opinions-from-a-35-majority-library-threemajority)); with any number of colours,
  the comparison of 3-Majority with the Voter model and the `O(n^{3/4} log^{7/8} n)` bound of
  Berenbrink et al. (PODC 2017), see [below](#3-majority-from-any-configuration-roadmap-maj-6-b),
  and the result it uses for few colours, Theorem 3.1 of Becchetti et al. (SODA 2016): from
  `k ≤ n^{1/3−ε}` colours, consensus within `O((k² √log n + k log n)(k + log n))` rounds w.h.p.;
  see [below](#3-majority-with-many-opinions-roadmap-maj-12-a). Together they give the
  `O(n^{3/4} log^{7/8} n)` bound without hypothesis.

**One model.** The 3-majority round is defined once, for colours of any type:
`ThreeMajority.stepCol`. The round `Plurality.step` of the plurality development is that round
at colours `Fin k` (`Plurality.step_eq_stepCol`, by `rfl`; likewise `run_eq_runCol` and
`count_eq_colourCount`), both on the same randomness `Tgt3 n`, and the bridge from colorings with
two colors to the two-opinion process, `Plurality.colorSet_step`, is derived from the bridge
`ThreeMajority.stepCol_bool` of the model with any colours.

**[Blueprint](https://formal-dynamics.github.io/leanamics/plurality/blueprint/)** ·
**[Blueprint as pdf](https://formal-dynamics.github.io/leanamics/plurality/blueprint.pdf)** ·
**[Dependency graph](https://formal-dynamics.github.io/leanamics/plurality/blueprint/dep_graph_document.html)** ·
**[API docs](https://formal-dynamics.github.io/leanamics/plurality/docs/)**

The blueprint ([blueprint/src/content.tex](blueprint/src/content.tex)) states
every lemma with a `\lean{}` tag pointing to its Lean declaration and a
`\uses{}` tag recording its dependencies, so the web version renders a
dependency graph and a formalization-progress view; `leanblueprint
checkdecls` (run in CI) fails the build if a tagged declaration doesn't
exist.

## Plurality consensus (library `Plurality`)

A Lean 4 + Mathlib formalization of

> L. Becchetti, A. Clementi, E. Natale, F. Pasquale, R. Silvestri, L. Trevisan,
> **Simple Dynamics for Plurality Consensus**, SPAA 2014,
> [doi:10.1145/2612669.2612677](https://doi.org/10.1145/2612669.2612677);
> journal version [arXiv:1310.2858](https://arxiv.org/abs/1310.2858).

> **Theorem 3.8.** Let `λ ≥ 3`. If `m` is the unique plurality color,
> `c_m ≥ n/λ` and the bias is at least `22 √(λ n log n)`, then all nodes
> support `m` after `O(λ log n)` rounds with high probability.

Formally (`Plurality.theorem_3_8` in [Plurality/Upper.lean](Plurality/Upper.lean)):
if `log n ≥ 40` and `k ≥ 2`, then after `10 T` rounds, where
`T = phases n λ ≤ 13 λ log n` (`Plurality.phases_le`), consensus on `m` holds
with probability at least `1 - 11 T / n`. `Plurality.theorem_3_8_bigO` states
this as `≤ 130 λ log n` rounds with probability `≥ 1 - 143 λ log n / n`.

### Status

| Paper | Lean | Status |
| --- | --- | --- |
| Model, Lemma 2.1 | `Model.lean`, `expected_count` | done |
| Lemmas 3.1, 3.2 | `lemma_3_1_a/b/c`, `lemma_3_2_a/b/c` | done |
| Lemmas 3.3, 3.4, 3.5 | `lemma_3_3`, `lemma_3_4`, `lemma_3_5` | done |
| Lemmas 3.6, 3.7 | `lemma_3_6`, `lemma_3_7_i`, `lemma_3_7_ii` | done |
| Lemma A.4 | `Dynamics.Kernel.nested_phases` | done |
| Theorem 3.8 | `theorem_3_8`, `theorem_3_8_bigO` | done |
| `k = 2` | `ThreeMajority.majority3_consensus_whp`, through the bridge `colorSet_run` | done |
| `k = 2` from a vanishing bias (gap `22√(3 n log n)`, `≤ 390 log n` rounds) | `majority3_vanishing_bias` (Theorem 3.8 with `λ = 3`, stated for `ThreeMajority.run`) | done |
| `k = 2` from **any** configuration (symmetry breaking, beyond the paper) | `majority3_symmetry_breaking`, `majority3_any_start`, `majority3_any_start_whp` | done |
| `k = 2`: the mean-field map `x ↦ 3x² - 2x³` (the core's `Dynamics.majorityMap`, also conformist transmission with `D = 1` and Galam's map), and binary 3-majority as conformist transmission with `D = 1` on counts, `Bin(n, 3x² - 2x³)` (beyond the paper) | `binKernel_meanField`, `conformistCountKernel`, `conformistCountKernel_meanField`, `binKernel_lumps` | done |
| Corollaries 3.10–3.12 | `corollary_3_10`, `corollary_3_11`, `corollary_3_12` | done |
| Observation 3.9 (adversary) | | open |
| Lemma 4.1, Theorem 4.2 (`Ω(k log n)`) | `lemma_4_1`, `theorem_4_2`, `theorem_4_2_log` | done, for `k ≤ n^{1/4-δ}` |
| Theorem 4.8 (a), Lemma 4.9 | `theorem_4_8_a`, `not_solver_of_drift` | done except rules with `Δ_r, Δ_b ≤ 1` |
| Theorem 4.8 (b), Lemma 4.10 | `theorem_4_8_b`, `not_solver_of_nonuniform` | done |
| Lemma 4.11, Theorem 4.12 (`h`-plurality) | `lemma_4_11`, `theorem_4_12`, `theorem_4_12_log` | done |

**Two opinions from any configuration** (`Plurality.majority3_any_start_whp` in
[Plurality/AnyStart.lean](Plurality/AnyStart.lean), roadmap MAJ-8): there is `C > 0` such that,
for `log n ≥ C`, binary 3-majority started from **any** configuration, including a perfectly
balanced one, has all nodes holding the same opinion after any `T ≥ C log n` rounds with
probability at least `1 - 1/n` (`majority3_any_start`: the same for `log n ≥ 40` with probability
`1 - C log n / n`). The proof follows the symmetry-breaking argument of Doerr, Goldberg, Minder,
Sauerwald and Scheideler (SPAA 2011) for the binary median dynamics, as described in Becchetti,
Clementi, Natale, *Consensus dynamics: an overview* (SIGACT News 2020, §4, Case 3). Near balance
one round moves the gap to order `√n` with probability `9/64` (Paley-Zygmund,
`jump_near_balance`), and above `√n` it grows by a constant factor except with exponentially small
probability (Hoeffding, `growth_far`). The hitting-time bound of Doerr et al. (Claim 2.9, the core
`Dynamics.Kernel.drift_hitting_log`) then shows that the gap reaches `22 √(3 n log n)` within
`O(log n)` rounds with probability `1 - 1/n` (`majority3_symmetry_breaking`), after which
`majority3_vanishing_bias` finishes. The constant `C` is not explicit, because the hitting-time
bound gives none.

The proof of Theorem 3.8 departs from the paper in a few places, and some
proofs in both versions of the paper have gaps. Both are recorded in
[FORMALIZATION_DIFFERENCES.md](FORMALIZATION_DIFFERENCES.md).

## Two opinions from a 3/5 majority (library `ThreeMajority`)

> **Theorem.** Each of `n` agents holds one of two opinions and, every round,
> simultaneously resamples three agents uniformly at random (with
> replacement) and adopts the majority of their opinions. If one opinion
> starts with at least a `60%` share, then after `O(log n)` rounds **all**
> agents hold that opinion with probability `1 - O(1/n)`.

Formally (`ThreeMajority.majority3_consensus_whp` in
[ThreeMajority/Main.lean](ThreeMajority/Main.lean)): if `log n ≥ 30` and the
initial opinion-`1` set `I₀` satisfies `|I₀| ≥ (3/5)n`, then after
`10 + (⌈6 log n⌉ + 2)` rounds the probability that consensus has *not* been
reached is at most `500/n`. The constants are deliberately crude in exchange
for a minimal analytic toolkit.

A self-contained paper proof, written to mirror the formalization
lemma-for-lemma, is in [latex/three_majority.tex](latex/three_majority.tex).

**Relation to the library `Plurality`.** This was the first, self-contained formalization of the
two-opinion case. The library `Plurality` generalizes it to `k` colors and to a vanishing bias:
with two opinions, `Plurality.majority3_vanishing_bias` gives consensus from a gap of
`22√(3 n log n)` (a fraction `1/2 + O(√(log n / n))`) within `390 log n` rounds, stated for the
process `ThreeMajority.run`. `Plurality` reuses this development through the pathwise bridge
`Plurality.colorSet_run`.

### Design

Like the push-protocol development of the library `RumorSpread` (in [epidemics](../epidemics)),
the two-opinion development avoids measure theory, `PMF`, `ENNReal`, kernels and martingales
entirely: all randomness is uniform over finite types. The one deliberate difference is that a
Chernoff bound *is* needed here; it is proved from scratch in the shared
[`dynamics`](../dynamics) library:

- **Probability** ([Prob.lean](ThreeMajority/Prob.lean), aliases of the shared
  [`Dynamics.Uniform`](../dynamics/Dynamics/Uniform.lean); `ThreeMajority.avg` is a
  reducible alias of `Dynamics.avg`): `avg` is a sum
  divided by a cardinality; `expList α T F` (the expectation of a
  trajectory functional over `T` i.i.d. uniform rounds) is defined by
  recursion on `T`, which makes conditioning on a round a definitional
  unfolding. New relative to `RumorSpread`: `avg_prod_pi`, the
  independence fact that the average of a product of functions of distinct
  coordinates factors as the product of the averages.
- **Model** ([Model.lean](ThreeMajority/Model.lean)): a round is
  `Tgt3 n := Fin n → Fin n × Fin n × Fin n` (every agent draws an ordered
  triple with replacement); `step I r` keeps the agents at least two of
  whose samples lie in `I`. `step_mono` is the monotone coupling: `step`
  is monotone in `I` for fixed `r`, though **not** in the round index.
- **One-round drift** ([OneRound.lean](ThreeMajority/OneRound.lean)): the
  exact cubic majority map `p(x) = 3x² - 2x³`, via the polynomial identity
  `maj(a,b,c) = ab+bc+ac-2abc` on `{0,1}`, plus the per-agent `{0,1}`
  decomposition of `(step I r).card` that the Chernoff bounds consume.
- **Chernoff** (shared [`Dynamics/Chernoff.lean`](../dynamics/Dynamics/Chernoff.lean),
  `Dynamics.avg_chernoff_*`): the only concentration tool, built from `1 + x ≤ exp x` and
  `avg_prod_pi` alone: the exponential-moment bound `𝔼[exp(tX)] ≤ exp(μ(eᵗ-1))`, Markov
  applied to `exp(tX)`, and the closed forms at the optimal `t = log(k/μ)`. These are
  *mean-scaled*, which is what keeps them useful once few dissenting agents remain. The
  final Markov step is `Dynamics.avg_markov_one` (`Dynamics/Tail.lean`).
- **Growth phase** ([Growth.lean](ThreeMajority/Growth.lean)): while the
  opinion-`1` fraction is in `[3/5, 3/4]` the majority map amplifies the
  bias by `≥ 5/4` per round in expectation; `10` rounds take the fraction
  past `3/4` except with probability `≤ 10 exp(-c₁n)`.
- **Saturation phase** ([Saturation.lean](ThreeMajority/Saturation.lean)):
  the dissent count contracts by `5/8` per round, in three stages:
  geometric descent to a `Θ(log n)` floor over `⌈6 log n⌉` rounds, one
  round from that floor to a fixed constant `10`, and one final Markov step
  to exactly `0`.
- **Elementary inequalities** ([Bounds.lean](ThreeMajority/Bounds.lean)):
  quadratically-tight lower bounds on `log` near `1`, `xᵏ/k! ≤ exp x`, and
  tangent-line bounds used to keep the threshold on `log n` modest.

Because the opinion count is not monotone in the round index, there is no
"good rounds" counting argument available (the device that carries the
growth phase of `RumorSpread`); every round genuinely needs concentration.

## 3-Majority from any configuration (roadmap MAJ-6 (b))

`AnyStart*.lean` formalizes Theorem 4 of Berenbrink, Clementi, Elsässer, Kling, Mallmann-Trenn,
Natale, *Ignore or comply? On breaking symmetry in consensus*, PODC 2017 (arXiv:1702.04921,
numbering of v1): with any number of colours, from any configuration, 3-Majority reaches
consensus within `O(n^{3/4} log^{7/8} n)` rounds w.h.p.

**The main theorem is unconditional.** The second phase of the paper's proof applies Theorem 3.1
of Becchetti, Clementi, Natale, Pasquale, Trevisan, *Stabilizing consensus with many opinions*,
SODA 2016 (arXiv:1508.06782): from `k ≤ n^{1/3−ε}` colours, consensus within
`O((k² √log n + k log n)(k + log n))` rounds w.h.p. `Bcnpt16Phase2 ε` states it, and the bridge
theorem `threeMaj_anyStart_consensus` takes `Bcnpt16Phase2 (1/24)` as a hypothesis, exactly as the
paper's proof uses it. That result is formalized in this package too
([next section](#3-majority-with-many-opinions-roadmap-maj-12-a), roadmap MAJ-12 (a)):
`bcnpt16Phase2_of_pos` proves `Bcnpt16Phase2 ε` for every `ε > 0`, and
`threeMaj_anyStart_consensus_unconditional` is Theorem 4 without hypothesis.

| BCEKMN17 (arXiv v1) | Lean |
| --- | --- |
| Model, Sections 2.1 and 2.2 (any colour type; ties broken by the first sample, same law) | `majColour`, `stepCol`, `runCol`, `voterStep`, `voterRun`, `colourCount`, `numColours`, `stepCol_bool` |
| Majorization `⪰`, Schur-convex observables | `Majorizes`, `countVec`, `SchurConvex`, `numColours_le_of_majorizes` |
| Definitions 1 and 2: AC-processes, protocol dominance | `acKernel`, `Dominates` |
| Proposition 1 (Rinott; cited without proof in the paper, proved here) | `multinomial_schurConvex`, `expect_le_of_majorizes` |
| Theorem 2, in distributional form (no coupling) | `ac_comparison`, `ac_numColours` |
| Equations (1), (2); Lemma 2 (3-Majority is at least as fast as Voter) | `alphaVoter_weight`, `alpha3M_weight`, `dominates_alpha3M_alphaVoter`, `voter_le_threeMaj` |
| Lemma 4, Equation (6): duality with coalescing walks | `walkStep`, `numColours_voterRun_le`, `voter_dual` |
| Equation (7); `E[X_t] ≤ 1 + 3n/t` in place of the variable drift theorem | `walk_drift_paper`, `walk_drift`, `walk_expect_le` |
| Lemma 3: at most `k` colours after `24 (n/k) log n` rounds w.p. `≥ 1 − 1/n` | `voter_reduce_whp` |
| Phase 1 of Theorem 4, the same bound for 3-Majority | `threeMaj_reduce_whp` |
| Theorem 8 (Theorem 3.1 of the SODA 2016 paper), proved in the [next section](#3-majority-with-many-opinions-roadmap-maj-12-a) | `Bcnpt16Phase2`, `bcnpt16Phase2_of_pos` |
| Theorem 4 from Phase 2 (the bridge) | `threeMaj_anyStart_consensus`, `anyStart_asymptotics` |
| Theorem 4: consensus fails after `T ≥ C n^{3/4} log^{7/8} n` rounds w.p. `≤ 2/n` | `threeMaj_anyStart_consensus_unconditional` |

The comparison of Theorem 2 is proved from Proposition 1 alone, by induction on time, without
the paper's coupling and Strassen's theorem; the Voter bound uses an exact occupancy computation
for coalescing walks instead of the variable drift theorem. The proof of Theorem 4 needs a minor
correction (Phase 1 must stop at `n^{1/4} log^{1/8} n` colours, not `n^{1/4}`), which the
formalization makes. The modules use the finite `Distribution` and `Kernel` layer of the shared
[`dynamics`](../dynamics) library (still no measure theory). Details:
[FORMALIZATION_DIFFERENCES.md](FORMALIZATION_DIFFERENCES.md#6-3-majority-from-any-configuration-anystart-roadmap-maj-6-b)
and the
[blueprint section](https://formal-dynamics.github.io/leanamics/plurality/blueprint/#sec:bcekmn-any-start).
The statements were pinned by a Claude agent and reviewed by a second agent before any proof;
the proofs were written by a Claude agent under the fixed-statement protocol.

## 3-Majority with many opinions (roadmap MAJ-12 (a))

`ManyOpinions*.lean` formalizes Theorem 3.1 of Becchetti, Clementi, Natale, Pasquale, Trevisan,
*Stabilizing consensus with many opinions*, SODA 2016 (arXiv:1508.06782, numbering of v1), the
adversary-free case: from any configuration with `k ≤ n^{1/3−ε}` colours (any constant `ε > 0`),
3-Majority reaches consensus within `O((k² √log n + k log n)(k + log n))` rounds w.h.p. Its form
`bcnpt16Phase2_of_pos` is the Phase 2 hypothesis of the previous section, which makes Theorem 4
of Berenbrink et al. unconditional (`threeMaj_anyStart_consensus_unconditional`).

| BCNPT16 (arXiv v1) | Lean |
| --- | --- |
| Model, Section 2 (the rule of the previous section) | `stepCol_apply`, `numColours_eq_card_image`, `colourCount_eq_card_filter` |
| Lemma 2.1, Equation (1): expected support after one round | `avg_colourCount_stepCol`, `avg_colourCount_stepCol_le` |
| Lemma 3.2, in finite-horizon form: hitting time under an additive drift | `hitProb_additive_drift` |
| Equation (3): the smallest support drifts down by `δ √n / j^{3/2}` per round | `min_count_drift` |
| Equation (6), Lemma B.1, in one-step form: no overshoot below `n/j − 64 √(j n log n)` w.p. `≥ 1 − 1/n²` | `min_count_overshoot` |
| Lemma 3.3: some colour falls to `n/j − 16 √(j n log n)` (or dies) within `O(j² √log n)` rounds w.p. `≥ 1/2` | `symmetry_breaking`, `BrokenSymmetry` |
| Lemma 3.4: the colour then has `O(j² log n)` agents after `O(j log n)` rounds w.p. `≥ 1 − 1/n` | `dropping_stage1` |
| Lemma 3.5: from `n/(2j)` agents, the colour dies within `O(j log n)` rounds w.p. `≥ 1/2` | `dropping_stage2` |
| Proof of Theorem 3.1: one colour dies per phase w.p. `≥ 1/5`; amplification over phases | `phase_colour_dies`, `hitProb_mul_le_event`, `consensus_of_phases` |
| Theorem 3.1, for `C k³ log n ≤ n`: consensus fails after `T ≥ C (k² √log n + k log n)(k + log n)` rounds w.p. `≤ 1/n` | `consensus_many_opinions` |
| Theorem 3.1 as stated, for `k ≤ n^{1/3−ε}`, `n ≥ N(ε)` | `bcnpt16Phase2_of_pos` |
| Theorem 4 of BCEKMN17 without hypothesis | `threeMaj_anyStart_consensus_unconditional` |

The proof follows the paper's (symmetry breaking by a drift argument, then two dropping stages,
then a colour dies per phase), with: Lemma 3.2 for a finite horizon, with a one-step overshoot
bound in place of Lemma B.1 (no optional stopping); the strong Markov property at the hitting
time of the symmetry-breaking stage, where the paper evaluates at a fixed time; Equation (3) near
the uniform configuration from the Paley–Zygmund inequality instead of the Central Limit
Theorem; and the threshold `16 √(j n log n)` and floor `240 j² log n` in Lemmas 3.3 and 3.4. The
statements assume `C k³ log n ≤ n`, which `k ≤ n^{1/3−ε}` implies for large `n`. The proof of
Lemma 3.4 needs a minor correction (with the threshold `√(j n log n)` of the paper, its iterated
union bound exceeds `1` for large `j`), as do the statement of Lemma 3.3 (it needs
`j³ log n = O(n)`) and the proofs of Lemma 3.3, Lemma B.1 and Theorem 3.1; the formalization
makes these corrections. Details:
[FORMALIZATION_DIFFERENCES.md](FORMALIZATION_DIFFERENCES.md#7-3-majority-with-many-opinions-manyopinions-roadmap-maj-12-a)
and the
[blueprint section](https://formal-dynamics.github.io/leanamics/plurality/blueprint/#sec:bcnpt16-many-opinions).
The statements were pinned by a Claude agent and reviewed by a second agent before any proof;
the proofs were written by a Claude agent under the fixed-statement protocol.

## Layout

Library `Plurality`:

| Module | Content |
| --- | --- |
| `Model` | Colorings, 3-input rules, `maj3`, rounds, the Markov kernel; `step`, `run`, `count` as `ThreeMajority.stepCol`, `runCol`, `colourCount` at colours `Fin k` |
| `Expectation` | Adoption probabilities and Lemma 2.1 |
| `Quantities` | `m(c)`, `M(c)`, `s(c)`, `α(c)`, `γ(c)`, `μ_j(c)`; Lemmas 3.1, 3.2 |
| `Numerics` | Explicit "sufficiently large `n`" bounds |
| `Growth` | Lemmas 3.3, 3.4, 3.5 |
| `Saturation` | Lemmas 3.6, 3.7 |
| `Upper` | The phases, one round of each phase, Theorem 3.8 |
| `Corollaries` | Corollaries 3.10, 3.11, 3.12 |
| `Binary` | The `k = 2` case via the library `ThreeMajority` |
| `AnyStart` | `k = 2` from any configuration: symmetry breaking, then the vanishing bias |
| `MeanField` | `k = 2`: the mean-field map, conformist transmission on counts and the lumping of binary 3-majority to it |
| `Lower` | Lemma 4.1 and Theorem 4.2 |
| `Rules` | 3-input rules, `Δ`, `δ`, solvers, consensus needs survival |
| `ClearMajority` | Theorem 4.8 (a) |
| `UniformRule` | Theorem 4.8 (b) |
| `HPlurality` | The `h`-plurality model, Lemma 4.11, Theorem 4.12 |

Library `ThreeMajority`: the two-opinion modules are described under [Design](#design), and
`AnyStart*.lean` and `ManyOpinions*.lean` in the two sections on many colours.

The package depends on `../dynamics` (finite distributions, kernels, Bernstein, Hoeffding and
multiplicative Chernoff bounds, Markov's inequality, the nested-phase lemma); the library
`Plurality` uses the library `ThreeMajority` (the round type `Tgt3 n`, the binary theorem and
elementary bounds). Like the rest of the repository it uses no measure theory, `PMF`/`ENNReal`
or martingales.

**Provenance.** For `Plurality/AnyStart*.lean` (binary 3-majority from any configuration), the
statements were fixed in advance by a Claude agent and reviewed by a second Claude agent, which checked them
against the source and numerically and found no problems; the proofs are by a Claude agent under
the fixed-statement protocol (statements unchanged, no placeholders, warning-free build, axiom
audit). The amplified statement `majority3_any_start_whp` was added after the first review, on the
reviewer's suggestion, and reviewed the same way. The moment lemmas (second and fourth moments of
independent sums, Paley-Zygmund) are those of the shared layer, `dynamics/Dynamics/Moments.lean`.
See [PROVENANCE.md](../PROVENANCE.md) for the other results.

## Building

```bash
lake exe cache get                   # download prebuilt Mathlib oleans (once)
lake build                           # verifies every proof, in both libraries
python3 ../scripts/check_axioms.py   # audits the theorems listed in Audit.lean
```

Toolchain: see [lean-toolchain](lean-toolchain). The main theorems of both libraries depend only
on the standard axioms (`propext`, `Classical.choice`, `Quot.sound`): [Audit.lean](Audit.lean)
prints their axioms, and `python3 ../scripts/check_axioms.py` (run in this directory) checks them.

## How to cite

See [How to cite](../README.md#how-to-cite) in the main README.
