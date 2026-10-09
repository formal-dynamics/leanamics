# 3-majority dynamics: a Lean 4 formalization

A complete, `sorry`-free Lean 4 + Mathlib formalization of the **3-majority**
opinion-dynamics process on `n` fully-mixing agents:

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

**Any number of colours, from any configuration.** The package also formalizes the comparison
of 3-Majority with the Voter model and the `O(n^{3/4} log^{7/8} n)` bound of Berenbrink et al.
(PODC 2017), conditional on a cited result that is not formalized; see
[below](#3-majority-from-any-configuration-roadmap-maj-6-b).

**Relation to `plurality/`.** This was the first, self-contained formalization of the
two-opinion case. The [plurality package](../plurality) generalizes it to `k` colors and to a
vanishing bias: with two opinions, `Plurality.majority3_vanishing_bias` gives consensus from a
gap of `22√(3 n log n)` (a fraction `1/2 + O(√(log n / n))`) within `390 log n` rounds, stated
for this package's process `ThreeMajority.run`. The plurality package reuses this development
through the pathwise bridge `Plurality.colorSet_run`.

**[Blueprint](https://formal-dynamics.github.io/leanamics/3-majority/blueprint/)** ·
**[Blueprint as pdf](https://formal-dynamics.github.io/leanamics/3-majority/blueprint.pdf)** ·
**[Dependency graph](https://formal-dynamics.github.io/leanamics/3-majority/blueprint/dep_graph_document.html)** ·
**[API docs](https://formal-dynamics.github.io/leanamics/3-majority/docs/)**

The blueprint ([blueprint/src/content.tex](blueprint/src/content.tex)) states
every lemma with a `\lean{}` tag pointing to its Lean declaration and a
`\uses{}` tag recording its dependencies, so the web version renders a
dependency graph and a formalization-progress view; `leanblueprint
checkdecls` (run in CI) fails the build if a tagged declaration doesn't
exist.

## Design

Like the sister [rumor_spread](../rumor_spread) development, this one avoids
measure theory, `PMF`, `ENNReal`, kernels and martingales entirely — all
randomness is uniform over finite types. The one deliberate difference is
that a Chernoff bound *is* needed here; it is proved from scratch in the shared
[`dynamics`](../dynamics) library:

- **Probability** ([Prob.lean](ThreeMajority/Prob.lean), aliases of the shared
  [`Dynamics.Uniform`](../dynamics/Dynamics/Uniform.lean); `ThreeMajority.avg` is a
  reducible alias of `Dynamics.avg`): `avg` is a sum
  divided by a cardinality; `expList α T F` — the expectation of a
  trajectory functional over `T` i.i.d. uniform rounds — is defined by
  recursion on `T`, which makes conditioning on a round a definitional
  unfolding. New relative to `rumor_spread`: `avg_prod_pi`, the
  independence fact that the average of a product of functions of distinct
  coordinates factors as the product of the averages.
- **Model** ([Model.lean](ThreeMajority/Model.lean)): a round is
  `Tgt3 n := Fin n → Fin n × Fin n × Fin n` (every agent draws an ordered
  triple with replacement); `step I r` keeps the agents at least two of
  whose samples lie in `I`. `step_mono` is the monotone coupling — `step`
  is monotone in `I` for fixed `r`, though **not** in the round index.
- **One-round drift** ([OneRound.lean](ThreeMajority/OneRound.lean)): the
  exact cubic majority map `p(x) = 3x² - 2x³`, via the polynomial identity
  `maj(a,b,c) = ab+bc+ac-2abc` on `{0,1}`, plus the per-agent `{0,1}`
  decomposition of `(step I r).card` that the Chernoff bounds consume.
- **Chernoff** (shared [`Dynamics/Chernoff.lean`](../dynamics/Dynamics/Chernoff.lean),
  `Dynamics.avg_chernoff_*`): the only concentration tool, built from `1 + x ≤ exp x` and
  `avg_prod_pi` alone — the exponential-moment bound `𝔼[exp(tX)] ≤ exp(μ(eᵗ-1))`, Markov
  applied to `exp(tX)`, and the closed forms at the optimal `t = log(k/μ)`. These are
  *mean-scaled*, which is what keeps them useful once few dissenting agents remain. The
  final Markov step is `Dynamics.avg_markov_one` (`Dynamics/Tail.lean`).
- **Growth phase** ([Growth.lean](ThreeMajority/Growth.lean)): while the
  opinion-`1` fraction is in `[3/5, 3/4]` the majority map amplifies the
  bias by `≥ 5/4` per round in expectation; `10` rounds take the fraction
  past `3/4` except with probability `≤ 10 exp(-c₁n)`.
- **Saturation phase** ([Saturation.lean](ThreeMajority/Saturation.lean)):
  the dissent count contracts by `5/8` per round, in three stages —
  geometric descent to a `Θ(log n)` floor over `⌈6 log n⌉` rounds, one
  round from that floor to a fixed constant `10`, and one final Markov step
  to exactly `0`.
- **Elementary inequalities** ([Bounds.lean](ThreeMajority/Bounds.lean)):
  quadratically-tight lower bounds on `log` near `1`, `xᵏ/k! ≤ exp x`, and
  tangent-line bounds used to keep the threshold on `log n` modest.

Because the opinion count is not monotone in the round index, there is no
"good rounds" counting argument available (the device that carries
`rumor_spread`'s growth phase); every round genuinely needs concentration.

## 3-Majority from any configuration (roadmap MAJ-6 (b))

`AnyStart*.lean` formalizes Theorem 4 of Berenbrink, Clementi, Elsässer, Kling, Mallmann-Trenn,
Natale, *Ignore or comply? On breaking symmetry in consensus*, PODC 2017 (arXiv:1702.04921,
numbering of v1): with any number of colours, from any configuration, 3-Majority reaches
consensus within `O(n^{3/4} log^{7/8} n)` rounds w.h.p.

**The main theorem is conditional.** The second phase of the paper's proof applies Theorem 3.1
of Becchetti, Clementi, Natale, Pasquale, Trevisan, *Stabilizing consensus with many opinions*,
SODA 2016 (arXiv:1508.06782): from `k ≤ n^{1/3−ε}` colours, consensus within
`O((k² √log n + k log n)(k + log n))` rounds w.h.p. That result is not formalized in this
repository (roadmap MAJ-12 (a)). `Bcnpt16Phase2 ε` states it, and
`threeMaj_anyStart_consensus` takes `Bcnpt16Phase2 (1/24)` as a hypothesis, exactly as the
paper's proof uses it. Everything else below is proved.

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
| Theorem 8 (Theorem 3.1 of the SODA 2016 paper): **a hypothesis, not proved** | `Bcnpt16Phase2` |
| Theorem 4, conditional: consensus fails after `T ≥ C n^{3/4} log^{7/8} n` rounds w.p. `≤ 2/n` | `threeMaj_anyStart_consensus`, `anyStart_asymptotics` |

The comparison of Theorem 2 is proved from Proposition 1 alone, by induction on time, without
the paper's coupling and Strassen's theorem; the Voter bound uses an exact occupancy computation
for coalescing walks instead of the variable drift theorem. The proof of Theorem 4 needs a minor
correction (Phase 1 must stop at `n^{1/4} log^{1/8} n` colours, not `n^{1/4}`), which the
formalization makes. The modules use the finite `Distribution` and `Kernel` layer of the shared
[`dynamics`](../dynamics) library (still no measure theory). Details:
[FORMALIZATION_DIFFERENCES.md](FORMALIZATION_DIFFERENCES.md) and the
[blueprint section](https://formal-dynamics.github.io/leanamics/3-majority/blueprint/#sec:bcekmn-any-start).
The statements were pinned by a Claude agent and reviewed by a second agent before any proof;
the proofs were written by a Claude agent under the fixed-statement protocol.

## Building

```bash
lake exe cache get   # download prebuilt Mathlib oleans (once)
lake build           # verifies every proof
```

Toolchain: see [lean-toolchain](lean-toolchain). The main theorems depend only
on the standard axioms (`propext`, `Classical.choice`, `Quot.sound`):
[Audit.lean](Audit.lean) prints their axioms, and `python3 ../scripts/check_axioms.py` (run in
this directory) checks them.

## How to cite

See [How to cite](../README.md#how-to-cite) in the main README.
