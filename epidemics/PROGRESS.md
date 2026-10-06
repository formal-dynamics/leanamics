<!-- The growth-regime section below is a copy of the root PROGRESS.md (left unchanged), so that this file holds the whole EPI-8 record. -->

# EPI-8 Growth.lean progress

Paper: Doerr–Kostrygin, arXiv:2303.11150, Lemma 9, Lemma 19, Theorem 21 (Appendix B.2).

## Status

Done. `lake build Epidemics.Revisited.Growth` succeeds with no warnings and no `sorry`.
`#print axioms` on the five theorems shows only `propext`, `Classical.choice`, `Quot.sound`.

## Theorems

All five statements in `epidemics/Epidemics/Revisited/Growth.lean` are unchanged. Each proof is `exact` of a helper:

| Theorem | Paper | Helper |
| --- | --- | --- |
| `variance_card_le` | Lemma 9 | `variance_card_le_proof` in `GrowthAux.lean` |
| `connect_tail` | Lemma 19 (i) | `connect_tail_proof` in `GrowthConnect.lean` |
| `connect_expect` | Lemma 19 (ii) | `connect_expect_proof` in `GrowthConnect.lean` |
| `growth_upper_tail` | Theorem 21, tail | `growth_upper_tail_proof` in `GrowthUpper.lean` |
| `growth_upper_expect` | Theorem 21, expectation | `growth_upper_expect_proof` in `GrowthUpper.lean` |

## Files

| File | Lines | Role |
| --- | --- | --- |
| `Growth.lean` | 73 | Frozen statements. Imports `GrowthUpper`. |
| `GrowthAux.lean` | 450 | Finite-distribution lemmas (support of a monotone kernel, variance of indicators, Cantelli, geometric sums) and Lemma 9. |
| `GrowthConnect.lean` | 273 | Lemma 19 by a gap potential on `Kernel.iterate`. |
| `GrowthReal.lean` | 1624 | Explicit constants: shrunk `f'`, round target `E0`, phase thresholds `k_j`, failure sums, and the exponential comparison lemmas. |
| `GrowthUpper.lean` | 1339 | One-round Cantelli bound, phase potential, crossing from `k_J` to `f n`, and both Theorem 21 proofs. |
| `Epidemics.lean` | 7 | Imports the four helper modules and `Growth`. |

`Defs.lean` is unchanged. `dynamics/` is unchanged.

## Proof sketch (Theorem 21)

`f` is shrunk only inside the phase construction, to `f' = min(f/2, 1/(8(a+1)))`. On `[1, f' n]` the round target `E0(k) = E(k) - A k^{3/4}` is positive and increasing for a small explicit `A` depending on `γlo, b`. Phases are `k_0 = 1`, `k_{j+1} = k_j + E0(k_j)`, up to `J = ⌊log_{1+γ}(f' n)⌋`, so `k_J ≤ f' n` and `k_J / n` is bounded below by a positive constant depending only on `γlo, γhi, a, b, f`.

One round from `k` nodes misses `E0(k)` with probability at most `Q(k) = q(k)/(1+q(k))`, by Cantelli. The phase index (largest `j ≤ J` with `k_j ≤ |S|`) is controlled by a potential `G` on `Kernel.iterate`: from phase `j < J` the next phase is reached with probability at least `1 - Q_j`, and `G` contracts by a fixed `x > 1` with `x Q* < 1`. After `J + r/2` rounds the probability of still being below `k_J` is at most `O(1) exp(-(log x / 2) r)`.

The remaining `r - r/2` rounds cross `[k_J, f n)` by Lemma 19, at a positive rate `connectP` coming from `k_J / n` and `a f < 1`. The two exponential rates are combined by taking `α` to be their minimum. The prefactor absorbs `√x` and `1/(1-f)`. Sets with `|S| > 1` start in a later phase, and `G` is antitone, so the same bound applies. `J ≤ ⌈log_{1+γ} n⌉`, so monotonicity of `notYet` moves the clock to the theorem's time.

The expectation sums `notYet ≤ 1` over the first `⌈log_{1+γ} n⌉` terms and a geometric series after that. `N` is `growthN a b f` (large enough for the logarithm and slack inequalities). It does not depend on `γ`.

## Deviations from the paper

- Lemma 19 does not use a dummy process. The potential is `g S = n - |S|` while `ℓ ≤ |S| < m`, and `0` once `|S| ≥ m`.
- The phase crossing does not use stochastic domination by sums of geometric random variables (Lemmas 10, 11, 25). It is an induction on `Kernel.iterate` with the phase potential `G`.
- `f` is shrunk to `f'` only to keep `E0` increasing on the phase range. The theorem's threshold stays `f n`, and Lemma 19 crosses `[k_J, f n)`.
- Cantelli is applied with gap `λ = A k^{3/4} E[X] / E(k)`, so `{X ≤ E0(k)} ⊆ {X ≤ E[X] - λ}`. The resulting bound is `q/(1+q)`, not Chebyshev's `Var/λ²`.
- `Distribution.prob` and `Kernel.event` are bridged by `prob_indicator_eq`, because `prob` decides propositions with `Classical.propDecidable`.
- Time is split in half: `r/2` rounds for the phase potential and `r - r/2` rounds for Lemma 19. Both exponential rates are therefore halved, and the constant `A` in the tail absorbs the resulting `√x` and the Lemma 19 ratio `1/(1-f)`.
- Constants are explicit and depend only on `γlo, γhi, a, b, c, f`. `N` may be enormous.

## Current errors

None.

---

# EPI-8 continued: Lemma 20, exponential shrinking regime (Theorem 31), total spreading time

Paper: Doerr–Kostrygin, arXiv:2303.11150: Lemma 20 (= Lemma 5 of the overview), Definition 11
(= Definition 4, upper), Theorem 31 (= Theorem 2, upper bounds, Appendix B.4), and the composition
of the regimes used for concrete protocols (Section 3.4, Appendix C, e.g. Theorem 51).

## Status (2026-10-06)

Done. All six pinned theorems are proved; `lake build Epidemics` succeeds with no warnings and no
`sorry`. `#print axioms` (also in `Audit.lean`) shows only `propext`, `Classical.choice`,
`Quot.sound` for all six. The pinned statements (up to `:=`) and `ShrinkingDefs.lean` are
unchanged since phase 1; only proofs and `import` lines were added. The old spec gate
(`scripts/agent-runs/epi8/check_spec.py`) still reports `SPEC OK`.

## Pinned

| Declaration | File | Paper | Content |
| --- | --- | --- | --- |
| `JumpsOver` (def) | `ShrinkingDefs.lean` | Lemma 20 | a path `[S₀, …, S_t]` has a round from `< lo` to `≥ hi` informed nodes |
| `RumorProcess.jumpProb` (def) | `ShrinkingDefs.lean` | Lemma 20 | probability of `JumpsOver` within `t` rounds, via `Kernel.trajectory` |
| `RumorProcess.UpperShrinking` (def) | `ShrinkingDefs.lean` | Definition 11 | `1 - p ≤ e^{-ρ} + a u/n` and `cov ≤ c/u` whenever `u = n - |S| ≤ g n` |
| `overshoot_round` | `Lemma20.lean` | Lemma 20 (its proof) | for `f' ∈ ]f + p(1-f), 1[`, one round from `|S| < f n` reaches `≥ f' n` w.p. `≤ C/n` |
| `jumpProb_le` | `Lemma20.lean` | Lemma 20 | `∃ f' ∈ ]f,1[, C`: `jumpProb (f n) (f' n) t S ≤ C/n · ∑_{i<t} notYet (f n) i S` |
| `shrinking_upper_tail` | `Shrinking.lean` | Theorem 31 / 2, tail | from `≤ g n` uninformed: `notYet n (⌈ln n / ρ⌉ + r) S ≤ A e^{-α r}` |
| `shrinking_upper_expect` | `Shrinking.lean` | Theorem 31 / 2, expectation | `∑_{t<R} notYet n t S ≤ ln n / ρ + B` |
| `spreading_upper_tail` | `Shrinking.lean` | Thm 21 + Lemma 19 + Thm 31 | `notYet n (⌈log_{1+γ} n⌉ + ⌈ln n / ρ⌉ + r) S ≤ A e^{-α r}` |
| `spreading_upper_expect` | `Shrinking.lean` | Thm 21 + Lemma 19 + Thm 31 | `∑_{t<R} notYet n t S ≤ log_{1+γ} n + ln n / ρ + B` |

`ShrinkingDefs.lean` contains only the three definitions, so a gate may freeze the whole file
(a definition's meaning is in its body, after `:=`). `Shrinking.lean` imports `Growth` (for the
assembly); `Lemma20.lean` imports only `ShrinkingDefs`. All three files are imported by
`Epidemics.lean`. `Defs.lean`, `Growth*.lean`, `dynamics/` and the root `PROGRESS.md` are unchanged.
Sanity checks run in a scratch file (not in the repository) confirmed `jumpProb … 0 S = 0`,
`jumpProb lo hi 1 S = P_S[|S| < lo ∧ hi ≤ |S₁|]`, and the two-round unfolding over `[S, S₁, S₂]`.

## Proved

| Theorem | Paper | Proof |
| --- | --- | --- |
| `overshoot_round` | Lemma 20 (its proof) | `overshoot_round_proof` in `Lemma20Aux.lean` |
| `jumpProb_le` | Lemma 20 | `jumpProb_le_proof` in `Lemma20Aux.lean` |
| `shrinking_upper_tail` | Theorem 31 / 2, tail | `shrinking_upper_tail_proof` in `ShrinkingUpper.lean` |
| `shrinking_upper_expect` | Theorem 31 / 2, expectation | `shrinking_upper_expect_proof` in `ShrinkingUpper.lean` |
| `spreading_upper_tail` | Thm 21 + Lemma 19 + Thm 31 | `spreading_upper_tail_proof` in `ShrinkingTotal.lean` |
| `spreading_upper_expect` | Thm 21 + Lemma 19 + Thm 31 | `spreading_upper_expect_proof` in `ShrinkingTotal.lean` |

Hypotheses that are kept for fidelity but not needed (`hf0, hf1, hf'1` in `overshoot_round`, `hf0`
in `jumpProb_le`, `hg1 : g < 1` in the four `Shrinking.lean` theorems) are silenced by
`have _ := h`.

## Remaining

Nothing.

## Current errors

None.

## Files (this section)

| File | Lines | Role |
| --- | --- | --- |
| `ShrinkingDefs.lean` | 51 | Pinned definitions `JumpsOver`, `jumpProb`, `UpperShrinking` (unchanged). |
| `ShrinkingAux.lean` | 164 | Generic tail tools: `notYet_succ`, `notYet_add_le` (Markov property at a fixed time), `tail_compose` (two exponential tails in sequence), `sum_notYet_le_of_tail` (tail ⇒ expectation), `one_sub_pow_le_exp`, `exp_split_le`. |
| `ShrinkingPotential.lean` | 316 | The potential `u + (β/n) u²`: one-round contraction `apply_shrinkPot_le`, iteration, Markov, and the stage-2 tail `notYet_shrink_stage2`. |
| `ShrinkingUpper.lean` | 321 | Explicit constants (`shrinkDelta`, `shrinkG0`, `shrinkBeta`, `shrinkK`, `shrinkA`, `shrinkAlpha`, `shrinkN`), their inequalities (`shrink_drift`, `shrink_varK`), stage 1 by Lemma 19, and Theorem 31. |
| `ShrinkingTotal.lean` | 146 | Middle stage by Lemma 19 (`notYet_middle_le`) and the total-time theorems. |
| `Lemma20Aux.lean` | 237 | `Kernel.trajectory` lemmas (`traj_mono`, `traj_add`, `traj_const`, `traj_head`), path decomposition, `jumpProb_le_sum`, and both Lemma 20 proofs. |
| `Lemma20.lean` | 57 | Pinned Lemma 20 statements. |
| `Shrinking.lean` | 96 | Pinned Theorem 31 and total-time statements. |

`Epidemics.lean` imports all of them; `Audit.lean` prints the axioms of the six theorems.

## Proof of Theorem 31 (differs from the paper's route)

The paper uses a target sequence `u_{j+1} = E0(u_j)`, Chebyshev per phase and domination by
geometric variables (Lemmas 32-37). Here a single quadratic potential suffices:

1. **Stage 1 (Lemma 19).** From at most `g n` uninformed nodes, each uninformed node is
   informed with probability at least `p₀ = 1 - e^{-ρlo} - a g > 0`, so `connect_tail` reaches at
   most `g₀ n` uninformed nodes with tail `(g / g₀) e^{-p₀ r}`.
2. **Stage 2 (potential).** With `u = n - |S| ≤ g₀ n`, `Φ = u + (β/n) u²` satisfies
   `E[Φ'] ≤ e^{-ρ} (1 + K/n) Φ`. This uses `E[u'] ≤ u (e^{-ρ} + a u/n)` (condition (i)) and
   `E[u'²] ≤ (1 + c) u + E[u']²` (Lemma 9 with covariance bound `c/u`; for `u = 0`, `c/0 = 0`
   keeps the identity). The parameters are `δ = e^{-ρhi}(1 - e^{-ρlo})/2` (so `x(1-x) ≥ 2δ` for
   `x = e^{-ρ}`), `g₀ = min(g, δ/(3(a+1)))`, `β = a/δ` (so `a + β (x + a g₀)² ≤ β x`) and
   `K = β(1+c) e^{ρhi}` (so `β(1+c) ≤ e^{-ρ} K`). Since `Φ ≥ 1` while some node is uninformed,
   after `T = ⌈ln n/ρ⌉ + r` rounds `P[T(·,n) > T] ≤ e^{-ρT}(1 + K/n)^T Φ(S)`. Then
   `n e^{-ρ⌈ln n/ρ⌉} ≤ 1`, `(1 + K/n)^{⌈ln n/ρ⌉} ≤ e^{K/ρlo + K}` (as `ln n ≤ n`) and, for
   `n ≥ 2K/ρlo`, `(1 + K/n)^r e^{-ρ r} ≤ e^{-ρlo r/2}`.
3. `tail_compose` joins the stages (rate `min(p₀, ρlo/2)/2`), and `sum_notYet_le_of_tail` gives
   the expectation `≤ ln n/ρ + 1 + A/(1 - e^{-α})`.

The total-time theorems chain the pinned `growth_upper_tail` (its prefactor replaced by
`max A 0`), the middle stage (Lemma 19, prefactor `(1-f)/g`) and Theorem 31 with two
`tail_compose` steps.

## Reusable pieces

- `notYet_add_le`, `tail_compose`, `sum_notYet_le_of_tail` (`ShrinkingAux`): compose any
  sequence of regimes given exponential tails, and turn tails into expectation bounds.
- `traj_mono`, `traj_add`, `traj_const`, `traj_head` (`Lemma20Aux`): basic calculus for
  `Dynamics.Kernel.trajectory` (path events); candidates to move to `dynamics/`.
- `jumpProb_le_sum`: per-round overshoot bound ⇒ path bound, for any thresholds.
- `expect_deficit_le`, `expect_deficit_sq_le`: first and second moments of the number of
  uninformed nodes after one round, reusable for the double-exponential regime (Theorem 43).

## Deviations from the paper

- **Lemma 20 is false as stated; two true versions are pinned.** The proof bounds one round:
  from `k < f n`, `P[k + X(k) ≥ f' n] = O(1/n)`. It then concludes that the whole process jumps
  over `[f n, f' n]` with probability `O(1/n)`, but the process may spend many rounds below `f n`
  with a chance to jump in each. Counterexample: from every `S` with `|S| < f n`, inform all nodes
  with probability `ε = c/n` and otherwise none. For `n ≥ c/p`, `p_k = ε ≤ p` and
  `c_k = ε(1 - ε) ≤ c/n`, but
  the process started from one node jumps from `1` to `n` with probability 1. (The same process
  with `ε_k = c k / n²` satisfies the lower exponential growth conditions, so the last sentence of
  Theorem 1, which rests on Lemma 20, is also unproved in general. That sentence is a lower-bound
  statement, outside this job.) Pinned instead: `overshoot_round`, the one-round estimate of the
  proof, for every `f' ∈ ]f + p(1-f), 1[`; and `jumpProb_le`, the path statement with the union
  bound over rounds, `P[jump within t rounds] ≤ C/n · E[number of those rounds started below f n]`,
  that is, `O(E[T(|S|, f n)] / n)`.
- Lemma 20's proof writes `E[X(k)] ≤ p n (1 - f)`; the correct bound is `p (n - k)`. The threshold
  `f + p(1-f)` for `f'` is still right, because `k + p(n - k) < n (f + p(1-f))` for `k < f n`.
- `overshoot_round` assumes the bounds only for the one starting set, and does not require it to
  be nonempty (Chebyshev does not need it). `jumpProb_le` assumes them for every nonempty `S`
  with `|S| < f n` (the paper's `1 ≤ k < f n`) and starts from a nonempty set.
- Definition 11's side condition `e^{-ρ_n} + a g < 1` is taken uniformly in `n`, as
  `e^{-ρlo} + a g < 1`. The per-`n` reading is not enough. If `e^{-ρ_n} + a g = 1 - δ_n` with
  `δ_n → 0` fast, then rounds near `g n` uninformed nodes shrink by a factor `1 - δ_n`, and escaping
  them costs `Θ(log n)` extra rounds, not `O(1)`. Lemma 19, which the paper uses to shrink `g`,
  likewise needs a uniform `p`.
- The paper's `ρ_n ∈ [ρlo, ρhi]` is kept (also for the uniform constants). The upper bound
  matters: for `ρ = ln n`, the term `a u / n` makes the shrinking double exponential, which takes
  about `log₂ ln n` rounds, not `ln n / ρ + O(1) = O(1)`.
- Starting sets: Theorem 31 starts from exactly `n - ⌊g n⌋` informed nodes; here from any `S` with
  `n - |S| ≤ g n`. The total-time theorems start from any nonempty `S` (the paper from one node).
- Time convention as in `Growth`: tails are `P[T > ⌈(1/ρ) ln n⌉ + r]`. This matches the paper's
  `P[T > (1/ρ) ln n + r]` up to replacing `A` by `A e^α`. Expectations are bounded through every
  partial sum of `∑_t P[T > t]`.
- Homogeneity (Definition 6) is not assumed: the conditions are bounds for every state, as for
  `UpperGrowth`.
- The total-time theorems are not single statements of the paper. They compose Theorem 21,
  Lemma 19 and Theorem 31 the way the paper does for concrete protocols. The middle range
  hypothesis is Lemma 19's: every uninformed node becomes informed with probability at least `p`
  when `f n ≤ |S|` and `n - |S| > g n`. Like `connect_tail`, it takes `0 < p ≤ 1`; the paper's
  Lemma 19 takes `0 < p < 1`. If `f + g ≥ 1` the middle range is empty and the hypothesis is
  vacuous. The growth and shrinking conditions have separate constants `a, c` and `a', c'`.
- Proof route (not a statement change): Theorem 31 is proved with a quadratic potential instead
  of the paper's phase calculus (Lemmas 32-37), see "Proof of Theorem 31" above. Lemma 20's path
  form is proved by a union bound along `Kernel.trajectory`.
