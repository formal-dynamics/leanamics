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
