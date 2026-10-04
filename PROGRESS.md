# EPI-8 Growth.lean progress

Paper: Doerr–Kostrygin, arXiv:2303.11150, Lemma 9, Lemma 19, Theorem 21 (Appendix B.2).

## Status

- `variance_card_le` (Lemma 9): proved in `Epidemics/Revisited/GrowthAux.lean` (`variance_card_le_proof`). File compiles. Not yet wired into `Growth.lean`.
- `connect_tail`, `connect_expect` (Lemma 19): in progress (`GrowthConnect.lean`).
- `growth_upper_tail`, `growth_upper_expect` (Theorem 21): not started.

## Plan

1. Finite-distribution lemmas: support of a monotone kernel, variance of a sum of indicators, Chebyshev, Cantelli, geometric sums. Done in `GrowthAux.lean`.
2. `variance_card_le` from `|S'| = |S| + ∑_{x ∉ S} 1[x ∈ S']` a.s. Done.
3. `connect_tail` by the potential `g S = if |S| < m then n - |S| else 0`, contraction `Kg ≤ (1-p) g` on `{|S| ≥ ℓ}`, then Markov.
4. `connect_expect` by summing the geometric tail.
5. Exponential regime: explicit constants depending only on `γlo, γhi, a, b, c, f`.
   Round target `E0(k) = E(k) - A k^{3/4}` with `A` small, phases `k_{j+1} = k_j + E0(k_j)` up to `J = ⌊log_{1+γ}(f' n)⌋`, failure `Q_j`, potential `G` on the phase index, then Lemma 19 from `k_J` to `f n`.
6. Expectation from the tail by `notYet ≤ 1` on the first `⌈log⌉` terms and a geometric series after that.

## Deviations from the paper (intended)

- No dummy process and no stochastic domination by geometric sums (Lemmas 10, 11, 25). Phase crossing uses a potential on `Kernel.iterate`.
- `f` is shrunk to `f' = min(f/2, 1/(8(a+1)))` only inside the phase construction; the final target stays `f n`, crossed by Lemma 19.
- `Distribution.prob` / `Kernel.event` indicators are bridged by `prob_indicator_eq` because `prob` uses `Classical.propDecidable`, which is not definitionally the `Decidable` instance of membership.
- Constants are explicit. `N` may be enormous.

## Current errors

None in `GrowthAux.lean` (`lake env lean` exits 0). `Growth.lean` still has the five `sorry`s.
