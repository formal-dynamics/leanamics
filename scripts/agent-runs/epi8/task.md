# Task: EPI-8, exponential growth regime upper bound (Doerr–Kostrygin, "Randomized rumor spreading revisited")

You are working in a git worktree of the Lean 4 + Mathlib monorepo Leanamics (lean package `epidemics/`,
which depends on `dynamics/` via a relative path). Your job: replace every `sorry` in
`epidemics/Epidemics/Revisited/Growth.lean` by a complete proof.

Paper: Doerr, Kostrygin, ICALP 2017, long version arXiv:2303.11150. A text extraction is in
`PAPER.txt` at the worktree root (Lemma 9 near "Lemma 9. Let a random variables"; Lemma 19 and
Appendix B.2 = Definition 9, Theorem 21, Lemmas 22–26, from "B.1 Homogeneous Rumor Spreading
Processes"; Lemmas 10/11 on sums of geometric variables). Read it.

## Fixed-statement protocol (mechanically checked afterwards; violations = run rejected)

- `epidemics/Epidemics/Revisited/Defs.lean` is FROZEN: do not change one byte.
- In `Growth.lean` the five theorem statements (from `theorem` to `:=`) and all
  `namespace`/`open`/`variable`/`end` lines are FROZEN, byte-identical. Only the proofs change.
- You may add helper files `epidemics/Epidemics/Revisited/GrowthAux*.lean` (or similar names under
  `Epidemics/Revisited/`) and import them from `Growth.lean` (adding `import` lines is allowed).
  Add every new file to `epidemics/Epidemics.lean`. Do not import anything outside Mathlib,
  `Dynamics.*` and `Epidemics.*`.
- Finite probability only (Dynamics.Distribution / Kernel / expList), no measure theory.
- Forbidden anywhere: `sorry`, `admit`, `axiom`, `opaque`, `native_decide`, `implemented_by`,
  `extern`. The final `lake build` must be warning-free (no unused variables, no linter warnings,
  no deprecated names) and `#print axioms` must show only propext, Classical.choice, Quot.sound.
- Do NOT run any writing git command (commit, checkout, stash, reset, ...). Read-only git is fine.
- Do not modify `dynamics/` (generic helpers you need go into your own Aux files).
- Build with `cd epidemics && lake build Epidemics.Revisited.Growth` (Mathlib is prebuilt; never
  run `lake update`, `lake clean`, or delete `.lake`). For quick checks use
  `lake env lean <file>`.

Maintain `PROGRESS.md` at the worktree root: what is proved, what remains, current errors, plan.
Update it whenever you finish a lemma, so that a resumed session can continue.

## Suggested route (you may deviate, statements stay fixed)

1. `variance_card_le` (Lemma 9). Almost surely `S ⊆ S'` (weights of non-supersets are zero, from
   `P.mono`), so `|S'| = |S| + ∑_{x ∉ S} 1[x ∈ S']`. Expand the variance of a sum of indicators:
   diagonal terms `Var ≤ E` for indicators, off-diagonal terms are `P.cov`, at most `c` each, and
   there are at most `(n - |S|)^2` of them (needs `0 ≤ c`).
2. `connect_tail` (Lemma 19 (i)) WITHOUT the paper's dummy process: let
   `g S = if (S.card : ℝ) < m then (n - S.card) else 0`. Show `K.apply g S ≤ (1 - p) * g S` for
   all `S` with `ℓ ≤ S.card` (states with `card ≥ m` stay there by monotonicity, so `g` stays 0;
   for `card < m` use `E[n - |S'|] = ∑_{x ∉ S} (1 - informProb S x) ≤ (n - |S|)(1 - p)`), iterate
   (states reached keep `ℓ ≤ card`, by monotonicity; e.g. carry the invariant in the induction
   or work with `g' S = if ℓ ≤ S.card then g S else (n:ℝ)` style), then Markov:
   `1[card < m] ≤ g / (n - m)`. `connect_expect` is the geometric sum of `connect_tail`.
3. `growth_upper_tail` (Theorem 21). Paper route: X(k) = number of newly informed nodes,
   `E[X] ≥ E(k) := γ k (1 - (a+1) k/n - b/ln n)`; round target `E0(k) = E(k) - A k^B` with
   `B = 3/4` and small `A`; Chebyshev/Cantelli (prove these for `Distribution` yourself) give
   `P[X(k) ≤ E0(k)] ≤ min(q(k), q(1)/(1+q(1)))` with `q(k) = (γ + c)/A^2 · k^{1-2B}`; targets
   `k_0 = 1, k_{j+1} = k_j + E0(k_j)`, `k_j ≥ α (1+γ)^j` up to `J = log_{1+γ} n - O(1)`, so
   `k_J ≥ δ n`; `∑_j Q_j = O(1)`. Note the paper also shrinks `f` to some `f' < 1/(2(a+1))` for the
   monotonicity of `E0`, then crosses `[k_J, f n)` with Lemma 19, using
   `p_k ≥ γ (k_J / n)(1 - a f - b / ln n) > 0` there (this is where `a f < 1` is used).
   For the phase-to-tail step, instead of stochastic domination by geometric sums (paper
   Lemmas 10, 11, 25) a potential-function induction on `K.iterate` is much easier in Lean:
   with phase(S) = largest `j ≤ J` with `k_j ≤ |S|`, phase never decreases, and from phase
   `j < J` one round reaches phase `≥ j + 1` with probability `≥ 1 - Q_j`, where `x Q_j < 1`
   for a fixed `x > 1`. Put `r_i = x (1 - Q_i) / (1 - x Q_i) ≥ 1` and `G(j) = ∏_{i=j}^{J-1} r_i`.
   Then by induction on `t`: `P_S[phase(S_t) < J] ≤ x^{-t} G(phase S)` (phase-`J` states give 0;
   otherwise use `Q_j G(j) + (1 - Q_j) G(j+1) ≤ G(j) / x` and that `G` is antitone). Hence
   `P[phase < J after J + r rounds] ≤ x^{-r} ∏_i (1 - Q_i)/(1 - x Q_i)`, and the product is
   bounded by `exp((x - 1)/(1 - x Q*) ∑_i Q_i) = O(1)`. Starting sets `S` with `|S| > 1` start in a
   later phase, which only helps. Combine with Lemma 19 by the Markov property
   (`Kernel.iterate_add_time`) and absorb `J ≤ ⌈log_{1+γ} n⌉ + O(1)` and the integer rounding
   into `A`. Make all constants explicit and depend only on `γlo, γhi, a, b, c, f`; take `N`
   large (it may be astronomically large, that is fine).
4. `growth_upper_expect` from `growth_upper_tail` (`notYet ≤ 1` for the first `⌈log⌉` terms, then
   a geometric series), with the same kind of `∃ B N`.

Useful API: `Dynamics.Kernel.iterate`, `iterate_mono`, `iterate_add_time`, `event`,
`Dynamics.Distribution.expect/prob/expect_mono/expect_add/expect_sum`, `Real.logb`,
`Real.exp`, `Finset.sum_range` lemmas. Look at `dynamics/Dynamics/Phases.lean` for a model of
induction on `K.iterate` with the `outside` indicator.

When everything builds without warnings and no `sorry` is left, write a final summary
(theorem list, files added, line counts, any deviations from the paper's proof) in PROGRESS.md
and stop.
