# MAJ-6 (b): 3-Majority from any configuration (progress)

Source: Berenbrink, Clementi, Elsässer, Kling, Mallmann-Trenn, Natale, *Ignore or Comply? On
breaking symmetry in consensus*, PODC 2017, arXiv:1702.04921 (v1), cited below as BCEKMN17 with
the numbering of v1. Roadmap row MAJ-6, part (b): the upper bound
`O(n^{3/4} log^{7/8} n)` for 3-Majority from any configuration, through the comparison of
anonymous consensus processes that dominates 3-Majority's colour reduction by the Voter
model's. Part (a) (the 2-Choices lower bound) is handled separately.

Status: **statements pinned** (phase 1 of the fixed-statement protocol). The pinned
declarations are listed in `PINNED.txt` at the repository root. Proved so far: the bridge to the
two-opinion model and the small infrastructure lemmas listed at the end.

## Files

All new files are imported from `ThreeMajority.lean`.

| File | Content |
| --- | --- |
| `ThreeMajority/AnyStartModel.lean` | k-colour 3-Majority on `Tgt3 n`, Voter, colour counts |
| `ThreeMajority/AnyStartMajorization.lean` | majorization, Schur-convex observables |
| `ThreeMajority/AnyStartComparison.lean` | AC-processes, dominance, Proposition 1, Theorem 2 |
| `ThreeMajority/AnyStartVsVoter.lean` | Equations (1), (2), both are AC-processes, Lemma 2 |
| `ThreeMajority/AnyStartVoter.lean` | coalescing walks, Lemma 4 (duality), Equation (7), Lemma 3 |
| `ThreeMajority/AnyStartMain.lean` | Phase 1, the cited Phase 2 result as a hypothesis, Theorem 4 |

`Audit.lean` prints the axioms of the package's main theorems, including the pinned theorems
listed here; `python3 ../scripts/check_axioms.py` (run in `3-majority/`) checks it.

## Pinned statements in words

Model (`AnyStartModel.lean`, BCEKMN17 Sections 2.1 and 2.2).

* `majColour c s`: the 3-Majority rule on a sample triple `s = (s₁, s₂, s₃)`: if `s₂` and `s₃`
  have the same colour adopt it, otherwise adopt the colour of `s₁`. `stepCol`, `runCol`: one
  round and a trajectory, on the existing round type `Tgt3 n` (every agent draws an ordered
  triple with replacement). `voterStep`, `voterRun`: Voter, with rounds `Fin n → Fin n`.
  `colourCount c a`: the number of agents of colour `a`. `numColours c`: the number of
  remaining colours; consensus is `numColours c ≤ 1`.
* `stepCol_bool` (proved): with colours `Bool`, `stepCol` is the package's two-opinion `step`.

Majorization (`AnyStartMajorization.lean`, Section 2.1).

* `Majorizes x y` (`x ⪰ y`): equal sums, and every sum of `y` over a set is at most a sum of
  `x` over a set of the same size (equivalently, the sum of the `j` largest entries of `y` is at
  most that of `x`, for every `j`). `countVec c`: the configuration vector as a real vector.
  `SchurConvex φ`: `φ` is monotone for the majorization of configuration vectors.
* `numColours_le_of_majorizes`: `countVec c ⪰ countVec c'` implies
  `numColours c ≤ numColours c'`.

Comparison framework (`AnyStartComparison.lean`, Section 2.2 and Appendix A.1).

* `acKernel α`: the one-round kernel of the AC-process with process function `α`
  (Definition 1): the agents draw their new colours independently from `α c`.
  `Dominates α α'`: `c ⪰ c'` implies `α c ⪰ α' c'` (Definition 2).
* `multinomial_schurConvex` (Proposition 1, Rinott): if `p ⪰ q`, then for every Schur-convex
  `φ`, the expectation of `φ` when the `n` agents draw i.i.d. from `q` is at most the one when
  they draw from `p`.
* `ac_comparison` (Theorem 2, distributional form): if `α` dominates `α'` and `c ⪰ c'`, then
  for every Schur-convex `φ` and every `T`, `E_{c'}[φ(P'_T)] ≤ E_c[φ(P_T)]`.
* `ac_numColours` (Theorem 2, for the number of colours): from the same configuration, the
  dominating process has at most `κ` colours at time `T` with at least the probability of the
  dominated one.

3-Majority versus Voter (`AnyStartVsVoter.lean`, Section 3.1).

* `alpha3M c`, `alphaVoter c`: the laws of the colour adopted by one agent.
  `alphaVoter_weight`: Equation (1), `α^V_a(c) = c_a/n`. `alpha3M_weight`: Equation (2),
  `α^{3M}_a(c) = x_a (1 + x_a − ‖x‖₂²)` with `x = c/n`.
* `apply_ofStep_stepCol`, `apply_ofStep_voterStep`: one uniform round of `stepCol`
  (resp. `voterStep`) is one step of `acKernel alpha3M` (resp. `acKernel alphaVoter`).
* `dominates_alpha3M_alphaVoter`: the inequality of the proof of Lemma 2.
* `voter_le_threeMaj` (Lemma 2): from the same configuration, after `T` rounds 3-Majority has
  at most `κ` colours with at least the probability that Voter has.

Voter bound (`AnyStartVoter.lean`, Section 3.2 and Appendix A.6).

* `walkStep Z y = y '' Z`: one step of coalescing random walks on the complete graph with
  self-loops.
* `numColours_voterRun_le` (Lemma 4, the inequality `T^k_V ≤ T^k_C`, pathwise): the colours of
  Voter after rounds `l` are at most the walks started on all nodes after the rounds `l` applied
  last to first (`List.foldr`).
* `voter_dual` (Equation (6), as the inequality used): `Pr[Voter has > k colours at T] ≤
  Pr[more than k walks remain at T]`.
* `walk_drift`: `E[X_{t+1} | X_t = x] ≤ x − x(x−1)/(3n)` for every `x`.
  `walk_drift_paper`: Equation (7), `≤ x − x²/(10n)` for `x ≥ 2`.
* `walk_expect_le`: `E[X_t] ≤ 1 + 3n/t` for `t ≥ 1`, from any initial set of walks.
* `voter_reduce_whp` (Lemma 3): for `n ≥ 2`, `k ≥ 1` and `T ≥ 24 (n/k) log n`, Voter has more
  than `k` colours at time `T` with probability at most `1/n`.

Main theorem (`AnyStartMain.lean`, Section 3 and Appendix A.7).

* `threeMaj_reduce_whp` (Phase 1): the same bound as Lemma 3, for 3-Majority.
* `Bcnpt16Phase2 ε` (Theorem 8 of BCEKMN17, that is Theorem 3.1 of Becchetti, Clementi, Natale,
  Pasquale, Trevisan, SODA 2016, for one `ε`): there are `C, N` such that for `n ≥ N`, from any
  configuration `Fin n → Fin n` with `k ≤ n^{1/3 − ε}` colours, consensus fails after any
  `T ≥ C (k² log^{1/2} n + k log n)(k + log n)` rounds with probability at most `1/n`.
* `threeMaj_anyStart_consensus` (Theorem 4): assuming `Bcnpt16Phase2 (1/24)`, there are
  `C, N` such that for `n ≥ N`, from any configuration `Fin n → Fin n`, consensus fails after
  any `T ≥ C n^{3/4} log^{7/8} n` rounds with probability at most `2/n`.

## Correspondence with the paper

| Paper (v1) | Lean |
| --- | --- |
| Section 2.1, configurations, `⪰` | `colourCount`, `numColours`, `countVec`, `Majorizes` |
| Schur-convex functions | `SchurConvex` |
| Definition 1 (AC-processes) | `acKernel` |
| Equations (1), (2) | `alphaVoter_weight`, `alpha3M_weight` |
| Definition 2 (protocol dominance) | `Dominates` |
| Theorem 2 | `ac_comparison`, `ac_numColours` |
| Lemma 1, Theorem 3, Theorem 6 (coupling, Strassen) | not formalized (see deviations) |
| Proposition 1 | `multinomial_schurConvex` |
| Lemma 2 | `dominates_alpha3M_alphaVoter`, `voter_le_threeMaj` |
| Lemma 4, Equation (6) | `numColours_voterRun_le`, `voter_dual` |
| Equation (7) | `walk_drift_paper` (and the stronger `walk_drift`) |
| Equations (18), (19), Theorem 7 (variable drift) | replaced by `walk_expect_le` |
| Lemma 3 | `voter_reduce_whp` |
| Phase 1 of Theorem 4 | `threeMaj_reduce_whp` |
| Theorem 8 (BCNPT16, Theorem 3.1) | `Bcnpt16Phase2` (hypothesis) |
| Theorem 4 | `threeMaj_anyStart_consensus` |

## Deviations from the source

1. **Tie-breaking.** The paper adopts a uniformly random sampled colour when the three samples
   have three different colours; here the first sample's colour is adopted. The samples are
   i.i.d., so the two rules have the same law (Equation (2) holds for `majColour`, which
   `alpha3M_weight` states), and this keeps the round type `Tgt3 n` of the package. With two
   colours the process is the package's `step` (`stepCol_bool`). The rule `majColour` is,
   pointwise, the rule of the cited Phase 2 paper (Becchetti et al., SODA 2016, Section 2:
   three samples uniform with repetition, the agent itself included; on three different
   colours, the first sample), so the Phase 2 hypothesis is stated for the process it is about.
2. **Theorem 2 is stated in distributional form, without the coupling.** The paper states
   `T^κ_{P'} ≥st T^κ_P` and derives it from a one-step coupling (Lemma 1) obtained from Strassen's
   theorem (Theorems 3 and 6). Here Theorem 2 is the inequality between expectations of
   Schur-convex observables at every fixed time, from configurations `c ⪰ c'`. It implies the
   statement about the number of colours (`ac_numColours`), which for processes that never
   create colours (both 3-Majority and Voter: `numColours_stepCol_le`,
   `numColours_voterStep_le`) is the stochastic domination of the hitting times. The
   distributional form follows from Proposition 1 alone, by induction on `T`: with `u_T`,
   `v_T` the expectations at time `T` for the dominated and the dominating process, the
   function `w(y) = max {u_T(z) : z ⪯ y}` is Schur-convex and satisfies `u_T ≤ w ≤ v_T`, so
   Proposition 1 applied to `w` gives the step from `T` to `T + 1`. Lemma 1 and Strassen's
   theorem are not needed.
3. **The Voter bound goes through `E[X_t] ≤ 1 + 3n/t` instead of the variable drift theorem.**
   On the complete graph with self-loops the number of walks after one step is the number of
   occupied cells when `x` balls go into `n` cells, so `E[X_{t+1} | X_t = x] = n(1 − (1 − 1/n)^x)
   ≤ x − x(x−1)/(3n)` for every `x` (`walk_drift`), which implies the paper's Equation (7) for
   `x ≥ 2` (`walk_drift_paper`). The paper's two-phase argument for (7) assumes `x > 100`
   ("`k` larger than a big constant") and treats constant `k` separately; the occupancy bound
   covers every `x` at once. Jensen's inequality (the drift bound is concave in `x`) then gives
   `E[X_t] ≤ 1 + 3n/t` (`walk_expect_le`), which replaces `E[T^k_C] ≤ 20 n/k`. Markov's
   inequality and restarts then give Lemma 3, as in the paper.
4. **Lemma 4 is formalized as the inequality the paper uses.** The paper proves the equality
   `T^k_V = T^k_C` under a coupling and only uses `T^k_V ≤ T^k_C`. Here the inequality is
   pathwise (`numColours_voterRun_le`) and is made probabilistic by time reversal of i.i.d.
   rounds (`Dynamics.expList_comp_reverse`, `Dynamics.Kernel.iterate_ofStep_foldr`). The
   duality is restated in this package, since it does not depend on the `voter` package.
5. **The cited Phase 2 result is a hypothesis.** Theorem 4's second phase applies Theorem 3.1
   of Becchetti, Clementi, Natale, Pasquale, Trevisan (SODA 2016), which is not part of
   BCEKMN17 and is not formalized in this repository. `threeMaj_anyStart_consensus` assumes it
   (`Bcnpt16Phase2 (1/24)`), exactly as the paper's proof does. The hypothesis is the statement
   of Theorem 3.1 of the SODA 2016 paper (arXiv:1508.06782 v1, "The Adversary-Free Case") for
   `ε = 1/24`, with two explicit choices. (i) "W.h.p." is `≥ 1 − 1/n`, while that paper defines
   it as `1 − O(n^{−λ})` for some constant `λ > 0`: the `1/n` form follows by running the
   phase `⌈2/λ⌉` times in a row, since colours never increase, the process is Markov and the
   bound holds from any configuration with at most `k` colours; this only changes `C` and `N`.
   (ii) "Reaches consensus within `T₀` rounds" is stated as "no consensus at any time
   `T ≥ T₀`" with probability at most `1/n`, which is the same event since consensus is
   absorbing.
6. **Explicit constants.** Lemma 3 and Phase 1 are stated with the explicit constant `24`
   (`T ≥ 24 (n/k) log n`, failure probability `≤ 1/n`, for `n ≥ 2`). Theorem 4 is asymptotic
   (`∃ C N`), as is the cited Phase 2 result it uses; its failure probability is `2/n` (one `1/n`
   for each phase).
7. **Colours.** The comparison framework and Lemmas 2 to 4 are stated for any finite colour
   type `σ`. Theorem 4 and the Phase 2 hypothesis use colours `Fin n`, the paper's `[k] ⊆ [n]`.

## Corrections to the source

* **The proof of Theorem 4 needs a minor correction.** Appendix A.7 applies Lemma 3 with
  `k = n^{1/4}`, which gives `O((n/k) log n) = O(n^{3/4} log n)` rounds for Phase 1, not
  `O(n^{3/4} log^{7/8} n)` (the overview of the two phases at the start of Section 3 says the
  same, "Voter reaches `O(n^{1/4})` colors in `O(n^{3/4} log^{7/8} n)` rounds", although its
  heading names `n^{1/4} log^{1/8} n` colours). The balanced choice is
  `k = n^{1/4} log^{1/8} n`: then Phase 1 takes `O(n^{3/4} log^{7/8} n)` rounds and Phase 2
  takes `O(k³ log^{1/2} n) = O(n^{3/4} log^{7/8} n)` rounds (and `k ≤ n^{1/3 − ε}` for
  `ε < 1/12` and `n` large). With this choice the statement of Theorem 4 holds as stated; this
  is the form used here.

Remarks (no correction needed):

* Equation (7) is stated without a range in Section 3.2, but its proof (Appendix A.6) covers
  only `x > 100`: the bound `⌈x/2⌉ ⌊x/4⌋/n ≥ x²/(10n)` fails for small `x` (for instance
  `x = 7`). The paper treats constant `k` by a separate argument, so Lemma 3 is unaffected, and
  the statement of (7) holds for every `x ≥ 2` anyway (deviation 3).
* Lemma 2's text says "the time Voter needs to reach consensus" while its display is about
  `T^κ` for every `κ`; the display is what is pinned.

## Numerical checks

Run on small cases with exact rational arithmetic: Equation (2) for `majColour` (all
configurations, `n ≤ 4`, three colours); the inequality of Lemma 2 (all pairs of configuration
vectors, `n ≤ 8`, up to four colours); `walk_drift` (`n < 60`, every `x ≤ n`) and Equation (7)
for `x ≥ 2`; `walk_expect_le` (exact walk chain, `n ≤ 15`, `t < 3n`); the bound of
`voter_reduce_whp` with the constant `24` (walk chain in floating point, `n ≤ 40`, every `k`);
and Lemma 2 itself, `Pr[3M has ≤ κ colours at T] ≥ Pr[Voter has ≤ κ colours at T]` (exact
chains on sorted configuration vectors, `n ≤ 6`, `T ≤ 6`, every start and `κ`). Also: the
sort-free `Majorizes` agrees with the sorted partial-sum definition (all integer vectors with
entries in `[−2, 3]`, length `≤ 4`); Proposition 1 for random Schur-convex observables
(`φ(x) = max {r(z) : z ⪯ x}` for random `r`) and `p ⪰ q` obtained by transfers or by
filtering random pairs (`n ≤ 5`, up to four colours; the same test fails for random
non-Schur-convex `φ`); `ac_comparison` for 3-Majority from `c` against Voter from `c' ⪯ c`
(random Schur-convex `φ`, `n ≤ 5`, three colours, `T ≤ 3`); the arithmetic of the proof plan
of `voter_reduce_whp` (`n < 3000`); and `⌊n^{1/4} log^{1/8} n⌋ ≤ n^{7/24}` for
`44 ≤ n < 10⁶` (it fails at `n = 42, 43`; Theorem 4 only needs large `n`). All passed.

## Proved so far

`stepCol_bool`, `runCol_eq_foldl`, `runCol_append`, `voterRun_eq_foldl`,
`image_stepCol_subset`, `numColours_stepCol_le`, `numColours_runCol_append_le`,
`numColours_voterStep_le`, `Majorizes.refl`, `Majorizes.trans`; and, from pinned lemmas still
open, `schurConvex_numColours_le` (from `numColours_le_of_majorizes`), `ac_numColours` (from
`ac_comparison`) and `walk_drift_paper` (from `walk_drift`).

## Remaining

16 pinned theorems (`sorry`). Suggested order: `numColours_le_of_majorizes`;
`alphaVoter_weight`, `alpha3M_weight`, `apply_ofStep_stepCol`, `apply_ofStep_voterStep`,
`dominates_alpha3M_alphaVoter`; `numColours_voterRun_le`, `voter_dual`, `walk_drift`,
`walk_expect_le`, `voter_reduce_whp`; `multinomial_schurConvex` (the hardest);
`ac_comparison`, `voter_le_threeMaj`; `threeMaj_reduce_whp`; `threeMaj_anyStart_consensus`.
