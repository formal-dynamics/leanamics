# Formalization differences

Where the statements and proofs of `3-majority/` deviate from their sources, and why. The
two-opinion theorem `majority3_consensus_whp` follows no specific paper (its own proof is in
[latex/three_majority.tex](latex/three_majority.tex)), so this file covers the multi-colour
results of roadmap MAJ-6 (b).

## 3-Majority from any configuration (`AnyStart*`, roadmap MAJ-6 (b))

Source: Berenbrink, Clementi, Elsässer, Kling, Mallmann-Trenn and Natale, *Ignore or comply? On
breaking symmetry in consensus*, PODC 2017, cited below as BCEKMN17, with the numbering of
arXiv:1702.04921 (v1): Theorem 4 (Section 3, proof in Appendix A.7), the comparison framework of
Sections 2.1 to 2.3 (Definitions 1 and 2, Proposition 1, Theorem 2) and Lemmas 2 to 4.

**The result is conditional on a cited theorem that is not formalized.** The second phase of the
proof of Theorem 4 applies Theorem 3.1 of Becchetti, Clementi, Natale, Pasquale, Trevisan,
*Stabilizing consensus with many opinions*, SODA 2016, arXiv:1508.06782 (restated as Theorem 8
of BCEKMN17). That theorem is not part of BCEKMN17 and is not formalized in this repository
(it is roadmap MAJ-12 (a)). The main theorem `threeMaj_anyStart_consensus` takes it as the
explicit hypothesis `Bcnpt16Phase2 (1/24)`, exactly as the paper's proof uses it; everything
else (the comparison framework, Lemmas 2 to 4, Phase 1 and the assembly of the two phases) is
proved. See difference 5 below for how the hypothesis is stated.

### The statements

Model (`AnyStartModel.lean`, Sections 2.1 and 2.2). `majColour c s` is the 3-Majority rule on a
sample triple `s = (s₁, s₂, s₃)`: if `s₂` and `s₃` have the same colour adopt it, otherwise
adopt the colour of `s₁`. `stepCol` and `runCol` are one round and a trajectory, on the
package's round type `Tgt3 n` (every agent draws an ordered triple with replacement);
`voterStep` and `voterRun` are Voter, with rounds `Fin n → Fin n`. `colourCount c a` is the
number of agents of colour `a`, `numColours c` the number of remaining colours; consensus is
`numColours c ≤ 1`. With colours `Bool`, `stepCol` is the package's two-opinion `step`
(`stepCol_bool`).

Majorization (`AnyStartMajorization.lean`, Section 2.1). `Majorizes x y` (the paper's `x ⪰ y`):
equal sums, and every sum of `y` over a set is at most a sum of `x` over a set of the same size
(equivalently, for every `j` the sum of the `j` largest entries of `y` is at most that of `x`).
`countVec c` is the configuration vector as a real vector, and `SchurConvex φ` says that `φ` is
monotone for the majorization of configuration vectors. `numColours_le_of_majorizes`:
`countVec c ⪰ countVec c'` implies `numColours c ≤ numColours c'`.

Comparison framework (`AnyStartComparison.lean`, Sections 2.2 and 2.3, Appendix A.1).

* `acKernel α`: the one-round kernel of the AC-process with process function `α` (Definition 1):
  the agents draw their new colours independently from `α c`. `Dominates α α'`: `c ⪰ c'`
  implies `α c ⪰ α' c'` (Definition 2).
* `multinomial_schurConvex` (Proposition 1, Rinott): if `p ⪰ q`, then for every Schur-convex `φ`
  the expectation of `φ` when the `n` agents draw i.i.d. from `q` is at most the one when they
  draw from `p`.
* `ac_comparison` (Theorem 2, distributional form): if `α` dominates `α'` and `c ⪰ c'`, then for
  every Schur-convex `φ` and every `T`, `E_{c'}[φ(P'_T)] ≤ E_c[φ(P_T)]`.
* `ac_numColours` (Theorem 2, for the number of colours): from the same configuration, the
  dominating process has at most `κ` colours at time `T` with at least the probability of the
  dominated one.

3-Majority versus Voter (`AnyStartVsVoter.lean`, Section 3.1).

* `alpha3M c`, `alphaVoter c`: the laws of the colour adopted by one agent. `alphaVoter_weight`
  is Equation (1), `α^V_a(c) = c_a/n`; `alpha3M_weight` is Equation (2),
  `α^{3M}_a(c) = x_a (1 + x_a − ‖x‖₂²)` with `x = c/n`.
* `apply_ofStep_stepCol`, `apply_ofStep_voterStep`: one uniform round of `stepCol` (resp.
  `voterStep`) is one step of `acKernel alpha3M` (resp. `acKernel alphaVoter`).
* `dominates_alpha3M_alphaVoter`: the inequality of the proof of Lemma 2.
* `voter_le_threeMaj` (Lemma 2): from the same configuration, after `T` rounds 3-Majority has at
  most `κ` colours with at least the probability that Voter has.

Voter bound (`AnyStartVoter.lean`, Section 3.2 and Appendix A.6).

* `walkStep Z y = y '' Z`: one step of coalescing random walks on the complete graph with
  self-loops.
* `numColours_voterRun_le` (Lemma 4, the inequality `T^k_V ≤ T^k_C`, pathwise): the colours of
  Voter after the rounds `l` are at most the walks started on all nodes after the rounds `l`
  applied last to first (`List.foldr`).
* `voter_dual` (Equation (6), as the inequality used): `Pr[Voter has > k colours at T] ≤
  Pr[more than k walks remain at T]`.
* `walk_drift`: `E[X_{t+1} | X_t = x] ≤ x − x(x−1)/(3n)` for every `x`; `walk_drift_paper`:
  Equation (7), `≤ x − x²/(10n)` for `x ≥ 2`.
* `walk_expect_le`: `E[X_t] ≤ 1 + 3n/t` for `t ≥ 1`, from any initial set of walks.
* `voter_reduce_whp` (Lemma 3): for `n ≥ 2`, `k ≥ 1` and `T ≥ 24 (n/k) log n`, Voter has more
  than `k` colours at time `T` with probability at most `1/n`.

Main theorem (`AnyStartMain.lean`, Section 3 and Appendix A.7; `AnyStartAsymptotics.lean`).

* `threeMaj_reduce_whp` (Phase 1): the bound of Lemma 3, for 3-Majority.
* `Bcnpt16Phase2 ε` (Theorem 8 of BCEKMN17, that is Theorem 3.1 of the SODA 2016 paper, for one
  `ε`): there are `C, N` such that for `n ≥ N`, from any configuration `Fin n → Fin n` with
  `k ≤ n^{1/3 − ε}` colours, consensus fails after any
  `T ≥ C (k² log^{1/2} n + k log n)(k + log n)` rounds with probability at most `1/n`. This is a
  definition (a proposition), not a theorem: it is not proved here.
* `threeMaj_anyStart_consensus` (Theorem 4, conditional): **assuming `Bcnpt16Phase2 (1/24)`**,
  there are `C, N` such that for `n ≥ N`, from any configuration `Fin n → Fin n`, consensus
  fails after any `T ≥ C n^{3/4} log^{7/8} n` rounds with probability at most `2/n`.
* `anyStart_asymptotics`: the real inequalities of Theorem 4, for the number of colours
  `phase1Colours n = ⌊n^{1/4} log^{1/8} n⌋` at which Phase 1 stops.

### Correspondence with the paper

| BCEKMN17 (arXiv v1) | Lean |
| --- | --- |
| Section 2.1, configurations, `⪰` | `colourCount`, `numColours`, `countVec`, `Majorizes` |
| Schur-convex functions | `SchurConvex`, `schurConvex_numColours_le` |
| Definition 1 (AC-processes) | `acKernel` |
| Equations (1), (2) | `alphaVoter_weight`, `alpha3M_weight` |
| Definition 2 (protocol dominance) | `Dominates` |
| Proposition 1 | `multinomial_schurConvex` (proof: `expect_le_of_majorizes`) |
| Theorem 2 | `ac_comparison`, `ac_numColours` |
| Lemma 1, Theorems 3 and 6 (coupling, Strassen) | not formalized (not needed, difference 2) |
| Lemma 2 | `dominates_alpha3M_alphaVoter`, `voter_le_threeMaj` |
| Lemma 4, Equation (6) | `numColours_voterRun_le`, `voter_dual` |
| Equation (7) | `walk_drift_paper` (and the stronger `walk_drift`) |
| Equations (18), (19), Theorem 7 (variable drift) | replaced by `walk_expect_le` (difference 3) |
| Lemma 3 | `voter_reduce_whp` |
| Phase 1 of Theorem 4 | `threeMaj_reduce_whp` |
| Theorem 8 (SODA 2016, Theorem 3.1) | `Bcnpt16Phase2` (a hypothesis, not proved) |
| Theorem 4 | `threeMaj_anyStart_consensus` (conditional on `Bcnpt16Phase2 (1/24)`) |

### Differences in the statements

1. **Tie-breaking.** The paper adopts a uniformly random sampled colour when the three samples
   have three different colours; here the first sample's colour is adopted. The samples are
   i.i.d., so the two rules have the same law (Equation (2) holds for `majColour`, which
   `alpha3M_weight` states), and this keeps the round type `Tgt3 n` of the package. With two
   colours the process is the package's `step` (`stepCol_bool`). The rule `majColour` is,
   pointwise, the rule of the SODA 2016 paper (its Section 2: three samples uniform with
   repetition, the agent itself included; on three different colours, the first sample), so the
   Phase 2 hypothesis is stated for the process it is about.
2. **Theorem 2 is stated in distributional form, without the coupling.** The paper states
   `T^κ_{P'} ≥st T^κ_P` and derives it from a one-step coupling (Lemma 1) obtained from
   Strassen's theorem (Theorems 3 and 6). Here Theorem 2 is the inequality between expectations
   of Schur-convex observables at every fixed time, from configurations `c ⪰ c'`. It implies the
   statement about the number of colours (`ac_numColours`), which for processes that never
   create colours (both 3-Majority and Voter: `numColours_stepCol_le`, `numColours_voterStep_le`)
   is the stochastic domination of the hitting times.
3. **Lemma 4 is formalized as the inequality the paper uses.** The paper proves the equality
   `T^k_V = T^k_C` under a coupling and only uses `T^k_V ≤ T^k_C`. Here the inequality is
   pathwise (`numColours_voterRun_le`) and is made probabilistic by time reversal of i.i.d.
   rounds (`Dynamics.expList_comp_reverse`, `Dynamics.Kernel.iterate_ofStep_foldr`). The duality
   is restated in this package, since it does not depend on the `voter` package.
4. **Explicit constants.** Lemma 3 and Phase 1 are stated with the explicit constant `24`
   (`T ≥ 24 (n/k) log n`, failure probability `≤ 1/n`, for `n ≥ 2`). Theorem 4 is asymptotic
   (`∃ C N`), as is the cited Phase 2 result it uses; its failure probability is `2/n` (one `1/n`
   for each phase). The proof takes `C = 49 + 4|C₂|`, where `C₂` is the constant of the Phase 2
   hypothesis, and a threshold `N` that is not explicit.
5. **The cited Phase 2 result is a hypothesis.** `threeMaj_anyStart_consensus` assumes
   `Bcnpt16Phase2 (1/24)`, the statement of Theorem 3.1 of the SODA 2016 paper (arXiv:1508.06782
   v1, "The Adversary-Free Case") for `ε = 1/24`, with two explicit choices.
   (i) "W.h.p." is `≥ 1 − 1/n`, while that paper defines it as `1 − O(n^{−λ})` for some constant
   `λ > 0`: the `1/n` form follows by running the phase `⌈2/λ⌉` times in a row, since colours
   never increase, the process is Markov and the bound holds from any configuration with at most
   `k` colours; this only changes `C` and `N`.
   (ii) "Reaches consensus within `T₀` rounds" is stated as "no consensus at any time `T ≥ T₀`"
   with probability at most `1/n`, which is the same event since consensus is absorbing.
   Formalizing this hypothesis is roadmap MAJ-12 (a); until then the theorem is conditional.
6. **Colours.** The comparison framework and Lemmas 2 to 4 are stated for any finite colour type
   `σ`. Theorem 4 and the Phase 2 hypothesis use colours `Fin n`, the paper's `[k] ⊆ [n]`.

### Differences in the proofs

1. **Proposition 1 gets a proof.** The paper cites it (Rinott; Marshall, Olkin, Arnold,
   Proposition 11.E.11) without proof. `expect_le_of_majorizes` (`AnyStartRinott.lean`) proves
   it without the decomposition by the agents of two colours and without binomial sums:
   * `expect_le_of_transfer` (one Robin Hood transfer from `a` to `b`): with `F(θ)` the
     expectation when `a` has mass `θ` and `b` mass `s − θ`, `F` is nondecreasing on `[s/2, s]`.
     Its derivative is a sum over agents `v`; swapping `a, b` for all agents and then for agent
     `v` only pairs the terms into products `(Π_θ − Π_{s−θ}) (φ(v ↦ a) − φ(v ↦ b))` of two
     factors of the same sign, both governed by whether the other agents have colour `a` at least
     as often as `b` (`sum_transferSlope_nonneg`, `transfer_term_nonneg`,
     `majorizes_countVec_update`).
   * `expect_le_of_partial_sums`: a chain of transfers (the Hardy–Littlewood–Pólya step
     `exists_transfer_step`, by strong induction on the number of differing colours), for `q`
     sorted along an enumeration of the colours and partial sums of `p` dominating those of `q`.
   * `expect_le_of_majorizes`: sorting (`exists_equiv_antitone`) and relabelling the colours of
     `p` (`expect_independent_perm`: Schur-convex observables are invariant under relabelling)
     reduce the sort-free `Majorizes` to that case.
2. **Theorem 2 from Proposition 1 alone.** By induction on `T`: with `u_T`, `v_T` the
   expectations at time `T` for the dominated and the dominating process, the function
   `w(y) = max {u_T(z) : z ⪯ y}` is Schur-convex and satisfies `u_T ≤ w ≤ v_T`, so Proposition 1
   applied to `w` gives the step from `T` to `T + 1`. Lemma 1 and Strassen's theorem are not
   needed.
3. **Lemma 2 without sorting.** `dominates_alpha3M_alphaVoter` takes a top set of the same size
   (`exists_top_set`, an exchange argument) and proves the sort-free form of the paper's
   inequality, `‖x‖₂² ∑_S x ≤ ∑_S x²` on a top set `S` (`sq_norm_mul_sum_le`, from
   `∑_{i∈S} ∑_j x_i x_j (x_i − x_j) ≥ 0`), instead of the paper's induction on the sorted
   vector. Equations (1) and (2) are normalized fibre counts (`uniform_map_weight`); for
   3-Majority, through the indicator identity `[maj = a] = [x₂ = a][x₃ = a] + [x₁ = a] −
   [x₂ = x₃][x₁ = a]` (`ite_majority_eq`) and `∑_{u,v} [c u = c v] = ∑_b c_b²`.
4. **The Voter bound goes through `E[X_t] ≤ 1 + 3n/t` instead of the variable drift theorem.**
   On the complete graph with self-loops the number of walks after one step is the number of
   occupied cells when `x` balls go into `n` cells, so `E[X_{t+1} | X_t = x] = n(1 − (1 − 1/n)^x)
   ≤ x − x(x−1)/(3n)` for every `x` (`walk_drift`, by the degree-3 Bonferroni bound
   `bonferroni_le_one_sub_pow`), which implies the paper's Equation (7) for `x ≥ 2`
   (`walk_drift_paper`). The paper's two-phase argument for (7) assumes `x > 100` ("`k` larger
   than a big constant") and treats constant `k` separately; the occupancy bound covers every
   `x` at once. The tangent-line bound of the concave map `x ↦ x − x(x−1)/(3n)`
   (`walk_drift_le_tangent`, in place of Jensen's inequality) and its monotonicity on `[0, n+1]`
   (`walk_drift_mono`) then give `E[X_t] ≤ 1 + 3n/t` (`walk_expect_le`), which replaces
   `E[T^k_C] ≤ 20 n/k`. Lemma 3 then follows as in the paper, by Markov's inequality and
   restarts: blocks of `⌈6n/k⌉` rounds, Markov on `X − 1` (the walks never vanish), and the
   shared `Kernel.geometric_blocks` with factor `1/2`.
5. **Theorem 4.** `T = T₁ + T₂` with `T₁ = ⌈24 (n/k) log n⌉` and `k = phase1Colours n`
   (the first remark on the sources explains this choice): after `T₁` rounds either more than `k` colours
   remain (probability `≤ 1/n`, by `threeMaj_reduce_whp`) or the Phase 2 hypothesis applies to
   the current configuration. The real inequalities (`1 ≤ k ≤ n^{7/24}`, both phases within
   `C n^{3/4} log^{7/8} n` rounds) are `anyStart_asymptotics`, through `log y ≤ y^{1/4}` and
   `log^{1/8} y ≤ y^{1/24}` for large `y`.

### Remarks on the sources

* **The proof of Theorem 4 needs a minor correction.** Appendix A.7 applies Lemma 3 with
  `k = n^{1/4}`, which gives `O((n/k) log n) = O(n^{3/4} log n)` rounds for Phase 1, not
  `O(n^{3/4} log^{7/8} n)` (the overview of the two phases at the start of Section 3 says the
  same, "Voter reaches `O(n^{1/4})` colors in `O(n^{3/4} log^{7/8} n)` rounds", although its
  heading names `n^{1/4} log^{1/8} n` colours). The balanced choice is `k = n^{1/4} log^{1/8} n`:
  then Phase 1 takes `O(n^{3/4} log^{7/8} n)` rounds and Phase 2 takes
  `O(k³ log^{1/2} n) = O(n^{3/4} log^{7/8} n)` rounds (and `k ≤ n^{1/3 − ε}` for `ε < 1/12` and
  `n` large). With this choice the statement of Theorem 4 holds as stated; this is the form
  formalized (`phase1Colours`).
* Equation (7) is stated without a range in Section 3.2, but its proof (Appendix A.6) covers only
  `x > 100`: the intermediate bound `⌈x/2⌉ ⌊x/4⌋/n ≥ x²/(10n)` does not hold for small `x` (for
  instance `x = 7`). The paper treats constant `k` by a separate argument, so Lemma 3 is
  unaffected, and Equation (7) itself holds for every `x ≥ 2` (`walk_drift_paper`). No
  correction is needed.
* Lemma 2's text says "the time Voter needs to reach consensus" while its display is about `T^κ`
  for every `κ`; the display is what is formalized.

### Numerical checks

Before the proofs, the statements were checked on small cases with exact rational arithmetic:
Equation (2) for `majColour` (all configurations, `n ≤ 4`, three colours); the inequality of
Lemma 2 (all pairs of configuration vectors, `n ≤ 8`, up to four colours); `walk_drift`
(`n < 60`, every `x ≤ n`) and Equation (7) for `x ≥ 2`; `walk_expect_le` (exact walk chain,
`n ≤ 15`, `t < 3n`); the bound of `voter_reduce_whp` with the constant `24` (walk chain in
floating point, `n ≤ 40`, every `k`); and Lemma 2 itself,
`Pr[3M has ≤ κ colours at T] ≥ Pr[Voter has ≤ κ colours at T]` (exact chains on sorted
configuration vectors, `n ≤ 6`, `T ≤ 6`, every start and `κ`). Also: the sort-free `Majorizes`
agrees with the sorted partial-sum definition (all integer vectors with entries in `[−2, 3]`,
length `≤ 4`); Proposition 1 for random Schur-convex observables (`φ(x) = max {r(z) : z ⪯ x}`
for random `r`) and `p ⪰ q` obtained by transfers or by filtering random pairs (`n ≤ 5`, up to
four colours; the same test fails for random observables that are not Schur-convex);
`ac_comparison` for 3-Majority from `c` against Voter from `c' ⪯ c` (random Schur-convex `φ`,
`n ≤ 5`, three colours, `T ≤ 3`); and `⌊n^{1/4} log^{1/8} n⌋ ≤ n^{7/24}` for `44 ≤ n < 10⁶` (it
does not hold at `n = 42, 43`; Theorem 4 only needs large `n`).
