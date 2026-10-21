# Paper vs. formalization

This file compares the Lean formalization in this package with its sources. Sections 1 to 5
are about the library `Plurality`, which formalizes

> L. Becchetti, A. Clementi, E. Natale, F. Pasquale, R. Silvestri, L. Trevisan,
> **Simple Dynamics for Plurality Consensus**

There are two versions of the paper:

* **SPAA**: Proceedings of SPAA 2014, pp. 247–256. Numbering in the library `Plurality` and in
  its part of the blueprint follows this version.
* **v3**: the journal version, [arXiv:1310.2858v3](https://arxiv.org/abs/1310.2858)
  (July 2015). Its upper-bound section is rewritten with different lemmas;
  its lower-bound section adds full proofs of Theorem 4.2 and a new Section 4.4.

The formalization of Theorem 3.8 follows the SPAA proof, which needs a minor
correction (small repairs, listed below). The v3 proof was checked and is not used (see Section 2).

Sections 6 and 7 are about the multi-colour results of the library `ThreeMajority` (roadmap
MAJ-6 (b) and MAJ-12 (a)). Its two-opinion theorem `majority3_consensus_whp` follows no specific
paper (its own proof is in [latex/three_majority.tex](latex/three_majority.tex)), so it has no
section here.

## 1. Theorem 3.8: how the Lean proof differs from SPAA

| | SPAA | Lean |
| --- | --- | --- |
| Hypotheses | `3 ≤ λ < √n`, `c_m ≥ n/λ`, `s ≥ 22√(λ n log n)`, "sufficiently large `n`" | `λ ≥ 3`, same bounds on `c_m` and `s`, `log n ≥ 40`, `k ≥ 2` |
| Conclusion | consensus in `10T ≤ 100 λ log n` rounds w.p. `≥ 1 - 11T/n²` | consensus in `10T ≤ 130 λ log n` rounds w.p. `≥ 1 - 11T/n` |
| Saturation phases | `M = {m}`, `s ≥ n/3`, `n - c_m ≤ (2n/3)(17/18)^{i-1}` | `n - c_m < max((n/3)(17/18)^j, n^{1/4} log n)` |
| Growth phases | `c_m > 2n/3`, or `M = {m}`, `c_m ≥ n/λ`, `s ≥ Λ(1+1/(6λ))^{i-1}` | same, with `T₁` chosen so that `Λ(1+1/(6λ))^{T₁} > n` |
| Per-round failure in growth | `1/n²` | `1/n` (union bound over colors) |

Reasons:

1. **The saturation phases are not preserved as defined.** The SPAA sets require
   `s(c) ≥ n/3`, but Lemma 3.7 only controls `n - c_m`, so nothing shows that a
   round keeps `s(c) ≥ n/3`. The Lean sets drop that condition:
   `n - c_m < n/3` already implies that `m` is the unique plurality color with
   `s(c) ≥ n/3` (`of_dissent_lt`). The threshold uses `max` with
   `n^{1/4} log n` so that the regime of Lemma 3.7(ii) also moves the chain
   forward.
2. **A union bound is missing.** Lemma 3.5 bounds the failure against *one*
   competing color, but entering the next growth phase needs the bias to grow
   against *all* of them. Colors without nodes stay empty
   (`count_step_eq_zero`), and fewer than `n - c_m` colors have nodes, so a
   round fails with probability at most `n/n² = 1/n`. The union bound over
   `k` colors that the paper would need gives the same order when `k ≤ n`.
3. **`λ < √n` is not needed.** It only makes the hypothesis
   `s ≥ 22√(λ n log n)` satisfiable.
4. **`k ≥ 2`** is used to locate the color attaining the bias; `k = 1` is
   trivially in consensus.
5. **Lemma 3.7** has no proof in SPAA or v3. The Lean proof uses Lemma 3.6
   with `s c_m ≥ n²/9` (first regime) and `s ≥ n - 2(n - c_m)` (second
   regime), the closed-form Chernoff upper tail, and Markov's inequality.
6. **Lemma A.4** has no proof in SPAA (the journal version drops it). The
   Lean proof (`Dynamics.Kernel.nested_phases`) does not need the hypothesis
   `ε ≤ ν`.

## 2. The journal version (arXiv v3)

v3 replaces Lemmas 3.3–3.7 by three new lemmas ("from plurality to
majority", "from majority to almost all", "the last step") and proves the
theorem in three sentences, without Lemma A.4. It fixes the two issues above
in spirit (its phases switch on `c_1 ≥ 2n/3`, and its per-color failure
probability is `1/n³`), but it has its own problems, so the formalization
keeps the SPAA proof:

* **An intermediate inequality that needs a minor correction.** The proof of "from plurality to
  majority" uses `μ_1 - μ_j ≥ (c_1 - c_j)(1 + c_1/(3n))` for every `j ≠ 1`.
  This fails for colors with few nodes: for `c = (n/3 + s, n/3, n/3 - s, 0)`
  and `j = 4`, `μ_1 - μ_4 = c_1(1 + s/n - 2s²/n²)`, which is below
  `c_1(1 + 1/9)` whenever `s < n/9`. The lemma's conclusion (stated with
  `s(c)` instead of `c_1 - c_j`) is still true, because `μ` is increasing in
  `c_j` and so `μ_1 - μ_j ≥ μ_1 - μ_2`.
* **Inconsistent constants.** One constant `α` plays two roles: the Chernoff
  width that gives failure probability `1/n³`, and the constant in the bias
  hypothesis. The step `2α√(2c_1 log n)/(c_1 - c_j) ≤ √(c_1/n)/(12√λ)` needs
  the second to be `24√2` times the first. Theorem 3.8 is stated with
  `24√(2λ n log n)` while Corollaries 3.10–3.12 still use `22`.
* **Garbled steps** in "from majority to almost all" (the line ending
  `= (7/9) μ_{-1}/n` and the final `≤ (8/9) Σ μ_i`), and hypotheses such as
  `n - c_1 = ω(log n)` that are only asymptotic.

## 3. Lower bounds (Section 4)

| Paper | Lean | Difference |
| --- | --- | --- |
| Lemma 4.1 | `lemma_4_1` | stated for `c_j ≤ n/k + b` (covers every `a ≤ b` at once) |
| Theorem 4.2 | `theorem_4_2`, `theorem_4_2_log` | explicit: monochromatic at time `T` w.p. `≤ kT/n²` whenever `b(1+3/k)^T ≤ n/k`; `k ≥ 3` |
| Theorem 4.8 (a), Lemma 4.9 | `theorem_4_8_a` | proved except for rules with `Δ_r, Δ_b ≤ 1`; needs `8 ∣ n` |
| Theorem 4.8 (b), Lemma 4.10 | `theorem_4_8_b` | explicit `η = 1/20`; needs `60 ∣ n`, `log n ≥ 20` |
| Lemma 4.11 | `lemma_4_11`, `lemma_4_11_paper` | factor `1 + 2h²/k`; allows `c_j ≤ a` |
| Theorem 4.12 | `theorem_4_12`, `theorem_4_12_log` | explicit: monochromatic w.p. `≤ kT e^{-2nh⁴/k⁴}` for `T ≤ (k/(2h²)) log(4/3)`; `k ≥ 3` |

The issues found while formalizing, in both SPAA and v3 unless stated
otherwise:

* **Theorem 4.2: range of `k`.** Lemma 4.1 needs `b ≥ k√(n log n)`, so the
  thresholds must start at `b_0 = max((n/k)^{1-ε}, k√(n log n))`, and the
  number of rounds obtained is `(k/3) log(n/(k b_0))`. This is `Ω(k log n)`
  for `k ≤ n^{1/4-δ}` but degenerates as `k → (n/log n)^{1/4}`, where
  `n/k = k√(n log n)`. The formal statement is parametrized by `b`, so it
  holds for every `k`; only the `Ω(k log n)` reading needs the smaller range.
  v3's full proof also has the typo `(1 - 3/k)^T` for `(1 + 3/k)^T`, and
  chooses the thresholds `b` after seeing the trajectory; the union bound
  needs the fixed schedule `b_t = (1 + 3/k)^t b_0` used here
  (`Dynamics.expList_escape`).
* **Lemma 4.9 (clear majority): a gap.** The proof shows that the number of
  red nodes is a supermartingale, but checks `E[X_{t+1} | X_t] ≤ X_t` only when
  red is the majority. From formula (7),
  `p(r) - c_r/n = (c_r/n)(c_b/n)(x(Δ_r - 2) + y(2 - Δ_b))` with
  `x = c_r/n, y = c_b/n`. The Lean proof uses that when `Δ_r ≤ 2 ≤ Δ_b` this
  is `≤ 0` in *every* state, so no optional stopping is needed
  (`not_solver_of_drift`), and by swapping the roles of the two colors this
  covers every non-majority pair except `Δ_r, Δ_b ≤ 1`. In that case the drift
  is positive when red is the minority: the process is pulled to
  `x* = (2 - Δ_b)/(4 - Δ_r - Δ_b)`, and which color eventually wins depends on
  how it leaves that point. The paper's argument does not address this, and it
  is left open. Also `(1 - ε)n ≤ 5n/8` gives `ε ≥ 3/8`, not `5/8` (still
  `> 1/4`).
* **Lemma 4.10 (uniform property)** is a sketch in the paper: it treats
  `δ_r = 1` with `(δ_g, δ_b) ∈ {(3,2), (4,1)}` (missing `(5,0)`) and asserts
  that `r` "will not converge" by iterating a one-round estimate. The Lean
  proof covers every non-uniform triple (some color has `δ ≤ 1` because the
  three counts sum to `6`) and makes the iteration rigorous: while `r` has at
  most `2n/5` nodes its count contracts by `0.97` in expectation, a chain
  frozen above `2n/5` turns this into a contraction in every state, and
  Hoeffding's inequality bounds the probability of being frozen.
* **Lemma 4.11** states the factor `1 + h²/k` but proves `1 + 2h²/k`; Theorem
  4.12 uses the proved version. Theorem 4.12 also applies Lemma 4.11 to colors
  with fewer than `n/k` nodes, which the lemma excludes; `lemma_4_11` allows
  `c_j ≤ a` to cover them.
* **Tie-breaking in `h`-plurality** is modelled by a uniform ordering of the
  sample positions: the tied position of smallest rank wins. All tied colors
  appear equally often, so each is chosen with the same probability, as the
  paper specifies.

## 4. Two opinions from any configuration (beyond the paper)

`Plurality/AnyStart.lean` proves that binary 3-majority reaches consensus from any configuration
within `O(log n)` rounds with high probability. The source of the argument is Becchetti,
Clementi, Natale, *Consensus dynamics: an overview* (SIGACT News 2020, §4, Case 3), which
describes the symmetry breaking of Doerr, Goldberg, Minder, Sauerwald and Scheideler (SPAA 2011)
for the binary median dynamics. The formal version differs as follows.

* **The dynamics.** The survey's argument is for the binary median dynamics (equivalently
  2-Choices: a node's own opinion and two samples). Here it is carried out for 3-majority (three
  samples, with replacement, possibly the node itself). Both have the same expected next fraction
  `3x² - 2x³`, so the drift computations carry over; the `√n` jump near balance is proved directly
  for 3-majority, from the variance `n p (1 - p)` of one round.
* **Explicit constants, except one.** The survey's `γ√n` jump and constant-factor growth are
  `jump_near_balance` (gap at most `4√n/25` becomes at least `√n/5` with probability `9/64`) and
  `growth_far` (for `0 ≤ s ≤ n/2`, the next gap exceeds `11s/8 - 2λ` except with probability
  `exp(-2λ²/n)`). The final round count `C log n` has a constant `C` that is only shown to exist,
  since the hitting-time bound `Dynamics.Kernel.drift_hitting_log` gives none.
* **The observable.** The survey uses `Z = ⌊s/(γ√n)⌋` on `{0, …, q}` with `q = ⌊(n/2)/(γ√n)⌋`
  and the target `α log q`, giving a gap `Ω(√(n log n))`. The proof uses
  `X = ⌊|s|/(√n/100)⌋`, which is at most `n`, with `q = n`, constants `c₁ = 5/4`,
  `c₂ = 1/320000`, `c₃ = 9/64`, `c₄ = 1000`, `c₆ = 1`, and the target `1000 log n`, that is
  `|s| ≥ 10 √n log n`. This is more than the `22 √(3 n log n)` needed by
  `majority3_vanishing_bias`, which is the threshold stated in `majority3_symmetry_breaking`.
  The absolute value and the symmetry between the two opinions (`step_compl`) replace the
  survey's tacit choice of the majority opinion.
* **"W.h.p." made explicit.** `majority3_any_start` holds for `log n ≥ 40` with failure
  probability `C log n / n`, inherited from the `429 log n / n` of `majority3_vanishing_bias`.
  `majority3_any_start_whp` runs it twice: from every configuration each block fails with
  probability at most `ε = C₀ log n / n`, consensus absorbs, so both fail with probability at
  most `ε² ≤ 1/n`. This needs `log n ≥ C` for the same unspecified `C`.
* **Large `n`.** As for the other theorems of this package, the statements apply only to
  astronomically large `n` (`log n ≥ 40`, or `log n ≥ C`).
* **The two stages.** The survey passes from the hitting time back to its Case 2 informally.
  Here the composition is `Dynamics.Kernel.hitProb_sub_le_event`: if from every state with a
  large gap consensus holds after `T` more rounds with probability `1 - ε`, then consensus holds
  at time `t + T` with probability at least `P(gap is large by time t) - ε`. It is proved by
  induction on `t` from the recursion of the hitting probability, and uses that consensus on
  either opinion is absorbing.

## 5. Not formalized from SPAA and v3

* **Observation 3.9 (adversary).** As stated ("Theorem 3.8 still holds")
  it cannot hold literally: an adversary that recolors even one node per round
  prevents exact consensus. The introduction states the intended claim: an
  almost-stable phase where all but `O(T)` nodes agree.
* **The case `Δ_r, Δ_b ≤ 1` of Theorem 4.8 (a)**, see Section 3.
* **v3 Section 4.4** (bias `O(√(kn))` can shrink in one round with constant
  probability) is new in v3. It relies on negative association of
  balls-in-bins counts, a reverse Chernoff bound and a lower bound on
  `P(X ≥ E X)` for binomials, none of which is in the finite probability
  layer yet.

## 6. 3-Majority from any configuration (`AnyStart*`, roadmap MAJ-6 (b))

Source: Berenbrink, Clementi, Elsässer, Kling, Mallmann-Trenn and Natale, *Ignore or comply? On
breaking symmetry in consensus*, PODC 2017, cited below as BCEKMN17, with the numbering of
arXiv:1702.04921 (v1): Theorem 4 (Section 3, proof in Appendix A.7), the comparison framework of
Sections 2.1 to 2.3 (Definitions 1 and 2, Proposition 1, Theorem 2) and Lemmas 2 to 4.

**The result is unconditional; the cited Phase 2 result is formalized separately.** The second
phase of the proof of Theorem 4 applies Theorem 3.1 of Becchetti, Clementi, Natale, Pasquale,
Trevisan, *Stabilizing consensus with many opinions*, SODA 2016, arXiv:1508.06782 (restated as
Theorem 8 of BCEKMN17). That theorem is not part of BCEKMN17; it is formalized in this package
(roadmap MAJ-12 (a), [next section](#7-3-majority-with-many-opinions-manyopinions-roadmap-maj-12-a)).
The bridge theorem `threeMaj_anyStart_consensus` takes it as the explicit hypothesis
`Bcnpt16Phase2 (1/24)`, exactly as the paper's proof uses it (see difference 5 below for how the
hypothesis is stated), and `threeMaj_anyStart_consensus_unconditional` discharges that hypothesis
with `bcnpt16Phase2_of_pos`, which proves `Bcnpt16Phase2 ε` for every `ε > 0`. Everything else
(the comparison framework, Lemmas 2 to 4, Phase 1 and the assembly of the two phases) is proved
in this section's files.

### 6.1 The statements

Model (`AnyStartModel.lean`, Sections 2.1 and 2.2). `majColour c s` is the 3-Majority rule on a
sample triple `s = (s₁, s₂, s₃)`: if `s₂` and `s₃` have the same colour adopt it, otherwise
adopt the colour of `s₁`. `stepCol` and `runCol` are one round and a trajectory, on the
round type `Tgt3 n` of the two-opinion model (every agent draws an ordered triple with
replacement);
`voterStep` and `voterRun` are Voter, with rounds `Fin n → Fin n`. `colourCount c a` is the
number of agents of colour `a`, `numColours c` the number of remaining colours; consensus is
`numColours c ≤ 1`. With colours `Bool`, `stepCol` is the two-opinion `ThreeMajority.step`
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
  definition (a proposition); `bcnpt16Phase2_of_pos` proves it for every `ε > 0` (next section).
* `threeMaj_anyStart_consensus` (Theorem 4 from Phase 2, the bridge): **assuming
  `Bcnpt16Phase2 (1/24)`**, there are `C, N` such that for `n ≥ N`, from any configuration
  `Fin n → Fin n`, consensus fails after any `T ≥ C n^{3/4} log^{7/8} n` rounds with probability
  at most `2/n`.
* `threeMaj_anyStart_consensus_unconditional` (Theorem 4, `ManyOpinionsMain.lean`): the same
  conclusion without hypothesis, `threeMaj_anyStart_consensus` applied to
  `bcnpt16Phase2_of_pos`.
* `anyStart_asymptotics`: the real inequalities of Theorem 4, for the number of colours
  `phase1Colours n = ⌊n^{1/4} log^{1/8} n⌋` at which Phase 1 stops.

### 6.2 Correspondence with the paper

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
| Theorem 8 (SODA 2016, Theorem 3.1) | `Bcnpt16Phase2`, proved for every `ε > 0` by `bcnpt16Phase2_of_pos` (next section) |
| Theorem 4 | `threeMaj_anyStart_consensus_unconditional`; the bridge `threeMaj_anyStart_consensus` (from `Bcnpt16Phase2 (1/24)`) |

### 6.3 Differences in the statements

1. **Tie-breaking.** The paper adopts a uniformly random sampled colour when the three samples
   have three different colours; here the first sample's colour is adopted. The samples are
   i.i.d., so the two rules have the same law (Equation (2) holds for `majColour`, which
   `alpha3M_weight` states), and this keeps the round type `Tgt3 n` of the two-opinion model.
   With two colours the process is `ThreeMajority.step` (`stepCol_bool`). The rule `majColour` is,
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
   hypothesis (`C₂ = 4 400 250` for the one given by `bcnpt16Phase2_of_pos`, so `C = 17 601 049`
   in `threeMaj_anyStart_consensus_unconditional`), and a threshold `N` that is not explicit.
5. **The cited Phase 2 result is a hypothesis of the bridge theorem.**
   `threeMaj_anyStart_consensus` assumes `Bcnpt16Phase2 (1/24)`, the statement of Theorem 3.1 of
   the SODA 2016 paper (arXiv:1508.06782 v1, "The Adversary-Free Case") for `ε = 1/24`, with two
   explicit choices.
   (i) "W.h.p." is `≥ 1 − 1/n`, while that paper defines it as `1 − O(n^{−λ})` for some constant
   `λ > 0`: the `1/n` form follows by running the phase `⌈2/λ⌉` times in a row, since colours
   never increase, the process is Markov and the bound holds from any configuration with at most
   `k` colours; this only changes `C` and `N`. (The proof of `bcnpt16Phase2_of_pos` gives the
   `1/n` form directly.)
   (ii) "Reaches consensus within `T₀` rounds" is stated as "no consensus at any time `T ≥ T₀`"
   with probability at most `1/n`, which is the same event since consensus is absorbing.
   `bcnpt16Phase2_of_pos` (roadmap MAJ-12 (a), next section) proves this hypothesis for every
   `ε > 0` without changing it, so `threeMaj_anyStart_consensus_unconditional` has no hypothesis.
6. **Colours.** The comparison framework and Lemmas 2 to 4 are stated for any finite colour type
   `σ`. Theorem 4 and the Phase 2 hypothesis use colours `Fin n`, the paper's `[k] ⊆ [n]`.

### 6.4 Differences in the proofs

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

### 6.5 Remarks on the sources

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

### 6.6 Numerical checks

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

## 7. 3-Majority with many opinions (`ManyOpinions*`, roadmap MAJ-12 (a))

Source: Becchetti, Clementi, Natale, Pasquale and Trevisan, *Stabilizing consensus with many
opinions*, SODA 2016, cited below as BCNPT16, with the numbering of arXiv:1508.06782 (v1):
Theorem 3.1 (Section 3, "The Adversary-Free Case"), with Lemma 2.1 (Equation (1)), Lemma 3.2
(hitting time under a drift), Lemma 3.3 (symmetry breaking, Equations (3) to (6) of its proof),
Lemmas 3.4 and 3.5 (the two dropping stages, proved in Appendix B) and Lemma B.1 (the overshoot
at the hitting time). The results with an adversary (Section 4, roadmap MAJ-12 (b)) are not
formalized.

Theorem 3.1 is the Phase 2 hypothesis `Bcnpt16Phase2 ε` of the previous section:
`bcnpt16Phase2_of_pos` proves it for every `ε > 0`, without changing its definition, so
`threeMaj_anyStart_consensus_unconditional` is Theorem 4 of BCEKMN17 without hypothesis.

### 7.1 The statements

Notation: `c_a` is the support of colour `a` (`colourCount`), `j` or `k` the number of colours
(`numColours`), `C_a'` the support of `a` after one round, `m = 16 √(j n log n)`. The model is the
one of the previous section (`majColour`, `stepCol`, `runCol`): its rule is, pointwise, the rule
of BCNPT16 (Section 2: three samples uniform with repetition, the agent itself included; on
three different colours, the first sample). Lemmas 2.1 and 3.2 are general; everything else is
about configurations `Fin n → Fin n`, as in `Bcnpt16Phase2`.

One round (`ManyOpinionsExpect.lean`, Section 2).

* `numColours_eq_card_image`, `colourCount_eq_card_filter`, `stepCol_apply` (proved by `rfl`):
  the model unfolded (number of colours, support of a colour, the rule "the colour of `s₂` if
  `s₂` and `s₃` agree, otherwise that of `s₁`").
* `avg_colourCount_stepCol` (Lemma 2.1, equality):
  `𝔼[C_a'] = c_a (1 + c_a/n − ∑_b c_b²/n²)`, for any finite colour type.
* `avg_colourCount_stepCol_le` (Lemma 2.1, inequality): `𝔼[C_a'] ≤ c_a (1 + c_a/n − 1/|W|)`,
  where `|W| = numColours c` is the number of remaining colours.

Hitting times (`ManyOpinionsDrift.lean`), for any finite Markov kernel `K`.

* `hitProb_additive_drift` (Lemma 3.2, finite horizon): let `I` be invariant and `B` a target. If,
  for `x ∈ I`, `f x ≤ M`, and, for `x ∈ I` outside `B`, `f x ≤ β`, `𝔼[f(X₁) | X₀ = x] ≥ f x + λ`
  (Hypothesis 1) and `P(f(X₁) > β | X₀ = x) ≤ η` (a one-step form of Hypothesis 2), then
  `λ t P_a(T_B > t) ≤ β + M η t` for every start `a ∈ I` with `f a ≥ 0` and every `t`.
* `hitProb_mul_le_event` (hit, then absorb; not stated in the paper): if from every state of `B`
  the chain is in an absorbing event `P` after `s` steps with probability at least `q`, then from
  any state it is in `P` at time `t + s` with probability at least `q P(T_B ≤ t)`.

Symmetry breaking (`ManyOpinionsBreaking.lean`, Lemma 3.3).

* `BrokenSymmetry j x` (unfolded by `brokenSymmetry_iff`): fewer than `j` colours remain, or at
  most `j` colours remain and one of them has between `1` and `n/j − m` agents.
* `min_count_drift` (Equation (3)): there are `δ > 0` and `C` such that, for every `x` with
  `j ≥ 2` colours, `C j³ log n ≤ n` and every colour above `n/j − m` agents, the expected smallest
  support among the colours of `x` after one round is at most the current one minus
  `δ √n / (j √j)` (a colour that dies counts with support `0`).
* `min_count_overshoot` (Equation (6) and Lemma B.1, one-step form): there is `C` such that, under
  the same hypotheses, one round puts some colour of `x` below `n/j − 64 √(j n log n)` agents with
  probability at most `1/n²`.
* `symmetry_breaking` (Lemma 3.3): there is `C` such that, from every `c` with `j ≥ 2` colours and
  `C j³ log n ≤ n`, the chain hits `BrokenSymmetry j` within any `t ≥ C j² √(log n)` rounds with
  probability at least `1/2`.

Dropping (`ManyOpinionsDropping.lean`).

* `dropping_stage1` (Lemma 3.4): there is `C` such that, for `j ≥ 2` with `C j³ log n ≤ n`, from
  every `x` with at most `j` colours and every colour `a` with at most `n/j − m` agents, at every
  time `t` with `C j log n ≤ t ≤ n` colour `a` has more than `C j² log n` agents with probability
  at most `1/n`.
* `dropping_stage2` (Lemma 3.5): there is `C` such that, for `j ≥ 2` with `C j³ log n ≤ n`, from
  every `x` with at most `j` colours and every colour `a` with at most `n/(2j)` agents, colour `a`
  has died after any `t ≥ C j log n` rounds with probability at least `1/2`.

Theorem 3.1 (`ManyOpinionsMain.lean`).

* `phase_colour_dies` (proof of Theorem 3.1, first sentence): there is `C` such that, from every
  `c` with `j ≥ 2` colours and `C j³ log n ≤ n`, after any `t ≥ C (j² √(log n) + j log n)` rounds
  fewer than `j` colours remain with probability at least `1/5`.
* `consensus_of_phases` (proof of Theorem 3.1, second sentence): if from every configuration with
  `2` to `k` colours a phase of `L` rounds removes a colour with probability at least `p ≤ 1`,
  then from at most `k` colours consensus fails after `M` phases with probability at most
  `(1 − p/2)^M 2^k`.
* `consensus_many_opinions` (Theorem 3.1, strong form): there is `C` such that, from every `c` with
  `k` colours and `C k³ log n ≤ n`, consensus fails after any
  `T ≥ C (k² √(log n) + k log n)(k + log n)` rounds with probability at most `1/n`.
* `bcnpt16Phase2_of_pos` (Theorem 3.1 as stated in the paper): `Bcnpt16Phase2 ε` for every
  `ε > 0`, that is, there are `C, N` such that for `n ≥ N`, from every configuration with
  `k ≤ n^{1/3 − ε}` colours, consensus fails after any `T ≥ C (k² √(log n) + k log n)(k + log n)`
  rounds with probability at most `1/n`. `bcnpt16Phase2_iff` unfolds the definition, unchanged
  from the previous section.
* `threeMaj_anyStart_consensus_unconditional`: Theorem 4 of BCEKMN17 (previous section) without
  hypothesis.

### 7.2 Correspondence with the paper

| BCNPT16 (arXiv v1) | Lean |
| --- | --- |
| Section 2, the 3-Majority rule | `stepCol_apply` (the model of the previous section) |
| Lemma 2.1, Equation (1) | `avg_colourCount_stepCol`, `avg_colourCount_stepCol_le` |
| Lemma 3.2 | `hitProb_additive_drift` (finite horizon, difference 1) |
| Lemma 3.3 | `symmetry_breaking` (hitting form, differences 3 and 4), `BrokenSymmetry` |
| Equation (3) | `min_count_drift` |
| Equations (4), (5) | inside the proof of `min_count_drift` (Equation (4) through Paley–Zygmund, proof difference 2) |
| Equation (6), Lemma B.1 | `min_count_overshoot` (one-step form, difference 5) |
| Lemma 3.4, Equation (7) | `dropping_stage1`, `stage1_step` |
| Lemma 3.5 | `dropping_stage2` |
| Proof of Theorem 3.1, one phase | `phase_colour_dies` (probability `1/5`, difference 6), `hitProb_mul_le_event` |
| Proof of Theorem 3.1, "standard probabilistic arguments" | `consensus_of_phases` |
| Theorem 3.1 | `consensus_many_opinions` (`C k³ log n ≤ n`), `bcnpt16Phase2_of_pos` (`k ≤ n^{1/3 − ε}`) |
| Section 4 (adversaries), Theorem 1.2, Corollary 4.1 | not formalized (roadmap MAJ-12 (b)) |

### 7.3 Differences in the statements

1. **Lemma 3.2 has a finite horizon.** The paper bounds `𝔼[τ] ≤ 2 α m / λ` by optional stopping
   and then applies Markov's inequality. Expectations of unbounded hitting times are not available
   in the finite setting of the package, so `hitProb_additive_drift` bounds `P(τ > t)` directly,
   at every finite `t`. Hypothesis 2 (`P_x(Y_τ ≥ α m) ≤ α m / n`, about the hitting time) is
   replaced by a one-step overshoot bound `P(f(X₁) > β | X₀ = x) ≤ η` outside the target, which
   gives `P(f(X'_t) > β) ≤ η t` for the stopped chain by a union bound; this also replaces
   Lemma B.1.
2. **Size of `k`.** All intermediate statements and `consensus_many_opinions` assume
   `C k³ log n ≤ n` for a constant `C`, which is what the proofs use and is implied by
   `k ≤ n^{1/3 − ε}` for `n ≥ N(ε)`; `bcnpt16Phase2_of_pos` recovers the paper's form.
3. **Threshold `16 √(j n log n)`** instead of `√(j n log n)` in Lemmas 3.3 and 3.4, and the floor
   `C j² log n` of Lemma 3.4 with an explicit large `C`: the proof of Lemma 3.4 needs them (see the
   remarks on the sources). Lemma 3.3 keeps its order of magnitude, `O(j² √(log n))` rounds.
4. **Hitting form of Lemma 3.3.** The paper states that at time `t = O(j² √(log n))` some colour
   is below the threshold with probability at least `1/2`; its proof only shows that the threshold
   is hit by time `t`. `symmetry_breaking` is stated as the hitting probability, and the phase
   lemma applies Lemmas 3.4 and 3.5 at the hitting time (`hitProb_mul_le_event`, the strong Markov
   property, proved by induction on `t` without stopping times). `BrokenSymmetry` also counts the
   death of a colour (the paper's minimum is over the initial colours, so a dead colour has
   support `0`) and records "at most `j` colours", so that it is a property of the state.
5. **Equations (3) and (6) are separate statements.** Equation (3) (`min_count_drift`) is stated
   with an existential `δ > 0` and the hypothesis `C j³ log n ≤ n`. Equation (6) is stated in
   one-step form (`min_count_overshoot`): from a configuration where every colour is above
   `n/j − 16 √(j n log n)`, one round puts a colour below `n/j − 64 √(j n log n)` with
   probability at most `1/n²`; this is the overshoot hypothesis of difference 1.
6. **Phase probability `1/5`** instead of `1/4`: the paper multiplies the probabilities `1/2` of
   Lemmas 3.3 and 3.5 and ignores the failure probability `1/n` of Lemma 3.4.
7. **Time windows.** Lemma 3.4 ("within `O(j log n)` rounds, `O(j² log n)` w.h.p.") is stated at
   every time `C j log n ≤ t ≤ n`, with failure probability `1/n`; Lemma 3.5 at every
   `t ≥ C j log n` (a dead colour stays dead).
8. **"W.h.p."** is `1 − 1/n` in Theorem 3.1 (as in `Bcnpt16Phase2`) and in Lemma 3.4, and `1/n²`
   in Equation (6).
9. **Colours.** Configurations are `Fin n → Fin n`, as in `Bcnpt16Phase2` (at most `n` colours
   can be present); Lemma 2.1 is stated for any finite colour type.

### 7.4 Differences in the proofs

1. **Lemma 3.2 without optional stopping.** On the stopped chain `K.stopped B`, the drift gives
   `𝔼[f(X'_t)] ≥ f(a) + λ t P(τ > t)`, and the one-step overshoot bound gives
   `𝔼[f(X'_t)] ≤ β + M η t`.
2. **Equation (3), near-uniform case, without the Central Limit Theorem.** The paper uses the
   Central Limit Theorem and negative association to show that some colour drops by
   `Ω(√(n/j))` with probability at least `1/2`. Here, with `w = √(n/j)` and `δ = 1/500`: if the
   smallest support is at most `n/j − w/250`, Lemma 2.1 for the smallest colour gives the drift (as
   in the paper, with `c_min ≥ n/(2j)`, Equation (5)). Otherwise, each new support `C_a'` has mean
   absolute deviation at least `(9/256) σ_a` from `n/j`, where `σ_a² ≥ n/(4j)` is its variance
   (`avg_abs_colourCount_stepCol_sub_ge`, from the Paley–Zygmund bound `avg_pz_zero_one` on the
   independent adoption indicators `adoptInd`, and `sum_variance_adoptInd_ge`), and the minimum of
   numbers summing to `n` is at most `n/j − (1/(2j)) ∑_a |C_a' − n/j|` (`inf'_colourCount_le`).
   The intermediate claim with probability `1/2` is not formalized. The second and fourth moment
   bounds are those of the shared layer (`dynamics/Dynamics/Moments.lean`).
3. **Equation (6).** Every colour of `x` has mean support at least `n/j − 2m` after one round
   (`le_avg_colourCount_stepCol_of_forall_lt`: Lemma 2.1 gives `𝔼[C_a'] ≥ c_a (1 + c_a/n − M/n)`
   with `M` the largest support, which is at most `n/j + (j − 1) m`, and the right-hand side is
   increasing in `c_a` on the relevant range); the Chernoff lower tail at `n/j − 4m` and a union
   bound over the at most `n` colours give `1/n²`.
4. **Lemma 3.3** applies Lemma 3.2 to the potential `breakPotential` (`n/j` minus the smallest
   support among the `j` colours, the paper's `Y_t`), with `λ = δ √n / (j √j)`,
   `β = 64 √(j n log n)`, `M = n/j` and `η = 1/n²`, inside the invariant set "at most `j` colours".
5. **Lemma 3.4: one moving target.** The proof follows Appendix B (the gap `n/j − c_a` grows by a
   factor `1 + 1/(4j)` per round until `c_a ≤ n/(2j)`, then `c_a` shrinks by `1 − 1/(4j)` per round
   down to a floor) with a single level per round, `stage1Level`:
   `max(n/j − m (1 + 1/(4j))^s, (n/(2j)) (1 − 1/(4j))^(s − s_A), K)` with
   `K = min(240 j² log n, n/(2j))`, `s_A = ⌈5 j log n⌉` and `⌈4 j log n⌉` further rounds. Each round
   leaves its level with probability at most `1/n²` (`stage1_step`, from the Chernoff upper tail
   with the mean bound of Lemma 2.1), and a union bound over the `t ≤ n` rounds gives `1/n`.
6. **Lemma 3.5** follows the paper's sketch with the potential `ψ = min(c_a, n/(2j))`:
   `𝔼ψ' ≤ (1 − 1/(2j)) ψ + (n/(4j²)) [c_a > n/(2j)]` (`avg_min_colourCount_stepCol_le`), escape
   above `n/(2j)` with probability at most `1/n⁴` per round (Chernoff), the recursion
   `expList_min_colourCount_le`, and Markov's inequality at time `⌈2 j log n⌉`; later times by
   monotonicity, since a dead colour stays dead.
7. **Amplification.** The paper's "standard probabilistic arguments" (a constant expected number
   of phases per colour) are the potential `2^{#colours}`: each phase multiplies its expectation by
   at most `1 − p/2` (`consensus_of_phases`), and `M = 10 (k + ⌈log n⌉)` phases with `p = 1/5` give
   `(9/10)^M 2^k ≤ 1/n`.
8. **Explicit constants.** The statements are existential (`∃ C`); the proofs take `δ = 1/500`,
   `C = 1024` in `min_count_drift`, `C = 2¹⁴` in `min_count_overshoot`, `C = 240` in
   `dropping_stage1`, `C = 1024` in `dropping_stage2`, hence `C = 145 409` in
   `symmetry_breaking`, `C = 293 349` in `phase_colour_dies` and `C = 4 400 250` in
   `consensus_many_opinions` (and in `bcnpt16Phase2_of_pos`, whose threshold `N(ε)` is not
   explicit).

### 7.5 Remarks on the sources

* **The proof of Lemma 3.4 needs a minor correction.** At the threshold `c_i = n/j − √(j n log n)`
  of the statement, the one-round Chernoff bound of Appendix B (Equation (7)) only gives failure
  probability `exp(−log n / 12) = n^{−1/12}`. The gap `n/j − c_i` grows by a factor at most
  `1 + 1/(2j)` per round, so during the first `j/10` rounds each per-round bound is still at least
  `n^{−1/10}`, and the iterated union bound exceeds `1` as soon as `j ≥ 20 n^{1/10}` (which
  `j ≤ n^{1/3 − ε}` allows). The same happens at the other end of the schedule: near the floor
  `c_i = j² log n` the exponent of Equation (7) is again about `log n / 12`. With the threshold
  `16 √(j n log n)` and the floor `C j² log n` for a large `C` (`dropping_stage1` takes `C = 240`)
  each round fails with probability at most `1/n²`; Lemma 3.3 reaches the larger threshold within
  the same `O(j² √(log n))` rounds and the floor is still `O(j² log n)`, so Theorem 3.1 is
  unaffected. Numerically, on the paper's own schedule with `n = 10^15`, `j = 1000`, the sum of the
  per-round bounds is about `46` with the paper's constants and below `10^{−200}` with `16` and
  `240`. The obstacle is the per-round union bound itself, not the constant of Equation (7): with
  the exact binomial tails of one round in place of Equation (7), the sum along the paper's
  schedule is still about `0.09`, `0.31` and `0.51` for
  `(n, j) = (10^12, 100), (10^15, 1000), (10^18, 5000)`, far above `1/n`, and grows with `j`.
* **The statement of Lemma 3.3 needs a minor correction**: it needs the hypothesis
  `j³ log n = O(n)`, as in Lemmas 3.4 and 3.5. Its proof uses `ĉ_m ≥ n/(2j)` whenever
  `ĉ_m > n/j − √(j n log n)`, and when `j³ log n > n` the threshold `n/j − √(j n log n)` is
  negative, so the event `∃ i : C_i^{(t)} ≤ n/j − √(j n log n)` is empty and has probability `0`.
* **The last step of the proof of Lemma 3.3 needs a minor correction.** The bound
  `P(∀ i : C_i^{(t)} ≥ n/j − √(j n log n)) ≤ P(τ > t)` compares an event at a fixed time with the
  hitting time; the composition in Theorem 3.1 should use the strong Markov property at `τ`
  (difference 4 in the statements). Also `𝔼[τ] < j² √(log n)` should read
  `𝔼[τ] ≤ (2α/ε) j² √(log n)` (Lemma 3.2 with `m = √(j n log n)` and `λ = ε √n / j^{3/2}`).
* **The proof of Lemma B.1 needs a minor correction.** The factorization
  `P(∧_s C_𝕞^{(s)} > θ) = ∏_s P(C_𝕞^{(s)} > θ | C_𝕞^{(s−1)} > θ)` treats `C_𝕞` as a Markov chain,
  while it is a function of the configuration. The one-step overshoot bound of difference 1 avoids
  this argument.
* **The proof of Theorem 3.1 needs a minor correction**: the probability of a phase is
  `1/4 − O(1/n)` rather than `1/4` (difference 6); any positive constant suffices.

### 7.6 Numerical checks

Before the proofs, a second agent checked the pinned statements against the paper (constants,
quantifier order, every constant chosen before `n`) and numerically: the exact drift ratio
`(c_𝕞 − 𝔼 min_a C_a') j^{3/2}/√n` of Equation (3) is at least `0.7` for `j = 2` (`n ≤ 10^7`, exact
binomial), at least `1.2` for `j = 3` (exact trinomial) and at least `2.4` for `j = 5, 10, 30`
(Monte Carlo, `n = 10^8`), against `δ = 1/500`; the probability in Equation (6) is below
`10^{−300}` at the worst configurations for `j ≤ 50` and `n ∈ {10^9, 10^12, 10^15}`; for Lemma 3.5,
the chain `Z' ~ Bin(n, (Z/n)(1 + Z/n − 1/j))`, which dominates the support of a colour when at
most `j` colours remain, is dead at `t = ⌈2 j log n⌉` with probability `1.0000` (exact,
`n ≤ 3·10^4`, `j ≤ 5`); for Lemma 3.4, along the schedule of its proof with `16` and `240`, the
sum of the exact one-round binomial tails is below `10^{−290}`. The statements are not vacuous:
for `j ≥ 2` the hypothesis `C j³ log n ≤ n` holds for all large `n`, and the uniform
configuration (for Equations (3) and (6)) or a small colour (for Lemmas 3.4 and 3.5) satisfies the
remaining hypotheses.
