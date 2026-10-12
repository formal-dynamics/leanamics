# MAJ-12 (a) progress: 3-Majority with many opinions (BCNPT16, Theorem 3.1)

Source: Becchetti, Clementi, Natale, Pasquale, Trevisan, *Stabilizing consensus with many
opinions*, SODA 2016, arXiv:1508.06782 (v1), called BCNPT16 below. Numbering is that of the arXiv
PDF: Lemma 2.1 (expected support, Equation (1)); Theorem 3.1 (adversary-free case); Lemma 3.2
(hitting time under a drift); Lemma 3.3 (symmetry breaking, Equations (3) to (6)); Lemmas 3.4 and
3.5 (dropping stages 1 and 2); Lemma B.1 (overshoot at the hitting time, Equation (6)).

## Status

Phase 1 (pin the statements): **done**. `lake build ThreeMajority` succeeds; the only warnings are
four `declaration uses 'sorry'`. `PINNED.txt` (repository root) lists 19 declarations (1
definition, 18 theorems). The gate freezes each declaration up to the first line containing `:=`,
so no pinned statement contains `:=` (the kernel in `symmetry_breaking` is written with a type
ascription instead of named arguments), and the bodies of the definitions that the statements rely
on are frozen through pinned unfolding lemmas proved by `rfl`/`Iff.rfl`: `brokenSymmetry_iff`,
`bcnpt16Phase2_iff` (the existing hypothesis of MAJ-6 (b), unchanged), `numColours_eq_card_image`,
`colourCount_eq_card_filter`, `stepCol_apply`.

Proved already (no `sorry` in their own proofs; they depend on the four remaining pins):
* The five unfolding lemmas (by `rfl`/`Iff.rfl`).
* Lemma 2.1 (`avg_colourCount_stepCol`, `avg_colourCount_stepCol_le`), fully proved.
* Lemma 3.2 in finite-horizon form (`hitProb_additive_drift`), fully proved.
* Lemma 3.3 (`symmetry_breaking`) from Lemma 3.2 and Equations (3) and (6).
* The phase lemma (`phase_colour_dies`) from Lemmas 3.3, 3.4 and 3.5.
* The amplification over phases (`consensus_of_phases`), fully proved.
* Theorem 3.1 (`consensus_many_opinions`, `bcnpt16Phase2_of_pos`) from the two previous items.
* MAJ-6 (b) without hypothesis (`threeMaj_anyStart_consensus_unconditional`).

Phase 2 (prove the pins): **done**. The four remaining statements are proved (next section);
`lake build ThreeMajority` succeeds **without warnings**, and `python3 ../scripts/check_axioms.py`
reports only `propext`, `Classical.choice`, `Quot.sound` for all 28 audited declarations,
including the new `ThreeMajority.bcnpt16Phase2_of_pos`,
`ThreeMajority.threeMaj_anyStart_consensus_unconditional` and
`ThreeMajority.consensus_many_opinions` (added to `Audit.lean`). No pinned header, pinned
definition or model definition was changed (checked against the pin commit).

## Phase 2 (proofs): what was proved and how

All four are proved; no current errors, no remaining work. Constants: `min_count_drift` with
`δ = 1/500`, `C = 1024`; `min_count_overshoot` with `C = 2^14`; `dropping_stage1` with
`C = 240`; `dropping_stage2` with `C = 1024`. Below, `m = 16 √(j n log n)`, `L = log n`.

New file `ThreeMajority/ManyOpinionsTails.lean` (499 lines, imported by `ManyOpinionsBreaking.lean`,
`ManyOpinionsDropping.lean` and the root `ThreeMajority.lean`):
* scalar facts: `mul_sqrt_le_div` (`D² j³ L ≤ n ⇒ D √(j n L) ≤ n/j`), `exp_neg_nat_mul_log`,
  `log_ge_of_two_le`, `ite_exists_le_sum` (union bound, pointwise);
* deterministic facts: dead colours stay dead (`colourCount_runCol_eq_zero`); every support at
  most `n/j + (j − 1) m'` when all colours exceed `n/j − m'` (`colourCount_le_of_forall_lt`);
  `∑_b (c_b/n)² ≤ M/n` (`sum_sq_div_le`); `min_{a∈J} c_a ≤ n/|J| − (1/(2|J|)) ∑_{a∈J} |c_a − n/|J||`
  for `J ⊇ image` (`inf'_colourCount_le`);
* mean bounds: `le_avg_colourCount_stepCol` (`𝔼 C_a' ≥ c_a (1 + c_a/n − M/n)`),
  `avg_colourCount_stepCol_le_of_le` (Lemma 2.1 at a level `b ≥ c_a`),
  `le_avg_colourCount_stepCol_of_forall_lt` (`𝔼 C_a' ≥ n/j − 2m'` under the hypotheses of (6));
* one-round tails at a threshold `k` (wrappers of `Dynamics.avg_chernoff_upper/lower` with
  `adoptInd`): `avg_colourCount_stepCol_ge` (`P(C_a' ≥ k) ≤ exp(−(k − μ)²/(k + μ))`),
  `avg_colourCount_stepCol_le_tail` (`P(C_a' ≤ k) ≤ exp(−(μ − k)²/(2μ))`);
* anti-concentration: `avg_abs_colourCount_stepCol_sub_ge` (`𝔼|C_a' − θ| ≥ (9/256) σ_a` for any
  `θ`, from `avg_pz_zero_one`; if `|𝔼C_a' − θ| ≥ σ_a/4` it is Jensen), and
  `sum_variance_adoptInd_ge` (`σ_a² ≥ n/(4j)` near the uniform configuration, from
  `(1 − 1/250)²/j ≤ p_a ≤ (1/2 + 1/250)(1 + 1/250)`).

Proofs of the pins:
* `min_count_overshoot` (Equation (6)): `𝔼 C_a' ≥ n/j − 2m` for every colour `a` of `x`, Chernoff
  lower tail at `n/j − 4m` with deviation `2m` (`exp(−2m²/μ) ≤ n^{-3}`), union bound over the
  `j ≤ n` colours. (The plan's mean bound `n/j − 3m` is improved to `n/j − 2m` by monotonicity of
  `c ↦ c (1 + c/n − M/n)`.)
* `dropping_stage2` (Lemma 3.5): `avg_colourCount_stepCol_le_half` and
  `avg_colourCount_stepCol_ge_shrink` (from `c_a ≤ b ≤ n/(2j)`:
  `P(C_a' ≥ b (1 − 1/(4j))) ≤ exp(−b/(32 j²))`); escape above `n/(2j)` with probability
  `≤ 1/n⁴` per round (`expList_colourCount_gt_half_le`, via `Dynamics.expList_escape`); the
  potential `min(c_a, n/(2j))` satisfies `𝔼ψ' ≤ (1 − 1/(2j)) ψ + (n/(4j²)) 1[c_a > n/(2j)]`
  (`avg_min_colourCount_stepCol_le`), iterated in `expList_min_colourCount_le`
  (`≤ (1 − 1/(2j))^s n/(2j) + (n/(4j²)) n^{-4} s²`); Markov at `t₀ = ⌈2 j L⌉` gives
  `P(alive) ≤ 1/2`; later times by monotonicity (`expList_append`). A dead start is trivial (this
  also covers `n = 1`).
* `dropping_stage1` (Lemma 3.4): one moving target `stage1Level n j m K s_A s =
  max(n/j − m (1 + 1/(4j))^s, (n/(2j)) (1 − 1/(4j))^(s − s_A), K)` with
  `K = min(240 j² L, n/(2j)) ≥ 64 j² L` (the caution of the plan), `s_A = ⌈5 j L⌉` (then
  `m (1 + 1/(4j))^{s_A} ≥ n`, from `log q ≥ 1 − 1/q`), `s_B = ⌈4 j L⌉`. One round fails with
  probability `≤ 1/n²` (`stage1_step`): above `n/(2j)` the level is the first term and
  `avg_colourCount_stepCol_ge_gap` applies (`exp(−g²/(32 j n))`, `g ≥ m`); below `n/(2j)` the next
  level is at least `(1 − 1/(4j))` times the current one and `avg_colourCount_stepCol_ge_shrink`
  applies. After `s_A + s_B ≤ 240 j L ≤ t` rounds the level is `K ≤ 240 j² L`; the union bound
  over the `t ≤ n` rounds gives `t/n² ≤ 1/n`.
* `min_count_drift` (Equation (3)): with `w = √n/√j`, the target drift is `(1/500) w/j`. Case
  `c_min ≤ n/j − w/250`: Lemma 2.1 for the smallest colour and `c_min ≥ n/(2j)` (Equation (5)).
  Case `c_min > n/j − w/250`: `inf'_colourCount_le` pointwise, `avg_abs_colourCount_stepCol_sub_ge`
  with `σ_a ≥ w/2` (`sum_variance_adoptInd_ge` with `u = w/(250 n)`, `j u ≤ 1/250` since
  `w ≤ n/j`): `𝔼 min ≤ n/j − 9w/1024 < c_min + w/250 − 9w/1024 ≤ c_min − w/1000`.

Deviations from the task plan (all inside proofs, none in statements): per-round failure
probabilities `1/n²` (stage 1) and `1/n⁴` (stage 2 escape) instead of `n^{-5}`, `n^{-10}`;
variance bound `n/(4j)` instead of `0.48 n/j`; constants as listed above.

Final line counts: `ManyOpinionsTails.lean` 499 (new), `ManyOpinionsBreaking.lean` 536 (was 332),
`ManyOpinionsDropping.lean` 730 (was 59).

## Review of the pins (second agent, before freezing)

* The 19 pinned statements were checked against the paper (statements, constants, quantifier
  order with every constant before `n`) and against the elaborated Lean terms (all divisions
  `n / j`, `n / (2 * j)`, `1 / n` are real divisions; `j ^ 2`, `j ^ 3` are real powers). No
  change to the Lean files was needed.
* The four `sorry` statements are true for a large enough constant (re-derived along the plan
  below) and are not vacuous: for `j ≥ 2` the hypothesis `C j³ log n ≤ n` holds for all large `n`,
  and the uniform configuration (for Equations (3) and (6)) or a small colour (for Lemmas 3.4 and
  3.5) satisfies the remaining hypotheses. Numerical checks: the exact drift ratio
  `(c_m − 𝔼 min_a C_a') j^{3/2}/√n` of Equation (3) is at least `0.7` for `j = 2`
  (`n ≤ 10^7`, exact binomial) and `1.2` for `j = 3` (exact trinomial), and at least `2.4` for
  `j = 5, 10, 30` (Monte Carlo, `n = 10^8`), against `δ = 1/500`; the probability in
  Equation (6) is below `10^{-300}` at the worst configurations for `j ≤ 50`,
  `n ∈ {10^9, 10^12, 10^15}`; for Lemma 3.5 the chain `Z' ~ Bin(n, (Z/n)(1 + Z/n − 1/j))`, which
  dominates the support of a colour when at most `j` colours remain, is dead at `t = ⌈2 j log n⌉`
  with probability `1.0000` (exact, `n ≤ 3·10^4`, `j ≤ 5`); for Lemma 3.4, along the schedule
  of its proof (see the corrections below) with `16` and `240` the sum of the exact one-round
  binomial tails is below `10^{-290}`.
* The proved composition really uses the four lemmas (`symmetry_breaking` uses Equations (3) and
  (6) through `hitProb_additive_drift`; `phase_colour_dies` uses Lemmas 3.3, 3.4, 3.5); the proved
  declarations use only `propext`, `Classical.choice`, `Quot.sound` besides the four `sorry`s.
* A frozen semantic check outside the repository verifies the elaborated pinned statements and
  the bodies of `BrokenSymmetry` and of the model definitions (`Tgt3`, `avg`, `expList`,
  `majColour`, `stepCol`, `runCol`, `colourCount`, `numColours`, `Bcnpt16Phase2`): do not change
  them, and do not add `variable`/`include` lines that change a pinned statement.

## Pinned statements (namespace `ThreeMajority`)

`ThreeMajority/ManyOpinionsExpect.lean` (one round):
* `numColours_eq_card_image`, `colourCount_eq_card_filter`, `stepCol_apply` (proved by `rfl`): the
  model of `AnyStartModel.lean` unfolded (number of colours, support of a colour, the update rule
  "second and third samples if they agree, else the first").
* `avg_colourCount_stepCol` (Lemma 2.1, equality): `𝔼[C_a'] = c_a (1 + c_a/n − ∑_b c_b²/n²)`,
  any finite colour type.
* `avg_colourCount_stepCol_le` (Lemma 2.1, inequality): `𝔼[C_a'] ≤ c_a (1 + c_a/n − 1/|W|)`,
  `|W| = numColours c`.

`ThreeMajority/ManyOpinionsDrift.lean` (generic finite Markov kernels):
* `hitProb_additive_drift` (Lemma 3.2, finite horizon): inside an invariant set `I` and outside
  the target `B`, if `f ≤ M`, `f ≤ β`, `𝔼[f(X₁)] ≥ f + λ` and `P(f(X₁) > β) ≤ η`, then
  `λ t P_a(T_B > t) ≤ β + M η t` for every start `a ∈ I` with `f a ≥ 0`.

`ThreeMajority/ManyOpinionsBreaking.lean` (symmetry breaking):
* def `BrokenSymmetry j x`: fewer than `j` colours, or at most `j` colours one of which has
  between `1` and `n/j − 16 √(j n log n)` agents; `brokenSymmetry_iff` unfolds it (`Iff.rfl`).
* `min_count_drift` (Equation (3)): `∃ δ > 0, C` such that for `j = numColours x ≥ 2`,
  `C j³ log n ≤ n` and every colour above `n/j − 16 √(j n log n)` agents, the expected smallest
  support among the colours of `x` after one round is at most the current one minus
  `δ √n / (j √j)`.
* `min_count_overshoot` (Equation (6), Lemma B.1, one-step form): under the same hypotheses, one
  round puts some colour of `x` below `n/j − 64 √(j n log n)` agents with probability at most
  `1/n²`.
* `symmetry_breaking` (Lemma 3.3): `∃ C`, from `c` with `j ≥ 2` colours and `C j³ log n ≤ n`,
  `P(T_{BrokenSymmetry j} ≤ t) ≥ 1/2` for every `t ≥ C j² √(log n)` (hitting probability of the
  round-based kernel `Kernel.ofStep stepCol`).

`ThreeMajority/ManyOpinionsDropping.lean` (dropping):
* `dropping_stage1` (Lemma 3.4): `∃ C`, for `j ≥ 2`, `C j³ log n ≤ n`, at most `j` colours and
  colour `a` with at most `n/j − 16 √(j n log n)` agents, at every time `C j log n ≤ t ≤ n` colour
  `a` has more than `C j² log n` agents with probability at most `1/n`.
* `dropping_stage2` (Lemma 3.5): `∃ C`, for `j ≥ 2`, `C j³ log n ≤ n`, at most `j` colours and
  colour `a` with at most `n/(2j)` agents, colour `a` is dead after any `t ≥ C j log n` rounds
  with probability at least `1/2`.

`ThreeMajority/ManyOpinionsMain.lean` (Theorem 3.1):
* `phase_colour_dies` (proof of Theorem 3.1, first sentence): `∃ C`, from `j ≥ 2` colours with
  `C j³ log n ≤ n`, after any `t ≥ C (j² √(log n) + j log n)` rounds fewer than `j` colours
  remain with probability at least `1/5`.
* `consensus_of_phases` (proof of Theorem 3.1, second sentence): if every phase of `L` rounds
  removes a colour with probability `≥ p` (`p ≤ 1`) from every configuration with `2` to `k`
  colours, consensus fails after `M` phases with probability `≤ (1 − p/2)^M 2^k`.
* `consensus_many_opinions` (Theorem 3.1, strong form): `∃ C`, from `c` with `k` colours and
  `C k³ log n ≤ n`, consensus fails after any `T ≥ C (k² √(log n) + k log n)(k + log n)` rounds
  with probability at most `1/n`.
* `bcnpt16Phase2_iff` (`Iff.rfl`): the existing definition `Bcnpt16Phase2 ε` unfolded.
* `bcnpt16Phase2_of_pos` (Theorem 3.1 as stated in the paper; **headline 1**): for every
  `ε > 0`, `Bcnpt16Phase2 ε`, the hypothesis of `threeMaj_anyStart_consensus`, unchanged.
* `threeMaj_anyStart_consensus_unconditional` (**headline 2**): Theorem 4 of BCEKMN17 (MAJ-6 (b))
  without hypothesis: consensus within `C n^{3/4} log^{7/8} n` rounds w.p. `≥ 1 − 2/n`.

Unpinned proved infrastructure: `adoptInd` and its lemmas (the support after one round is a sum of
independent `{0,1}` coordinates), trajectory facts (`image_runCol_subset`, `numColours_runCol_le`,
`numColours_runCol_lt_of_dead`, `event_ofStep_stepCol`, `prob_ofStep_numColours_lt`),
`hitProb_mul_le_event` (hit, then absorb), `ManyOpinionsMoments.lean` (second and fourth moments
and Paley–Zygmund, copied from `plurality/` since packages do not depend on each other), the
potential `breakPotential` of Lemma 3.3.

## Deviations from the source

1. **Finite horizon** (Lemma 3.2). The paper bounds `𝔼[τ] ≤ 2 α m / λ` by optional stopping and
   then applies Markov's inequality; expectations of unbounded hitting times are not available in
   the finite setting, so `hitProb_additive_drift` bounds `P(τ > t)` directly (same proof, on the
   stopped chain `K.stopped B`). Its Hypothesis 2 is replaced by a one-step overshoot bound
   `P(f(X₁) > β | X₀ = x) ≤ η` off the target, which gives `P(f(X'_t) > β) ≤ η t` by a union
   bound; this also replaces Lemma B.1.
2. **Size of `k`.** All intermediate statements and `consensus_many_opinions` assume
   `C k³ log n ≤ n` for a constant `C`, which is what the proofs use and is implied by
   `k ≤ n^{1/3 − ε}` for `n ≥ N(ε)`; `bcnpt16Phase2_of_pos` recovers the paper's form.
3. **Threshold `16 √(j n log n)`** instead of `√(j n log n)` in Lemmas 3.3 and 3.4 (see the
   corrections below). Lemma 3.3 is unchanged in order of magnitude (`O(j² √(log n))`).
4. **Hitting form of Lemma 3.3.** The paper states that at time `t = 2 j² √(log n)` some colour is
   below the threshold with probability `≥ 1/2`; its proof only shows that the threshold is hit
   by time `t`. `symmetry_breaking` is stated as the hitting probability, and the phase lemma
   applies Lemmas 3.4 and 3.5 at the hitting time (`hitProb_mul_le_event`, the strong Markov
   property, proved by induction without stopping times). `BrokenSymmetry` also counts the
   death of a colour (the paper's minimum is over the initial colours, so a dead colour has
   support `0`) and records "at most `j` colours" so that it is a property of the state.
5. **Equation (3), near-uniform case.** The paper uses the Central Limit Theorem and negative
   association to claim `P(∃ i : C_i' ≤ n/j − 6ε √(n/j)) ≥ 1/2`. The plan proves Equation (3)
   instead from Paley–Zygmund (`avg_pz_zero_one`): each support has mean absolute deviation from
   `n/j` at least `(9/256) σ`, `σ² ≈ n/j`, and the minimum of `j` numbers summing to `n` is at
   most `n/j − (1/(2j)) ∑ |C_i − n/j|`. The intermediate claim with `1/2` is not formalized.
6. **Phase probability `1/5`** instead of `1/4` (the paper multiplies the probabilities `1/2` of
   Lemmas 3.3 and 3.5 and ignores the failure probability `1/n` of Lemma 3.4).
7. **Time windows.** Lemma 3.4 ("within `O(j log n)` rounds, `O(j² log n)` w.h.p.") is stated at
   every time `C j log n ≤ t ≤ n` with failure probability `1/n`; Lemma 3.5 for every
   `t ≥ C j log n` (a dead colour stays dead).
8. **"w.h.p."** is `1 − 1/n` in Theorem 3.1 (as in `Bcnpt16Phase2`) and in Lemma 3.4, `1/n²` in
   Equation (6).
9. **Amplification.** The paper's "standard probabilistic arguments" (a constant amortized number
   of phases per colour) are the potential `2^{#colours}`: each phase multiplies its expectation
   by at most `1 − p/2`, and `M = 10 (k + ⌈log n⌉)` phases give `(9/10)^M 2^k ≤ 1/n`.
10. **Colours.** Configurations are `Fin n → Fin n`, as in `Bcnpt16Phase2` (at most `n` colours are
   valid); Lemma 2.1 is stated for any finite colour type. The update rule `majColour` (second and
   third samples if they agree, else the first) is the paper's rule.

## Corrections needed in the source (all minor)

* **Proof of Lemma 3.4.** At the threshold `c_i = n/j − √(j n log n)` the one-round Chernoff bound
  of Appendix B (Equation (7)) only gives failure probability `exp(−log n / 12) = n^{-1/12}`. The
  gap `n/j − c_i` grows by a factor at most `1 + 1/(2j)` per round, so during the first `j/10`
  rounds each per-round bound is still at least `n^{-1/10}`, and the iterated union bound exceeds
  `1` as soon as `j ≥ 20 n^{1/10}` (allowed by `j ≤ n^{1/3 − ε}`). The same happens at the other
  end of the schedule: near the floor `c_i = j² log n` the exponent of Equation (7) is about
  `log n / 12` again. With the threshold `16 √(j n log n)` and the floor `C j² log n` for a large
  `C` (`dropping_stage1`, `C = 240` suffices) the failure is at most `n^{-5}` per round; Lemma 3.3
  reaches the larger threshold within the same `O(j² √(log n))` rounds, and the floor is still
  `O(j² log n)`. (Checked numerically on the paper's own schedule: for `n = 10^15`, `j = 1000` the
  sum of the per-round bounds is about `46` with the paper's constants and below `10^{-200}` with
  `16` and `240`. The obstacle is the per-round union bound itself, not the constant of
  Equation (7): with the exact binomial tails of one round in place of Equation (7), the sum along
  the paper's schedule is still about `0.09`, `0.31`, `0.51` for
  `(n, j) = (10^12, 100), (10^15, 1000), (10^18, 5000)`, far above `1/n`, and grows with `j`.)
* **Proof of Lemma 3.3, last step.** The bound `P(∀ i : C_i^{(t)} ≥ n/j − √(j n log n)) ≤ P(τ > t)`
  compares a fixed-time event with the hitting time; the composition in Theorem 3.1 should use
  the strong Markov property at `τ` (deviation 4). Also `𝔼[τ] < j² √(log n)` should read
  `𝔼[τ] ≤ (2α/ε) j² √(log n)` (Lemma 3.2 with `m = √(j n log n)`, `λ = ε √n / j^{3/2}`).
* **Lemma 3.3 needs `j³ log n = O(n)`**: its proof uses `ĉ_m ≥ n/(2j)` whenever
  `ĉ_m > n/j − √(j n log n)`; the statement has no hypothesis on `j`. The statement itself needs
  the hypothesis too (a minor correction, as in Lemmas 3.4 and 3.5): when `j³ log n > n` the
  threshold `n/j − √(j n log n)` is negative, so the event `∃ i : C_i^{(t)} ≤ n/j − √(j n log n)`
  is empty and has probability `0`.
* **Proof of Lemma B.1.** The factorization
  `P(∧_s C_𝕞^{(s)} > θ) = ∏_s P(C_𝕞^{(s)} > θ | C_𝕞^{(s−1)} > θ)` treats `C_𝕞` as a Markov chain,
  while it is a function of the configuration. The one-step overshoot bound of deviation 1 avoids
  this argument.
* **Proof of Theorem 3.1**: the phase probability is `1/4 − O(1/n)` rather than `1/4`
  (deviation 6); any positive constant suffices.

## Files

`ThreeMajority/ManyOpinionsExpect.lean`, `ManyOpinionsMoments.lean`, `ManyOpinionsDrift.lean`,
`ManyOpinionsBreaking.lean`, `ManyOpinionsDropping.lean`, `ManyOpinionsMain.lean`, imported from
`ThreeMajority.lean`.

## Plan for the four remaining lemmas (as given before Phase 2; carried out above)

1. `min_count_overshoot`: for each colour `a` of `x`, the mean `n p_a` is at least
   `n/j − 3 · 16 √(j n log n)` (deviations `d_b = c_b − n/j > −m` sum to `0`, so
   `∑ d_b² ≤ 2 j² m²`), then the multiplicative Chernoff lower tail (`avg_chernoff_lower_mul`)
   with deviation `m`, failure `exp(−m²/(2n)) = n^{-128 j}`, and a union bound over the colours.
2. `dropping_stage2`: one-round escape above `n/(2j)` has probability `≤ exp(−n/(24 j³))` (Chernoff
   upper tail, `avg_chernoff_upper`); the expectation of `min(C_a, n/(2j))` contracts by
   `1 − 1/(2j)` per round up to the escape probability (`expList_escape`); Markov at time
   `⌈2 j log n⌉ + 1`; a dead colour stays dead.
3. `dropping_stage1`: moving target (`expList_escape`) in three blocks: the gap `n/j − C_a` grows
   by `1 + 1/(4j)` per round until `C_a ≤ n/(2j)` (`≤ 5 j log n` rounds), then `C_a` shrinks by
   `1 − 1/(4j)` until the floor `K' = min(C j² log n, n/(2j))` (`≤ 4 j log n` rounds), then stays
   below it (the hypothesis `C j³ log n ≤ n` only gives `C j² log n ≤ n/j`, hence the `min`;
   `K' ≤ C j² log n` suffices); each round fails with
   probability `≤ n^{-5}` (Chernoff upper tail with mean bound `φ(h) = h (1 + h/n − 1/j)`,
   increasing in `h`).
4. `min_count_drift`: two cases. Far from uniform (`c_𝕞 ≤ n/j − κ √(n/j)`, `κ = 1/250`), Lemma 2.1
   for the minimizing colour. Near uniform, the pointwise bound
   `min_a C_a' ≤ n/j − (1/(2j)) ∑_a |C_a' − n/j|` and the anti-concentration
   `𝔼|C_a' − n/j| ≥ (9/256) σ_a` with `σ_a² = n p_a (1 − p_a) ≥ 0.48 n/j` (Paley–Zygmund,
   `avg_pz_zero_one`). `δ = 1/500` works.
