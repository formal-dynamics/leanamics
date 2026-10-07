# Concentration and probability audit (PROGRESS file)

Job: remove the duplicated concentration, tail, indicator and probability-monotonicity lemmas
across the Leanamics packages (follow-up of `dynamics/EXPECTATION_AUDIT.md`, sections 3, 4 and 6
of its audit). This file is both the audit report and the PROGRESS file of the job.

## Status

* **Phase 1 (pin the statements): done** (commit `0992685`). 19 new general statements in
  `dynamics/Dynamics/Tail.lean` (new) and `dynamics/Dynamics/Concentration.lean`;
  `PINNED.txt` (83 lines) freezes them with `avg_hoeffding`, `avg_bernstein`, `variance` and
  the main theorems of `median/`, `plurality/`, `3-majority/`.
* **Phase 2 (prove, switch the packages, delete the copies): done.** No `sorry` remains; the
  four required builds are warning-free; all 83 pinned declarations depend only on
  `propext`, `Classical.choice`, `Quot.sound` (some on a subset); the pinned text is unchanged.
  Scope change in phase 2: only `dynamics/`, `median/`, `plurality/`, `3-majority/` may be
  edited, so the copies in `moran/`, `voter/`, `undecided/` remain (see Remaining).

### Pinned

`PINNED.txt`, one line per declaration, `<path> <name as written after the keyword>`.

**New general statements, `dynamics/Dynamics/Tail.lean`** (all `sorry`):

| Declaration | Statement | Replaces |
| --- | --- | --- |
| `Distribution.prob_mono` | `(∀ ⦃a⦄, s a → t a) → p.prob s ≤ p.prob t` | `Plurality.prob_mono_set`, `Median.prob_mono_set'` |
| `Distribution.expect_lt_one` | `f ≤ 1`, `0 < p.weight b`, `f b < 1` ⟹ `p.expect f < 1` | `Moran.expect_lt_one`, `Voter.expect_lt_one` |
| `avg_lt_one` | `[Nonempty α]`, `f ≤ 1`, `f b < 1` ⟹ `avg f < 1` | `Undecided.avg_lt_one`, private `Median.avg_lt_one` |
| `avg_markov` | `X ≥ 0`, `c > 0` ⟹ `P(c ≤ X) ≤ avg X / c` | (general Markov; the next line is its corollary) |
| `avg_markov_one` | `Yᵢ ≥ 0` ⟹ `P(1 ≤ ∑ᵢ Yᵢ(ωᵢ)) ≤ ∑ᵢ avg Yᵢ` | `Plurality.markov_one`; inline in `Median.falses_tail_markov`, `ThreeMajority.saturation_stage2c` |
| `Kernel.one_sub_avg_le_prob_ofStep` | `bad ≥ 0`, `¬P (step s r) → 1 ≤ bad r` ⟹ `1 - avg bad ≤ (ofStep step s).prob P` | `Median.prob_step_ge`, `Plurality.le_prob_step` |
| `Kernel.iterate_monotone` | `f ≤ K.apply f` ⟹ `Monotone (n ↦ K.iterate n f a)` | inductions in `Moran.fixation_mono`, `Voter.colorProbability_mono`, `Median.event_absorb_mono` |
| `Kernel.event_monotone` | `P a → (K a).prob P = 1` ⟹ `Monotone (n ↦ K.event P n a)` | `Median.event_absorb_mono` |
| `exp_neg_two_log` | `1 ≤ n` ⟹ `exp (-(2 log n)) = 1 / n²` | `Plurality.exp_neg_two_log`, `Median.exp_neg_two_log` |
| `one_le_of_log_pos` | `0 < log n` ⟹ `1 ≤ n` | `Plurality.one_le_of_log_pos`, `Median.one_le_of_log_pos` |

**New general statements, `dynamics/Dynamics/Concentration.lean`** (all `sorry`; sums
`X = ∑ᵢ Yᵢ(ωᵢ)` over uniform `ω : Fin n → γ`, coordinates `{0,1}`-valued unless said):

| Declaration | Statement | Replaces |
| --- | --- | --- |
| `avg_lower_tail_le_of_mgf` | `t ≤ 0` ⟹ `P(X ≤ k) ≤ avg (exp (t X)) · exp (-(t k))` (any `X`) | inline in `ThreeMajority.avg_tail_le` |
| `avg_hoeffding_lower` | `[Nonempty γ]`, `λ ≥ 0` ⟹ `P(X + λ ≤ 𝔼X) ≤ exp(-2λ²/n)` | `Median.avg_hoeffding_lower` |
| `variance_le_avg_of_zero_one` | `f ∈ {0,1}` ⟹ `variance f ≤ avg f` | `Median.variance_fcoord_le` |
| `avg_chernoff_mgf` | `avg (exp (t X)) ≤ exp (μ (eᵗ - 1))`, every real `t` | `ThreeMajority.avg_exp_le` |
| `avg_chernoff_upper` | `t ≥ 0` ⟹ `P(k ≤ X) ≤ exp (μ (eᵗ - 1) - t k)` | `ThreeMajority.avg_tail_ge` |
| `avg_chernoff_lower` | `t ≤ 0` ⟹ `P(X ≤ k) ≤ exp (μ (eᵗ - 1) - t k)` | `ThreeMajority.avg_tail_le` |
| `avg_chernoff_upper_log` | `𝔼X ≤ μ`, `0 < μ ≤ k` ⟹ `P(k ≤ X) ≤ exp (k - μ - k log (k/μ))` | `ThreeMajority.avg_tail_ge_log_le`, `ThreeMajority.avg_tail_ge_log` |
| `avg_chernoff_lower_log` | `μ ≤ 𝔼X`, `0 < k ≤ μ` ⟹ `P(X ≤ k) ≤ exp (k - μ - k log (k/μ))` | `ThreeMajority.avg_tail_le_log_ge`, `ThreeMajority.avg_tail_le_log` |
| `avg_chernoff_lower_mul` | `0 ≤ δ < 1` ⟹ `P(X ≤ (1-δ)𝔼X) ≤ exp (-(δ² 𝔼X / 2))` | `Plurality.chernoff_lower` |

(`μ` above is `∑ᵢ avg Yᵢ = 𝔼X` in the first three Chernoff lines.)

**Existing declarations frozen in place** (`Concentration.lean`, edited by phase 2):
`avg_hoeffding`, `avg_bernstein` (dynamics blueprint `thm:concentration`, used by median and
plurality) and the definition `variance` that two pinned statements mention. No new definition
was needed.

**Main theorems frozen** (selection rule of the previous job: README names, `Audit.lean`, and
the `\lean{}` names of blueprint `theorem`/`corollary` environments):

* `median/`: `med3_monotone`, `threshold_step`, `threshold_run`, `step_mem`, `step_mem_Icc`,
  `step_of_consensus`, `expected_ones`, `absorbed` (`Median/Basic.lean`), `binary_consensus`
  (`Median/BinaryAssembly.lean`), `consensus_whp` (`Median/Binary.lean`).
* `3-majority/`: `majority3_consensus_whp`, `majority3_consensus_fail_le`,
  `majority3_consensus_fail_le_clean`, `hfloor4_of_hbig` (`ThreeMajority/Main.lean`).
* `plurality/`: the 47 lines of the previous job, unchanged (every theorem of `Audit.lean`,
  every name of the README status table, every `\lean{}` name of the blueprint's
  theorem/corollary environments, including the definitions `ofSet`, `lamK`, `balancedSet`,
  `extinctRounds`, `hBalancedSet`).

A script checked that each of the 83 lines names exactly one declaration of its file.

### Proved (phase 2)

**`dynamics/`** (`Tail.lean` 180 lines, `Concentration.lean` 360 → 579 lines):

* `Tail.lean`, each proof 3-12 lines: `prob_mono` (pointwise indicator comparison under
  `expect_mono`), `expect_lt_one` (`sum_lt_sum`), `avg_lt_one` (`sum_lt_sum` and
  `div_lt_div_iff_of_pos_right`), `avg_markov` (`1[c ≤ X] ≤ X/c`), `avg_markov_one`
  (pointwise `1[1 ≤ ∑] ≤ ∑`, `avg_sum`, `avg_eval`; empty `γ` by `simp [avg]`),
  `one_sub_avg_le_prob_ofStep` (`prob_ofStep`, `avg_le_avg`), `iterate_monotone` (mirror of
  `iterate_antitone`), `event_monotone` (`iterate_monotone` with `f = 1[P]`; `prob` and
  `event` share the classical decision, so `habs` applies definitionally),
  `exp_neg_two_log`, `one_le_of_log_pos`.
* `Concentration.lean`: `avg_lower_tail_le_of_mgf` (mirror of `avg_tail_le_of_mgf`),
  `avg_hoeffding_lower` (Hoeffding for `1 - Yᵢ`), `variance_le_avg_of_zero_one`
  (`variance_le_avg_sq`, `f² = f`), `avg_chernoff_mgf` (through the existing `avg_exp_sum`,
  so the MGF factorization is no longer re-proved), `avg_chernoff_upper`/`lower` (two
  4-line `calc`s through `avg_tail_le_of_mgf`/`avg_lower_tail_le_of_mgf`), the closed forms
  (`t = log (k/μ)`, 8 lines each), `avg_chernoff_lower_mul` (closed lower form at
  `k = (1-δ)μ`; degenerate cases `δ = 0`, `μ = 0` by the new helper `avg_ite_le_one`).
  Unpinned helpers: `avg_ite_le_one` (an indicator average is at most `1`, also on an empty
  type) and the scalar `half_sub_inv_le_log`, `one_sub_mul_log_one_sub_ge` (moved from
  `plurality/Plurality/Tail.lean`, not duplicated).
* Pre-existing over-long line in `Absorption.lean` wrapped.

**`median/`** (`Median/*.lean`: 2788 → 1806 lines): `Median/BinaryPhases.lean` (dead, 771 lines) deleted.
`BinaryMoves.lean` lost `exp_ge_pow'` (→ `Real.pow_div_factorial_le_exp`),
`sub_one_div_le_log'` (`log_five_fourth_ge`/`log_eight_seventh_ge` now use
`Real.one_sub_inv_le_log_of_pos`), `exp_neg_two_log`, `one_le_of_log_pos`, `prob_mono_set'`,
`prob_step_ge` (call sites: `Kernel.one_sub_avg_le_prob_ofStep step _ x _ h0 h1`),
`event_absorb_mono` (66 lines; `BinaryAssembly` uses `Kernel.event_monotone`);
`BinaryAux.lean` lost `avg_hoeffding_lower` and `variance_fcoord_le`, and
`falses_tail_markov` is now 2 lines (`avg_markov_one`); the private `Median.avg_lt_one`
(`Basic.lean`, 31 lines) is replaced by `Dynamics.avg_lt_one`. `Median/Defs.lean` imports
`Dynamics.Tail`.

**`3-majority/`**: `ThreeMajority/Chernoff.lean` (229 lines) deleted; `Growth.lean` and
`Saturation.lean` call `Dynamics.avg_chernoff_lower_log`/`avg_chernoff_upper_log` directly
(`ThreeMajority.avg` is reducible, so the statements apply as they are);
`saturation_stage2c` uses `Dynamics.avg_markov_one` (its inline Markov step and a needless
`Nonempty` instance are gone); `exp_ge_pow` deleted (→ `Real.pow_div_factorial_le_exp` in
`Bounds`, `Main`, `Saturation`, plurality `Numerics`). Blueprint tags `lem:mgf`,
`lem:chernoff`, `lem:chernofflog`, `lem:exppow` point to the Dynamics/Mathlib names;
README, CLAUDE.md, the blueprint's file map and `latex/three_majority.tex` updated.

**`plurality/`**: `Plurality/Tail.lean` (117 lines) deleted (`chernoff_lower`, `markov_one`,
`threeMajority_avg_eq`; its two scalar helpers moved to `Concentration.lean`);
`Growth.lean` lost `exp_neg_two_log`, `Saturation.lean` lost `one_le_of_log_pos`,
`Upper.lean` lost `prob_mono_set` and `le_prob_step`. Call sites use
`avg_chernoff_lower_mul`, `avg_chernoff_upper_log` (no more `threeMajority_avg_eq` rewrites),
`avg_markov_one`, `Distribution.prob_mono`, and `Kernel.one_sub_avg_le_prob_ofStep step ...`.
Blueprint `lem:tails` retagged; README layout table and dependency paragraph updated.

**Documentation in `dynamics/`**: README module table (new `Tail` row, `Concentration`
row), blueprint (`thm:chernoff`, `lem:tail`), `Audit.lean` (`#print axioms` for the 19 new
declarations).

Net Lean change since phase 1: +313 / −1498 lines (771 of them the dead file).

### Remaining

Nothing inside the four editable packages. Outside them (not editable in this job):

1. `moran/`, `voter/`, `undecided/` still prove their own copies: `Moran.expect_lt_one`,
   `Voter.expect_lt_one` (→ `Distribution.expect_lt_one`, same statement),
   `Undecided.avg_lt_one` (→ `avg_lt_one`, same statement), and the inductions inside
   `Moran.fixation_mono` and `Voter.colorProbability_mono` (→ one-line corollaries of
   `Kernel.iterate_monotone`; both names are blueprint-tagged, so keep them);
   optionally `Moran.fixation_le_one`, `Voter.colorProbability_le_one` → `Kernel.iterate_le_one`.
   Since Lean resolves the packages' own names first, deleting each copy retargets its call
   sites with no other change.
2. `PROVENANCE.md` (root): record this refactor if desired; root `README.md` might mention
   that median, plurality and 3-majority take their concentration bounds from `dynamics/`.
3. Optional, by scope (Deviation 9): `Moran.map_weight_pos`, `Plurality.avg_prod_iter`,
   `Plurality.avg_eval_two`, `Plurality.ite_one_zero_nonneg`.

### Errors

* Phase 1: none.
* Phase 2 (all fixed): (1) `Real.pow_div_factorial_le_exp` takes `x` explicitly
  (`variable (x y : ℝ)` in Mathlib), so the first median build failed until the calls became
  `Real.pow_div_factorial_le_exp _ hx k`. (2) `BinaryAssembly.lean` still named
  `prob_mono_set'` (my replacement had covered `BinaryMoves.lean` only); the job was
  interrupted by a usage limit at that point and resumed. (3) A scripted deletion of an
  indented line in plurality `Saturation.lean` left two spaces and broke the indentation
  (parse error), fixed. (4) In plurality `Upper.lean`, passing `stepWith maj3` as the round
  function made the goals mention `stepWith maj3 x r` while the hypotheses mention
  `step x r`; `linarith` treats these as different atoms (`step` is not reducible). Passing
  `Plurality.step` itself fixed it. (5) A linter note on a redundant `<;>` in my new median
  line, fixed (`<;> simp [h]`).

### Verification (final state)

Scratch files and the local gate are in `/tmp/concgate/` (outside the repository).

* `lake build Dynamics`, `lake build Median`, `lake build ThreeMajority`,
  `lake build Plurality` (run one after the other): all `Build completed successfully`,
  0 `warning`/`error` lines. Plurality prints its four pre-existing `info:` lines
  `Error in Linarith.normalizeDenominatorsLHS` (`Upper.lean`, `info` severity from Mathlib's
  `linarith` preprocessing, unrelated to this job).
* `#print axioms` on all 83 pinned declarations (median from `median/`, the rest from
  `plurality/`, whose environment contains dynamics, 3-majority and plurality): every set is
  within `[propext, Classical.choice, Quot.sound]`. Subsets: `Plurality.ofSet`,
  `Plurality.deltaCount_sum`, `Median.threshold_step`, `Median.threshold_run`,
  `Median.step_of_consensus` (`[propext, Quot.sound]`); `Median.med3_monotone`,
  `Median.step_mem`, `Median.step_mem_Icc` (`[propext]`).
* Pinned text: for every line of `PINNED.txt`, the declaration from its keyword to `:=` is
  identical at `0992685` and in the working tree (0 mismatches).
* Blueprints: every `\lean{}` name exists in the environment of the package root
  (dynamics 53, median 19, plurality 137, 3-majority 93; the only other match is the literal
  `\lean{...}` inside a LaTeX comment of two blueprints).
* `grep` for `sorry|admit|axiom|native_decide|implemented_by|extern` in the four packages:
  only `#print axioms` lines; `set_option`: only the pre-existing declaration-level
  `set_option maxHeartbeats 1000000 in` on `Median.binary_consensus`.
* Every changed Lean line is at most 100 characters (two pre-existing over-long lines in
  touched files, `Absorption.lean` and a docstring of `Median/Binary.lean`, were wrapped).

### Pitfalls (for later work)

* **Name resolution.** Inside `namespace Median`/`Plurality`/`Moran`/`Voter`/`Undecided`
  a bare name resolves to the package's own declaration first, then to `open Dynamics`.
  Deleting a local copy silently retargets its call sites to the Dynamics version.
* `prob_mono`'s hypothesis is strict-implicit, so a set inclusion `h : A ⊆ B` is accepted for
  the events `(· ∈ A)`, `(· ∈ B)` by definitional unfolding.
* `one_sub_avg_le_prob_ofStep`: pass the package's own step function (`Median.step`,
  `Plurality.step`) so that the hypothesis of a miss mentions the same term as the rest of
  the proof; the kernels unfold to `Kernel.ofStep` of it.
* `Distribution.prob` and `Kernel.event` both decide their event classically; proofs that
  compare them should start with `classical`.
* Do not build two packages that share `dynamics/` concurrently.

## Deviations

1. **No paper numbering.** `dynamics/` is a generic library without a source paper (as in the
   expectation job); docstrings cite the replaced package lemmas, the package blueprint labels
   (`lem:tails`, `lem:mgf`, `lem:chernoff`, `lem:chernofflog`) and the textbook statements
   (Dubhashi–Panconesi, Theorem 1.1; Mitzenmacher–Upfal, Theorem 4.5).
2. **Chernoff and Hoeffding stay with `{0,1}`-valued coordinates.** The MGF bound also holds
   for `[0,1]`-valued coordinates (convexity of `exp`), but every caller has `{0,1}`
   coordinates and `avg_hoeffding` uses the same hypothesis; a `[0,1]` version would force a
   conversion at every call site.
3. **`avg_markov_one` assumes `0 ≤ Yᵢ`, not `Yᵢ ∈ {0,1}`** (weaker than
   `Plurality.markov_one`): Markov needs only nonnegativity, and the median copy only has
   `fcoord_nonneg` at hand. Plurality and 3-majority derive nonnegativity from their `{0,1}`
   lemmas.
4. **Dropped `[Nonempty γ]`** in `avg_chernoff_lower_mul` (present in
   `Plurality.chernoff_lower`) and in `variance_le_avg_of_zero_one`: both statements are true
   on an empty type (the averages vanish), so the hypothesis was only a proof convenience.
   `avg_hoeffding_lower` keeps it, as `avg_hoeffding` does.
5. **The exact-mean closed forms are not separate declarations.**
   `ThreeMajority.avg_tail_ge_log`/`avg_tail_le_log` are the special case `μ = 𝔼X` of the
   bound forms `avg_chernoff_upper_log`/`avg_chernoff_lower_log` (hypothesis `le_of_eq`);
   stating both would itself be duplication.
6. **Predicates rather than sets** in `prob_mono` and `one_sub_avg_le_prob_ofStep`, matching
   `Distribution.prob` and `Kernel.prob_ofStep`; the set forms of the copies are instances
   (see Pitfalls).
7. **Two monotonicity statements**: the general `Kernel.iterate_monotone` (what Moran and Voter
   need, for their own indicators `allMutant`, `allColor`) and its absorbing-event form
   `Kernel.event_monotone` (what Median needs). Median's copy is stated as
   `∀ T₁ T₂ a, T₁ ≤ T₂ → ...`; the pinned form is `Monotone`, which unfolds to the same.
8. **Numeric duplicates that Mathlib has get no new declaration**: `exp_ge_pow`/`exp_ge_pow'`
   are `Real.pow_div_factorial_le_exp`, `sub_one_div_le_log'` is
   `Real.one_sub_inv_le_log_of_pos` after `(q - 1)/q = 1 - q⁻¹`. The two numeric duplicates
   Mathlib does not state for `n : ℕ` (`exp_neg_two_log`, `one_le_of_log_pos`) are pinned
   verbatim in the copies' form, since they are the conversions applied right after the tail
   bounds.
9. **Not consolidated, by scope** (single copies, not concentration/tail/indicator/
   monotonicity, or model-specific; see section F of the audit): `Moran.map_weight_pos`,
   `Plurality.avg_prod_iter`, `Plurality.avg_eval_two`, median's `bernstein_exp_le`,
   `markov_exp`, `markov_le` and the other `log n ≥ 128` numerics (their only second copy is
   the dead `BinaryPhases.lean`, whose deletion removes the duplication),
   `Plurality.ite_one_zero_nonneg` (Mathlib `ite_nonneg zero_le_one le_rfl`, optional).
10. **Existing pinned-in-place statements**: `avg_hoeffding`, `avg_bernstein`, `variance` are
    frozen although unchanged, because phase 2 edits their file and the packages depend on
    them. The earlier bridges of the expectation job are not re-pinned (not touched here).
11. **Phase 2 scope**: the moran, voter and undecided copies are listed in the audit and
    have general versions, but could not be deleted (those directories were not editable in
    phase 2). Their pinned replacements are proved and ready.
12. **3-majority's Chernoff names are deleted, not aliased.** The 3-majority blueprint now tags
    `Dynamics.avg_chernoff_*` and `Real.pow_div_factorial_le_exp`; its prose says the Lean
    closed forms are the bound versions (the exact-mean forms are the equality case). This
    differs from the expectation job, which kept `ThreeMajority.avg_*` wrappers.
13. **`Plurality.ite_one_zero_nonneg` is kept** (7 call sites, some with an explicit
    proposition in `linarith` hints): replacing it by `ite_nonneg zero_le_one le_rfl` would
    lengthen those lines for no gain; it is a one-line indicator fact, not a duplicate.

## Audit

State audited: commit `96f3cd0` (branch `conc-dedup`). Method: list of every `lemma`/`theorem`
name of the 9 packages (outside `.lake`), names occurring more than once; `grep` for
`prob|markov|chernoff|hoeffding|bernstein|tail|union|indicator|ind|lt_one|weight_pos|escape|
variance|exp_ge_pow|mgf|monotone|antitone` in declaration names and for inline Markov steps;
reading of every hit; search of the pinned Mathlib (`2d8c533b...`).

### A. Concentration and tail bounds

| Fact | Copies (live code) | General version |
| --- | --- | --- |
| Markov `P(∑Yᵢ ≥ 1) ≤ ∑ 𝔼Yᵢ` | `Plurality.markov_one` (`Tail.lean`); inline in `Median.falses_tail_markov` (`BinaryAux.lean`) and `ThreeMajority.saturation_stage2c` (`Saturation.lean`) | `avg_markov_one` (from `avg_markov`) |
| Markov on `exp(tX)`, `t ≥ 0` | `Dynamics.avg_tail_le_of_mgf`; inline again in `ThreeMajority.avg_tail_ge` | existing |
| Markov on `exp(tX)`, `t ≤ 0` | inline in `ThreeMajority.avg_tail_le` | `avg_lower_tail_le_of_mgf` |
| MGF factorization | `Dynamics.avg_exp_sum`; inline again in `ThreeMajority.avg_exp_le` | existing |
| Chernoff MGF bound `≤ exp(μ(eᵗ-1))` | `ThreeMajority.avg_exp_le` | `avg_chernoff_mgf` |
| Chernoff tails, parametric | `ThreeMajority.avg_tail_ge`, `avg_tail_le` (two near-identical proofs) | `avg_chernoff_upper`, `avg_chernoff_lower` |
| Chernoff tails, closed form | `ThreeMajority.avg_tail_ge_log`, `avg_tail_le_log`, `avg_tail_ge_log_le`, `avg_tail_le_log_ge` (the first two are special cases of the last two; four similar proofs) | `avg_chernoff_upper_log`, `avg_chernoff_lower_log` |
| Multiplicative lower tail `exp(-δ²μ/2)` | `Plurality.chernoff_lower` with helpers `half_sub_inv_le_log`, `one_sub_mul_log_one_sub_ge` | `avg_chernoff_lower_mul` |
| Hoeffding lower tail | `Median.avg_hoeffding_lower` | `avg_hoeffding_lower` |
| Variance of a `{0,1}` coordinate `≤` mean | `Median.variance_fcoord_le` (specialized to `fcoord`) | `variance_le_avg_of_zero_one` |
| Hoeffding upper tail, Bernstein, `variance` | `Dynamics` only (used by median, plurality) | pinned in place |

Plurality's numeric post-processing after `avg_bernstein` (`lemma_3_3`) and median's
`bernstein_exp_le` both simplify a Bernstein exponent, but with different constants (`b = 2`
inline, `b = 1` through an intermediate `D`): not copies of each other.

### B. Probability monotonicity, strict bounds, one-round lower bounds

| Fact | Copies (live code) | General version |
| --- | --- | --- |
| `prob` monotone in the event | `Plurality.prob_mono_set` (`Upper.lean`), `Median.prob_mono_set'` (`BinaryMoves.lean`) | `Distribution.prob_mono` |
| `1 - 𝔼[bad] ≤ P(one round lands in A)` | `Plurality.le_prob_step` (`Upper.lean`, for `kernel maj3`), `Median.prob_step_ge` (`BinaryMoves.lean`, for `kernel n Bool`) | `Kernel.one_sub_avg_le_prob_ofStep` |
| subharmonic iterates / absorbing events are nondecreasing | `Moran.fixation_mono` (`Isothermal.lean`), `Voter.colorProbability_mono` (`Main.lean`), `Median.event_absorb_mono` (`BinaryMoves.lean`, 66 lines); `dynamics/` has only `Kernel.iterate_antitone` | `Kernel.iterate_monotone`, `Kernel.event_monotone` |
| `iterate n f ≤ 1` for `f ≤ 1` | re-derived in `Moran.fixation_le_one`, `Voter.colorProbability_le_one` | existing `Kernel.iterate_le_one` (`Phases.lean`) |
| strict bound `𝔼f < 1` | `Moran.expect_lt_one`, `Voter.expect_lt_one` (verbatim); `Undecided.avg_lt_one` (uniform case); private `Median.avg_lt_one` (`Basic.lean`, uniform `{0,1}` case) | `Distribution.expect_lt_one`, `avg_lt_one` |

### C. Indicators

All indicator lemmas are model-specific instances of `Dynamics.avg_indicator`
(`Median.avg_false_ind`/`avg_true_ind`, `Plurality.avg_color_indicator`,
`Undecided.avg_indicator_eq`/`avg_indicator_ne`, `ThreeMajority.avg_ind`/`avg_ind_eq`,
`Voter.avg_maps_agree`, `Moran.typeInd_*`): no duplication. `Plurality.ite_one_zero_nonneg`
is Mathlib's `ite_nonneg zero_le_one le_rfl` (single copy).

### D. Scalar helpers of the tail bounds

| Fact | Copies (live code) | Resolution |
| --- | --- | --- |
| `xᵏ/k! ≤ exp x` | `ThreeMajority.exp_ge_pow` (`Bounds.lean`, blueprint `lem:exppow`), `Median.exp_ge_pow'` | Mathlib `Real.pow_div_factorial_le_exp` |
| `(q-1)/q ≤ log q` | `Median.sub_one_div_le_log'` | Mathlib `Real.one_sub_inv_le_log_of_pos` |
| `exp(-2 log n) = 1/n²` | `Plurality.exp_neg_two_log` (`Growth.lean`), `Median.exp_neg_two_log` | `Dynamics.exp_neg_two_log` |
| `0 < log n → 1 ≤ n` | `Plurality.one_le_of_log_pos` (`Saturation.lean`), `Median.one_le_of_log_pos` | `Dynamics.one_le_of_log_pos` |
| `markov_exp`, `markov_le`, `bernstein_exp_le`, `two_le_of_log`, `big_log_le`, `log_five_fourth_ge`, `log_eight_seventh_ge`, `exp_le_inv_sq`, `inv_sq_le_exp`, `exp_half_pow_four` | `Median` (`BinaryMoves.lean`) only, plus the dead `BinaryPhases.lean` | median-specific constants; deleting the dead file removes the duplicates |

### E. Dead code

`median/Median/BinaryPhases.lean` (771 lines) is imported by nothing (`Median.lean` imports
`Basic` and `Binary`; `Binary` → `BinaryAssembly` → `BinaryMoves` → `BinaryAux`). It is the WIP
original of `BinaryMoves.lean` (which says it is a copy differing only in `sat_move`) and
contains a second copy of every median lemma of sections B and D.

### F. Out of scope (noted, not pinned)

* `Moran.map_weight_pos` (`0 < p.weight a → 0 < (p.map f).weight (f a)`): generic, single
  copy; a candidate for `Distribution.lean` later.
* `Plurality.avg_prod_iter` (Fubini for `avg` on `β × δ`; Mathlib `Finset.expect_product'`
  through `avg_eq_expect`) and `Plurality.avg_eval_two` (two coordinates of a uniform
  `Fin m → γ` are independent): independence lemmas, single copies, blueprint `lem:hadopt`.
* Union bounds over rounds re-proved by induction in 3-majority and voter, inline Markov and
  reverse-Markov steps in `rumor_spread/`: model-specific (expectation audit, section 4).

### G. Mathlib

* Has: `Real.pow_div_factorial_le_exp` (`Analysis/Complex/Exponential.lean`),
  `Real.one_sub_inv_le_log_of_pos` and `Real.log_pos_iff` (`Analysis/SpecialFunctions/Log/
  Basic.lean`), `Finset.expect_lt_expect` (`Algebra/Order/BigOperators/Expect.lean`, a route
  to `avg_lt_one` through `avg_eq_expect`), `Finset.expect_product'`, `ite_nonneg`.
* No finite (`Finset.expect`/`Finset.sum`-level) Markov, Chernoff, Hoeffding or Bernstein
  bound; the measure-theoretic ones (`MeasureTheory.mul_meas_ge_le_integral`,
  `ProbabilityTheory.measure_sum_ge_le_of_iIndepFun`, ...) are excluded by the repository's
  design (no measure theory).
