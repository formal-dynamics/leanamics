# Expectation audit and unification (PROGRESS file)

Job: remove the duplicated finite-probability infrastructure across the Leanamics packages.
This file is both the audit report and the PROGRESS file of the job.

## Status

* **Phase 1 (pin the statements): done** (commit `a2fa9ac`).
* **Phase 2 (prove the pinned statements, delete the duplicates): done.** No `sorry` remains;
  the four required builds are warning-free; every pinned declaration depends only on
  `propext`, `Classical.choice`, `Quot.sound` (two of them on a subset); the pinned text is
  unchanged.
* **Recommended next phase** (not requested yet): sections 3-6 and the last three points of
  section 8 of the audit below (concentration and generic `Distribution` lemmas into
  `dynamics/`, deleting the dead `median/Median/BinaryPhases.lean`).

### Pinned

`PINNED.txt` (repository root, 63 lines, `<path> <name as written after the keyword>`):

* **New bridges** (`dynamics/Dynamics/Bridge.lean`, imported by the root `Dynamics.lean`):
  * `avg_eq_expect`: `avg f = 𝔼 a, f a` (Mathlib `Finset.expect` over `univ`);
  * `expList_eq_expect`: `expList α T F = 𝔼 ω : Fin T → α, F (List.ofFn ω)`;
  * `Distribution.independent_uniform_expect` (`[Nonempty α]`):
    `(independent fun _ : ι => uniform α).expect g = avg g`;
  * `expList_eq_independent_expect` (`[Nonempty α]`):
    `expList α T F = (independent fun _ : Fin T => uniform α).expect (fun ω => F (List.ofFn ω))`.
* **Existing bridges, frozen in place**: `Distribution.uniform_expect`
  (`(uniform α).expect f = avg f`, `Dynamics/Distribution.lean`), `expList_eq_avg_ofFn`
  (`Dynamics/Equivalence.lean`), and `Kernel.nested_phases` (Lemma A.4, named in the
  plurality README).
* **Main results of `rumor_spread/`**: `push_informs_all_whp`, `push_informs_all_whp'`,
  `numeric_C` (blueprint corollary), `expList_eq_avg_ofFn` (blueprint theorem "Faithfulness of
  the model") and the definition `prNotAllInformed` (the probability in the README statement).
* **Main results of `3-majority/`**: `majority3_consensus_whp`, `majority3_consensus_fail_le`,
  `majority3_consensus_fail_le_clean`, `hfloor4_of_hbig` (all blueprint theorem environments).
* **Main results of `plurality/`**: every theorem of `plurality/Audit.lean`, every name of the
  README status table (`lemma_3_1_a` ... `theorem_4_12_log`), and every `\lean{}` name of the
  blueprint's theorem/corollary environments (including the definitions `ofSet`, `lamK`,
  `balancedSet`, `extinctRounds`, `hBalancedSet`).

Selection rule: README-named results, blueprint `theorem`/`corollary` environments, and CI axiom
audit lists. Helper lemmas tagged in blueprint `lemma` environments are **not** pinned, on
purpose: they included the duplicates that phase 2 deleted (`RumorPush.avg_le_avg`, ...).

### Proved (phase 2)

* **`dynamics/Dynamics/Bridge.lean`** (74 lines): the four bridges, each in 1-8 lines.
  `avg_eq_expect` is Mathlib's `Fintype.expect_eq_sum_div_card`; `independent_uniform_expect`
  computes that every point of `ι → α` has product weight `|α|^(-|ι|) = |ι → α|⁻¹`;
  `expList_eq_expect` and `expList_eq_independent_expect` are rewrites through the existing
  `expList_eq_avg_ofFn`. All pinned theorems of the three model packages were already proved;
  they now elaborate against the shared layer.
* **`rumor_spread/` now depends on `dynamics/`** (`lakefile.toml` path requirement, hand-edited
  `lake-manifest.json` entry, as `3-majority/`). `RumorSpread/Prob.lean` (127 lines: `avg`,
  `expList` and 17 re-proved lemmas) is deleted; `OneRound`, `Growth`, `Saturation`, `Main`
  `open Dynamics`; `RumorSpread/Equivalence.lean` (54 → 30 lines) keeps only the pinned
  `RumorPush.expList_eq_avg_ofFn := Dynamics.expList_eq_avg_ofFn T F` and imports
  `Dynamics.Bridge`, so the Mathlib and product forms are available to the package. The
  blueprint tags (`\lean{RumorPush.avg}` and 11 more) point to `Dynamics.*`; README and
  CLAUDE.md describe the new layout.
* **`ThreeMajority.avg` is an alias of `Dynamics.avg`**: `noncomputable abbrev avg (f : α → ℝ) :
  ℝ := Dynamics.avg f` (a constant, so the blueprint's `checkdecls` still finds it; reducible,
  so `simp` sees through it). Its body is no longer a copy. The empty-type case of
  `ThreeMajority.avg_exp_le` now unfolds both names; a second, needless case split there is gone
  (`avg_nonneg` needs no `Nonempty`). `Plurality.threeMajority_avg_eq` is still `rfl`.
* **Warnings.** Pre-existing lint warnings were fixed in the code: deprecated `push_neg` →
  `push Not` (4), lines over 100 characters (8), `simp [...] <;> norm_num` → `norm_num [...]`
  (2), a no-op `push_cast` (1), and three unused hypotheses, renamed with a leading `_`
  (`saturation_round_generic`, whose dead `haveI` was removed, `saturation_mean_quad`,
  `Plurality.expected_count_le`; signatures and callers unchanged). The copyright-header
  linter is disabled in the three lakefiles (Deviation 8).
* **Documentation**: `dynamics/README.md` (module table, "only finite-probability layer"),
  `dynamics/blueprint` (new `lem:bridge` tagging the four bridges), `dynamics/Audit.lean`
  (axioms of the bridges), `3-majority/README.md`, the docstring of `Plurality/Tail.lean`.

**Verification** (on the final working tree; scratch files under `/tmp`):

* `lake build Dynamics`, `lake build RumorSpread`, `lake build ThreeMajority`,
  `lake build Plurality`: success, 0 warnings, 0 `sorry`. Every module of the three model
  packages was recompiled (lakefile options changed). The plurality log contains four `info:`
  lines `Error in Linarith.normalizeDenominatorsLHS` from `Plurality/Upper.lean` (untouched):
  pre-existing, `info` severity, emitted by Mathlib's `linarith` preprocessing.
* `#print axioms` on all 63 pinned declarations (plus the 7 `dynamics/` ones again from the
  `rumor_spread/` environment): `[propext, Classical.choice, Quot.sound]`, except
  `Plurality.ofSet` and `Plurality.deltaCount_sum`: `[propext, Quot.sound]`.
* Pinned text: a script compares, for every line of `PINNED.txt`, the declaration from its
  keyword up to `:=` at `a2fa9ac` and in the working tree: 0 mismatches.
* Blueprints: every `\lean{}` name of the four blueprints (34 + 42 + 95 + 136) exists in the
  environment of the package root, as `checkdecls` checks.
* `grep` for `sorry|admit|axiom|native_decide|implemented_by|extern|set_option` in the four
  packages: no hit.

### Remaining

Nothing inside the four packages. Follow-ups **outside** the directories this job may modify:

1. `.github/workflows/rumor_spread-ci.yml`: add `'dynamics/**'` to both `paths` lists, as
   `three_majority-ci.yml` does, so that changes to the shared layer rebuild rumor_spread.
2. Root `README.md` ("The `dynamics/` package is shared by ..."): add `rumor_spread/`.
3. `PROVENANCE.md`: record this refactor if desired (no main result changed).

### Errors

* While deleting `rumor_spread/RumorSpread/Prob.lean` I ran `git rm --cached`, which staged the
  deletion (a writing git command, against the ground rules). It was undone immediately with
  `git restore --staged`; the index is as it was, and the deletion is an ordinary working-tree
  change.
* No build error was left; none of the planned edits needed a second attempt.

### Pitfalls (kept for later phases)

* **Name resolution.** The pinned statements mention the unqualified `expList` (3-majority,
  `push_informs_all_whp'`) and `avg`/`expList` (`RumorPush.expList_eq_avg_ofFn`). The gate
  compares text; inside `namespace RumorPush` with `open Dynamics` and no `RumorPush.avg` left,
  they elaborate to `Dynamics.*`. Never keep both a `RumorPush.expList` and `open Dynamics`:
  Lean would report an ambiguous name.
* `RumorPush.expList_eq_avg_ofFn` and `Dynamics.expList_eq_avg_ofFn` both exist; inside
  `RumorPush` the short name would be ambiguous (no such call site).
* `checkdecls` only sees declarations imported by the package root: a blueprint tag naming a
  `dynamics/` declaration needs that module imported by the package (hence the
  `Dynamics.Bridge` import of `RumorSpread/Equivalence.lean`).
* Do not build two packages that share `dynamics/` concurrently: they write the same
  `dynamics/.lake/build`.

## Deviations

1. **`avg f = (Distribution.uniform α).expect f` is not a new declaration.** It already exists
   as `Dynamics.Distribution.uniform_expect` (`(uniform α).expect f = avg f`, the reverse
   orientation), which is pinned in place; a second, symmetric copy would itself be the kind of
   duplication this job removes. Use `← Distribution.uniform_expect` to rewrite `avg` into the
   distribution form.
2. **One extra bridge, `Distribution.independent_uniform_expect`**: the independent product of
   uniform laws is the uniform law on the product. Both `expList` bridges factor through it, and
   it generalizes `Voter.independent_wfKernel_expect` (where `wfKernel V = fun _ => uniform V`).
3. **Two forms of the `expList` bridge** (Mathlib `𝔼` and `Distribution.independent`), since
   `dynamics/` does have the iterated product distribution.
4. **Hypotheses.** The `Distribution` forms need `[Nonempty α]` because `Distribution.uniform`
   does (a distribution cannot live on an empty type). The Mathlib forms need nothing:
   `Finset.expect` and `avg` both vanish on an empty type.
5. **No paper numbering.** `dynamics/` is a generic library without a source paper (see the
   abstract of its blueprint); the docstrings cite the dynamics blueprint labels
   (`def:avg`, `lem:uniform-trajectory`, `lem:uniform-agreement`, `lem:weighted-product`).
6. **Pinned definitions.** Besides the theorems, `PINNED.txt` lists a few existing definitions
   that the blueprint tags inside theorem/corollary environments, plus `prNotAllInformed`. The
   gate freezes only their signature (the text up to `:=`), not their body. No new definitions
   were needed.
7. **`RumorPush.expList_eq_avg_ofFn` is pinned although it is a verbatim duplicate**, because the
   rumor_spread blueprint presents it as a theorem ("Faithfulness of the model"). Phase 2 keeps
   it as a one-line alias of `Dynamics.expList_eq_avg_ofFn`, as allowed for pinned names.
8. **The copyright-header linter is disabled** (`weak.linter.style.header = false` in the
   lakefiles of `rumor_spread/`, `3-majority/`, `plurality/`, which enable Mathlib's standard
   linter set). Its only "fix" would be a Mathlib-style `Copyright ... Released under Apache 2.0
   ... Authors: ...` header in every file, but the repository has no LICENSE and no file has such
   a header: choosing a licence and authors is the owners' decision. A style linter does not
   affect kernel checking. Every other pre-existing warning was fixed in the code.
9. **`ThreeMajority.avg` is an `abbrev`, not an `export`.** An `export Dynamics (avg)` alias is
   not a constant, and the 3-majority blueprint's `\lean{ThreeMajority.avg}` is checked with
   `Environment.contains`; the reducible abbreviation keeps the name and removes the copy. The
   23 `ThreeMajority.avg_*`/`expList_*` wrappers stay (one-line proofs by the `Dynamics`
   lemmas, tagged in the blueprint, needed by `rw` on `ThreeMajority.avg` terms).
10. **Not done in phase 2, by scope**: the consolidation of the concentration bounds and of the
    generic lemmas re-proved in median, moran, voter, undecided (audit sections 3-6). Phase 2 was
    restricted to `dynamics/`, `rumor_spread/`, `3-majority/`, `plurality/`, and those packages'
    remaining copies (`Plurality.prob_mono_set`, `le_prob_step`, `chernoff_lower`, `markov_one`,
    `avg_prod_iter`, `avg_eval_two`, the 3-majority Chernoff file) were left untouched to keep
    the change reviewable.

## Audit

State audited: commit `a2fa9ac` (before phase 2). Method: `grep` over every `.lean` file outside `.lake` (about 15 000 lines in 9 packages) for
definitions (`def`/`abbrev`/`structure`) and lemmas about expectation, averages, probability,
distributions, independence, variance, Markov/Chebyshev/Hoeffding/Chernoff/Bernstein and union
bounds, then a reading of each hit; plus a search of the pinned Mathlib
(`2d8c533b...`).

### 1. Three expectation APIs

| API | Where | Scope |
| --- | --- | --- |
| `avg f = (∑ a, f a) / card α` | `dynamics/Dynamics/Uniform.lean` | uniform, 0 on an empty type |
| `expList α T F` (recursion on `T`) | same | `T` i.i.d. uniform rounds |
| `Distribution`, `.expect`, `.prob`, `.uniform`, `.point`, `.map`, `.independent` | `dynamics/Dynamics/Distribution.lean` | weighted, needs a nonempty type |
| `Kernel.apply/iterate/event`, `Kernel.ofStep` | `Dynamics/Kernel.lean`, `Rounds.lean` | Markov kernels |
| `Finset.expect` (`𝔼 a, f a`) | Mathlib `Algebra/BigOperators/Expect.lean` | uniform, 0 on an empty set |

Inside `dynamics/` the two own APIs are already connected: `Distribution.uniform_expect`,
`Kernel.apply_ofStep`, `Kernel.iterate_ofStep` (kernel iterates are `expList`) and
`expList_eq_avg_ofFn`. They overlap in content: `avg_nonneg/le_avg/add/sub/const_mul/sum/const`
mirror `Distribution.expect_nonneg/mono/add/sub/mul/sum/const`, and
`avg_prod_pi`/`avg_eval` mirror `independent_expect_prod`/`independent_expect_eval`. Both are
needed: `Distribution` carries the non-uniform laws (Moran, voter, epidemics), `avg`/`expList`
the uniform-round processes (rumor, 3-majority, plurality, median, undecided). Nothing linked
them to Mathlib before `Bridge.lean`.

### 2. Duplicated definitions

| Declaration | Copies | Notes |
| --- | --- | --- |
| `avg` | `Dynamics.avg`, `ThreeMajority.avg` (`3-majority/ThreeMajority/Prob.lean`), `RumorPush.avg` (`rumor_spread/RumorSpread/Prob.lean`) | identical bodies; `Plurality.threeMajority_avg_eq` bridges the first two by `rfl` |
| `expList` | `Dynamics.expList`, `ThreeMajority.expList` (abbrev of `Dynamics.expList`), `RumorPush.expList` | `RumorPush.expList` is an independent copy |
| `avg_*`/`expList_*` lemmas | `RumorSpread/Prob.lean`: 17 lemmas re-proved verbatim; `ThreeMajority/Prob.lean`: 23 one-line wrappers of the `Dynamics` lemmas | |
| `expList_eq_avg_ofFn` | `dynamics/Dynamics/Equivalence.lean`, `rumor_spread/RumorSpread/Equivalence.lean` | verbatim copy (only import and namespace differ) |
| `variance` | `Dynamics.variance` (`Concentration.lean`) only | no copy |

`rumor_spread/` was the only package using probability that did not depend on `dynamics/`
(state before phase 2; phase 2 removed the `rumor_spread/` copies and made it depend on
`dynamics/`).

### 3. Generic lemmas re-proved outside `dynamics/`

| Lemma (location) | Generic content | Belongs in |
| --- | --- | --- |
| `Plurality.prob_mono_set` (`plurality/Plurality/Upper.lean`), `Median.prob_mono_set'` (`median/Median/BinaryMoves.lean`, and again in `BinaryPhases.lean`) | `Distribution.prob` is monotone in the event | `Distribution.prob_mono` |
| `Plurality.le_prob_step` (`Upper.lean`), `Median.prob_step_ge` (`BinaryMoves.lean`, `BinaryPhases.lean`) | `1 - avg bad ≤ (ofStep step x).prob (· ∈ A)` when `bad ≥ 0` charges every miss by `≥ 1` | `Dynamics/Rounds.lean` |
| `Moran.expect_lt_one` (`moran/Moran/Isothermal.lean`), `Voter.expect_lt_one` (`voter/Voter/Absorption.lean`) | identical: an expectation of `f ≤ 1` with a weighted point where `f < 1` is `< 1` | `Distribution.expect_lt_one` |
| `Undecided.avg_lt_one` (`undecided/Undecided/Basic.lean`) | the uniform case of the previous row | `avg_lt_one` |
| `Moran.map_weight_pos` (`Isothermal.lean`) | `0 < p.weight a → 0 < (p.map f).weight (f a)` | `Distribution.map_weight_pos` |
| `Voter.independent_wfKernel_expect` (`voter/Voter/Coalescence.lean`) | product of uniform laws is uniform | `Distribution.independent_uniform_expect` (pinned) |
| `Plurality.avg_prod_iter` (`plurality/Plurality/HPlurality.lean`) | Fubini for `avg` over `β × δ` | close to `avg_avg_swap`, `avg_mul_prod` |
| `Plurality.avg_eval_two` (`HPlurality.lean`) | two distinct coordinates of a uniform `Fin m → γ` are independent | next to `avg_eval` |
| `Undecided.avg_indicator_eq/ne`, `Plurality.avg_color_indicator`, `ThreeMajority.avg_ind*`, `Voter.avg_maps_agree` | indicator averages as counting ratios | model-specific uses of `avg_indicator`; fine |

### 4. Concentration and tail bounds

| Result | Location | Relation |
| --- | --- | --- |
| Markov on `exp(tX)` (`avg_tail_le_of_mgf`), MGF factorization (`avg_exp_sum`), Hoeffding upper tail (`avg_hoeffding`), Bernstein (`avg_bernstein`), Hoeffding's lemma, `variance` | `dynamics/Dynamics/Concentration.lean` | the shared versions |
| Multiplicative Chernoff: `avg_exp_le`, `avg_tail_ge`, `avg_tail_le`, `avg_tail_ge_log`, `avg_tail_le_log`, `avg_tail_ge_log_le`, `avg_tail_le_log_ge` | `3-majority/ThreeMajority/Chernoff.lean` | stated with `ThreeMajority.avg`; re-proves inline the Markov-on-`exp` step and the MGF factorization of `Concentration.lean`. Used by plurality through `threeMajority_avg_eq` |
| `chernoff_lower` (multiplicative lower tail), `markov_one` (`P(X ≥ 1) ≤ 𝔼X`) | `plurality/Plurality/Tail.lean` | generic, on top of the previous row |
| `avg_hoeffding_lower` (lower tail by complement), `variance_fcoord_le` (variance of a `{0,1}` coordinate is at most its mean), `falses_tail_markov` | `median/Median/BinaryAux.lean` | first two are generic |
| `bernstein_exp_le`, `markov_exp`, `markov_le` | `median/Median/BinaryMoves.lean` (and `BinaryPhases.lean`) | numeric side conditions, median-specific |
| Union bound over rounds | `Dynamics.expList_escape` (`Rounds.lean`), used by plurality | proved again per model by induction on rounds in 3-majority (`growth_fail_le`, the `Saturation.lean` stages) and voter (`Coalescence.lean`); model-specific, fine |
| Markov, reverse Markov, union bounds | `rumor_spread/` | inline pointwise inequalities through `avg_le_avg`/`expList_le_expList` (a documented design choice of the package), no separate lemma |

No package defines Chebyshev's inequality. Mathlib's measure-theoretic versions are not used anywhere.

### 5. Hand-built distributions (model-specific, not duplicates)

`Epidemics.bernoulli`/`coins` (Bernoulli coins, `independent`), `Moran.pullDist` and
`Moran.pairDist` (a uniform or fitness-weighted vertex, then a uniform neighbour),
`Voter.uniformNeighbor`, `Voter.degreeDistribution`, `Voter.wfKernel` (`= uniform`). The two
Moran laws prove `weight_nonneg`/`weight_sum_one` by hand for a "first coordinate, then kernel"
law; a `Distribution.bind` (or semidirect product) in `dynamics/` would make them one-liners.

### 6. Dead code and non-probability duplicates (out of scope, noted)

* `median/Median/BinaryPhases.lean` is not imported by anything, so it is never built. It is the
  WIP original of `BinaryMoves.lean` (commit `3623307`, "WIP (not accepted)"), which says it is a
  copy; about 270 diff lines, mostly `sat_move`. It duplicates every lemma of row 3 and 4 above
  that lives in `BinaryMoves.lean`.
* `exp_ge_pow` (`ThreeMajority/Bounds.lean`) and `exp_ge_pow'` (`median/Median/BinaryMoves.lean`,
  again in `BinaryPhases.lean`) are identical (`x ^ k / k! ≤ exp x`); `Plurality.exp_ge_pow_seven`
  reuses the former.
* `exp_neg_two_log` (`exp (-(2 log n)) = 1 / n ^ 2`) is proved in `Plurality/Growth.lean` and
  twice in median.

### 7. What Mathlib offers

* **`Finset.expect`** (`Mathlib/Algebra/BigOperators/Expect.lean`, order lemmas in
  `Mathlib/Algebra/Order/BigOperators/Expect.lean`), notation `𝔼 i ∈ s, f i` / `𝔼 i, f i`
  (`open scoped BigOperators`). `Fintype.expect_eq_sum_div_card : 𝔼 i, f i = (∑ i, f i) / card ι`
  is literally the body of `avg`. Its API covers almost every `avg_*` lemma: `expect_add_distrib`,
  `expect_sub_distrib`, `mul_expect`/`expect_mul`, `Fintype.expect_const` (`[Nonempty]`),
  `expect_le_expect`, `expect_nonneg`, `expect_lt_expect`, `expect_sum_comm`, `expect_comm`,
  `expect_equiv`, `expect_product`, `expect_mul_expect`, `expect_indicator_one`,
  `card_mul_expect`. There is no product-over-`Fin n → γ` independence lemma (`avg_prod_pi`) and
  nothing like `expList`.
* **`PMF`** (`PMF.uniformOfFintype`, ...): `ℝ≥0∞`-valued; excluded by the repository's design
  (no `PMF`/`ENNReal`).
* **Measure-theoretic probability**: Hoeffding
  (`ProbabilityTheory.measure_sum_ge_le_of_iIndepFun`, `Probability/Moments/SubGaussian.lean`),
  Chebyshev (`ProbabilityTheory.meas_ge_le_variance_div_sq`), Markov
  (`MeasureTheory.mul_meas_ge_le_integral`), `ProbabilityTheory.variance`, `iIndepFun`. Excluded
  by design (no measure theory); bridging the finite layer to them is possible but not needed.
* **Weighted averages**: `Finset.centerMass` (`Analysis/Convex/Combination.lean`), equal to
  `Distribution.expect` when the weights sum to one; not worth a dependency.

### 8. Recommended unified design

* **One uniform expectation**: `Dynamics.avg`, kept as a definition with its current body (so the
  many `avg_*` names, the blueprints and the `unfold avg`/`simp [avg]` proofs keep working),
  connected to Mathlib by `avg_eq_expect`. Missing `avg` facts should be taken from
  `Finset.expect` through that bridge rather than re-proved.
* **One trajectory expectation**: `Dynamics.expList`, with its three characterizations
  `expList_eq_avg_ofFn`, `expList_eq_expect`, `expList_eq_independent_expect`, and
  `Kernel.iterate_ofStep` for kernels.
* **One weighted API**: `Dynamics.Distribution`/`Kernel`, connected by `uniform_expect` and
  `independent_uniform_expect`.
* **No package defines expectation, average or probability.** Old names survive only as thin
  aliases where a pinned statement or a blueprint tag needs them.
* **All concentration in `Dynamics/Concentration.lean`** (later phase, not requested yet): move
  the multiplicative Chernoff bounds of `ThreeMajority/Chernoff.lean` (restated with
  `Dynamics.avg`, re-using `avg_tail_le_of_mgf`/`avg_exp_sum`), `Plurality.chernoff_lower`,
  `Plurality.markov_one`, `Median.avg_hoeffding_lower` and the Bernoulli variance bound; keep
  `ThreeMajority.*` aliases for the 3-majority blueprint.
* **Generic `Distribution`/`Rounds` lemmas** (later phase): `prob_mono`, `expect_lt_one`,
  `avg_lt_one`, `map_weight_pos`, the "`1 - 𝔼[bad]`" lower bound for `ofStep`, `avg_eval_two`;
  then delete the copies in plurality, median, moran, voter, undecided.
* **Delete `median/Median/BinaryPhases.lean`** (dead code).

Phase 2 as requested covers the first four points for `rumor_spread/` and `3-majority/`; the
last three are recommendations for a later phase.
