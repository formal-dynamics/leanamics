# PROGRESS: EPI-5, PULL and PUSH–PULL rumor spreading on `K_n`

Job: roadmap row EPI-5. Sources: [KSSV00] Karp, Schindelhauer, Shenker, Vöcking, *Randomized
rumor spreading*, FOCS 2000 (§1.2 model, §2 push vs pull, Thm 2.1 push&pull); [FG85] Frieze,
Grimmett, Discrete Appl. Math. 10 (1985) (PUSH, partner "someone else").

## Status

* **Phase 1 (pin statements): done** (commit `5f5515b`). `PINNED.txt` (repo root) lists the 17
  pinned declarations.
* **Phase 2 (proofs): done.** Every pinned statement is proved; no `sorry`. A clean
  `lake build RumorSpread` (all sources touched) reports 0 warnings and 0 errors. `#print axioms`
  on all 17 pinned declarations (scratch file in `/tmp`): only `propext`, `Classical.choice`,
  `Quot.sound`. The pinned text (docstring and statement up to `:=`) was compared mechanically with
  the committed phase-1 files: identical. No pinned statement turned out false.

## Pinned (frozen up to `:=`), all in namespace `RumorPush`

`RumorSpread/PullModel.lean`
* `pullStep I r = I ∪ {v | r v ∈ I}`: one PULL round.
* `pullRun I l = l.foldl pullStep I`: rounds consumed head first, like `run`.
* `pushPullStep I r = step I r ∪ pullStep I r`: one PUSH–PULL round, same calls.
* `pushPullRun I l = l.foldl pushPullStep I`.
* `prPullNotAllInformed n v₀ T`, `prPushPullNotAllInformed n v₀ T`: `expList (Tgt n) T` of the
  indicator "not all informed", as `prNotAllInformed` for PUSH.
* `run_subset_pushPullRun`, `pullRun_subset_pushPullRun`: pathwise domination.

`RumorSpread/PullOneRound.lean` (phase lemmas, all exact, `hn : 2 ≤ n`; `m = |I|`, `u = n - m`)
* `pull_prob_stuck_singleton`: P(PULL round from `{v₀}` informs nobody) `= (1 - 1/(n-1))^(n-1)`.
* `pull_avg_card_step`: `𝔼|pullStep I r| = m + u · m/(n-1)`.
* `pull_avg_uninformed`: `𝔼(n - |pullStep I r|) = u(u-1)/(n-1)`.
* `pull_avg_uninformed_le`: `𝔼(n - |pullStep I r|) ≤ u²/n` (quadratic shrinking).
* `pushPull_avg_uninformed`: `𝔼(n - |pushPullStep I r|) = u(u-1)/(n-1) · (1 - 1/(n-1))^m`.

`RumorSpread/PullMain.lean`
* `pull_informs_all_whp`: `prPullNotAllInformed n v₀ ⌈160 log n⌉₊ ≤ 2/n` for `n ≥ 2`.
* `pull_informs_all_whp'`: complement form, P(all informed) `≥ 1 - 2/n`.

`RumorSpread/PullPushPull.lean`
* `pushPull_informs_all_whp`, `pushPull_informs_all_whp'`: the same for PUSH–PULL.

Sanity checks done in phase 1 (outside the repo, scripts in `/tmp/pullcheck`): all five
one-round formulas agree with brute-force enumeration of `Tgt n` for every `I`, `n ≤ 6`; the
exact PULL failure probability at `⌈160 ln n⌉` rounds (count chain, `n ≤ 200`) is `≈ 0`; the
minimum over `n ≤ 400`, `1 ≤ m ≤ n/2` of P(PULL good round) is `≈ 0.63` (needed: `≥ 1/8`).

## Proved (phase 2): files in dependency order

| file | lines | content |
| --- | --- | --- |
| `PullFoldl.lean` | 54 | `List.foldl` of an inflationary monotone step: `subset_foldl`, `foldl_mono`, `foldl_subset_foldl` (pathwise domination), `foldl_append_eq_univ` |
| `PullModel.lean` | 132 | pinned defs; `mem_pullStep`, `step_mono`, `pullStep_mono`, `pushPullStep_mono`, `run_eq_foldl`; the two domination theorems |
| `PullIndep.lean` | 118 | independence of the calls: `avg_pi_prod` (any finite product, via `Fintype.prod_sum`), `avg_tgt_mul_prod`, `avg_tgt_coord`; per-call probabilities `avg_call_mem`, `avg_call_not_mem`, `avg_call_ne` |
| `PullOneRound.lean` | 200 | `card_pullStep`, `uninformed_eq_sum`, `pull_avg_new` (`𝔼X`), and the five pinned one-round lemmas |
| `PullPhases.lean` | 353 | generic two-phase argument for any inflationary step driven by i.i.d. rounds: `goodRoundOf`, `goodCountOf`, `pow_goodCountOf_mul_card_le`, `expList_half_pow_goodCountOf`, `phase1Of`, `saturationOf`, `notAllOf_le`, `notAllOf_antitone`, `rounds_le_ceil_160`, `notAllOf_le_two_div` |
| `PullGood.lean` | 153 | `pull_avg_new_sq_le` (`𝔼X² ≤ μ + μ²`), `pull_prob_goodRound` (P(good) `≥ 1/8`, second moment), `pull_avg_uninformed_contract` |
| `PullMain.lean` | 49 | `pull_informs_all_whp` (instance of `notAllOf_le_two_div`) and its complement |
| `PullPushPull.lean` | 59 | `pushPull_informs_all_whp` (pointwise domination by PULL) and its complement |

Proof routes actually taken (vs. the phase-1 plan):
* PULL good rounds: proved P(good) `≥ 1/8` (mathematically the argument gives `≥ 3/16`; `1/8`
  is what the PUSH constants `numeric_A/B/C` need). Paley–Zygmund is done with pointwise bounds
  only: not good ⇒ `X < μ/4`, and `X·1[good] ≤ X²/(2t) + (t/2)·1[good]` with `t = 4(1+μ)/3`,
  pushed through `avg_le_avg`; no Cauchy–Schwarz needed.
* PUSH–PULL: proved from `pull_informs_all_whp` by pointwise domination at the same round count
  (no monotonicity in `T` needed there); `run_subset_pushPullRun` is proved but not needed.
* PULL main: `rounds_le_ceil_160` (`(⌈117L⌉₊+23)+⌈6L⌉₊ ≤ ⌈160L⌉₊`) plus `notAllOf_antitone`.

Reusable pieces: `avg_pi_prod` (independence of coordinates, any finite product);
`PullPhases.lean` (the whole PUSH-style `O(log n)` argument for any monotone spreading step, given
the two one-round inputs); `PullFoldl.lean` (domination/persistence for `List.foldl` dynamics).
`avg`/`expList` are this package's own copies (`Prob.lean`); if they are deduplicated against
`dynamics/`, `avg_pi_prod` is a candidate to move there.

## Remaining

Nothing required. Optional follow-ups: blueprint entries (`blueprint/src/content.tex`, with
`\lean{}` tags) and a section in `latex/rumor_push.tex`; re-deriving PUSH from `PullPhases.lean`
to remove the duplication with `Growth.lean`/`Saturation.lean`/`prNotAllInformed_le`.

## Errors / blockers

None. (Tactic note for later edits: an unannotated `Finset.prod_eq_zero hw (if_pos h)` elaborated
`if_pos` at type `Fin n` and failed with `CommMonoidWithZero (Fin n)`; give `(f := ...)`.)

## Changes outside the new files

* `RumorSpread.lean`: imports the eight `Pull*` modules (four pinned files, four helper files).
* `lakefile.toml`: `weak.linter.style.header = false`. Mathlib's header linter (part of
  `mathlibStandardSet`) warned "Copyright too short!" on *every* file of the package, including
  all pre-existing ones (no file in the monorepo carries a Mathlib copyright header, and there is
  no LICENSE to cite). Disabling just this linter is what makes the build warning-free (as
  required). Revert this line if the warning is wanted.

## Deviations from the paper

1. **Partner choice excludes self-calls.** [KSSV00, §1.2] lets every player choose its partner
   uniformly from *all* players (its §2 startup analysis mentions a player "calling itself"). We
   reuse `rumor_spread`'s round model `Tgt n` (uniform among the *other* `n - 1` nodes, the
   [FG85] convention), as the job requires reusing the PUSH round model. Only constants change:
   the exact one-round formulas have `n - 1` where KSSV's heuristics have `n` (e.g. the expected
   uninformed count after a PULL round is `u(u-1)/(n-1)` instead of KSSV's `s² n = u²/n`; we
   pin the exact form and the bound `≤ u²/n`).
2. **Round count `⌈160 ln n⌉ = O(log n)`, not sharp.** [KSSV00, Thm 2.1] gives
   `log₃ n + O(log log n)` rounds for push&pull. As the job asks, we pin `O(log n)` with an
   explicit, deliberately crude constant, chosen so that both proofs reuse the PUSH numerics
   `numeric_A/B/C` with margin (and PUSH–PULL also follows from PUSH by domination). Sharp
   times are the target of EPI-8 (Doerr–Kostrygin).
3. **"w.h.p." with exponent 1.** [KSSV00, footnote 1]: w.h.p. means probability
   `≥ 1 - n^{-α}` for an arbitrary constant `α`. We pin failure probability `≤ 2/n` (the job's
   `1 - C/n` form, and the same form as `push_informs_all_whp`).
4. **Spreading time only.** [KSSV00, Thm 2.1] also bounds the number of transmissions
   (`O(n log log n)`) and stops push&pull with an age counter; we run exactly `T` rounds (= their
   scheme with termination age `T`) and do not count messages. §3 (median-counter algorithm),
   robustness and the lower bounds are out of scope.
5. **PULL.** KSSV discuss PULL only informally in §2 (no numbered theorem): `O(log n)` rounds to
   inform about `n/2` nodes w.h.p., then quadratic shrinking. We pin the classical statement
   "PULL informs all nodes in `O(log n)` rounds w.h.p." and the quadratic shrinking **in
   expectation only** (exact one-round formula, `≤ u²/n`), not the w.h.p. Chernoff version used
   in the proof of Thm 2.1 (phase 3), since this package avoids Chernoff bounds by design.
6. **Optional PUSH sharp bound** `log₂ n + ln n` ([FG85], Pittel) mentioned in EPI-5 is not
   pinned.
7. `n ≥ 2` throughout (for `n = 1` there is no round configuration, `Tgt 1` is empty); start
   from a single informed node `v₀`, arbitrary, as in the sources.
