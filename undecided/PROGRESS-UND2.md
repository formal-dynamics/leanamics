# UND-2: sequential undecided-state dynamics (approximate majority), progress

Source: D. Angluin, J. Aspnes, D. Eisenstat, *A simple population protocol for fast robust
approximate majority*, Distributed Computing 21(2):87–102, 2008 [AAE08]. Journal manuscript:
<https://cs.yale.edu/homes/aspnes/papers/approximate-majority-abstract.html>.

## Status

**Phase 1 (pin the statements): done. Phase 2 (proofs): done.** All three pinned theorems are
proved. `lake build Undecided` (clean rebuild) is warning-free; `#print axioms` for
`consensus_whp`, `majority_whp`, `approximate_majority` gives only `propext`, `Classical.choice`,
`Quot.sound` (also via `python3 ../scripts/check_axioms.py`, which now audits them through
`Audit.lean`). No `sorry`/`admit`/`axiom`/`native_decide`/`set_option` in the new files. The pinned
text (each declaration up to `:=`) was checked unchanged against the phase-1 copy; the only edit to
`SequentialMain.lean` outside the proofs is its `import` line.

Phase-1 sanity checks (not committed) passed by `decide`: each row of the transition table on 2-
and 3-agent configurations, `run` applying interactions left to right,
`Fintype.card (Interaction n) = n (n - 1)` for `n = 2, 3`; `#print` confirmed that `update` is
`Undecided.update` and `run` folds `Sequential.step`.

## Pinned

`undecided/Undecided/Sequential.lean` (namespace `Undecided.Sequential`), reusing `Undecided.Op`,
`Config`, `count`, `update` from `Undecided/Basic.lean`:

* `Interaction n`: ordered pairs `(initiator, responder)` of distinct agents (subtype of
  `Fin n × Fin n`), drawn uniformly by `Dynamics.expList (Interaction n) T`.
* `step s p`: the responder `p.1.2` takes `update (s p.1.2) (s p.1.1)`; the others are unchanged.
  This is exactly the table of [AAE08, §3] under `x ↦ .a`, `y ↦ .b`, blank `↦ .u`.
* `run s l := l.foldl step s` (the form used by `Dynamics.Kernel.iterate_ofStep`).

`undecided/Undecided/SequentialMain.lean`:

* `consensus_whp` [AAE08, Thm 1]: `∀ c : ℕ, ∃ C, ∀ n ≥ 2, ∀ s` non-blank (`∃ v, s v ≠ .u`),
  `∀ T ≥ C n log n`: `1 - C / n ^ c ≤ P[count .a = n ∨ count .b = n after T interactions]`.
* `majority_whp` [AAE08, Thm 2 + Thm 1]: `∀ c : ℕ, ∃ C, ∀ n ≥ 2, ∀ s` (blanks allowed) with
  `C √n log n ≤ count s .a - count s .b`, `∀ T ≥ C n log n`:
  `1 - C / n ^ c ≤ P[count .a = n after T interactions]`.
* `approximate_majority`: the same with error `1 - C / n` (the `c = 1` case; the requested form).

## Proved

All in `undecided/Undecided/`, namespace `Undecided.Sequential` (1924 lines in the nine
`Sequential*.lean` files).

| file | lines | content |
| --- | --- | --- |
| `Sequential.lean` | 43 | pinned model: `Interaction`, `step`, `run` |
| `SequentialMartingale.lean` | 130 | generic (any `step : S → R → S`): `pathSum` with linearity and monotonicity, `expList_exp_pathSum_le` (weighted supermartingale over a finite horizon), `expList_ind_le_of_weight` (Markov), `expList_le_expList_of_length`, `expList_one_sub` |
| `SequentialCounts.lean` | 279 | `count_add`, `sum_interaction`, `card_interaction` (`n(n-1)`), `avg_transition` (one-step formula), `count_step`, `avg_step_counts`, `count_step_u`, `Cons`, absorption (`step_of_cons`, `cons_run`), `nonblank_run` |
| `SequentialPotentials.lean` | 238 | `stepSC` (P1, cf. [AAE08, Lemmas 2–4]), `stepC` (central region), `central_pairs` |
| `SequentialCorners.lean` | 434 | `stepB` (blank corner, cf. Lemma 6), `stepX`, `stepY` (opinion corners, cf. Lemma 7) |
| `SequentialGap.lean` | 114 | `stepM` (the gap stays positive) |
| `SequentialConsensus.lean` | 448 | path-sum decompositions, `Sxy_le`, `ps_notCons`, `cons_of_small`, `five_events`, `prob_notCons_le` (Thm 1, explicit), `gap_event_le`, `prob_notAllX_le` (Thm 2, explicit) |
| `SequentialWhp.lean` | 131 | `constC c = 40000(c+2) + 16^c`, `threshold_le`, `error_le`, `gap_error_le` |
| `SequentialMain.lean` | 107 | the pinned `consensus_whp`, `majority_whp`, `approximate_majority` |

Explicit forms (for `n ≥ 16`, any `L`, `T ≥ 256L + 34576nL + 6336n`):
`P[not in consensus at T] ≤ 9n e^{-L}` from a non-blank start (`prob_notCons_le`), and
`P[not all x at T] ≤ 9n e^{-L} + exp(-(x₀-y₀)²/(2(60nL + 11n)))` if `x₀ > y₀`
(`prob_notAllX_le`). The pinned theorems take `L = (c+2) log n` and `C = constC c`.

Also updated: `Undecided.lean` (imports every new file), `Audit.lean` (the three theorems), the
blueprint (`blueprint/src/content.tex`, new section, all 40 `\lean{}` names checked to exist) and
`README.md` (a paragraph on the sequential results; provenance made precise).

## Remaining

Nothing required. Outside `undecided/` (not editable in this phase), suggested: mark ROADMAP row
UND-2 as done and correct its `ω(√(n log n))` to `ω(√n log n)` (deviation 1). Possible follow-ups:
the `√(n log n)` gap of Condon et al. (no initial blanks), realistic constants (the proof's
constants are far from the simulated `≈ 4 n log n`), the generic supermartingale layer could move
to `dynamics/`.

## Errors

None outstanding. (Resolved during phase 2: Lean API renames such as `le_or_lt` → `le_or_gt` and
`div_add_div_same` → `add_div`, deprecated `push_neg`, a heartbeat timeout in `gap_event_le` fixed
by avoiding `set`.)

## Plan (phase 2, as executed; simpler than the paper's route, same ideas)

Only some constants are needed, so the four-region bookkeeping of [AAE08, §4] is replaced by six
weighted supermartingales, all instances of one generic lemma (`SequentialMartingale.lean`): if
`avg_p exp(φ s p) · F(step s p) ≤ F s` for all `s`, then
`E[exp(∑_path φ) · F(X_T)] ≤ F(X_0)`, hence (Markov) `P[∑_path φ ≥ L] ≤ F(X_0) e^{-L} / min F`.

Notation: counts `x, y, b`, `u = x - y`, `v = x + y`, `g = 1/(n(n-1))`; per-step indicators
`I_vb` (xb, yb), `I_xy` (xy, yx), `I_ch = I_vb + I_xy`; regions (`n ≥ 16`):
`R_b : 8v ≤ n`, `R_x : 8x ≥ 7n ∧ x < n`, `R_y` symmetric, `R_c : 8v > n ∧ 8x < 7n ∧ 8y < 7n`.

| bound | weight `φ` | potential `F` |
| --- | --- | --- |
| P1 state-changing steps (paper §4.4) | `(I_vb/5 - I_xy/6)/n` | `1/(u² + 4n)` |
| PC central steps (`P[change] ≥ 1/128`) | `(R_c - 256 I_ch)/256` | `1` |
| PB blank corner | `(5/(16n))(R_b - 64 I_xy)` | `1/v` |
| PX x corner | `(5/(32n))(R_x - 128 I_ch)` | `3y + b + 1` |
| PY y corner | symmetric | `3x + b + 1` |
| PM (Thm 2) `u` stays positive | `-(λ²/2) I_ch` | `exp(-λ max(u, 0))` |

Deterministic glue: `b_T - b_0 = S_xy - S_vb` (so `S_xy ≤ S_vb + n`); non-consensus is
absorbing backwards (not in consensus at `T` ⇒ all `T` steps were non-consensus steps);
`notCons ≤ R_c + R_b + R_x + R_y`. Off the six events (failure `≤ 9n e^{-L}` + `e^{-u₀²/(2N)}`):
`S_ch < N := 60nL + 11n` and `#non-consensus steps < 256L + 34576nL + 6336n`. Then
`L = (c+2) log n`, `λ = u₀/N`, `C = 40000(c+2) + 16^c` (small `n < 16` vacuous).
Proof-technique deviation: the paper's coupling + Azuma (§5) is replaced by PM (since
`P[u↑] - P[u↓] = g b u ≥ 0` while `u ≥ 0`, and `cosh λ ≤ exp(λ²/2)`).

## Deviations from the paper (and from the task text)

1. **Gap `√n · log n`, not `√(n log n)`.** The task text and ROADMAP row UND-2 say
   `C √(n log n)` / `ω(√(n log n))`. [AAE08, Thm 2 and abstract] assumes `ω(√n log n)`, and its
   proof (fair-walk coupling + Azuma over `Θ(n log n)` steps, whose fluctuation is
   `√(n log n · log n)`) cannot reach `√(n log n)`. We pin the paper's hypothesis. The
   `Ω(√(n log n))` threshold is a later result of Condon, Hajiaghayi, Kirkpatrick, Maňuch,
   *Approximate majority analyses using tri-molecular chemical reaction networks*, Natural
   Computing 2020 (their §1.4: "their [AAE] majority-consensus analysis assumes an initial gap of
   `√n lg n`, while ours is `√(n lg n)`"), for initial configurations *without blanks*
   (`x + y = n`), by a different route (emulating a tri-molecular CRN). Not pinned here;
   candidate follow-up row. The ROADMAP row's `ω(√(n log n))` should read `ω(√n log n)` for AAE08.
2. **`ω(·)` replaced by `C · (·)`** with `C` existential (depending on `c`). This implies the
   paper's `ω` form (a gap that is `ω(√n log n)` eventually exceeds `C √n log n`) and is what the
   paper's proof establishes.
3. **"With high probability" = for every `c : ℕ`, error `≤ C n^{-c}`.** [AAE08, Thm 1] says "for
   any fixed `c > 0`"; natural `c` loses nothing (`n^{-⌈c⌉} ≤ n^{-c}`). The explicit constants
   (`6769 n log n + 6773 c n log n + 2552 n`, error `5 n^{-c}`) and "sufficiently large `n`" are
   absorbed into `C` (small `n` become vacuous since `1 - C / n^c ≤ 0`).
4. **Time bound in the correctness theorem.** [AAE08, Thm 2] concludes eventual convergence to
   the majority; we conclude convergence to the majority within `C n log n` interactions, which
   is Thm 2 ∧ Thm 1 (exactly what the proof of Thm 2 shows, and what the task asks).
5. **Majority taken to be `x` (`Op.a`)**, without loss of generality by the `x ↔ y` symmetry of
   the protocol; the paper speaks of "the initial majority value".
6. **"Within `T` interactions" as "at every time `T ≥ C n log n`"**: equivalent because the
   consensus configurations are absorbing; `τ*` (first time `x = n` or `y = n`) is not defined.
7. **`2 ≤ n`**: an interaction needs two distinct agents (for `n ≤ 1` the interaction type is
   empty and `expList` would be `0`); the paper's statements are for sufficiently large `n`.
8. **Notation**: reuse of `Undecided.Op` with `x ↦ .a`, `y ↦ .b`, blank `b ↦ .u` (note that the
   letter `b` means opinion `y` in Lean but blank in the paper). The task's rules
   `B + X → X + X`, `B + Y → Y + Y` are unordered CRN notation (as in ROADMAP line 57); with the
   responder as the agent that changes, they are AAE's `(x, b) → (x, x)`, `(y, b) → (y, y)`,
   initiator first, which is what `step` implements.
9. **Probability model**: finite horizon, `T` i.i.d. uniform interactions via `Dynamics.expList`
   (the paper's filtration/stopping-time language is not used in the statements).
10. **Not covered**: the epidemic-triggered start (§6, Thm 3, gap `Ω(n^{3/4+ε})`), Byzantine
    agents (§7), more than two values (§8).

Proof-route deviations (the statements are unaffected):

11. **Potentials and constants.** P1 uses `1/(u² + 4n)` instead of the paper's `1/(u² + 2n)`
    (makes the `xy`-to-`vb` ratio `5/6 < 1` with simple constants); the central region is handled
    by a Bernoulli-type supermartingale (`P[change] ≥ 1/128` there) instead of [AAE08, Lemma 5];
    the corners use `8v ≤ n` and `8x ≥ 7n` as in Table 1, with our own weights. Constants are far
    larger than the paper's (`C = 40000(c+2) + 16^c`), which the `∃ C` statements allow.
12. **No stopping times.** Fixed horizon `T`; consensus is absorbing, so "not in consensus at `T`"
    means every one of the `T` interactions happened outside consensus, and the counters only
    count interactions in non-consensus regions (`XR` requires `x < n`).
13. **Theorem 2 via PM** instead of the coupling with a fair walk and Azuma (see the plan).
