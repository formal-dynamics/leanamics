# Progress: FND-3, Chernoff bounds for independent, non-identical Bernoulli(pᵢ)

## Status: done (phase 2 complete, all pinned statements proved)

- `lake build Dynamics` (in `dynamics/`) succeeds with **no warnings**.
- No `sorry`/`admit`/`axiom`/`native_decide`/`implemented_by`/`extern`/`set_option` in
  `Dynamics/Chernoff*.lean`.
- Axioms: `#print axioms` on all 13 pinned declarations (scratch file in `/tmp`) gives only
  `propext`, `Classical.choice`, `Quot.sound`; `python3 ../scripts/check_axioms.py` (the
  12 theorems are now listed in `Audit.lean`) reports "Checked 24 declarations: only standard
  Lean axioms."
- Pinned texts: a script compared every declaration of `PINNED.txt`, from its keyword up to
  its first `:=`, against both the phase-1 snapshot and `HEAD`: all identical.

**Source.** M. Mitzenmacher, E. Upfal, *Probability and Computing*, CUP 2005, §4.2.1:
Theorem 4.4 bound (4.1) (upper tail, ratio form, `δ > 0`), Theorem 4.5 bounds (4.4) (lower
tail, ratio form) and (4.5) (`e^{-μδ²/2}`), both for `0 < δ < 1`, and Exercise 4.7 (any
`μ_L ≤ μ ≤ μ_H` may replace `μ`, with non-strict `≤`). Checked against the book text.

## Files

- `Dynamics/Chernoff.lean` (251 lines): the pinned definition `Distribution.bernoulli`, the
  12 pinned theorems (each a short corollary of the helpers), and two unpinned Bernoulli
  lemmas placed after the definition they need: `bernoulli_expect`
  (`𝔼 f = p f(true) + (1-p) f(false)`) and `sum_bernoulli_expect` (the head count over `S`
  has mean `∑_{i∈S} pᵢ`).
- `Dynamics/ChernoffAux.lean` (269 lines): all reusable machinery (list below).
- `Dynamics.lean`: imports `Dynamics.Chernoff`.
- `Audit.lean`: `#print axioms` for the 12 theorems.
- `blueprint/src/content.tex`: theorem `thm:chernoff` with `\lean{}` tags for the 13
  pinned declarations (`\leanok`), in "Rounds, concentration and phases".
- `README.md`: module-table row for `Chernoff`; the remark that the Chernoff bounds live only
  in 3-majority is updated.
- `PINNED.txt` (repository root): unchanged.

## Pinned (13 declarations, all in `dynamics/Dynamics/Chernoff.lean`), all proved

Notation: `X ω = ∑ i, Y i (ω i)`, `Y i ∈ {0,1}`; `δ > 0` (upper), `0 < δ < 1` (lower).

| Declaration | Setting | Statement |
|---|---|---|
| `Distribution.bernoulli p h0 h1` | def | `Distribution Bool`, weight `if b then p else 1 - p` |
| `Distribution.chernoff_upper_ratio` | `independent P` | `∑ᵢ (P i).expect (Y i) ≤ μH →` `P(X ≥ (1+δ)μH) ≤ (e^δ/(1+δ)^(1+δ))^μH` |
| `Distribution.chernoff_upper` | `independent P` | same hyp. `→ ≤ exp (-(δ²μH/(2+δ)))` |
| `Distribution.chernoff_lower_ratio` | `independent P` | `μL ≤ ∑ᵢ (P i).expect (Y i) →` `P(X ≤ (1-δ)μL) ≤ (e^(-δ)/(1-δ)^(1-δ))^μL` |
| `Distribution.chernoff_lower` | `independent P` | same hyp. `→ ≤ exp (-(δ²μL/2))` |
| `Distribution.bernoulli_chernoff_upper_ratio` | coins `bernoulli (p i)`, heads in `S` | `∑_{i∈S} p i ≤ μH →` ratio bound |
| `Distribution.bernoulli_chernoff_upper` | idem | `→ exp (-(δ²μH/(2+δ)))` |
| `Distribution.bernoulli_chernoff_lower_ratio` | idem | `μL ≤ ∑_{i∈S} p i →` ratio bound |
| `Distribution.bernoulli_chernoff_lower` | idem | `→ exp (-(δ²μL/2))` |
| `avg_chernoff_upper_ratio` | uniform `ω : ι → γ`, `avg` of indicator | `∑ᵢ avg (Y i) ≤ μH →` ratio |
| `avg_chernoff_upper` | idem | `→ exp (-(δ²μH/(2+δ)))` |
| `avg_chernoff_lower_ratio` | idem | `μL ≤ ∑ᵢ avg (Y i) →` ratio |
| `avg_chernoff_lower` | idem | `→ exp (-(δ²μL/2))` |

## Proof structure and reusable lemmas (`ChernoffAux.lean`)

Scalar (namespace `Dynamics`):
- `two_mul_div_two_add_le_log_one_add`: `2δ/(2+δ) ≤ log (1+δ)` for `δ ≥ 0`, as the first term
  of Mathlib's `hasSum_log_sub_log_of_abs_lt_one` at `x = δ/(2+δ)` (`le_hasSum`).
- `half_sub_inv_le_log_of_le_one`, `neg_add_sq_div_two_le_one_sub_mul_log`:
  `(1-δ) log (1-δ) ≥ -δ + δ²/2` (copied from `Plurality.half_sub_inv_le_log` /
  `one_sub_mul_log_one_sub_ge`; `dynamics/` cannot import `plurality/`).
- `sub_one_add_mul_log_le`, `neg_sub_one_sub_mul_log_le`: the exponents of the ratio forms
  are `≤ -δ²/(2+δ)` resp. `≤ -δ²/2`.
- `exp_div_rpow_self_rpow`: `(e^c / a^a)^μ = exp (μ (c - a log a))` for `a > 0`.

Probability (namespace `Dynamics.Distribution`):
- `prob_le_expect_exp`: Markov for `exp (t X)` on any `Distribution`, for any event that
  forces `t k ≤ t X` (covers both tails and both signs of `t`).
- `independent_expect_exp_sum`: the mgf factors over `independent` (from
  `independent_expect_prod`).
- `expect_exp_mul_le`: one `{0,1}` trial, `𝔼 e^{tY} ≤ exp (𝔼Y (eᵗ - 1))`.
- `independent_expect_exp_sum_le`: `𝔼 exp (t X) ≤ exp (μ (eᵗ - 1))` for all real `t`.
- `sum_expect_nonneg`: `μ ≥ 0`.
- `prob_ge_le_exp` / `prob_le_le_exp`: `P(X ≥ k) ≤ exp (μH (eᵗ-1) - t k)` for `t ≥ 0`,
  `P(X ≤ k) ≤ exp (μL (eᵗ-1) - t k)` for `t ≤ 0` (Exercise 4.7 is built in here).
- `sum_ite_mem_ite_eq_card`: the head count over `S` as a sum of `{0,1}` coordinates.
- `independent_expect_eq_avg`: an independent product of uniform-weight factors is the
  uniform average over `ι → γ`.
- `avg_indicator_le_of_independent` (namespace `Dynamics`): transfers any bound proved for
  all uniform-factor `independent` products to `avg` of an indicator over `ι → γ`, including
  the corner cases `IsEmpty (ι → γ)` and `IsEmpty γ ∧ IsEmpty ι` (so the `avg` theorems need
  no `Nonempty γ`).

Main theorems: ratio forms take `t = log (1+δ)` resp. `t = log (1-δ)` in
`prob_ge_le_exp`/`prob_le_le_exp` and rewrite with `exp_log`, `exp_div_rpow_self_rpow`,
`ring`; closed forms multiply the scalar exponent bounds by `μH ≥ 0` (from
`sum_expect_nonneg`) resp. `μL ≥ 0`, and for `μL < 0` use `prob_le_one` (the bound exceeds
`1`). Bernoulli forms apply the general ones to
`Y i b = if i ∈ S then (if b = true then 1 else 0) else 0`. Uniform forms apply
`avg_indicator_le_of_independent` to the general ones.

## Remaining

Nothing in this job. Suggested follow-ups outside `dynamics/` (not allowed in this job):
mark FND-3 done in `ROADMAP.md` and add a `PROVENANCE.md` entry; switch `epidemics/` to
`Distribution.bernoulli` (identical to `Epidemics.bernoulli`); optionally replace
`Plurality.half_sub_inv_le_log`/`one_sub_mul_log_one_sub_ge` and the 3-majority mean-scaled
tails by the shared versions.

## Errors encountered (all fixed)

- `lake env lean Dynamics/Chernoff.lean` used a stale `.olean` of `ChernoffAux`: run
  `lake build Dynamics.ChernoffAux` first.
- `rw [← Fintype.sum_ite_mem]` without arguments rewrote the wrong sum; give `S p`.
- `log_nonneg (by linarith)` needs the argument type ascribed.
- `expect` is ambiguous with `Finset.expect` outside `namespace Distribution`.

## Deviations from the source

1. **`≤` instead of `<` in (4.1).** M&U state the ratio upper tail with strict `<`; it fails
   when `μ = 0` (both sides equal `1`). Exercise 4.7 itself uses `≤`. All pinned bounds are
   non-strict.
2. **Closed upper form `exp (-δ²μH/(2+δ))` for all `δ > 0`** (requested by the roadmap
   prompt) instead of Theorem 4.4 (4.2), `e^{-δ²μ/3}` for `0 < δ ≤ 1`. It is stronger
   (`2 + δ ≤ 3` on that range) and is the standard consequence of (4.1) via
   `log (1+δ) ≥ 2δ/(2+δ)`. (4.2), (4.3) (`R ≥ 6μ ⇒ 2^{-R}`) and Corollary 4.6 (two-sided) are
   not pinned: not requested, and they are one-line corollaries that can be added unpinned.
3. **Finite model of the trials.** "Independent Poisson trials with `Pr(Xᵢ = 1) = pᵢ`" is
   modelled on the finite product `Distribution.independent P : Distribution (ι → α)` (the
   existing product of `dynamics/`) with `Xᵢ = Y i (ω i)`, `Y i` `{0,1}`-valued and
   `pᵢ = (P i).expect (Y i)`; `μ` is written `∑ᵢ pᵢ` (equal to `𝔼X`) rather than `𝔼X`. The
   coordinate type `α` is common to all trials, as in `Distribution.independent`;
   non-identical trials come from different `P i` and `Y i`. Probabilities are
   `Distribution.prob` of a `Prop` (or `avg` of an indicator in the uniform-round form).
4. **Exercise 4.7 is built in.** Every bound is stated for `μH ≥ μ` (upper) or `μL ≤ μ`
   (lower); the exact-mean statements of Theorems 4.4/4.5 are the case `le_rfl`. No sign
   condition on `μH`/`μL` is needed (as in the exercise); `μL < 0` makes the event empty.
5. **Subsets of coins.** The Bernoulli forms count heads over any `S : Finset ι`
   (`S = univ` is the textbook statement). Generalization motivated by EPI-2/EPI-3, which
   count open edges among a subset of the pairs of identical coins `Epidemics.coins`.
6. **Three settings** (general, Bernoulli coins, uniform rounds `avg` over `ι → γ`), the last
   so that packages can apply the bounds to one round (`Kernel.prob_ofStep`) and as a
   drop-in for `ThreeMajority.avg_tail_*` / `Plurality.chernoff_lower` (the latter also
   allows `δ = 0`, trivially). The `avg` forms need no `Nonempty γ`.
7. **New definition `Distribution.bernoulli`** duplicates `Epidemics.bernoulli` (identical
   signature and body, so the two are interchangeable); switching `epidemics/` to the shared
   one is left to a follow-up outside this job's scope. No other definition is introduced
   (expectation, probability, product and averages are the existing `dynamics/` API).
8. `δ` ranges are the source's: `δ > 0` (upper), `0 < δ < 1` (lower).
9. **Proof route** is the textbook one (Markov on `e^{tX}`, `1 + x ≤ eˣ` per trial,
   `t = log (1 ± δ)`); the only non-textbook step is the series proof of
   `log (1+δ) ≥ 2δ/(2+δ)`.
