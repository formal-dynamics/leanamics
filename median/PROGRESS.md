# Progress: `Median/ManyValues.lean` (fast consensus, odd case of Theorem 21)

## Status: done

- [x] `binary_consensus_fast` (C = 128)
- [x] `median_consensus_fast` (C = 128, via the theorem `binary_consensus_fast`)
- [x] `odd_split_consensus` (C' = 2C, via the theorem `median_consensus_fast`)

`lake build` is clean (no warnings), and `lake env lean Audit.lean` shows only `propext`,
`Classical.choice`, `Quot.sound` for the three theorems. No `set_option` is used anywhere.

## Spec gate: the header of `ManyValues.lean` must stay byte-identical

A first version added `import Median.ManyValuesMedian` (helper files). The spec gate rejects any
change to the `import`/`namespace`/`open`/`variable` lines, even an added import. So the final
version adds **nothing outside the three proof bodies**: `git diff` removes exactly the three
`sorry` lines, and the header and statements are byte-identical to the baseline. Everything is
proved by local `have`s inside the proofs (no helper files; `ManyValuesFast.lean` is unchanged
from `HEAD`, and its `quad_move` is re-proved inline). Only `Median.Basic` and `Median.Binary`
(and their imports) are available.

## Heartbeats (one declaration carries the whole binary development)

- A tactic-level `set_option maxHeartbeats N in` does **not** raise the per-declaration budget
  (tested), so each proof must fit in the default 200000.
- `#count_heartbeats in` is useless here: theorem proofs elaborate asynchronously (it reports
  only the statement), and with `Elab.async false` it ran for over 10 minutes. Measure instead by
  compiling scratch copies with `set_option maxHeartbeats L in` for several `L`.
- `nlinarith` was the cost: in the original `quad_move` six calls took about 8 s of 10 s
  (100k–150k heartbeats for that lemma alone). All `nlinarith` calls are replaced by `linarith`
  with the explicit product facts (`mul_le_mul_of_nonneg_left …`), and `linarith only [...]` is
  used in large contexts.
- Current costs: `binary_consensus_fast` 75k–100k, the other two below 75k.

## Structure of the proofs

### `binary_consensus_fast` (sections marked in the proof)
After `intro n _ hL` (with `x`, `Δ` introduced only before the growth segment, to keep the
`linarith` contexts small):
- (A) scalar facts: `β = 512 log n ≤ n/8`, `1/2 ≤ log 2 ≤ 1`, `hceil : w ≤ q ^ ⌈log w / log q⌉₊`.
- (B) kernel lemmas for `Median.kernel n Bool`: `hmono_set`; `hchain` (every state of `B i` moves
  into `B (i+1)` w.p. `≥ 1 - ε`, so `B T` after `T` rounds w.p. `≥ 1 - Tε`); `hcomp`
  (Markov property: compose two segments, add the failures).
- (C) `hquad` = `quad_move` (`m < t ≤ n/8 ⟹ m' < max (4t²/n) β` except w.p. `n⁻²`, Bernstein).
- (D) segments: linear saturation `hlin` (6 rounds, `n/4 → n/8`, `(7/8)^6 ≤ 1/2`); quadratic
  `hquadseg` (thresholds `q_j = (n/4)(1/2)^(2^j)`, `4 q_j²/n = q_{j+1}`); consensus `hcons`
  (`nested_phases`, `T = 2`, `ℓ = 4`, failure `10/n²`).
- (E) `T₃ = ⌈log (log n / log 2) / log 2⌉₊` with `q_T₃ ≤ β`, `T₃ ≤ 2 log log n + 3`; then
  `intro x Δ`, growth `hgrowth` (gap threshold `(5/4)^i Δ`), `T₁ = ⌈log (n/Δ) / log (5/4)⌉₊ + 1`
  with `n < (5/4)^T₁ Δ`, `T₁ ≤ 5 log (n/Δ) + 2`; composition, padding (`event_absorb_mono`) and
  budget: `T₁ + 6 + T₃ + 8 ≤ 128 (log (n/Δ) + log log n)` (`log log n ≥ 1`), failure
  `(T₁ + T₃ + 16)/n² ≤ 128/n`.

### `median_consensus_fast`
Same `C` as `binary_consensus_fast`, applied to `u ↦ decide (v ≤ x u)` (monotone,
`threshold_run`) and `u ↦ decide (x u ≤ v)` (antitone: `med3` commutes with antitone maps to
`Bool`, an 8-case check; `hrun_anti` by induction on the round list). The gaps are the two
hypotheses (`#{v ≤ x} + #{x < v} = n`). Both binary runs all-`true` force `run x l = const v`;
`1[y⁺] + 1[y⁻] ≤ 1[x] + 1` and linearity of `expList` give `1 - 2C/n`.

### `odd_split_consensus`
`C' = 2C` from `median_consensus_fast`. Counting fiber by fiber over the image
(`card_eq_sum_card_fiberwise`): `#{x < v} = k c`, `#{x ≤ v} = (k+1) c` with `c = n/(2k+1)`, so
both margins equal `c` (the hypothesis on `(univ.image x).card` is not needed), and
`log (n/c) = log (2k+1)`. Padding from `⌈C (…)⌉₊` to `⌈2C (…)⌉₊` rounds: `expList T F` is
nondecreasing in `T` for `F l = 1[run x l = const v]` (`expList_append`, `step_of_consensus`),
since `α` has no `Fintype` (no kernel).

## Log
- Session 1: all three proved with helper files imported into `ManyValues.lean`; rejected by the
  spec gate (added import line).
- Session 2: everything inlined into the three proof bodies; `nlinarith` removed for the heartbeat
  budget; helper files deleted, `ManyValuesFast.lean` restored to `HEAD`.
