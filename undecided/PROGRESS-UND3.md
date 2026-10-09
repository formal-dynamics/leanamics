# UND-3, remaining part: the `Ω(md(c))` lower bound (SODA 2015, Theorem 8)

Source: L. Becchetti, A. Clementi, E. Natale, F. Pasquale, R. Silvestri, *Plurality consensus in
the gossip model*, SODA 2015, arXiv:1407.2565 (v2) [BCNPS15]. Lemmas and theorems share one
counter: Lemma 3 (first round), Lemma 6 (descent of the undecided), Lemma 7 (plateau),
Theorem 8 (lower bound); equations (16), (17) (proof of Lemma 6), (19), (20) (proof of Lemma 7).
The paper writes `Λ(c) = R(c)² / md(c)` (Section 2.1).

## Status

All six pinned statements are proved. `lake build Undecided` succeeds with no warnings, and
`python3 ../scripts/check_axioms.py` reports only `propext`, `Classical.choice`, and `Quot.sound`.
The two forms of Theorem 8 (`lower_bound_whp`, `lower_bound_consensus`) are proved from Lemmas 3, 6
and 7 (file `Undecided/LowerBound.lean`).

| declaration | file | status |
| --- | --- | --- |
| `first_round` (Lemma 3) | `LowerBoundFirst.lean` | proved (`C = 100`) |
| `undecided_square` ((16)) | `LowerBoundDescent.lean` | proved (`C = 8`) |
| `undecided_not_below` ((17)) | `LowerBoundDescent.lean` | proved (`C = 8`, independent of `γ`) |
| `descent` (Lemma 6) | `LowerBoundDescent.lean` | proved (witness `γ = 24`, `C = 1000000`; envelope in `LowerBoundDescentCore.lean`) |
| `plateau_step` (proof of Lemma 7) | `LowerBoundPlateau.lean` | proved (`C = 16 γ²`) |
| `plateau` (Lemma 7) | `LowerBoundPlateau.lean` | proved (`C = C_step + 14 γ²`) |
| `lower_bound_whp`, `lower_bound_consensus` (Thm 8) | `LowerBound.lean` | proved from the above |
| `ratioR`, `ratioLam` and their basic facts | `LowerBoundBasic.lean` | proved |

Helper files (no pinned statements): `LowerBoundArith.lean` (range and exponential inequalities),
`LowerBoundRound.lean` (one-round deterministic cores `first_of_good`, `square_of_good`,
`not_below_of_good`, and `miss_round_le`), `LowerBoundDescentCore.lean` (`descentGrowth`,
`descent_step_of_good`, `descentGrowth_phaseA`, `descentGrowth_phaseB`, `envelope_le`). No `sorry`
remains.

## The pinned statements in words

Notation: `x` is a configuration of `n` nodes with `k` colours (`Config n k`), `cᵢ` its colour
counts, `q` its undecided count (`und`), `maxCount = maxᵢ cᵢ`, `md` the monochromatic distance,
`R = ∑ᵢ cᵢ / maxᵢ cᵢ` (`ratioR`), `Λ = R² / md` (`ratioLam`); `miss S T x` is the probability of
not being in `S` after `T` rounds from `x`. All constants are existential (`∃ C`), "w.h.p." is
`1 - C/n` (one-round steps: `1 - C/n²`), and the range of `k` is `C k ≤ (n / log n)^{a}` with
the paper's exponent `a`.

* **Basic facts** (`LowerBoundBasic.lean`, proved): `md ≤ R ≤ k`, the paper's (2) `Λ ≤ k`,
  `md ≤ Λ`; without undecided nodes `R = n / maxᵢ cᵢ` and `Λ = n² / ∑ᵢ cᵢ²`; the paper's (20)
  `µᵢ = (1 + (2δ + cᵢ)/n) cᵢ` and (19) `E[Q' - n/2] = (2δ² - ∑ⱼ cⱼ²)/n`, with `δ = q - n/2`.
* **`first_round`** (Lemma 3; `a = 1/2`): from `x` without undecided nodes and a plurality
  colour `m`, after one round, w.h.p., `c_m ≥ n/(2R²)`, every colour is at most `2n/R²`, and
  `n(1 - 2/Λ) ≤ q ≤ n(1 - 1/(2Λ))` (`R`, `Λ` of `x`).
* **`undecided_square`** ((16); `a = 1/6`): if `q = (1 + δ)n/2` and `1 - δ ≥ 1/(2k)`, then after
  one round `Q' ≤ (1 + δ²) n/2` with probability `≥ 1 - C/n²`.
* **`undecided_not_below`** ((17), corrected; `a = 1/6`): for every `γ ≥ 1` and `D ∈ (0, k]`, if
  every colour is at most `γ n/D`, then after one round `Q' ≥ n/2 - 2γ² n/D` with probability
  `≥ 1 - C/n²` (`C` does not depend on `γ`).
* **`descent`** (Lemma 6, corrected; `a = 1/6`): there are `γ ≥ 1` and `C` such that, for `x`
  without undecided nodes with `md(x) ≥ C` and `y` satisfying the conclusion of Lemma 3 (every
  colour at most `2n/R(x)²`, `n(1 - 2/Λ(x)) ≤ q ≤ n(1 - 1/(2Λ(x)))`), there is a round
  `t ≤ C log n` such that, w.h.p., every colour stays at most `γ n/md(x)` at each round `s ≤ t`,
  and at round `t` moreover `|q - n/2| ≤ 2γ² n/md(x)`.
* **`plateau_step`** (one round of Lemma 7, corrected; `a = 1/4`): for every `γ ≥ 1` there is
  `C` such that, if `C ≤ D ≤ k`, `|q - n/2| ≤ 2γ² n/D` and every colour is at most
  `B ∈ [γ n/D, 2γ n/D]`, then after one round, with probability `≥ 1 - C/n²`, every colour is at
  most `(1 + (4γ² + 2γ + 1)/D) B` and still `|q - n/2| ≤ 2γ² n/D`.
* **`plateau`** (Lemma 7, corrected; `a = 1/4`): for every `γ ≥ 1` there is `C` such that, if
  `C ≤ D ≤ k`, `|q - n/2| ≤ 2γ² n/D` and every colour is at most `γ n/D`, then for every
  `T ≤ D/C`, after `T` rounds, w.h.p., every colour is at most `2γ n/D` and
  `|q - n/2| ≤ 2γ² n/D`.
* **`lower_bound_whp`** (Theorem 8; `a = 1/6`): for `x` without undecided nodes and every
  `T ≤ md(x)/C`, after `T` rounds, w.h.p., every colour is at most `C n/md(x)`.
* **`lower_bound_consensus`** (Theorem 8, convergence time; `a = 1/6`): for `x` without
  undecided nodes and every `T` with `C(T + 1) ≤ md(x)`, the probability that all nodes hold the
  same colour after `T` rounds is at most `C/n` (consensus is absorbing, so this is the
  probability of converging within `T` rounds).

## Deviations from the source

1. **Explicit "w.h.p.", `O`, `Ω`, `o`, "sufficiently small `ε`"**: one existential constant `C`
   per statement: `log n ≥ C`, `C k ≤ (n / log n)^{a}` with the paper's exponent `a`
   (`1/2` for `k = o(√(n/log n))` in Lemma 3, `1/4` in Lemma 7, `1/6` in Lemma 6 and Theorem 8),
   failure probability `C/n`, `T ≤ md/C` rounds for `Ω(md)`. The one-round steps (16), (17) and
   the step of Lemma 7 are stated with failure `C/n²` (true, since a bad round has probability
   `(k + 4)/n³` at deviation level `3 log n`), so that they can be iterated over `O(log n)`
   (respectively `O(md) ≤ n`) rounds.
2. **All colours, not only the plurality.** The lower bound needs that *no* colour reaches all
   nodes. The paper tracks `C₁` only, but its arguments use properties of the largest colour
   (`∑ⱼ cⱼ² ≤ c₁ (n - q)`, `c₁ ≥ (n - q)/k`), and another colour may overtake the initial
   plurality when there is no bias. All upper bounds are stated for `maxCount`. Lemma 3 also
   keeps the paper's lower bound for the plurality colour `m`.
3. **Theorem 8, form of the conclusion.** "The convergence time is `Ω(md(c̄))` w.h.p." becomes
   (a) `lower_bound_whp`: at every round `T ≤ md(x)/C`, w.h.p. no colour exceeds `C n/md(x)`
   nodes (what the proof shows), and (b) `lower_bound_consensus`: if `C(T + 1) ≤ md(x)`, the
   probability of being in a monochromatic configuration after `T` rounds is at most `C/n`.
   The `+ 1` excludes `T = 0` with `md(x) < C` (for instance a monochromatic `x`). Convergence
   means: all nodes hold the same colour (the target of Section 2); the all-undecided
   configuration, also absorbing, is not counted as convergence.
4. **Initial configurations without undecided nodes** (`count x none = 0`), as in the paper
   (Section 2.1: "In the initial state we always have `q⁽⁰⁾ = 0`"). No bias is assumed, as in
   the paper.
5. **Lemma 6: deterministic round, all rounds before it.** The paper says that w.h.p. there is a
   round `t̄ = O(log n)` with `C₁ ≤ γn/md` and `|Q - n/2| ≤ 2γ²/md`. Corrections and changes:
   * `2γ²/md(c̄)` is a typo for `2γ² n/md(c̄)` (also in the proof of Theorem 8);
   * the round `t` is deterministic (it depends on `n`, `Λ(c̄)`, `md(c̄)`; the proof gives the
     first `s` with `(1 - 1/Λ)^{2^s} ≤ 4γ²/md`), and the bound `γ n/md` on the colours holds at
     every round `s ≤ t`, not only at `t`. This is what the proof shows, and the per-round form
     `lower_bound_whp` needs it: when `md(c̄) ≪ log Λ(c̄)`, some rounds `T ≤ md/C` lie before `t̄`.
     (For the convergence time itself the paper's composition is fine: at `t̄` there are
     `≈ n/2` undecided nodes, so the process has not converged before `t̄`, consensus being
     absorbing.) It also avoids a random round `t̄` (a stopping time) in the composition.
   * (16) is stated for every `δ` with `1 - δ ≥ 1/(2k)` (also `δ < 1/md(c̄)`, possibly negative),
     which contains the paper's range `1/md(c̄) ≤ δ ≤ 1 - 1/(2Λ(c̄))` since `Λ ≤ k`; the
     paper's computation holds verbatim on the larger range.
6. **(17) needs a minor correction.** The paper's proof writes `∑ⱼ cⱼ² = c₁² md(c̄)`, with the
   monochromatic distance of the *initial* configuration instead of the current one. The bound
   `∑ⱼ cⱼ² ≤ (maxⱼ cⱼ)(n - q) ≤ γ n²/md` gives `E[Q'] ≥ n/2 - γ n/md` and the statement for
   every `γ ≥ 1`.
7. **Lemma 7 needs minor corrections.**
   * Growth factor `1 + (4γ² + 2γ + 1)/md` instead of `1 + (2γ(γ + 1) + 1)/md`: with
     `|δ| ≤ 2γ² n/md`, the term `2δ/n` of (20) is at most `4γ²/md`, not `2γ²/md`. The number of
     rounds changes accordingly (still `Ω(md)`).
   * The lower bound `E[Δ'] ≥ -(4/9) n/md` uses `∑ⱼ cⱼ² ≤ k ((n - q)/k)²`, which is the wrong
     direction (Cauchy–Schwarz gives `≥`). With `∑ⱼ cⱼ² ≤ (maxⱼ cⱼ)(n - q) ≤ (2γ n/md)(2n/3)`
     one gets `E[Δ'] ≥ -(4γ/3) n/md`, which stays inside the window `-2γ² n/md` for `γ ≥ 1`.
     The lemma is stated for `γ ≥ 1` instead of "an arbitrary positive constant `γ`": the proof's
     invariant (the window `|Δ| ≤ 2γ² n/md`, which is part of the formal conclusion) is not
     preserved for `γ < 1/2`, since from `q = n/2` and many colours of size `2γ n/md` one gets
     `E[Δ'] = -γ n/md < -2γ² n/md`. Whether the paper's conclusion (which bounds only `C_m`) holds
     for small `γ` is left open; Theorem 8 only needs one large `γ`.
   * `md(c̄)` is a real parameter `D` with `C ≤ D ≤ k`; the paper assumes `md(c̄) ≥ 8γ²`, a
     "sufficiently large constant".
8. **Lemma 3** is stated with the same constant `C` for the range `C k ≤ (n / log n)^{1/2}`
   (the paper: `k = o(√(n / log n))`), which is what its Chernoff bounds need
   (`E[C_m'] = n/R² ≥ n/k² ≥ C² log n`).
9. **Lemma 4** (`R(C⁽¹⁾) ≤ md(c̄)(1 + o(1))`) is not used by the lower bound and is not pinned.
10. **Model**: as for `plurality_whp` (sampling with replacement, possibly oneself; finite
    probability via `expList`); `k` is the size of the palette (colours may be absent).

## Errors in the source (summary)

* Lemma 6 / Theorem 8: `|Q - n/2| ≤ 2γ²/md(c̄)` should read `2γ² n/md(c̄)` (typo).
* Proof of Lemma 6, before (17): `∑ⱼ cⱼ² = c₁² md(c̄)` uses the initial instead of the current
  monochromatic distance; needs a minor correction (bound by `maxⱼ cⱼ (n - q)`).
* Proof of Lemma 7: the factor `2γ(γ + 1)` should be `2γ(2γ + 1)` (from `2|δ| ≤ 4γ² n/md`); the
  lower bound on `E[Δ']` bounds `∑ⱼ cⱼ²` in the wrong direction; the proof's window invariant
  needs `γ > 1/2` (stated here for `γ ≥ 1`), not an arbitrary `γ > 0`. Minor corrections.
* Lemmas 6 and 7 bound only the initial plurality `C₁`, whereas the argument (and the lower bound)
  needs the largest colour at each round. Minor correction.

Not an error, but a change of form: Lemma 6 is stated with a deterministic round and a colour bound
at every round before it, which the per-round form `lower_bound_whp` of Theorem 8 needs (the
paper's composition is sufficient for the convergence time, by absorption).

## How the proofs are organised

Every one-round statement follows from the good event `Good ℓ m y z` of `PluralityRound.lean`
with `ℓ = 3 log n` (`round_le`, `bad_le`: a bad round has probability `(k + 4)/n³`), by a
deterministic lemma on a good round. `plateau` and `descent` use `Dynamics.expList_escape` with
moving targets. In `descent` the colour envelope is the recursion `descentGrowth` (phase A at most
`8n/D`, phase B at most `γ n/D` with `γ = 24`), and the undecided count tracks
`max((1 - 1/Λ)^{2^s}, 4γ²/D)` until that quantity hits the window `4γ²/D`.
