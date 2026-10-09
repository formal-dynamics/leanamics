import Undecided.LowerBoundBasic

/-! # The `Ω(md(c))` lower bound (UND-3): the descent of the undecided (SODA 2015, Lemma 6)

[BCNPS15, Lemma 6]: let `k ≤ ε (n / log n)^{1/6}`. If after the first round
`n / (2R(c̄)²) ≤ c_m⁽¹⁾ ≤ 2n / R(c̄)²` and `n (1 - 2/Λ(c̄)) ≤ q⁽¹⁾ ≤ n (1 - 1/(2Λ(c̄)))`, then
within the next `O(log n)` rounds there is a round `t̄` with `C_m ≤ γ n / md(c̄)` and
`|Q - n/2| ≤ 2γ² n / md(c̄)` w.h.p., for a sufficiently large constant `γ`.

Its proof has two one-round steps, stated separately (with failure probability `C / n²`, so
that they can be iterated over `O(log n)` rounds):
* (16) `undecided_square`: from `q = (1 + δ) n/2` with `1 - δ ≥ 1/(2k)`, w.h.p.
  `Q' ≤ (1 + δ²) n/2` (the number of undecided nodes approaches `n/2` doubly exponentially);
* (17) `undecided_not_below`: if all colours are at most `γ n / D`, then w.h.p.
  `Q' ≥ n/2 - 2γ² n / D` (`Q` cannot jump over the window around `n/2`).

Corrections (see `PROGRESS-UND3.md`):
* the conclusion `|Q - n/2| ≤ 2γ² / md(c̄)` of the paper is a typo for `2γ² n / md(c̄)`;
* the proof of (17) uses `∑ⱼ cⱼ² = c₁² md(c̄)`, which mixes the current configuration and the
  initial one; the bound `∑ⱼ cⱼ² ≤ maxⱼ cⱼ · (n - q) ≤ maxⱼ cⱼ · n` gives (17) for every `γ ≥ 1`;
* the bound is kept for **every** colour (`maxCount`), not only the initial plurality;
* the round `t̄` is deterministic here (it depends only on `n`, `Λ(c̄)` and `md(c̄)`), and the
  colours stay below `γ n / md(c̄)` at **every** round up to `t̄`, not only at `t̄`: this is what
  the proof gives, and it is needed for the per-round form `lower_bound_whp` of Theorem 8 at
  times before `t̄` (when `md(c̄) ≪ log Λ(c̄)`);
* (16) is stated for every `δ` with `1 - δ ≥ 1/(2k)`, a larger range than the paper's
  `1/md(c̄) ≤ δ ≤ 1 - 1/(2Λ(c̄))` (as `Λ(c̄) ≤ k`).
-/

namespace Undecided.Plurality
open Finset Dynamics Real

/-- **Equation (16) of [BCNPS15]** (proof of Lemma 6): the undecided nodes approach `n/2`
doubly exponentially. There is `C > 0` such that, for every `n` with `log n ≥ C`, every `k` with
`C k ≤ (n / log n)^{1/6}`, every configuration `y` with `q = (1 + δ) n/2` and
`1 - δ ≥ 1/(2k)`, after one round, with probability at least `1 - C / n²`,
`Q' ≤ (1 + δ²) n/2`. -/
theorem undecided_square : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, C ≤ Real.log n →
    ∀ k : ℕ, C * k ≤ ((n : ℝ) / Real.log n) ^ ((1 : ℝ) / 6) →
    ∀ (y : Config n k) (δ : ℝ), und y = (1 + δ) * n / 2 → 1 / (2 * k) ≤ 1 - δ →
      miss {z | und z ≤ (1 + δ ^ 2) * n / 2} 1 y ≤ C / n ^ 2 := by
  sorry

/-- **Equation (17) of [BCNPS15]** (proof of Lemma 6, corrected): `Q` cannot jump below the
window around `n/2`. There is `C > 0` such that, for every `γ ≥ 1`, every `n` with
`log n ≥ C`, every `k` with `C k ≤ (n / log n)^{1/6}`, every `D ∈ (0, k]` and every
configuration `y` whose colours are all at most `γ n / D`, after one round, with probability at
least `1 - C / n²`, `Q' ≥ n/2 - 2γ² n / D`. -/
theorem undecided_not_below : ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ, 1 ≤ γ → ∀ n : ℕ, C ≤ Real.log n →
    ∀ k : ℕ, C * k ≤ ((n : ℝ) / Real.log n) ^ ((1 : ℝ) / 6) → ∀ D : ℝ, 0 < D → D ≤ k →
    ∀ y : Config n k, (maxCount y : ℝ) ≤ γ * n / D →
      miss {z | (n : ℝ) / 2 - 2 * γ ^ 2 * n / D ≤ und z} 1 y ≤ C / n ^ 2 := by
  sorry

/-- **Lemma 6 of [BCNPS15]** (descent of the undecided, corrected). There are `γ ≥ 1` and
`C > 0` such that, for every `n` with `log n ≥ C`, every `k` with `C k ≤ (n / log n)^{1/6}`,
every initial configuration `x` without undecided nodes and with `md(x) ≥ C`, and every
configuration `y` as after the first round (Lemma 3: all colours at most `2n / R(x)²`, and
`n (1 - 2/Λ(x)) ≤ q ≤ n (1 - 1/(2Λ(x)))`), there is a round `t ≤ C log n` such that, with
probability at least `1 - C / n` each: at every round `s ≤ t` all colours are at most
`γ n / md(x)`; and at round `t` moreover `|q - n/2| ≤ 2γ² n / md(x)`. -/
theorem descent : ∃ γ C : ℝ, 1 ≤ γ ∧ 0 < C ∧ ∀ n : ℕ, C ≤ Real.log n →
    ∀ k : ℕ, C * k ≤ ((n : ℝ) / Real.log n) ^ ((1 : ℝ) / 6) →
    ∀ x : Config n k, count x none = 0 → C ≤ md x →
    ∀ y : Config n k, (maxCount y : ℝ) ≤ 2 * n / ratioR x ^ 2 →
      n * (1 - 2 / ratioLam x) ≤ und y → und y ≤ n * (1 - 1 / (2 * ratioLam x)) →
      ∃ t : ℕ, (t : ℝ) ≤ C * Real.log n ∧
        (∀ s ≤ t, miss {z | (maxCount z : ℝ) ≤ γ * n / md x} s y ≤ C / n) ∧
        miss {z | (maxCount z : ℝ) ≤ γ * n / md x ∧
          |und z - n / 2| ≤ 2 * γ ^ 2 * n / md x} t y ≤ C / n := by
  sorry

end Undecided.Plurality
