import Mathlib

/-! # Deterministic one-round inequalities for the majority phase (UND-1)

Plain real arithmetic behind the phases of `Undecided.majority_whp`. Here `A`, `B`, `Q` are the
numbers of `a`-, `b`- and undecided nodes (`A + B + Q = n`), and `A'`, `B'`, `Q'` the numbers
after a *good* round, i.e. within `Λ` of the exact expectations
`A (n - B + Q)/n`, `B (n - A + Q)/n`, `(Q² + 2AB)/n` (Clementi et al., MFCS 2018, (1)–(3)).

* `bias_next`: the bias grows by the factor `1 + Q/n`, up to `2Λ`.
* `undec_next`: the undecided nodes are at least `n/3 - (A - B)²/(2n)`, up to `Λ`
  (Clementi et al., (4)).
* `contract`: the potential `12B + Q` contracts by `5/6` in expectation once
  `B + 2Q ≤ 2n/3` and `Q ≤ n/3`.
* `first_det`, `growth_det`, `bridge_det`, `fin_det`: one good round in each phase.
-/

namespace Undecided

/-- The bias after a good round: `A' - B' > (A - B)(1 + Q/n) - 2Λ`. -/
lemma bias_next {n A B Q A' B' Λ : ℝ} (hn : 0 < n)
    (ha : A * (n - B + Q) / n < A' + Λ) (hb : B' < B * (n - A + Q) / n + Λ) :
    (A - B) * (1 + Q / n) - 2 * Λ < A' - B' := by
  have h : A * (n - B + Q) / n - B * (n - A + Q) / n = (A - B) * (1 + Q / n) := by
    field_simp
    ring
  linarith

/-- The undecided nodes after a good round: `Q' > n/3 - (A - B)²/(2n) - Λ`, since
`(Q² + 2AB)/n - n/3 + (A - B)²/(2n) = 3 (Q - n/3)²/(2n)`. -/
lemma undec_next {n A B Q Q' Λ : ℝ} (hn : 0 < n) (hsum : A + B + Q = n)
    (hq : (Q ^ 2 + 2 * A * B) / n < Q' + Λ) :
    n / 3 - (A - B) ^ 2 / (2 * n) - Λ < Q' := by
  have hA : A = n - B - Q := by linarith
  subst hA
  have h : (Q ^ 2 + 2 * (n - B - Q) * B) / n - (n / 3 - (n - B - Q - B) ^ 2 / (2 * n))
      = 3 * (Q - n / 3) ^ 2 / (2 * n) := by
    field_simp
    ring
  have : 0 ≤ 3 * (Q - n / 3) ^ 2 / (2 * n) := by positivity
  linarith

/-- **Contraction** of `12B + Q` in expectation, when `B + 2Q ≤ 2n/3` and `Q ≤ n/3`. -/
lemma contract {n A B Q : ℝ} (hn : 0 < n) (hB : 0 ≤ B) (hQ : 0 ≤ Q)
    (hsum : A + B + Q = n) (h1 : B + 2 * Q ≤ 2 * n / 3) (h2 : Q ≤ n / 3) :
    12 * (B * (n - A + Q) / n) + (Q ^ 2 + 2 * A * B) / n ≤ 5 / 6 * (12 * B + Q) := by
  have e : n - A + Q = B + 2 * Q := by linarith
  rw [e]
  have hAn : A ≤ n := by linarith
  have k1 : B * (B + 2 * Q) ≤ B * (2 * n / 3) := mul_le_mul_of_nonneg_left h1 hB
  have k2 : Q * Q ≤ Q * (n / 3) := mul_le_mul_of_nonneg_left h2 hQ
  have k3 : A * B ≤ n * B := mul_le_mul_of_nonneg_right hAn hB
  have k4 : 0 ≤ Q * n := mul_nonneg hQ hn.le
  have e2 : 12 * (B * (B + 2 * Q) / n) + (Q ^ 2 + 2 * A * B) / n
      = (12 * (B * (B + 2 * Q)) + Q * Q + 2 * (A * B)) / n := by ring
  rw [e2, div_le_iff₀ hn]
  nlinarith [k1, k2, k3, k4]

/-- A nonnegative bias does not decrease by the factor `1 + Q/n`. -/
lemma le_mul_one_add {n S Q : ℝ} (hn : 0 < n) (hS : 0 ≤ S) (hQ : 0 ≤ Q) :
    S ≤ S * (1 + Q / n) := by
  have : 0 ≤ S * (Q / n) := mul_nonneg hS (div_nonneg hQ hn.le)
  nlinarith

/-- If the bias is at most `4n/5`, a good round leaves at least `n/100` undecided nodes. -/
lemma undec_of_le {n A B Q Q' Λ : ℝ} (hn : 0 < n) (hΛn : 300 * Λ ≤ n)
    (hsum : A + B + Q = n) (hS0 : 0 ≤ A - B) (h45 : A - B ≤ 4 * n / 5)
    (hq : (Q ^ 2 + 2 * A * B) / n < Q' + Λ) : n / 100 ≤ Q' := by
  have hQ' := undec_next hn hsum hq
  have hsq : (A - B) ^ 2 ≤ (4 * n / 5) ^ 2 := pow_le_pow_left₀ hS0 h45 2
  have : (A - B) ^ 2 / (2 * n) ≤ 8 * n / 25 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  linarith

/-- **First round.** From a bias of at least `402Λ`, a good round gives a bias of at least
`400Λ`, and either `n/100` undecided nodes or a bias of at least `400Λ + n/20`. -/
lemma first_det {n A B Q A' B' Q' Λ : ℝ} (hn : 0 < n) (hΛ : 0 ≤ Λ) (hΛn : 2000 * Λ ≤ n)
    (hQ : 0 ≤ Q) (hsum : A + B + Q = n) (hS : 402 * Λ ≤ A - B)
    (ha : A * (n - B + Q) / n < A' + Λ) (hb : B' < B * (n - A + Q) / n + Λ)
    (hq : (Q ^ 2 + 2 * A * B) / n < Q' + Λ) :
    400 * Λ ≤ A' - B' ∧ (n / 100 ≤ Q' ∨ 400 * Λ + n / 20 ≤ A' - B') := by
  have hS' := bias_next hn ha hb
  have hS0 : 0 ≤ A - B := le_trans (by linarith) hS
  have hm := le_mul_one_add hn hS0 hQ
  refine ⟨by linarith, ?_⟩
  by_cases h45 : A - B ≤ 4 * n / 5
  · exact Or.inl (undec_of_le hn (by linarith) hsum hS0 h45 hq)
  · right
    linarith

/-- **Growth round** (Clementi et al., phase `H4`/`H5`/`H7` → `H4`/`H6`). If the bias is at
least `g ∈ [400Λ, 7n/10]` and there are `n/100` undecided nodes or the bias exceeds
`g + n/20`, then after a good round the same holds with `g` replaced by
`min (201g/200) (7n/10)`. -/
lemma growth_det {n A B Q A' B' Q' Λ g : ℝ} (hn : 0 < n) (hΛ : 0 ≤ Λ) (hΛn : 2000 * Λ ≤ n)
    (hg1 : 400 * Λ ≤ g) (hg2 : g ≤ 7 * n / 10) (hQ : 0 ≤ Q) (hsum : A + B + Q = n)
    (hS : g ≤ A - B) (hor : n / 100 ≤ Q ∨ g + n / 20 ≤ A - B)
    (ha : A * (n - B + Q) / n < A' + Λ) (hb : B' < B * (n - A + Q) / n + Λ)
    (hq : (Q ^ 2 + 2 * A * B) / n < Q' + Λ) :
    min (201 / 200 * g) (7 * n / 10) ≤ A' - B' ∧
      (n / 100 ≤ Q' ∨ min (201 / 200 * g) (7 * n / 10) + n / 20 ≤ A' - B') := by
  have hS' := bias_next hn ha hb
  have hS0 : 0 ≤ A - B := le_trans (by linarith) hS
  have hm := le_mul_one_add hn hS0 hQ
  have hgrow : 201 / 200 * g ≤ A' - B' := by
    rcases hor with hq1 | hs
    · have hQn : 1 / 100 ≤ Q / n := by
        rw [le_div_iff₀ hn]
        linarith
      have : (A - B) * (101 / 100) ≤ (A - B) * (1 + Q / n) :=
        mul_le_mul_of_nonneg_left (by linarith) hS0
      linarith
    · linarith
  refine ⟨le_trans (min_le_left _ _) hgrow, ?_⟩
  by_cases h45 : A - B ≤ 4 * n / 5
  · exact Or.inl (undec_of_le hn (by linarith) hsum hS0 h45 hq)
  · right
    have : min (201 / 200 * g) (7 * n / 10) ≤ 7 * n / 10 := min_le_right _ _
    linarith

/-- **Bridge round.** If the bias is at least `2n/3` and `12B + Q ≤ ψ` with `195Λ ≤ ψ`, then
after a good round the bias dropped by less than `2Λ` and `12B' + Q' ≤ 9ψ/10`. -/
lemma bridge_det {n A B Q A' B' Q' Λ ψ : ℝ} (hn : 0 < n) (hB : 0 ≤ B) (hQ : 0 ≤ Q)
    (hsum : A + B + Q = n) (hS : 2 * n / 3 ≤ A - B) (hψ : 12 * B + Q ≤ ψ)
    (hψΛ : 195 * Λ ≤ ψ)
    (ha : A * (n - B + Q) / n < A' + Λ) (hb : B' < B * (n - A + Q) / n + Λ)
    (hq : Q' < (Q ^ 2 + 2 * A * B) / n + Λ) :
    A - B - 2 * Λ < A' - B' ∧ 12 * B' + Q' ≤ 9 / 10 * ψ := by
  have hS' := bias_next hn ha hb
  have hm := le_mul_one_add hn (by linarith : 0 ≤ A - B) hQ
  have hc := contract hn hB hQ hsum (by linarith) (by linarith)
  exact ⟨by linarith, by linarith⟩

/-- **Final phase, expectation**: on `12B + Q ≤ n/3` the potential contracts by `5/6`. -/
lemma fin_expect {n A B Q : ℝ} (hn : 0 < n) (hB : 0 ≤ B) (hQ : 0 ≤ Q)
    (hsum : A + B + Q = n) (h : 12 * B + Q ≤ n / 3) :
    12 * (B * (n - A + Q) / n) + (Q ^ 2 + 2 * A * B) / n ≤ 5 / 6 * (12 * B + Q) :=
  contract hn hB hQ hsum (by linarith) (by linarith)

/-- **Final phase, stability**: a good round keeps `12B + Q ≤ n/3`. -/
lemma fin_det {n A B Q B' Q' Λ : ℝ} (hn : 0 < n) (hΛn : 234 * Λ ≤ n)
    (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hsum : A + B + Q = n) (h : 12 * B + Q ≤ n / 3)
    (hb : B' < B * (n - A + Q) / n + Λ) (hq : Q' < (Q ^ 2 + 2 * A * B) / n + Λ) :
    12 * B' + Q' ≤ n / 3 := by
  have hc := fin_expect hn hB hQ hsum h
  linarith

end Undecided
