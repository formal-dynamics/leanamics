import Mathlib

/-! # Real inequalities for the `k`-colour undecided-state dynamics (UND-3)

Pure real-number lemmas behind one round of the analysis; `c` is the size of the plurality
colour, `μ = c(c + 2q)/n` its expected next size, `ℓ = 3 log n` the deviation parameter.

* **Thresholds** (`thr_step`): an invariant `X + σ√(ℓc) ≤ tc` (with `X` a colour community or
  the non-plurality mass) is restored after a round in which the plurality has at least
  `μ - 2√(ℓμ)` nodes, as soon as `X' ≤ tμ - (2t + σ)√(ℓμ)` (`key_ratio`, `key_growth`,
  `key_drift` give this inequality in the three regimes of the analysis).
* **Progress** (`phi_next`): `Φ = c(c + 2q)/n` is multiplied by `(1 - a)(1 + η - b)` when the
  expectation of `c' + 2q'` is at least `n(1 + η)`; `sq_gap_of_small` and `gap_nonfinal` give
  `η ≥ 1/4` for small `Φ` and `η ≥ κ/(4000B)` outside the final set.
* **Final phase** (`fpsi_expect`, `fpsi_keep`): `4S + q` contracts by `3/4` in expectation on
  `{4S + q ≤ n/10}`, and this set is kept by a good round.
-/

namespace Undecided.Plurality
open Real

/-! ### Square roots -/

lemma sqrt_mul_le_of_le {ℓ x y : ℝ} (hℓ : 0 ≤ ℓ) (h : x ≤ y) : √(ℓ * x) ≤ √(ℓ * y) :=
  sqrt_le_sqrt (mul_le_mul_of_nonneg_left h hℓ)

/-- `√(ℓμ) ≤ μ / s` as soon as `s² ℓ ≤ μ`. -/
lemma sqrt_le_div {ℓ μ s : ℝ} (hℓ : 0 ≤ ℓ) (hs : 0 < s) (h : s ^ 2 * ℓ ≤ μ) :
    √(ℓ * μ) ≤ μ / s := by
  have hμ : 0 ≤ μ := le_trans (by positivity) h
  rw [show μ / s = √((μ / s) ^ 2) from (sqrt_sq (by positivity)).symm]
  apply sqrt_le_sqrt
  rw [div_pow, le_div_iff₀ (by positivity)]
  nlinarith

/-! ### Thresholds -/

/-- `t c - σ √(ℓ c)` is monotone in `c` on `c ≥ σ²ℓ/(4t²)`. -/
lemma thr_mono {ℓ t σ c c' : ℝ} (hℓ : 0 ≤ ℓ) (ht : 0 < t) (hσ : 0 ≤ σ) (hc : 0 ≤ c)
    (hcc : c ≤ c') (h : σ ^ 2 * ℓ ≤ 4 * t ^ 2 * c) :
    t * c - σ * √(ℓ * c) ≤ t * c' - σ * √(ℓ * c') := by
  have hc' : 0 ≤ c' := hc.trans hcc
  have ha := sqrt_nonneg c
  have hab : √c ≤ √c' := sqrt_le_sqrt hcc
  have hl := sqrt_nonneg ℓ
  rw [sqrt_mul hℓ, sqrt_mul hℓ]
  have e1 : c = √c ^ 2 := (sq_sqrt hc).symm
  have e2 : c' = √c' ^ 2 := (sq_sqrt hc').symm
  -- `σ√ℓ ≤ 2t√c`
  have hkey : σ * √ℓ ≤ 2 * t * √c := by
    have h1 : (σ * √ℓ) ^ 2 ≤ (2 * t * √c) ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, sq_sqrt hℓ, sq_sqrt hc]
      nlinarith
    exact (sq_le_sq₀ (by positivity) (by positivity)).mp h1
  have hprod : 0 ≤ (√c' - √c) * (t * (√c' + √c) - σ * √ℓ) := by
    apply mul_nonneg (by linarith)
    nlinarith
  nlinarith

/-- **Threshold step.** If the plurality ends the round with at least `μ - 2√(ℓμ)` nodes,
`μ ≥ 16ℓ`, `σ²ℓ ≤ 2t²μ` and `X' ≤ tμ - (2t + σ)√(ℓμ)`, then `X' + σ√(ℓC') ≤ tC'`. -/
lemma thr_step {ℓ t σ μ C' X' : ℝ} (hℓ : 0 ≤ ℓ) (ht : 0 < t) (hσ : 0 ≤ σ) (hμ : 16 * ℓ ≤ μ)
    (hmono : σ ^ 2 * ℓ ≤ 2 * t ^ 2 * μ) (hC' : μ - 2 * √(ℓ * μ) ≤ C')
    (hX' : X' ≤ t * μ - (2 * t + σ) * √(ℓ * μ)) :
    X' + σ * √(ℓ * C') ≤ t * C' := by
  have hμ0 : 0 ≤ μ := le_trans (by positivity) hμ
  have hs : √(ℓ * μ) ≤ μ / 4 := sqrt_le_div hℓ (by norm_num) (by linarith)
  have hs0 := sqrt_nonneg (ℓ * μ)
  set cm := μ - 2 * √(ℓ * μ) with hcm
  have hcm0 : μ / 2 ≤ cm := by linarith
  have hmono' : σ ^ 2 * ℓ ≤ 4 * t ^ 2 * cm := by
    have : 2 * t ^ 2 * μ ≤ 4 * t ^ 2 * cm := by nlinarith [sq_nonneg t]
    linarith
  have h1 := thr_mono hℓ ht hσ (by linarith) hC' hmono'
  have h2 : √(ℓ * cm) ≤ √(ℓ * μ) := sqrt_mul_le_of_le hℓ (by linarith)
  have h3 : σ * √(ℓ * cm) ≤ σ * √(ℓ * μ) := mul_le_mul_of_nonneg_left h2 hσ
  nlinarith

/-- The key inequality from a ratio bound `μX ≤ rμ` with margin `(t - r)μ` (zone A, with
`r = t/2`, and the first round). -/
lemma key_ratio {ℓ t σ E μ μX X' r : ℝ} (hX' : X' ≤ μX + E * √(ℓ * μ)) (hμX : μX ≤ r * μ)
    (hbig : (2 * t + σ + E) * √(ℓ * μ) ≤ (t - r) * μ) :
    X' ≤ t * μ - (2 * t + σ) * √(ℓ * μ) := by
  nlinarith

/-- The key inequality in the growth regime: `μ ≥ 16c/9` and `σ ≥ 3(2t + E)`. -/
lemma key_growth {ℓ t σ E c μ X μX X' : ℝ} (hℓ : 0 ≤ ℓ) (hc : 0 < c)
    (hX' : X' ≤ μX + E * √(ℓ * μ)) (hμX : μX * c ≤ X * μ) (hinv : X + σ * √(ℓ * c) ≤ t * c)
    (hg : 16 / 9 * c ≤ μ) (hσE : 3 * (2 * t + E) ≤ σ) (hσ : 0 ≤ σ) :
    X' ≤ t * μ - (2 * t + σ) * √(ℓ * μ) := by
  have hμ : 0 ≤ μ := by linarith
  have hsc := sqrt_nonneg (ℓ * c)
  have hsμ := sqrt_nonneg (ℓ * μ)
  -- `(4/3) c √(ℓμ) ≤ √(ℓc) μ`
  have hroot : 4 / 3 * c * √(ℓ * μ) ≤ √(ℓ * c) * μ := by
    have h1 : (4 / 3 * c * √(ℓ * μ)) ^ 2 ≤ (√(ℓ * c) * μ) ^ 2 := by
      have e1 : (4 / 3 * c * √(ℓ * μ)) ^ 2 = 16 / 9 * c ^ 2 * (ℓ * μ) := by
        rw [mul_pow, mul_pow, sq_sqrt (by positivity)]
        ring
      have e2 : (√(ℓ * c) * μ) ^ 2 = ℓ * c * μ ^ 2 := by
        rw [mul_pow, sq_sqrt (by positivity)]
      rw [e1, e2]
      have : 0 ≤ ℓ * c * μ := by positivity
      nlinarith
    exact (sq_le_sq₀ (by positivity) (by positivity)).mp h1
  have h2 : X * μ ≤ (t * c - σ * √(ℓ * c)) * μ := mul_le_mul_of_nonneg_right (by linarith) hμ
  have h3 : σ * (4 / 3 * c * √(ℓ * μ)) ≤ σ * (√(ℓ * c) * μ) := mul_le_mul_of_nonneg_left hroot hσ
  have h4 : X' * c ≤ (t * μ - (2 * t + σ) * √(ℓ * μ)) * c := by
    have h5 : X' * c ≤ (μX + E * √(ℓ * μ)) * c := mul_le_mul_of_nonneg_right hX' hc.le
    have h6 : 0 ≤ (σ / 3 - 2 * t - E) * (c * √(ℓ * μ)) :=
      mul_nonneg (by linarith) (by positivity)
    nlinarith
  exact le_of_mul_le_mul_right h4 hc

/-- The key inequality in the drift regime: the deterministic drift
`Xμ - μX c ≥ (t/2) κ c³/n` beats the deviations. -/
lemma key_drift {ℓ t σ E κ c μ n X μX X' : ℝ} (hc : 0 < c) (hμ : 0 ≤ μ)
    (hX' : X' ≤ μX + E * √(ℓ * μ)) (hμX : μX * c ≤ X * μ - t / 2 * κ * c ^ 3 / n)
    (hX : X ≤ t * c) (hbig : (2 * t + σ + E) * √(ℓ * μ) ≤ t / 2 * κ * c ^ 2 / n) :
    X' ≤ t * μ - (2 * t + σ) * √(ℓ * μ) := by
  have h1 : X * μ ≤ t * c * μ := mul_le_mul_of_nonneg_right hX hμ
  have h2 : μX * c ≤ (t * μ - t / 2 * κ * c ^ 2 / n) * c := by
    have e : t / 2 * κ * c ^ 3 / n = (t / 2 * κ * c ^ 2 / n) * c := by ring
    rw [e] at hμX
    nlinarith
  have h3 : μX ≤ t * μ - t / 2 * κ * c ^ 2 / n := le_of_mul_le_mul_right h2 hc
  linarith

/-! ### Progress of `Φ = c(c + 2q)/n` -/

/-- **One step of `Φ`.** If the plurality ends with at least `μ - 2√(ℓμ)` nodes, the undecided
with at least `μq - 2√(ℓn)`, and `μ + 2μq ≥ n(1 + η)`, then
`C'(C' + 2Q')/n ≥ (1 - a)(1 + η - b) μ`, where `2√(ℓμ) ≤ aμ` and `6√(ℓn) ≤ bn`. -/
lemma phi_next {n ℓ μ μq C' Q' η a b : ℝ} (hn : 0 < n) (hℓ : 0 ≤ ℓ) (hμ : 0 ≤ μ)
    (hμn : μ ≤ n) (hC' : μ - 2 * √(ℓ * μ) ≤ C') (hQ' : μq - 2 * √(ℓ * n) ≤ Q')
    (hsum : n * (1 + η) ≤ μ + 2 * μq) (ha : 2 * √(ℓ * μ) ≤ a * μ) (hb : 6 * √(ℓ * n) ≤ b * n)
    (ha1 : a ≤ 1) (hηb : b ≤ 1 + η) :
    (1 - a) * (1 + η - b) * μ ≤ C' * (C' + 2 * Q') / n := by
  have hs : √(ℓ * μ) ≤ √(ℓ * n) := sqrt_mul_le_of_le hℓ hμn
  have hC1 : (1 - a) * μ ≤ C' := by nlinarith
  have hC0 : 0 ≤ (1 - a) * μ := mul_nonneg (by linarith) hμ
  have hS1 : n * (1 + η - b) ≤ C' + 2 * Q' := by nlinarith
  have hS0 : 0 ≤ n * (1 + η - b) := mul_nonneg hn.le (by linarith)
  rw [le_div_iff₀ hn]
  have := mul_le_mul hC1 hS1 hS0 (hC0.trans hC1)
  nlinarith

/-- If `Φ = c(c + 2q)/n < n/(8(1 + B))` and `S ≤ Bc`, then `(n - c - 2q)² ≥ n²/4`: either
`c + 2q ≤ n/2`, or the plurality, hence all decided nodes, are few and `q > 3n/4`. -/
lemma sq_gap_of_small {n c q S B : ℝ} (hn : 0 < n) (hc : 0 ≤ c) (hq : 0 ≤ q) (hS : 0 ≤ S)
    (hB : 0 ≤ B) (hsum : c + q + S = n) (hSB : S ≤ B * c)
    (hsmall : c * (c + 2 * q) / n < n / (8 * (1 + B))) :
    n ^ 2 / 4 ≤ (n - c - 2 * q) ^ 2 := by
  by_cases h : c + 2 * q ≤ n / 2
  · nlinarith
  · replace h := not_le.mp h
    have h8 : 0 < 8 * (1 + B) := by positivity
    rw [div_lt_div_iff₀ hn h8] at hsmall
    -- `c (n/2) < c(c + 2q)`, so `8(1 + B) c n/2 < n²`, i.e. `(1 + B) c < n/4`
    have h1 : c * (n / 2) * (8 * (1 + B)) ≤ c * (c + 2 * q) * (8 * (1 + B)) := by
      apply mul_le_mul_of_nonneg_right _ h8.le
      exact mul_le_mul_of_nonneg_left h.le hc
    have h2 : (1 + B) * c < n / 4 := by nlinarith
    have h3 : n / 2 < c + 2 * q - n := by nlinarith
    nlinarith

/-- Outside the final set `{4S + q ≤ n/10}`, with `W ≥ κcS` and `S ≤ Bc`:
`κ n² ≤ 4000 B ((n - c - 2q)² + 2W)`. -/
lemma gap_nonfinal {n c q S W B κ : ℝ} (hn : 0 < n) (hc : 0 ≤ c) (hS : 0 ≤ S)
    (hB : 1 ≤ B) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hsum : c + q + S = n) (hSB : S ≤ B * c)
    (hW : κ * c * S ≤ W) (hnf : n / 10 < 4 * S + q) :
    κ * n ^ 2 ≤ 4000 * B * ((n - c - 2 * q) ^ 2 + 2 * W) := by
  have hgap : n - c - 2 * q = S - q := by linarith
  rw [hgap]
  have hW0 : 0 ≤ W := le_trans (by positivity) hW
  have hκB : κ ≤ B := by linarith
  by_cases h : n / 40 ≤ |S - q|
  · have h1 : (n / 40) ^ 2 ≤ (S - q) ^ 2 := by
      rw [← sq_abs (S - q)]
      exact pow_le_pow_left₀ (by positivity) h 2
    have h2 : κ * n ^ 2 ≤ B * n ^ 2 := mul_le_mul_of_nonneg_right hκB (by positivity)
    nlinarith
  · replace h := not_le.mp h
    have hlt := (abs_lt.mp h).1
    have hS3 : 3 * n / 200 < S := by linarith
    -- `B W ≥ κ (Bc) S ≥ κ S²`
    have h1 : κ * S * S ≤ κ * S * (B * c) := mul_le_mul_of_nonneg_left hSB (by positivity)
    have h2 : B * (κ * c * S) ≤ B * W := mul_le_mul_of_nonneg_left hW (by linarith)
    have h3 : (3 * n / 200) ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ (by positivity) hS3.le 2
    have h4 : κ * (3 * n / 200) ^ 2 ≤ κ * S ^ 2 := mul_le_mul_of_nonneg_left h3 hκ0.le
    nlinarith [sq_nonneg (S - q)]

/-! ### The final phase -/

/-- On `{4S + q ≤ n/10}`, `E[4S' + q'] ≤ 3/4 (4S + q)`. -/
lemma fpsi_expect {n c q S μS μq : ℝ} (hn : 0 < n) (hc : c ≤ n) (hS : 0 ≤ S)
    (hq : 0 ≤ q) (hμS : μS ≤ S * (S + 2 * q) / n) (hμq : μq ≤ (q ^ 2 + 2 * c * S + S ^ 2) / n)
    (hF : 4 * S + q ≤ n / 10) :
    4 * μS + μq ≤ 3 / 4 * (4 * S + q) := by
  rw [le_div_iff₀ hn] at hμS hμq
  have hS40 : S ≤ n / 40 := by linarith
  have hq10 : q ≤ n / 10 := by linarith
  have h1 : S * S ≤ S * (n / 40) := mul_le_mul_of_nonneg_left hS40 hS
  have h2 : S * q ≤ S * (n / 10) := mul_le_mul_of_nonneg_left hq10 hS
  have h3 : q * q ≤ q * (n / 10) := mul_le_mul_of_nonneg_left hq10 hq
  have h4 : c * S ≤ n * S := mul_le_mul_of_nonneg_right hc hS
  have h5 : (4 * μS + μq) * n ≤ 3 / 4 * (4 * S + q) * n := by nlinarith
  exact le_of_mul_le_mul_right h5 hn

/-- The final set `{4S + q ≤ n/10}` is kept by a good round. -/
lemma fpsi_keep {n ℓ S q S' Q' μS μq : ℝ} (hS' : S' ≤ μS + 2 * √(ℓ * n))
    (hQ' : Q' ≤ μq + 2 * √(ℓ * n)) (hexp : 4 * μS + μq ≤ 3 / 4 * (4 * S + q))
    (hF : 4 * S + q ≤ n / 10) (hdev : 10 * √(ℓ * n) ≤ n / 40) :
    4 * S' + Q' ≤ n / 10 := by
  linarith

end Undecided.Plurality
