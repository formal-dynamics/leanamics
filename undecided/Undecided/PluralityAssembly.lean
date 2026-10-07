import Undecided.PluralityStages
import Undecided.MajorityAssembly

/-! # Assembling the stages of the `k`-colour dynamics (UND-3)

`plurality_explicit` is the explicit form of `Undecided.Plurality.plurality_whp`. With
`K = (1 + α)²/α` (so that `θκ = 1/K` for `θ = 1/(1 + α)`, `κ = 1 - θ`) and `C = 10⁵ K²`: if
`log n ≥ C` and `(C k)³ log n ≤ n`, every configuration `x` without undecided nodes in which
colour `m` beats every other colour by the factor `1 + α` misses consensus on `m` after
`⌈C md(x) log n⌉` rounds with probability at most `6/n`.

The parameters: `ℓ = 3 log n` (a bad round has probability `p = (k + 4)/n³`), `φ = n/(2k²)`,
`B = 2 md(x)`, `λ = 1 + κ/(8000B)`. The rounds are split as `T = (T₂ + 1) + T₃`:

* main stage (`main_stage`), `T₂ + 1` rounds with `T₂ = ⌈log(4k²)/log λ⌉₊`, so that
  `φ λ^T₂ ≥ 2n > n` and the configuration is in `Fpsi` (`Gset_sub`);
  `T₂ ≤ 96000 K md(x) log n + 1` (`log λ ≥ κ/(16000 B)`);
* final stage (`fin_stage`), `T₃ = ⌈8 log n⌉₊` rounds: `(3/4)^T₃ ≤ n⁻²`.

The failure probability is at most `T p + (3/4)^T₃ n/10 ≤ 5/n + 1/n`, and
`T ≤ C md(x) log n`.
-/

namespace Undecided.Plurality
open Finset Dynamics Real

/-- `ε/2 ≤ log(1 + ε)` for `0 ≤ ε ≤ 1`. -/
lemma half_le_log_one_add {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) : ε / 2 ≤ log (1 + ε) := by
  have h := one_sub_inv_le_log_of_pos (x := 1 + ε) (by linarith)
  have e : 1 - (1 + ε)⁻¹ = ε / (1 + ε) := by field_simp; ring
  rw [e] at h
  have : ε / 2 ≤ ε / (1 + ε) := div_le_div_of_nonneg_left h0 (by linarith) (by linarith)
  linarith

/-- `(3/4)^T ≤ e^{-T/4}`. -/
lemma three_quarters_pow_le (T : ℕ) : (3 / 4 : ℝ) ^ T ≤ exp (-(T / 4)) := by
  have h : (3 / 4 : ℝ) ≤ exp (-(1 / 4)) := by
    have := add_one_le_exp (-(1 / 4 : ℝ))
    linarith
  calc (3 / 4 : ℝ) ^ T ≤ exp (-(1 / 4)) ^ T := pow_le_pow_left₀ (by norm_num) h T
    _ = exp (-(T / 4)) := by rw [← exp_nat_mul]; ring_nf

/-- `e^{-3 log n} = 1/n³`. -/
lemma exp_neg_three_log {n : ℕ} (hn : (0 : ℝ) < n) :
    exp (-(3 * log (n : ℝ))) = 1 / (n : ℝ) ^ 3 := by
  have h3 : exp (3 * log (n : ℝ)) = (n : ℝ) ^ 3 := by
    rw [show (3 : ℝ) * log n = ((3 : ℕ) : ℝ) * log n by norm_num, exp_nat_mul, exp_log hn]
  rw [exp_neg, h3, one_div]

/-- `e^{-2 log n} = 1/n²`. -/
lemma exp_neg_two_log' {n : ℕ} (hn : (0 : ℝ) < n) :
    exp (-(2 * log (n : ℝ))) = 1 / (n : ℝ) ^ 2 := by
  have h2 : exp (2 * log (n : ℝ)) = (n : ℝ) ^ 2 := by
    rw [show (2 : ℝ) * log n = ((2 : ℕ) : ℝ) * log n by norm_num, exp_nat_mul, exp_log hn]
  rw [exp_neg, h2, one_div]

variable {n k : ℕ}

/-- The plurality colour has at least `n/k` nodes when there are no undecided nodes. -/
lemma n_div_le_cnt (x : Config n k) (m : Fin k) (hq : und x = 0)
    (hplur : ∀ i, cnt x i ≤ cnt x m) : (n : ℝ) ≤ k * cnt x m := by
  have h := und_add_sum x
  rw [hq, zero_add] at h
  rw [← h]
  calc ∑ i, cnt x i ≤ ∑ _i : Fin k, cnt x m := sum_le_sum fun i _ => hplur i
    _ = k * cnt x m := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ### The constants -/

section
variable {α : ℝ}

lemma K_ge_four (hα : 0 < α) : 4 ≤ (1 + α) ^ 2 / α := by
  rw [le_div_iff₀ hα]
  nlinarith [sq_nonneg (α - 1)]

lemma theta_pos (hα : 0 < α) : 0 < 1 / (1 + α) := by positivity

lemma theta_lt_one (hα : 0 < α) : 1 / (1 + α) < 1 := by
  rw [div_lt_one (by linarith)]
  linarith

lemma theta_kappa (hα : 0 < α) :
    (1 / (1 + α)) ^ 2 * (1 - 1 / (1 + α)) ^ 2 = 1 / ((1 + α) ^ 2 / α) ^ 2 := by
  have h : 1 + α ≠ 0 := by linarith
  field_simp
  ring

lemma inv_kappa_le (hα : 0 < α) : 1 / (1 - 1 / (1 + α)) ≤ (1 + α) ^ 2 / α := by
  have hκ : 1 - 1 / (1 + α) = α / (1 + α) := by field_simp; ring
  rw [hκ, one_div_div, div_le_div_iff_of_pos_right hα]
  nlinarith

end

/-! ### The numerical conditions from `2·10¹² K² k³ log n ≤ n` -/

section
variable {N L K k θ B φ : ℝ}

lemma hyp_h1 (hk1 : 1 ≤ k) (hK : 0 < K) (hL : 0 ≤ L) (hθ : θ ^ 2 * (1 - θ) ^ 2 = 1 / K ^ 2)
    (hφ : φ = N / (2 * k ^ 2)) (hbig : 2000000000000 * K ^ 2 * k ^ 3 * L ≤ N) :
    1024 * (3 * L) ≤ θ ^ 2 * (1 - θ) ^ 2 * φ := by
  rw [hθ, hφ, div_mul_div_comm, one_mul, le_div_iff₀ (by positivity)]
  have h1 : k ^ 2 ≤ k ^ 3 := by nlinarith
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ K ^ 2 * L)
  have h3 : 0 ≤ K ^ 2 * L * k ^ 3 := by positivity
  linarith

lemma hyp_h2 (hN : 0 < N) (hK : 0 < K) (hL : 0 ≤ L) (hB0 : 0 ≤ B)
    (hB3 : 1 + B ≤ 3 * k) (hθ : θ ^ 2 * (1 - θ) ^ 2 = 1 / K ^ 2)
    (hbig : 2000000000000 * K ^ 2 * k ^ 3 * L ≤ N) :
    2048 * N ^ 2 * (3 * L) ≤ θ ^ 2 * (1 - θ) ^ 2 * (N / (20 * (1 + B))) ^ 3 := by
  have hBB : (1 + B) ^ 3 ≤ 27 * k ^ 3 := by
    have := pow_le_pow_left₀ (by linarith) hB3 3
    nlinarith
  have h1 : 49152000 * (K ^ 2 * L) * (1 + B) ^ 3 ≤ N := by
    have := mul_le_mul_of_nonneg_left hBB (by positivity : 0 ≤ 49152000 * (K ^ 2 * L))
    nlinarith
  rw [hθ, div_pow, div_mul_div_comm, one_mul, le_div_iff₀ (by positivity)]
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ N ^ 2)
  nlinarith

lemma hyp_h3 (hk1 : 1 ≤ k) (hK : 0 < K) (hL : 0 ≤ L) (hθ1 : θ < 1) (hB0 : 0 ≤ B)
    (hB3 : 1 + B ≤ 3 * k) (hBκ : B / (1 - θ) ≤ 2 * k * K)
    (hbig : 2000000000000 * K ^ 2 * k ^ 3 * L ≤ N) :
    (16 * (4000 * B) / (1 - θ)) ^ 2 * (3 * L) ≤ N / (8 * (1 + B)) := by
  have hu0 : 0 ≤ B / (1 - θ) := div_nonneg hB0 (by linarith)
  rw [le_div_iff₀ (by positivity)]
  have e : (16 * (4000 * B) / (1 - θ)) ^ 2 * (3 * L) * (8 * (1 + B))
      = 98304000000 * (B / (1 - θ)) ^ 2 * L * (1 + B) := by ring
  rw [e]
  have h1 : (B / (1 - θ)) ^ 2 ≤ (2 * k * K) ^ 2 := pow_le_pow_left₀ hu0 hBκ 2
  have h2 : 98304000000 * (B / (1 - θ)) ^ 2 * L * (1 + B)
      ≤ 98304000000 * (2 * k * K) ^ 2 * L * (3 * k) := by
    apply mul_le_mul _ hB3 (by linarith) (by positivity)
    apply mul_le_mul_of_nonneg_right _ hL
    exact mul_le_mul_of_nonneg_left h1 (by norm_num)
  have e2 : 98304000000 * (2 * k * K) ^ 2 * L * (3 * k) = 1179648000000 * (K ^ 2 * k ^ 3 * L) :=
    by ring
  have h3 : 0 ≤ K ^ 2 * k ^ 3 * L := by positivity
  linarith

lemma hyp_h4 (hk1 : 1 ≤ k) (hK : 0 < K) (hL : 0 ≤ L) (hθ1 : θ < 1) (hB0 : 0 ≤ B)
    (hBκ : B / (1 - θ) ≤ 2 * k * K) (hbig : 2000000000000 * K ^ 2 * k ^ 3 * L ≤ N) :
    (48 * (4000 * B) / (1 - θ)) ^ 2 * (3 * L) ≤ N := by
  have hu0 : 0 ≤ B / (1 - θ) := div_nonneg hB0 (by linarith)
  have e : (48 * (4000 * B) / (1 - θ)) ^ 2 * (3 * L) = 110592000000 * (B / (1 - θ)) ^ 2 * L := by
    ring
  rw [e]
  have h1 : (B / (1 - θ)) ^ 2 ≤ (2 * k * K) ^ 2 := pow_le_pow_left₀ hu0 hBκ 2
  have h2 : 110592000000 * (B / (1 - θ)) ^ 2 * L ≤ 110592000000 * (2 * k * K) ^ 2 * L := by
    apply mul_le_mul_of_nonneg_right _ hL
    exact mul_le_mul_of_nonneg_left h1 (by norm_num)
  have h3 : k ^ 2 ≤ k ^ 3 := by nlinarith
  have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ K ^ 2 * L)
  have e2 : 110592000000 * (2 * k * K) ^ 2 * L = 442368000000 * (K ^ 2 * L * k ^ 2) := by ring
  have e3 : 2000000000000 * K ^ 2 * k ^ 3 * L = 2000000000000 * (K ^ 2 * L * k ^ 3) := by ring
  have h5 : 0 ≤ K ^ 2 * L * k ^ 2 := by positivity
  linarith

lemma hyp_h5 (hk1 : 1 ≤ k) (hK4 : 4 ≤ K) (hL : 0 ≤ L)
    (hbig : 2000000000000 * K ^ 2 * k ^ 3 * L ≤ N) : 160000 * (3 * L) ≤ N := by
  have h1 : (1 : ℝ) ≤ K ^ 2 * k ^ 3 := by
    have : (1 : ℝ) ≤ K ^ 2 := by nlinarith
    have : (1 : ℝ) ≤ k ^ 3 := one_le_pow₀ hk1
    nlinarith
  have h2 := mul_le_mul_of_nonneg_right h1 hL
  nlinarith

lemma k_le_N (hk1 : 1 ≤ k) (hK4 : 4 ≤ K) (hL1 : 1 ≤ L)
    (hbig : 2000000000000 * K ^ 2 * k ^ 3 * L ≤ N) : k ≤ N := by
  have h1 : k ≤ k ^ 3 := by
    have : 0 ≤ k * (k - 1) * (k + 1) :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    nlinarith
  have h2 : (1 : ℝ) ≤ 2000000000000 * K ^ 2 * L := by nlinarith
  have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ k ^ 3)
  nlinarith

end

/-! ### The number of rounds -/

/-- `T₂ ≤ 96000 K md log n + 1`. -/
lemma T₂_le {N L K θ B md ε k : ℝ} (hN4 : 4 ≤ N) (hk1 : 1 ≤ k) (hkN : k ≤ N)
    (hL : L = log N) (hθ1 : θ < 1) (hκK : 1 / (1 - θ) ≤ K) (hmd : 1 ≤ md) (hB : B = 2 * md)
    (hε : ε = (1 - θ) / (4000 * B) / 2) (hε0 : 0 < ε) (hlog : ε / 2 ≤ log (1 + ε)) :
    log (4 * k ^ 2) / log (1 + ε) ≤ 96000 * K * md * L := by
  have hlogpos : 0 < log (1 + ε) := by linarith
  have h2 : log (4 * k ^ 2) ≤ 3 * L := by
    have e : 3 * log N = log (N ^ 3) := by rw [log_pow]; norm_num
    rw [hL, e]
    apply log_le_log (by positivity)
    have h3 : k ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ (by linarith) hkN 2
    have h5 : 4 * N ^ 2 ≤ N ^ 3 := by nlinarith
    nlinarith
  have hL0 : 0 ≤ L := by
    rw [hL]; exact log_nonneg (by linarith)
  have h4k : 0 ≤ log (4 * k ^ 2) := log_nonneg (by nlinarith)
  have h3 : log (4 * k ^ 2) / log (1 + ε) ≤ 3 * L / (ε / 2) :=
    div_le_div₀ (by positivity) h2 (by positivity) hlog
  have h4 : 3 * L / (ε / 2) ≤ 96000 * K * md * L := by
    rw [div_le_iff₀ (by positivity), hε, hB]
    have h5 : 1 ≤ K * (1 - θ) := by
      rw [div_le_iff₀ (by linarith)] at hκK
      linarith
    have e : 96000 * K * md * L * ((1 - θ) / (4000 * (2 * md)) / 2 / 2)
        = 3 * L * (K * (1 - θ)) := by
      field_simp
      ring
    rw [e]
    nlinarith
  linarith

/-- `(3/4)^T₃ · n/10 ≤ 1/n` once `T₃ ≥ 8 log n`. -/
lemma T3_bound {N L : ℝ} (hN : 0 < N) (hL : L = log N) {T₃ : ℕ} (hT₃ : 8 * L ≤ T₃) :
    (3 / 4 : ℝ) ^ T₃ * (N / 10) ≤ 1 / N := by
  have h1 : (3 / 4 : ℝ) ^ T₃ ≤ 1 / N ^ 2 := by
    refine (three_quarters_pow_le T₃).trans ?_
    have h2 : exp (-(T₃ / 4 : ℝ)) ≤ exp (-(2 * L)) := exp_le_exp.mpr (by linarith)
    have h3 : exp (-(2 * L)) = 1 / N ^ 2 := by
      have h4 : exp (2 * L) = N ^ 2 := by
        rw [hL, show (2 : ℝ) * log N = ((2 : ℕ) : ℝ) * log N by norm_num, exp_nat_mul,
          exp_log hN]
      rw [exp_neg, h4, one_div]
    linarith
  calc (3 / 4 : ℝ) ^ T₃ * (N / 10) ≤ 1 / N ^ 2 * (N / 10) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ ≤ 1 / N := by
        rw [div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) hN]
        nlinarith

/-- `T (k + 4) e^{-3 log n} ≤ 5/n` once `T ≤ n` and `k ≤ n`. -/
lemma p_bound {N L k T : ℝ} (hN : 0 < N) (hL : L = log N) (hk : 0 ≤ k) (hkN : k ≤ N)
    (hN1 : 1 ≤ N) (hT : T ≤ N) :
    T * ((k + 4) * exp (-(3 * L))) ≤ 5 / N := by
  have h3 : exp (-(3 * L)) = 1 / N ^ 3 := by
    have h4 : exp (3 * L) = N ^ 3 := by
      rw [hL, show (3 : ℝ) * log N = ((3 : ℕ) : ℝ) * log N by norm_num, exp_nat_mul,
        exp_log hN]
    rw [exp_neg, h4, one_div]
  rw [h3]
  have hk4 : k + 4 ≤ 5 * N := by linarith
  have h1 : T * ((k + 4) * (1 / N ^ 3)) ≤ N * (5 * N * (1 / N ^ 3)) :=
    mul_le_mul hT (mul_le_mul_of_nonneg_right hk4 (by positivity)) (by positivity) hN.le
  have e : N * (5 * N * (1 / N ^ 3)) = 5 / N := by field_simp
  linarith

/-- The total number of rounds is at most `C md log n`. -/
lemma rounds_bound {L K C md T₂ T₃ : ℝ} (hK4 : 4 ≤ K) (hC : C = 100000 * K ^ 2) (hL1 : 1 ≤ L)
    (hmd : 1 ≤ md) (hT₂ : T₂ ≤ 96000 * K * md * L + 1) (hT₃ : T₃ ≤ 8 * L + 1) :
    T₂ + 1 + T₃ ≤ C * md * L := by
  have h2 : 1 ≤ md * L := by nlinarith
  have h3 : 96000 * K + 11 ≤ C := by rw [hC]; nlinarith
  have h4 : (96000 * K + 11) * (md * L) ≤ C * (md * L) :=
    mul_le_mul_of_nonneg_right h3 (by positivity)
  have h5 : 8 * L + 3 ≤ 11 * (md * L) := by nlinarith
  nlinarith

/-- `C md log n ≤ n` from `C³k³ log n ≤ n`, `md ≤ k`. -/
lemma Cmd_le {C md k L N : ℝ} (hC1 : 1 ≤ C) (hk1 : 1 ≤ k) (hmdk : md ≤ k) (hL0 : 0 ≤ L)
    (hk : C ^ 3 * k ^ 3 * L ≤ N) : C * md * L ≤ N := by
  have h1 : C * md * L ≤ C * k * L :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmdk (by linarith)) hL0
  have h0 : 1 ≤ C * k := by nlinarith
  have h2 : C * k ≤ (C * k) ^ 3 := by
    have : 0 ≤ (C * k) * (C * k - 1) * (C * k + 1) :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    nlinarith
  have h3 : C * k * L ≤ (C * k) ^ 3 * L := mul_le_mul_of_nonneg_right h2 hL0
  have e : (C * k) ^ 3 * L = C ^ 3 * k ^ 3 * L := by ring
  linarith

/-- `log` of a natural number cast. -/
lemma cast_four_sq (k : ℕ) : ((4 * k ^ 2 : ℕ) : ℝ) = 4 * (k : ℝ) ^ 2 := by push_cast; ring

variable {n k : ℕ}

/-- **Composition of the stages**: under the numerical conditions, if `n < φ λ^T₂`,
`(3/4)^T₃ n/10 ≤ 1/n` and `(T₂ + 1 + T₃) p ≤ 5/n`, the probability of missing consensus on `m`
after `T₂ + 1 + T₃` rounds is at most `6/n`. -/
theorem stage_bound [NeZero n] {ℓ θ B φ ε : ℝ} (H : Hyp n ℓ θ B φ) {m : Fin k}
    {x : Config n k} (hund : und x = 0) (hθx : ∀ i, i ≠ m → cnt x i ≤ θ * cnt x m)
    (hB : B = 2 * md x) (hφ2 : 2 * φ ≤ mu x m) (hε : (1 - θ) / (4000 * B) / 2 = ε)
    {T₂ T₃ : ℕ} (hT₂ : (n : ℝ) < φ * (1 + ε) ^ T₂)
    (hT₃ : (3 / 4 : ℝ) ^ T₃ * ((n : ℝ) / 10) ≤ 1 / n)
    (hp : ((T₂ + 1 + T₃ : ℕ) : ℝ) * ((k + 4) * exp (-ℓ)) ≤ 5 / n) :
    miss (allM m) (T₂ + 1 + T₃) x ≤ 6 / n := by
  have hmain := main_stage H hund hθx hB hφ2 T₂
  rw [hε] at hmain
  have hsub := Gset_sub (ℓ := ℓ) (θ := θ) (B := B) (m := m) hT₂
  have hfin := fin_stage H.hℓ H.h5 m T₃
  set p := (k + 4 : ℝ) * exp (-ℓ) with hpdef
  have hp0 : 0 ≤ p := by positivity
  have hE : ∀ y ∈ (Gset ℓ θ B φ (1 + ε) m T₂ : Set (Config n k)),
      miss (allM m) T₃ y ≤ 1 / n + T₃ * p := by
    intro y hy
    have hyF := hsub hy
    refine (hfin y hyF).trans ?_
    have hψ : psi y m ≤ n / 10 := hyF
    have : (3 / 4 : ℝ) ^ T₃ * psi y m ≤ (3 / 4) ^ T₃ * (n / 10) :=
      mul_le_mul_of_nonneg_left hψ (by positivity)
    linarith
  have hcomp := miss_comp (T₁ := T₂ + 1) (T₂ := T₃) (by positivity) hE x
  calc miss (allM m) (T₂ + 1 + T₃) x
      ≤ miss (Gset ℓ θ B φ (1 + ε) m T₂) (T₂ + 1) x + (1 / n + T₃ * p) := hcomp
    _ ≤ ((T₂ + 1 : ℕ) : ℝ) * p + (1 / n + T₃ * p) := by linarith
    _ = ((T₂ + 1 + T₃ : ℕ) : ℝ) * p + 1 / n := by push_cast; ring
    _ ≤ 5 / n + 1 / n := by linarith
    _ = 6 / n := by ring

/-- The facts about the initial configuration: no undecided nodes, every other colour has at
most `θ c_m` nodes, `1 ≤ md ≤ k` and `µ_m ≥ n/k²`. -/
lemma start_facts {α θ : ℝ} (hα : 0 < α) (hθ : 1 / (1 + α) = θ) (hn0 : (0 : ℝ) < n)
    (x : Config n k) (m : Fin k) (hq : count x none = 0)
    (hb : ∀ i, i ≠ m → (1 + α) * count x (some i) ≤ (count x (some m) : ℝ)) :
    und x = 0 ∧ (∀ i, i ≠ m → cnt x i ≤ θ * cnt x m) ∧ 1 ≤ md x ∧ md x ≤ k ∧
      2 * ((n : ℝ) / (2 * k ^ 2)) ≤ mu x m := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Fin.pos m
  have hund : und x = 0 := by unfold und; rw [hq]; simp
  have hθx : ∀ i, i ≠ m → cnt x i ≤ θ * cnt x m := fun i hi => by
    have := hb i hi
    unfold cnt
    rw [← hθ, one_div_mul_eq_div, le_div_iff₀ (by linarith)]
    linarith
  have hθ1 : θ ≤ 1 := by
    rw [← hθ, div_le_one (by linarith)]
    linarith
  have hplur : ∀ i, cnt x i ≤ cnt x m := fun i => by
    by_cases hi : i = m
    · rw [hi]
    · have := hθx i hi
      have := cnt_nonneg x m
      nlinarith
  have hcn := n_div_le_cnt x m hund hplur
  have hc : 0 < cnt x m := by
    by_contra h
    have : cnt x m = 0 := le_antisymm (not_lt.mp h) (cnt_nonneg x m)
    rw [this, mul_zero] at hcn
    linarith
  refine ⟨hund, hθx, one_le_md x ⟨m, by have := hc; unfold cnt at this; exact_mod_cast this⟩,
    md_le_card x, ?_⟩
  have e : mu x m = cnt x m ^ 2 / n := by unfold mu; rw [hund]; ring
  rw [e, le_div_iff₀ hn0]
  have h1 : (n : ℝ) ^ 2 ≤ (k * cnt x m) ^ 2 := pow_le_pow_left₀ hn0.le hcn 2
  have e2 : 2 * ((n : ℝ) / (2 * k ^ 2)) * n = n ^ 2 / k ^ 2 := by field_simp
  rw [e2, div_le_iff₀ (by positivity)]
  nlinarith

/-- **UND-3, explicit form.** -/
theorem plurality_explicit {α : ℝ} (hα : 0 < α) (x : Config n k) (m : Fin k)
    (hL : 100000 * ((1 + α) ^ 2 / α) ^ 2 ≤ log n)
    (hk : (100000 * ((1 + α) ^ 2 / α) ^ 2 * k) ^ 3 * log n ≤ n)
    (hq : count x none = 0)
    (hb : ∀ i, i ≠ m → (1 + α) * count x (some i) ≤ (count x (some m) : ℝ)) :
    miss (allM m) ⌈100000 * ((1 + α) ^ 2 / α) ^ 2 * md x * log n⌉₊ x ≤ 6 / n := by
  -- the constants
  have hK4 := K_ge_four hα
  have hθ0 := theta_pos hα
  have hθ1 := theta_lt_one hα
  have hθκ := theta_kappa hα
  have hκK := inv_kappa_le hα
  generalize hK : (1 + α) ^ 2 / α = K at hK4 hθκ hκK hL hk ⊢
  generalize hθ : 1 / (1 + α) = θ at hθ0 hθ1 hθκ hκK
  generalize hC : 100000 * K ^ 2 = C at hL hk ⊢
  generalize hLdef : log (n : ℝ) = L at hL hk ⊢
  have hC1 : 1600000 ≤ C := by rw [← hC]; nlinarith
  have hL1 : 1600000 ≤ L := by linarith
  -- sizes
  have hn1 : 1 < n := by
    by_contra h
    have : (n : ℝ) ≤ 1 := by exact_mod_cast not_lt.mp h
    have := log_nonpos (Nat.cast_nonneg n) this
    linarith
  haveI : NeZero n := ⟨by omega⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Fin.pos m
  have hbig : 2000000000000 * K ^ 2 * k ^ 3 * L ≤ n := by
    have hK1 : K ^ 2 ≤ K ^ 6 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have h1 : 2000000000000 * K ^ 2 ≤ C ^ 3 := by rw [← hC]; nlinarith
    have h2 : 0 ≤ k ^ 3 * L := by positivity
    have h3 := mul_le_mul_of_nonneg_right h1 h2
    rw [mul_pow] at hk
    linarith
  have hkn : (k : ℝ) ≤ n := k_le_N hk1 hK4 (by linarith) hbig
  have hN4 : (4 : ℝ) ≤ n := by
    have := hyp_h5 hk1 hK4 (by linarith) hbig
    linarith
  have hL0 : 0 ≤ L := by linarith
  have hK0 : 0 < K := by linarith
  -- the initial configuration
  obtain ⟨hund, hθx, hmd1, hmdk, hφ2⟩ := start_facts hα hθ hn0 x m hq hb
  -- the parameters
  generalize hB : 2 * md x = B
  have hB1 : 1 ≤ B := by linarith
  have hB3 : 1 + B ≤ 3 * k := by linarith
  have hBκ : B / (1 - θ) ≤ 2 * k * K := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul (by linarith) hκK (by have := hθ1; positivity) (by positivity)
  generalize hφ : (n : ℝ) / (2 * k ^ 2) = φ at hφ2
  have H : Hyp n (3 * L) θ B φ :=
    ⟨hn0, by positivity, hθ0, hθ1, hB1, hyp_h1 hk1 hK0 hL0 hθκ hφ.symm hbig,
      hyp_h2 hn0 hK0 hL0 (by linarith) hB3 hθκ hbig,
      hyp_h3 hk1 hK0 hL0 hθ1 (by linarith) hB3 hBκ hbig,
      hyp_h4 hk1 hK0 hL0 hθ1 (by linarith) hBκ hbig, hyp_h5 hk1 hK4 hL0 hbig⟩
  -- the rate `λ = 1 + ε`
  generalize hε : (1 - θ) / (4000 * B) / 2 = ε
  have hε0 : 0 < ε := by rw [← hε]; have := hθ1; positivity
  have hε1 : ε ≤ 1 := by
    rw [← hε, div_div, div_le_one (by positivity)]
    nlinarith
  have hlog : ε / 2 ≤ log (1 + ε) := half_le_log_one_add hε0.le hε1
  -- the rounds
  obtain ⟨T₂, hT₂⟩ : ∃ T₂, T₂ = ⌈log (4 * (k : ℝ) ^ 2) / log (1 + ε)⌉₊ := ⟨_, rfl⟩
  obtain ⟨T₃, hT₃⟩ : ∃ T₃, T₃ = ⌈8 * L⌉₊ := ⟨_, rfl⟩
  have hpow : 4 * (k : ℝ) ^ 2 ≤ (1 + ε) ^ T₂ := by
    have h := Undecided.le_pow_ceil (n := 4 * k ^ 2)
      (Nat.succ_le_of_lt (by have := Fin.pos m; positivity)) (q := 1 + ε) (by linarith)
    rw [cast_four_sq] at h
    rw [hT₂]
    exact h
  have hT₂n : (n : ℝ) < φ * (1 + ε) ^ T₂ := by
    have e : φ * (4 * k ^ 2) = 2 * n := by rw [← hφ]; field_simp; ring
    have h1 : φ * (4 * k ^ 2) ≤ φ * (1 + ε) ^ T₂ :=
      mul_le_mul_of_nonneg_left hpow (by rw [← hφ]; positivity)
    linarith
  have hT₂le : (T₂ : ℝ) ≤ 96000 * K * md x * L + 1 := by
    have h0 : 0 ≤ log (4 * (k : ℝ) ^ 2) / log (1 + ε) :=
      div_nonneg (log_nonneg (by nlinarith)) (by linarith)
    have h1 := Nat.ceil_lt_add_one h0
    rw [← hT₂] at h1
    have := T₂_le hN4 hk1 hkn hLdef.symm hθ1 hκK hmd1 hB.symm hε.symm hε0 hlog
    linarith
  have hT₃le : (T₃ : ℝ) ≤ 8 * L + 1 := by
    rw [hT₃]; exact (Nat.ceil_lt_add_one (by positivity)).le
  have hTle : ((T₂ + 1 + T₃ : ℕ) : ℝ) ≤ C * md x * L := by
    push_cast
    exact rounds_bound hK4 hC.symm (by linarith) hmd1 hT₂le hT₃le
  have hCmd : C * md x * L ≤ n := Cmd_le (by linarith) hk1 hmdk hL0 (by rw [mul_pow] at hk; exact hk)
  have hfail := stage_bound H hund hθx hB.symm hφ2 hε hT₂n
    (T3_bound hn0 hLdef.symm (by rw [hT₃]; exact Nat.le_ceil _))
    (p_bound hn0 hLdef.symm (by positivity) hkn (by linarith) (hTle.trans hCmd))
  have hceil : T₂ + 1 + T₃ ≤ ⌈C * md x * L⌉₊ := by
    have := hTle.trans (Nat.le_ceil _)
    exact_mod_cast this
  exact (miss_allM_antitone x m hceil).trans hfail

end Undecided.Plurality

namespace Undecided.Plurality
open Finset Dynamics Real

variable {n k : ℕ}

/-- The probability that all nodes hold `m` is one minus the miss probability. -/
lemma prob_allM_eq [NeZero n] (T : ℕ) (x : Config n k) (m : Fin k) :
    expList (Fin n → Fin n) T
        (fun l => if l.foldl step x = (fun _ => some m) then (1 : ℝ) else 0)
      = 1 - miss (allM m) T x := by
  classical
  have h (l : List (Fin n → Fin n)) :
      (if l.foldl step x = (fun _ => some m) then (1 : ℝ) else 0)
        = 1 - (if l.foldl step x ∈ allM m then (0 : ℝ) else 1) := by
    by_cases hl : l.foldl step x = fun _ => some m
    · rw [if_pos hl, if_pos (show l.foldl step x ∈ allM m from hl)]
      norm_num
    · rw [if_neg hl, if_neg (show l.foldl step x ∉ allM m from hl)]
      norm_num
  simp_rw [h]
  rw [Undecided.expList_one_sub]
  rfl

/-- From `C k ≤ (n / log n)^{1/3}` to `(C k)³ log n ≤ n`. -/
lemma cube_of_rpow {C k L N : ℝ} (hCk : 0 ≤ C * k) (hL : 0 < L) (hN : 0 ≤ N)
    (h : C * k ≤ (N / L) ^ ((1 : ℝ) / 3)) : (C * k) ^ 3 * L ≤ N := by
  have h3 := pow_le_pow_left₀ hCk h 3
  rw [show (1 : ℝ) / 3 = ((3 : ℕ) : ℝ)⁻¹ by norm_num,
    rpow_inv_natCast_pow (by positivity) (by norm_num)] at h3
  rwa [le_div_iff₀ hL] at h3

end Undecided.Plurality
