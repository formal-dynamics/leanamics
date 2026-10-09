import Epidemics.Revisited.LowerPush
import Epidemics.Revisited.LowerPull
import Epidemics.Revisited.LowerPushPull
import Epidemics.Revisited.DoubleShrinkingRound

/-! # Total time: lower tails and expectations (EPI-8, Theorems 51 to 53, lower bounds)

The two phases are joined at a fixed time with `reach_add_le` (`m' = n / 2`):

* **Push.** With `a = ⌊log₂ n⌋`, `b = ⌊ln n⌋` and `t* = a + b - r`, split
  `t* ≤ s + τ` with `s = a - ⌈r/2⌉` and `τ = b - ⌊r/2⌋`. The growth phase reaches `n / 2`
  within `s` rounds with probability at most `2^{s+1} / n ≤ 2 · 2^{-r/2}`, and from fewer than
  `n / 2` informed nodes, `push_final_lower_explicit` bounds the probability of informing
  everybody within `τ` rounds by `1600 e^{(τ - ln(n/2))/2} = O(e^{-(ln 2 / 4) r})`.
* **Pull and push–pull** (`double_tail_generic`, growth factor `ρ = 2` or `3`). With
  `a = ⌊log_ρ n⌋`, `d = ⌊log₂ ln n⌋`, split `τ = d - r₀` (the range of the final phase) and
  `s = t* - τ`. The first term is at most `2 ρ^{r₀} 2^{-r/2}` and the second `C n^{-1/2}`,
  which is `O(e^{-(ln 2 / 4) r})` because a positive `t*` forces `r ≤ 2 log₂ n`.
* **Expectations** (`sum_notYet_ge_of_tail`, the mirror of `sum_notYet_le_of_tail`): an
  exponential lower tail before `t₀` gives `∑_{t < R} P[T > t] ≥ t₀ - A / (1 - e^{-κ})` for every
  `R ≥ t₀`, and `t₀ ≥ X + Y - 2` for `t₀ = ⌊X⌋ + ⌊Y⌋`.

When `t* = 0`, the reach probability is `0`, since one informed node is not everybody.
-/

namespace Epidemics.Revisited
open Finset Dynamics RumorProcess Real

variable {n : ℕ}

/-! ### From lower tails to expectations -/

/-- Mirror of `sum_notYet_le_of_tail`: if finishing `r` rounds before `t₀` has probability at
most `A e^{-κ r}`, every partial sum of the tail series with at least `t₀` terms is at least
`t₀ - A / (1 - e^{-κ})`. -/
lemma sum_notYet_ge_of_tail (P : RumorProcess n) {m A κ : ℝ} (hA : 0 ≤ A) (hκ : 0 < κ)
    (t₀ : ℕ) (S : Finset (Fin n))
    (h : ∀ r : ℕ, 1 - P.notYet m (t₀ - r) S ≤ A * exp (-κ * r)) {R : ℕ} (hR : t₀ ≤ R) :
    (t₀ : ℝ) - A / (1 - exp (-κ)) ≤ ∑ t ∈ range R, P.notYet m t S := by
  have hq : exp (-κ) < 1 := by
    have hneg : -κ < 0 := by linarith
    simpa [exp_zero] using exp_lt_exp.mpr hneg
  have hsub : ∑ t ∈ range t₀, P.notYet m t S ≤ ∑ t ∈ range R, P.notYet m t S :=
    sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr hR)
      (fun t _ _ => notYet_nonneg P m t S)
  have hterm : ∀ j ∈ range t₀, 1 - P.notYet m (t₀ - 1 - j) S ≤ A * exp (-κ) ^ j := by
    intro j _
    have heq : t₀ - 1 - j = t₀ - (j + 1) := by omega
    rw [heq]
    refine le_trans (h (j + 1)) (mul_le_mul_of_nonneg_left ?_ hA)
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    push_cast
    linarith
  have hreach : ∑ t ∈ range t₀, (1 - P.notYet m t S) ≤ A / (1 - exp (-κ)) := by
    rw [← sum_range_reflect (fun t => 1 - P.notYet m t S) t₀]
    calc ∑ j ∈ range t₀, (1 - P.notYet m (t₀ - 1 - j) S)
        ≤ ∑ j ∈ range t₀, A * exp (-κ) ^ j := sum_le_sum hterm
      _ = A * ∑ j ∈ range t₀, exp (-κ) ^ j := by rw [mul_sum]
      _ ≤ A * (1 - exp (-κ))⁻¹ :=
          mul_le_mul_of_nonneg_left (geom_partial_le (exp_pos _).le hq t₀) hA
      _ = A / (1 - exp (-κ)) := by rw [div_eq_mul_inv]
  have hsplit : ∑ t ∈ range t₀, (1 - P.notYet m t S) =
      t₀ - ∑ t ∈ range t₀, P.notYet m t S := by
    rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, mul_one]
  linarith

/-- Expectation form of a lower tail at time `⌊X⌋ + ⌊Y⌋`: every partial sum of the tail
series with at least `X + Y` terms is at least `X + Y - B`. -/
lemma lower_expect_of_tail (Pf : ∀ n : ℕ, RumorProcess n) (X Y : ℕ → ℝ) {A κ : ℝ}
    (hA : 0 ≤ A) (hκ : 0 < κ) (N : ℕ)
    (htail : ∀ n : ℕ, N ≤ n → ∀ S : Finset (Fin n), S.card = 1 → ∀ r : ℕ,
      1 - (Pf n).notYet n (⌊X n⌋₊ + ⌊Y n⌋₊ - r) S ≤ A * exp (-κ * r))
    (hX : ∀ n, N ≤ n → 0 ≤ X n) (hY : ∀ n, N ≤ n → 0 ≤ Y n) :
    ∃ B : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ S : Finset (Fin n), S.card = 1 → ∀ R : ℕ,
      X n + Y n ≤ R → X n + Y n - B ≤ ∑ t ∈ range R, (Pf n).notYet n t S := by
  refine ⟨2 + A / (1 - exp (-κ)), N, fun n hn S hS R hR => ?_⟩
  have hfX := Nat.floor_le (hX n hn)
  have hfY := Nat.floor_le (hY n hn)
  have hlX := Nat.lt_floor_add_one (X n)
  have hlY := Nat.lt_floor_add_one (Y n)
  have hR' : ⌊X n⌋₊ + ⌊Y n⌋₊ ≤ R := by
    have : ((⌊X n⌋₊ + ⌊Y n⌋₊ : ℕ) : ℝ) ≤ R := by
      push_cast
      linarith
    exact_mod_cast this
  have hsum := sum_notYet_ge_of_tail (Pf n) hA hκ (⌊X n⌋₊ + ⌊Y n⌋₊) S (htail n hn S hS) hR'
  push_cast at hsum
  linarith

/-! ### Real-number helpers -/

lemma pow_floor_logb_le {ρ x : ℝ} (hρ : 1 < ρ) (hx : 1 ≤ x) : ρ ^ ⌊logb ρ x⌋₊ ≤ x :=
  pow_le_of_logb hρ (by linarith) (Nat.floor_le (logb_nonneg hρ hx))

/-- `r ≤ 2 log₂ x` gives `(ln 2 / 2) r ≤ ln x`. -/
lemma log_ge_of_le_two_logb {x r : ℝ} (h : r ≤ 2 * logb 2 x) : log 2 / 2 * r ≤ log x := by
  have hl2 : 0 < log 2 := log_pos (by norm_num)
  have hmul := mul_le_mul_of_nonneg_right h hl2.le
  have hid : 2 * logb 2 x * log 2 = 2 * log x := by
    unfold logb
    field_simp
  linarith

lemma inv_le_exp_of_log {x r : ℝ} (hx : 0 < x) (h : log 2 / 2 * r ≤ log x) :
    1 / x ≤ exp (-(log 2 / 2) * r) := by
  rw [one_div, ← exp_log hx, ← exp_neg]
  exact exp_le_exp.mpr (by linarith)

lemma rpow_neg_half_le_exp {x r : ℝ} (hx : 0 < x) (h : log 2 / 2 * r ≤ log x) :
    x ^ (-(1 / 2 : ℝ)) ≤ exp (-(log 2 / 4) * r) := by
  rw [rpow_def_of_pos hx]
  exact exp_le_exp.mpr (by linarith)

lemma one_le_mul_exp_neg {q c : ℝ} (h : exp c ≤ q) : 1 ≤ q * exp (-c) := by
  have := mul_le_mul_of_nonneg_right h (exp_pos (-c)).le
  rwa [← exp_add, add_neg_cancel, exp_zero] at this

/-- `p / (x / 2) ≤ 2 K e` from `p q ≤ x K` and `q e ≥ 1`. -/
lemma div_half_le_of_mul {x p q K e : ℝ} (hx : 0 < x) (hp : 0 ≤ p) (he : 0 ≤ e)
    (hpq : p * q ≤ x * K) (hqe : 1 ≤ q * e) : p / (x / 2) ≤ 2 * K * e := by
  have h1 : p ≤ x * K * e := by
    calc p = p * 1 := (mul_one p).symm
      _ ≤ p * (q * e) := mul_le_mul_of_nonneg_left hqe hp
      _ = (p * q) * e := by ring
      _ ≤ (x * K) * e := mul_le_mul_of_nonneg_right hpq he
  rw [div_le_iff₀ (by positivity)]
  calc p ≤ x * K * e := h1
    _ = 2 * K * e * (x / 2) := by ring

/-- `exp((ln 2 / 2) r) ≤ ρ^k` whenever `ρ ≥ 2` and `k ≥ r / 2`. -/
lemma exp_le_pow_of_half {ρ r : ℝ} {k : ℕ} (hρ : 2 ≤ ρ) (hk : r / 2 ≤ k) :
    exp (log 2 / 2 * r) ≤ ρ ^ k := by
  have hl2 : 0 < log 2 := log_pos (by norm_num)
  calc exp (log 2 / 2 * r) ≤ exp ((k : ℝ) * log 2) := by
        apply exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hk hl2.le]
    _ = (2 : ℝ) ^ k := by rw [exp_nat_mul, exp_log (by norm_num)]
    _ ≤ ρ ^ k := pow_le_pow_left₀ (by norm_num) hρ k

/-- One informed node out of `n ≥ 2` is not everybody. -/
lemma one_sub_notYet_zero {P : RumorProcess n} (hn : 2 ≤ n) {S : Finset (Fin n)}
    (hS : S.card = 1) : 1 - P.notYet n 0 S = 0 := by
  have hb : below (n : ℝ) S = 1 := by
    simp only [below]
    rw [if_pos]
    rw [hS]
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    push_cast
    linarith
  rw [notYet_zero, hb, sub_self]

/-! ### Pull and push–pull: double exponential final phase -/

/-- Lower tail for a protocol whose growth multiplies the expected number of informed nodes by
at most `ρ ≥ 2` and whose final phase (from at least `n / 2` uninformed nodes, within
`log₂ ln n - r₀` rounds) succeeds with probability at most `C n^{-1/2}`. -/
lemma double_tail_generic (Pf : ∀ n : ℕ, RumorProcess n) {ρ C : ℝ} (hρ : 2 ≤ ρ) (hC : 0 ≤ C)
    (r₀ N₀ : ℕ)
    (hgrowth : ∀ n : ℕ, ∀ m : ℝ, 0 < m → ∀ (t : ℕ) (S : Finset (Fin n)),
      1 - (Pf n).notYet m t S ≤ ρ ^ t * S.card / m)
    (hfinal : ∀ n : ℕ, N₀ ≤ n → ∀ S : Finset (Fin n), 2 * S.card ≤ n → ∀ t : ℕ,
      (t : ℝ) + r₀ ≤ logb 2 (log n) →
        1 - (Pf n).notYet n t S ≤ C * (n : ℝ) ^ (-(1 / 2 : ℝ))) :
    ∃ A κ : ℝ, 0 ≤ A ∧ 0 < κ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ S : Finset (Fin n),
      S.card = 1 → ∀ r : ℕ,
        1 - (Pf n).notYet n (⌊logb ρ n⌋₊ + ⌊logb 2 (log n)⌋₊ - r) S ≤ A * exp (-κ * r) := by
  obtain ⟨N₁, hN₁⟩ := exists_le_log ((2 : ℝ) ^ r₀)
  have hρ1 : 1 < ρ := by linarith
  have hρ0 : 0 < ρ := by linarith
  have hρr₀ : 1 ≤ ρ ^ r₀ := one_le_pow₀ hρ1.le
  have hl2 : 0 < log 2 := log_pos (by norm_num)
  refine ⟨2 * ρ ^ r₀ + C, log 2 / 4, by positivity, by positivity, max N₀ (max N₁ 3), ?_⟩
  intro n hn S hS r
  have hn₀ : N₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn₁ : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn3 : 3 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hnr : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog1 : 1 ≤ log (n : ℝ) := by
    rw [le_log_iff_exp_le hn0]
    exact le_trans (lt_trans exp_one_lt_d9 (by norm_num)).le hnr
  obtain ⟨a, ha⟩ : ∃ a, a = ⌊logb ρ (n : ℝ)⌋₊ := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = ⌊logb 2 (log (n : ℝ))⌋₊ := ⟨_, rfl⟩
  rw [← ha, ← hd]
  have hlogb0 : 0 ≤ logb 2 (log (n : ℝ)) := logb_nonneg (by norm_num) hlog1
  have hr₀ : (r₀ : ℝ) ≤ logb 2 (log (n : ℝ)) := by
    rw [le_logb_iff_rpow_le (by norm_num) (by linarith), rpow_natCast]
    exact hN₁ n hn₁
  have hdr₀ : r₀ ≤ d := by
    rw [hd]
    exact Nat.le_floor hr₀
  have hdle : (d : ℝ) ≤ logb 2 (log (n : ℝ)) := by
    rw [hd]
    exact Nat.floor_le hlogb0
  have hale : (a : ℝ) ≤ logb ρ n := by
    rw [ha]
    exact Nat.floor_le (logb_nonneg hρ1 (by linarith))
  have hρa : ρ ^ a ≤ n := by
    rw [ha]
    exact pow_floor_logb_le hρ1 (by linarith)
  have hlogρ : logb ρ n ≤ logb 2 n := by
    unfold logb
    exact div_le_div_of_nonneg_left (log_nonneg (by linarith)) hl2
      (log_le_log (by norm_num) hρ)
  have hlog2 : logb 2 (log (n : ℝ)) ≤ logb 2 n :=
    logb_le_logb_of_le (by norm_num) (by linarith)
      (le_trans (log_le_sub_one_of_pos hn0) (by linarith))
  rcases Nat.eq_zero_or_pos (a + d - r) with h0 | hpos
  · rw [h0, one_sub_notYet_zero (by omega) hS]
    positivity
  · have hrlt : r < a + d := by omega
    have hrle : (r : ℝ) ≤ 2 * logb 2 n := by
      have : (r : ℝ) ≤ a + d := by exact_mod_cast hrlt.le
      linarith
    have hlogr := log_ge_of_le_two_logb hrle
    have hτ : ((d - r₀ : ℕ) : ℝ) + r₀ ≤ logb 2 (log (n : ℝ)) := by
      rw [Nat.cast_sub hdr₀]
      linarith
    have hmono := notYet_antitone (Pf n) n
      (show a + d - r ≤ (a + d - r - (d - r₀)) + (d - r₀) by omega) S
    have hB : 0 ≤ C * (n : ℝ) ^ (-(1 / 2 : ℝ)) := mul_nonneg hC (rpow_nonneg hn0.le _)
    have hjoin := reach_add_le (Pf n) (m := n) (m' := (n : ℝ) / 2) hB
      (a + d - r - (d - r₀)) (d - r₀)
      (fun T hT => hfinal n hn₀ T (by
        have h2 : (2 * T.card : ℝ) < n := by linarith
        have h2' : 2 * T.card < n := by exact_mod_cast h2
        omega) (d - r₀) hτ) S
    have hgrow := hgrowth n ((n : ℝ) / 2) (by positivity) (a + d - r - (d - r₀)) S
    rw [hS, Nat.cast_one, mul_one] at hgrow
    have he2 : 0 ≤ exp (-(log 2 / 2) * r) := (exp_pos _).le
    have hfirst : ρ ^ (a + d - r - (d - r₀)) / ((n : ℝ) / 2) ≤
        2 * ρ ^ r₀ * exp (-(log 2 / 2) * r) := by
      by_cases hcase : r ≤ a + r₀
      · have hs : a + d - r - (d - r₀) + r = a + r₀ := by omega
        have hpq : ρ ^ (a + d - r - (d - r₀)) * ρ ^ r ≤ n * ρ ^ r₀ := by
          rw [← pow_add, hs, pow_add]
          exact mul_le_mul_of_nonneg_right hρa (by positivity)
        have hqe : 1 ≤ ρ ^ r * exp (-(log 2 / 2) * r) := by
          rw [neg_mul]
          exact one_le_mul_exp_neg (exp_le_pow_of_half hρ (by linarith))
        exact div_half_le_of_mul hn0 (by positivity) he2 hpq hqe
      · have hs : a + d - r - (d - r₀) = 0 := by omega
        rw [hs, pow_zero]
        have hinv := inv_le_exp_of_log hn0 hlogr
        have hid : 1 / ((n : ℝ) / 2) = 2 * (1 / (n : ℝ)) := by field_simp
        rw [hid]
        have := mul_le_mul_of_nonneg_right hρr₀ he2
        linarith
    have hsecond : C * (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ C * exp (-(log 2 / 4) * r) :=
      mul_le_mul_of_nonneg_left (rpow_neg_half_le_exp hn0 hlogr) hC
    have hexp : exp (-(log 2 / 2) * r) ≤ exp (-(log 2 / 4) * r) := by
      apply exp_le_exp.mpr
      have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      nlinarith
    have hfirst' : 2 * ρ ^ r₀ * exp (-(log 2 / 2) * r) ≤ 2 * ρ ^ r₀ * exp (-(log 2 / 4) * r) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    have hsum : (2 * ρ ^ r₀ + C) * exp (-(log 2 / 4) * r) =
        2 * ρ ^ r₀ * exp (-(log 2 / 4) * r) + C * exp (-(log 2 / 4) * r) := by ring
    linarith

theorem pull_tail_explicit :
    ∃ A κ : ℝ, 0 ≤ A ∧ 0 < κ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ S : Finset (Fin n),
      S.card = 1 → ∀ r : ℕ,
        1 - (pull n).notYet n (⌊logb 2 n⌋₊ + ⌊logb 2 (log n)⌋₊ - r) S ≤ A * exp (-κ * r) :=
  double_tail_generic pull (le_refl 2) (by norm_num : (0 : ℝ) ≤ 128) 5 3
    (fun _ _ hm t S => pull_growth_lower hm t S)
    (fun n hn S hS t ht => pull_final_lower_explicit n hn S hS t (by exact_mod_cast ht))

theorem pushPull_tail_explicit :
    ∃ A κ : ℝ, 0 ≤ A ∧ 0 < κ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ S : Finset (Fin n),
      S.card = 1 → ∀ r : ℕ,
        1 - (pushPull n).notYet n (⌊logb 3 n⌋₊ + ⌊logb 2 (log n)⌋₊ - r) S ≤
          A * exp (-κ * r) :=
  double_tail_generic pushPull (by norm_num : (2 : ℝ) ≤ 3) (by positivity : (0 : ℝ) ≤ 128 * exp 1 ^ 2)
    5 3 (fun _ _ hm t S => pushPull_growth_lower hm t S)
    (fun n hn S hS t ht => pushPull_final_lower_explicit n hn S hS t (by exact_mod_cast ht))

/-! ### Push: exponential final phase -/

theorem push_tail_explicit :
    ∃ A κ : ℝ, 0 ≤ A ∧ 0 < κ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ S : Finset (Fin n),
      S.card = 1 → ∀ r : ℕ,
        1 - (push n).notYet n (⌊logb 2 n⌋₊ + ⌊log n⌋₊ - r) S ≤ A * exp (-κ * r) := by
  have hl2 : 0 < log 2 := log_pos (by norm_num)
  have hl21 : log 2 ≤ 1 := le_trans log_two_lt_d9.le (by norm_num)
  refine ⟨2 + 1600 * exp ((log 2 + 1 / 2) / 2), log 2 / 4, by positivity, by positivity, 2, ?_⟩
  intro n hn S hS r
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hlogn0 : 0 ≤ log (n : ℝ) := log_nonneg (by linarith)
  obtain ⟨a, ha⟩ : ∃ a, a = ⌊logb 2 (n : ℝ)⌋₊ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = ⌊log (n : ℝ)⌋₊ := ⟨_, rfl⟩
  rw [← ha, ← hb]
  have hlogle : log (n : ℝ) ≤ logb 2 n := by
    unfold logb
    rw [le_div_iff₀ hl2]
    nlinarith
  have hba : b ≤ a := by
    rw [ha, hb]
    exact Nat.floor_mono hlogle
  have hale : (a : ℝ) ≤ logb 2 n := by
    rw [ha]
    exact Nat.floor_le (le_trans hlogn0 hlogle)
  have hble : (b : ℝ) ≤ log n := by
    rw [hb]
    exact Nat.floor_le hlogn0
  have h2a : (2 : ℝ) ^ a ≤ n := by
    rw [ha]
    exact pow_floor_logb_le (by norm_num) (by linarith)
  rcases Nat.eq_zero_or_pos (a + b - r) with h0 | hpos
  · rw [h0, one_sub_notYet_zero hn hS]
    positivity
  · have hrlt : r < a + b := by omega
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have hrle : (r : ℝ) ≤ 2 * logb 2 n := by
      have h1 : (r : ℝ) ≤ a + b := by exact_mod_cast hrlt.le
      have h2 : (b : ℝ) ≤ a := by exact_mod_cast hba
      linarith
    have hlogr := log_ge_of_le_two_logb hrle
    have hmono := notYet_antitone (push n) n
      (show a + b - r ≤ (a - (r - r / 2)) + (b - r / 2) by omega) S
    obtain ⟨B, hBdef⟩ : ∃ B : ℝ,
        B = 1600 * exp ((1 / 2 : ℝ) * (((b - r / 2 : ℕ) : ℝ) - log ((n : ℝ) / 2))) :=
      ⟨_, rfl⟩
    have hB : 0 ≤ B := by
      rw [hBdef]
      positivity
    have hjoin := reach_add_le (push n) (m := n) (m' := (n : ℝ) / 2) hB
      (a - (r - r / 2)) (b - r / 2)
      (fun T hT => by
        refine le_trans (push_final_lower_explicit n T (b - r / 2)) ?_
        rw [hBdef]
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply exp_le_exp.mpr
        have : log ((n : ℝ) / 2) ≤ log ((n : ℝ) - T.card) :=
          log_le_log (by positivity) (by linarith)
        linarith) S
    have hgrow := push_growth_lower (n := n) (m := (n : ℝ) / 2) (by positivity)
      (a - (r - r / 2)) S
    rw [hS, Nat.cast_one, mul_one] at hgrow
    have he2 : 0 ≤ exp (-(log 2 / 2) * r) := (exp_pos _).le
    -- the growth phase
    have hfirst : (2 : ℝ) ^ (a - (r - r / 2)) / ((n : ℝ) / 2) ≤
        2 * 1 * exp (-(log 2 / 2) * r) := by
      have hs : a - (r - r / 2) + (r - r / 2) = a := by omega
      have hpq : (2 : ℝ) ^ (a - (r - r / 2)) * 2 ^ (r - r / 2) ≤ n * 1 := by
        rw [← pow_add, hs, mul_one]
        exact h2a
      have hhalf : (r : ℝ) / 2 ≤ ((r - r / 2 : ℕ) : ℝ) := by
        rw [Nat.cast_sub (Nat.div_le_self r 2)]
        have := (Nat.cast_div_le : ((r / 2 : ℕ) : ℝ) ≤ (r : ℝ) / (2 : ℕ))
        push_cast at this
        linarith
      have hqe : 1 ≤ (2 : ℝ) ^ (r - r / 2) * exp (-(log 2 / 2) * r) := by
        rw [neg_mul]
        exact one_le_mul_exp_neg (exp_le_pow_of_half (le_refl 2) hhalf)
      exact div_half_le_of_mul hn0 (by positivity) he2 hpq hqe
    -- the final phase
    have hexpo : (1 / 2 : ℝ) * (((b - r / 2 : ℕ) : ℝ) - log ((n : ℝ) / 2)) ≤
        (log 2 + 1 / 2) / 2 + -(log 2 / 4) * r := by
      have hlogdiv : log ((n : ℝ) / 2) = log n - log 2 := log_div hn0.ne' (by norm_num)
      rw [hlogdiv]
      have hlr : log 2 * r ≤ 1 * r := mul_le_mul_of_nonneg_right hl21 hr0
      by_cases hcase : r / 2 ≤ b
      · rw [Nat.cast_sub hcase]
        have h2h : (r : ℝ) ≤ 2 * ((r / 2 : ℕ) : ℝ) + 1 := by
          have : r ≤ 2 * (r / 2) + 1 := by omega
          exact_mod_cast this
        linarith
      · have hz : b - r / 2 = 0 := by omega
        rw [hz, Nat.cast_zero]
        linarith
    have hsecond : B ≤ 1600 * exp ((log 2 + 1 / 2) / 2) * exp (-(log 2 / 4) * r) := by
      rw [hBdef, mul_assoc, ← exp_add]
      exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr hexpo) (by norm_num)
    have hexp : exp (-(log 2 / 2) * r) ≤ exp (-(log 2 / 4) * r) := by
      apply exp_le_exp.mpr
      nlinarith
    have hsum : (2 + 1600 * exp ((log 2 + 1 / 2) / 2)) * exp (-(log 2 / 4) * r) =
        2 * exp (-(log 2 / 4) * r) +
          1600 * exp ((log 2 + 1 / 2) / 2) * exp (-(log 2 / 4) * r) := by ring
    linarith

/-! ### Expectations -/

theorem push_expect_explicit :
    ∃ B : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ S : Finset (Fin n), S.card = 1 → ∀ R : ℕ,
      logb 2 n + log n ≤ R → logb 2 n + log n - B ≤ ∑ t ∈ range R, (push n).notYet n t S := by
  obtain ⟨A, κ, hA, hκ, N, h⟩ := push_tail_explicit
  exact lower_expect_of_tail push (fun n => logb 2 n) (fun n => log n) hA hκ (max N 1)
    (fun n hn => h n (le_trans (le_max_left _ _) hn))
    (fun n hn => logb_nonneg (by norm_num)
      (by exact_mod_cast le_trans (le_max_right _ _) hn))
    (fun n hn => log_nonneg (by exact_mod_cast le_trans (le_max_right _ _) hn))

/-- `log₂ ln n ≥ 0` for `n ≥ 3`. -/
lemma logb_log_nonneg {n : ℕ} (hn : 3 ≤ n) : 0 ≤ logb 2 (log (n : ℝ)) := by
  have hnr : (3 : ℝ) ≤ n := by exact_mod_cast hn
  apply logb_nonneg (by norm_num)
  rw [le_log_iff_exp_le (by linarith)]
  exact le_trans (lt_trans exp_one_lt_d9 (by norm_num)).le hnr

theorem pull_expect_explicit :
    ∃ B : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ S : Finset (Fin n), S.card = 1 → ∀ R : ℕ,
      logb 2 n + logb 2 (log n) ≤ R →
        logb 2 n + logb 2 (log n) - B ≤ ∑ t ∈ range R, (pull n).notYet n t S := by
  obtain ⟨A, κ, hA, hκ, N, h⟩ := pull_tail_explicit
  exact lower_expect_of_tail pull (fun n => logb 2 n) (fun n => logb 2 (log n)) hA hκ (max N 3)
    (fun n hn => h n (le_trans (le_max_left _ _) hn))
    (fun n hn => logb_nonneg (by norm_num)
      (by exact_mod_cast le_trans (by norm_num) (le_trans (le_max_right _ _) hn)))
    (fun n hn => logb_log_nonneg (le_trans (le_max_right _ _) hn))

theorem pushPull_expect_explicit :
    ∃ B : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ S : Finset (Fin n), S.card = 1 → ∀ R : ℕ,
      logb 3 n + logb 2 (log n) ≤ R →
        logb 3 n + logb 2 (log n) - B ≤ ∑ t ∈ range R, (pushPull n).notYet n t S := by
  obtain ⟨A, κ, hA, hκ, N, h⟩ := pushPull_tail_explicit
  exact lower_expect_of_tail pushPull (fun n => logb 3 n) (fun n => logb 2 (log n)) hA hκ
    (max N 3)
    (fun n hn => h n (le_trans (le_max_left _ _) hn))
    (fun n hn => logb_nonneg (by norm_num)
      (by exact_mod_cast le_trans (by norm_num) (le_trans (le_max_right _ _) hn)))
    (fun n hn => logb_log_nonneg (le_trans (le_max_right _ _) hn))

end Epidemics.Revisited
