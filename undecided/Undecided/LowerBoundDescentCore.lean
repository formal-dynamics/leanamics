import Undecided.LowerBoundRound

/-! # Descent envelope (UND-3, Lemma 6)

Deterministic one-round step and the colour envelope used by `descent`. The undecided count
falls as `q ≤ (1 + e_s) n / 2` with `e_s = max(u^{2^s}, w)`, while every colour is at most
`descentGrowth s`, a product of one-round factors `min(2, 1 + e_s + M_s/n) + ε`.
-/

namespace Undecided.Plurality
open Finset Dynamics Real

variable {n k : ℕ}

lemma descent_miss_one_eq [NeZero n] (S : Set (Config n k)) (x : Config n k) :
    miss S 1 x =
      avg (fun r : Fin n → Fin n => by classical exact if step x r ∈ S then (0 : ℝ) else 1) := by
  classical
  unfold miss
  rw [expList_succ (T := 0)]
  simp only [expList_zero, List.foldl_cons, List.foldl_nil]
  rfl

/-- Colour envelope. `descentGrowth s` is `M_0` after `s` factors
`min(2, 1 + e_r + M_r/n) + ε`. -/
noncomputable def descentGrowth (n ε : ℝ) (e : ℕ → ℝ) (M0 : ℝ) : ℕ → ℝ :=
  Nat.rec M0 (fun r Mr => Mr * (min (2 : ℝ) (1 + e r + Mr / n) + ε))

lemma descentGrowth_zero (n ε : ℝ) (e : ℕ → ℝ) (M0 : ℝ) :
    descentGrowth n ε e M0 0 = M0 := rfl

lemma descentGrowth_succ (n ε : ℝ) (e : ℕ → ℝ) (M0 : ℝ) (s : ℕ) :
    descentGrowth n ε e M0 (s + 1) =
      descentGrowth n ε e M0 s *
        (min (2 : ℝ) (1 + e s + descentGrowth n ε e M0 s / n) + ε) := rfl

lemma max_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : max a b ^ 2 = max (a ^ 2) (b ^ 2) := by
  rcases le_total a b with h | h
  · have h2 : a ^ 2 ≤ b ^ 2 := by nlinarith only [ha, hb, h]
    rw [max_eq_right h, max_eq_right h2]
  · have h2 : b ^ 2 ≤ a ^ 2 := by nlinarith only [ha, hb, h]
    rw [max_eq_left h, max_eq_left h2]

/-- `(1 - 1/Λ)^{2^s} ≤ exp(-2^s / Λ)` for `Λ ≥ 1`. -/
lemma u_pow_le {Λ : ℝ} (hΛ : 1 ≤ Λ) (s : ℕ) :
    (1 - 1 / Λ) ^ (2 ^ s) ≤ exp (-((2 : ℝ) ^ s) / Λ) := by
  have hΛ0 : 0 < Λ := by linarith
  have hu1 : 1 / Λ ≤ 1 := by
    rw [div_le_one hΛ0]
    exact hΛ
  have hu0 : 0 ≤ 1 - 1 / Λ := by linarith
  have hexp : 1 - 1 / Λ ≤ exp (-1 / Λ) := by
    have hcomm : 1 - 1 / Λ = -1 / Λ + 1 := by ring
    rw [hcomm]
    exact add_one_le_exp (-1 / Λ)
  calc (1 - 1 / Λ) ^ (2 ^ s) ≤ exp (-1 / Λ) ^ (2 ^ s) :=
        pow_le_pow_left₀ hu0 hexp _
    _ = exp (((2 ^ s : ℕ) : ℝ) * (-1 / Λ)) := by rw [← Real.exp_nat_mul]
    _ = exp (-((2 : ℝ) ^ s) / Λ) := by
        congr 1
        push_cast
        ring

lemma descentGrowth_nonneg {n ε M0 : ℝ} {e : ℕ → ℝ} (hn : 0 < n) (hε : 0 ≤ ε) (hM0 : 0 ≤ M0)
    (he : ∀ s, 0 ≤ e s) (s : ℕ) : 0 ≤ descentGrowth n ε e M0 s := by
  induction s with
  | zero => simpa [descentGrowth_zero] using hM0
  | succ s ih =>
    rw [descentGrowth_succ]
    refine mul_nonneg ih ?_
    refine add_nonneg ?_ hε
    refine le_min (by norm_num) ?_
    have hdiv : 0 ≤ descentGrowth n ε e M0 s / n := div_nonneg ih hn.le
    linarith only [he s, hdiv]

lemma descentGrowth_ge {n ε M0 : ℝ} {e : ℕ → ℝ} (hn : 0 < n) (hε : 0 ≤ ε) (hM0 : 0 ≤ M0)
    (he : ∀ s, 0 ≤ e s) (s : ℕ) : M0 ≤ descentGrowth n ε e M0 s := by
  induction s with
  | zero => simp [descentGrowth_zero]
  | succ s ih =>
    have hnn : 0 ≤ descentGrowth n ε e M0 s := descentGrowth_nonneg hn hε hM0 he s
    rw [descentGrowth_succ]
    have hinner : (1 : ℝ) ≤ 1 + e s + descentGrowth n ε e M0 s / n := by
      have hdiv : 0 ≤ descentGrowth n ε e M0 s / n := div_nonneg hnn hn.le
      linarith only [he s, hdiv]
    have hfac : (1 : ℝ) ≤ min 2 (1 + e s + descentGrowth n ε e M0 s / n) + ε := by
      have hmin : (1 : ℝ) ≤ min 2 (1 + e s + descentGrowth n ε e M0 s / n) :=
        le_min (by norm_num) hinner
      linarith only [hε, hmin]
    calc M0 ≤ descentGrowth n ε e M0 s := ih
      _ ≤ descentGrowth n ε e M0 s *
            (min 2 (1 + e s + descentGrowth n ε e M0 s / n) + ε) :=
          le_mul_of_one_le_right hnn hfac

/-- Phase A: the factor is at most `2 + ε`, so `M_s ≤ M_0 (2 + ε)^s ≤ M_0 2^s exp(ε s / 2)`. -/
lemma descentGrowth_phaseA {n ε M0 : ℝ} {e : ℕ → ℝ} (hn : 0 < n) (hε : 0 ≤ ε) (hM0 : 0 ≤ M0)
    (he : ∀ s, 0 ≤ e s) (s : ℕ) :
    descentGrowth n ε e M0 s ≤ M0 * (2 : ℝ) ^ s * exp (ε * (s : ℝ) / 2) := by
  induction s with
  | zero =>
    simp only [descentGrowth_zero, pow_zero, Nat.cast_zero, mul_zero, zero_div, Real.exp_zero,
      mul_one]
    exact le_rfl
  | succ s ih =>
    have hnn := descentGrowth_nonneg hn hε hM0 he s
    have hfac : min (2 : ℝ) (1 + e s + descentGrowth n ε e M0 s / n) + ε ≤ 2 + ε := by
      have := min_le_left (2 : ℝ) (1 + e s + descentGrowth n ε e M0 s / n)
      linarith only [this]
    have hstep : descentGrowth n ε e M0 (s + 1) ≤ descentGrowth n ε e M0 s * (2 + ε) := by
      rw [descentGrowth_succ]
      exact mul_le_mul_of_nonneg_left hfac hnn
    have htwo : (2 : ℝ) + ε ≤ 2 * exp (ε / 2) := by
      have h1 : ε / 2 + 1 ≤ exp (ε / 2) := add_one_le_exp (ε / 2)
      have hcomm : (1 : ℝ) + ε / 2 = ε / 2 + 1 := by ring
      calc 2 + ε = 2 * (1 + ε / 2) := by ring
        _ = 2 * (ε / 2 + 1) := by rw [hcomm]
        _ ≤ 2 * exp (ε / 2) := mul_le_mul_of_nonneg_left h1 (by norm_num)
    have hMexp : 0 ≤ M0 * (2 : ℝ) ^ s * exp (ε * (s : ℝ) / 2) := by
      positivity
    have hexp_add : ε * (s : ℝ) / 2 + ε / 2 = ε * ((s + 1 : ℕ) : ℝ) / 2 := by
      push_cast
      ring
    calc descentGrowth n ε e M0 (s + 1) ≤ descentGrowth n ε e M0 s * (2 + ε) := hstep
      _ ≤ (M0 * (2 : ℝ) ^ s * exp (ε * (s : ℝ) / 2)) * (2 + ε) :=
          mul_le_mul_of_nonneg_right ih (by linarith only [hε])
      _ ≤ (M0 * (2 : ℝ) ^ s * exp (ε * (s : ℝ) / 2)) * (2 * exp (ε / 2)) :=
          mul_le_mul_of_nonneg_left htwo hMexp
      _ = M0 * (2 : ℝ) ^ (s + 1) * (exp (ε * (s : ℝ) / 2) * exp (ε / 2)) := by ring
      _ = M0 * (2 : ℝ) ^ (s + 1) * exp (ε * (s : ℝ) / 2 + ε / 2) := by rw [← Real.exp_add]
      _ = M0 * (2 : ℝ) ^ (s + 1) * exp (ε * ((s + 1 : ℕ) : ℝ) / 2) := by rw [hexp_add]

/-- `2 √(2 ℓ M) ≤ ε M` once `M ≥ M_0` and `ε = 2 √(2 ℓ / M_0)`. -/
lemma rel_dev_le {ℓ M0 M ε : ℝ} (hℓ : 0 ≤ ℓ) (hM0 : 0 < M0) (hM : M0 ≤ M)
    (hε : ε = 2 * √(2 * ℓ / M0)) : 2 * √(2 * ℓ * M) ≤ ε * M := by
  have hMpos : 0 < M := lt_of_lt_of_le hM0 hM
  have hrad : 0 ≤ 2 * ℓ / M0 := div_nonneg (by linarith only [hℓ]) hM0.le
  have hsq : √(2 * ℓ * M) ≤ √(2 * ℓ / M0) * M := by
    have hl : 0 ≤ √(2 * ℓ * M) := sqrt_nonneg _
    have hr : 0 ≤ √(2 * ℓ / M0) * M := mul_nonneg (sqrt_nonneg _) hMpos.le
    rw [← sq_le_sq₀ hl hr]
    have hnonneg : 0 ≤ 2 * ℓ * M := mul_nonneg (by linarith only [hℓ]) hMpos.le
    rw [sq_sqrt hnonneg, mul_pow, sq_sqrt hrad]
    have hrhs : 2 * ℓ / M0 * M ^ 2 = 2 * ℓ * M ^ 2 / M0 := by ring
    rw [hrhs, le_div_iff₀ hM0]
    have hmul : M * M0 ≤ M * M := mul_le_mul_of_nonneg_left hM hMpos.le
    calc 2 * ℓ * M * M0 = 2 * ℓ * (M * M0) := by ring
      _ ≤ 2 * ℓ * (M * M) := mul_le_mul_of_nonneg_left hmul (by linarith only [hℓ])
      _ = 2 * ℓ * M ^ 2 := by ring
  calc 2 * √(2 * ℓ * M) ≤ 2 * (√(2 * ℓ / M0) * M) :=
        mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ = (2 * √(2 * ℓ / M0)) * M := by ring
    _ = ε * M := by rw [hε]

/-- The envelope `(8 n / D) exp(∑_{j < d} exp(-2^j) + d δ)` stays at most `γ n / D`
when `δ d ≤ 1/6` and `γ ≥ 24`. -/
lemma envelope_le {n D γ δ : ℝ} {d : ℕ} (hn : 0 < n) (hD : 0 < D)
    (hδ : (d : ℝ) * δ ≤ 1 / 6) (hγ : (24 : ℝ) ≤ γ) :
    (8 * n / D) * exp (∑ j ∈ Finset.range d, exp (-((2 : ℝ) ^ j)) + (d : ℝ) * δ) ≤
      γ * n / D := by
  have hsum := sum_exp_neg_two_pow_le d
  have harg : ∑ j ∈ Finset.range d, exp (-((2 : ℝ) ^ j)) + (d : ℝ) * δ ≤ 1 := by
    linarith only [hsum, hδ]
  have hnn : 0 ≤ 8 * n / D := div_nonneg (by positivity) hD.le
  calc (8 * n / D) * exp (∑ j ∈ Finset.range d, exp (-((2 : ℝ) ^ j)) + (d : ℝ) * δ)
      ≤ (8 * n / D) * exp 1 := mul_le_mul_of_nonneg_left (exp_le_exp.mpr harg) hnn
    _ ≤ (8 * n / D) * 3 := mul_le_mul_of_nonneg_left exp_one_le_three hnn
    _ = 24 * n / D := by ring
    _ ≤ γ * n / D := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hγ hn.le) hD.le

/-- Phase B, from round `a` on: `M_{a+d} ≤ (8 n / D) exp(∑_{j < d} exp(-2^j) + d (γ/D + ε))`,
using `e_{a+d} ≤ exp(-2^d)` and the inductive colour bound `M ≤ γ n / D`. -/
lemma descentGrowth_phaseB {n ε γ D M0 : ℝ} {e : ℕ → ℝ} {a N : ℕ}
    (hn : 0 < n) (hD : 0 < D) (hε : 0 ≤ ε) (hγ : (24 : ℝ) ≤ γ)
    (hM0 : 0 ≤ M0) (he : ∀ s, 0 ≤ e s)
    (hbase : descentGrowth n ε e M0 a ≤ 8 * n / D)
    (hdrift : ∀ d ≤ N, (d : ℝ) * (γ / D + ε) ≤ 1 / 6)
    (he_decay : ∀ d < N, e (a + d) ≤ exp (-((2 : ℝ) ^ d)))
    (d : ℕ) (hd : d ≤ N) :
    descentGrowth n ε e M0 (a + d) ≤
      (8 * n / D) * exp (∑ j ∈ Finset.range d, exp (-((2 : ℝ) ^ j)) +
        (d : ℝ) * (γ / D + ε)) := by
  induction d with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_mul, add_zero,
      Real.exp_zero, mul_one]
    exact hbase
  | succ d ih =>
    have hdN : d ≤ N := by omega
    have hd_lt : d < N := by omega
    have hIH := ih hdN
    have hMγ : descentGrowth n ε e M0 (a + d) ≤ γ * n / D :=
      hIH.trans (envelope_le hn hD (hdrift d hdN) hγ)
    have hnn := descentGrowth_nonneg hn hε hM0 he (a + d)
    have hMn : descentGrowth n ε e M0 (a + d) / n ≤ γ / D := by
      rw [div_le_iff₀ hn]
      calc descentGrowth n ε e M0 (a + d) ≤ γ * n / D := hMγ
        _ = (γ / D) * n := by ring
    have hfac : min (2 : ℝ) (1 + e (a + d) + descentGrowth n ε e M0 (a + d) / n) + ε ≤
        1 + exp (-((2 : ℝ) ^ d)) + γ / D + ε := by
      have hmin := min_le_right (2 : ℝ) (1 + e (a + d) + descentGrowth n ε e M0 (a + d) / n)
      linarith only [hmin, he_decay d hd_lt, hMn]
    have hexp : 1 + exp (-((2 : ℝ) ^ d)) + γ / D + ε ≤
        exp (exp (-((2 : ℝ) ^ d)) + γ / D + ε) := by
      have := add_one_le_exp (exp (-((2 : ℝ) ^ d)) + γ / D + ε)
      linarith only [this]
    have hstep : descentGrowth n ε e M0 (a + (d + 1)) ≤
        descentGrowth n ε e M0 (a + d) *
          exp (exp (-((2 : ℝ) ^ d)) + γ / D + ε) := by
      have hidx : a + (d + 1) = (a + d) + 1 := by omega
      rw [hidx, descentGrowth_succ]
      calc descentGrowth n ε e M0 (a + d) *
            (min 2 (1 + e (a + d) + descentGrowth n ε e M0 (a + d) / n) + ε)
          ≤ descentGrowth n ε e M0 (a + d) *
              (1 + exp (-((2 : ℝ) ^ d)) + γ / D + ε) :=
            mul_le_mul_of_nonneg_left hfac hnn
        _ ≤ descentGrowth n ε e M0 (a + d) *
              exp (exp (-((2 : ℝ) ^ d)) + γ / D + ε) :=
            mul_le_mul_of_nonneg_left hexp hnn
    have hsum : ∑ j ∈ Finset.range (d + 1), exp (-((2 : ℝ) ^ j)) =
        ∑ j ∈ Finset.range d, exp (-((2 : ℝ) ^ j)) + exp (-((2 : ℝ) ^ d)) := by
      rw [Finset.sum_range_succ]
    have hcoeff : (d : ℝ) * (γ / D + ε) + (γ / D + ε) = ((d + 1 : ℕ) : ℝ) * (γ / D + ε) := by
      push_cast
      ring
    calc descentGrowth n ε e M0 (a + (d + 1))
        ≤ descentGrowth n ε e M0 (a + d) *
            exp (exp (-((2 : ℝ) ^ d)) + γ / D + ε) := hstep
      _ ≤ ((8 * n / D) * exp (∑ j ∈ Finset.range d, exp (-((2 : ℝ) ^ j)) +
            (d : ℝ) * (γ / D + ε))) *
            exp (exp (-((2 : ℝ) ^ d)) + γ / D + ε) :=
          mul_le_mul_of_nonneg_right hIH (exp_nonneg _)
      _ = (8 * n / D) * exp (∑ j ∈ Finset.range (d + 1), exp (-((2 : ℝ) ^ j)) +
            ((d + 1 : ℕ) : ℝ) * (γ / D + ε)) := by
          have hreassoc : ((8 * n / D) * exp (∑ j ∈ Finset.range d, exp (-((2 : ℝ) ^ j)) +
                (d : ℝ) * (γ / D + ε))) * exp (exp (-((2 : ℝ) ^ d)) + γ / D + ε) =
              (8 * n / D) * (exp (∑ j ∈ Finset.range d, exp (-((2 : ℝ) ^ j)) +
                (d : ℝ) * (γ / D + ε)) * exp (exp (-((2 : ℝ) ^ d)) + γ / D + ε)) := by ring
          rw [hreassoc, ← Real.exp_add]
          congr 1
          congr 1
          calc ∑ j ∈ Finset.range d, exp (-((2 : ℝ) ^ j)) + (d : ℝ) * (γ / D + ε) +
                (exp (-((2 : ℝ) ^ d)) + γ / D + ε)
              = ∑ j ∈ Finset.range d, exp (-((2 : ℝ) ^ j)) + exp (-((2 : ℝ) ^ d)) +
                ((d : ℝ) * (γ / D + ε) + (γ / D + ε)) := by ring
            _ = ∑ j ∈ Finset.range d, exp (-((2 : ℝ) ^ j)) + exp (-((2 : ℝ) ^ d)) +
                ((d + 1 : ℕ) : ℝ) * (γ / D + ε) := by rw [hcoeff]
            _ = ∑ j ∈ Finset.range (d + 1), exp (-((2 : ℝ) ^ j)) +
                ((d + 1 : ℕ) : ℝ) * (γ / D + ε) := by rw [← hsum]

/-- On a good round, colours grow by at most `min(2, 1 + e + M/n) + ε`, the undecided count
stays at least `n/2 - 2 γ² n / D`, and it is at most `(1 + e') n / 2` when
`e' ≥ max(e², w²)`. -/
lemma descent_step_of_good {ℓ γ D M e w e' ε : ℝ} {m : Fin k} {y z : Config n k}
    (hn : 0 < (n : ℝ)) (hk : 0 < k) (hℓ : 0 ≤ ℓ) (h6 : 6 * ℓ ≤ n)
    (hγ : 1 ≤ γ) (hD : 0 < D) (hM : 0 ≤ M) (he : 0 ≤ e) (hw : 0 ≤ w)
    (hε : 0 ≤ ε)
    (hmax : (maxCount y : ℝ) ≤ M) (hMγ : M ≤ γ * n / D)
    (hlo : (1 - w) * n / 2 ≤ und y) (hhi : und y ≤ (1 + e) * n / 2)
    (hemargin : e ≤ 1 - 1 / (k : ℝ))
    (hdevU : 2 * √(ℓ * n) ≤ n / (16 * (k : ℝ) ^ 3))
    (hdevD : 2 * √(ℓ * n) ≤ n / D)
    (h6M : 6 * ℓ ≤ 2 * M)
    (hdevC : 2 * √(2 * ℓ * M) ≤ ε * M)
    (he' : max (e ^ 2) (w ^ 2) ≤ e')
    (hG : Good ℓ m y z) :
    (maxCount z : ℝ) ≤ M * (min 2 (1 + e + M / n) + ε) ∧
      n / 2 - 2 * γ ^ 2 * n / D ≤ und z ∧
      und z ≤ (1 + e') * n / 2 := by
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = 2 * und y / n - 1 := ⟨_, rfl⟩
  have hundδ : und y = (1 + δ) * n / 2 := by
    rw [hδdef]
    field_simp
    ring
  have h2hi : 2 * und y ≤ (1 + e) * n := by
    calc 2 * und y ≤ 2 * ((1 + e) * n / 2) := mul_le_mul_of_nonneg_left hhi (by norm_num)
      _ = (1 + e) * n := by ring
  have hδhi : δ ≤ e := by
    rw [hδdef, sub_le_iff_le_add, div_le_iff₀ hn]
    linarith only [h2hi]
  have h2lo : (1 - w) * n ≤ 2 * und y := by
    calc (1 - w) * n = 2 * ((1 - w) * n / 2) := by ring
      _ ≤ 2 * und y := mul_le_mul_of_nonneg_left hlo (by norm_num)
  have hδlo : -w ≤ δ := by
    rw [hδdef]
    have heq : (1 - w) * n / n = 1 - w := by field_simp
    have hdiv : (1 - w) * n / n ≤ 2 * und y / n := div_le_div_of_nonneg_right h2lo hn.le
    linarith only [heq, hdiv]
  have habs : |δ| ≤ max e w := by
    rw [abs_le]
    constructor
    · calc -(max e w) ≤ -w := neg_le_neg (le_max_right e w)
        _ ≤ δ := hδlo
    · calc δ ≤ e := hδhi
        _ ≤ max e w := le_max_left e w
  have hδsq : δ ^ 2 ≤ max (e ^ 2) (w ^ 2) := by
    have hmax0 : 0 ≤ max e w := le_trans he (le_max_left _ _)
    calc δ ^ 2 ≤ (max e w) ^ 2 := by
          rw [sq_le_sq, abs_of_nonneg hmax0]
          exact habs
      _ = max (e ^ 2) (w ^ 2) := max_sq he hw
  have hmargin : 1 / (2 * (k : ℝ)) ≤ 1 - δ := by
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have h1e : 1 / (k : ℝ) ≤ 1 - e := by linarith only [hemargin]
    have h1δ : 1 / (k : ℝ) ≤ 1 - δ := by linarith only [h1e, hδhi]
    have hhalf : 1 / (2 * (k : ℝ)) ≤ 1 / (k : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hk0]
      nlinarith only [hk0.le]
    exact hhalf.trans h1δ
  have hsq := square_of_good hn hk hℓ h6 hundδ hmargin hdevU hG
  have hlow := not_below_of_good hn hℓ h6 hγ hD (hmax.trans hMγ) hdevD hG
  have hup : und z ≤ (1 + e') * n / 2 := by
    have hδe : δ ^ 2 ≤ e' := hδsq.trans he'
    calc und z ≤ (1 + δ ^ 2) * n / 2 := hsq
      _ ≤ (1 + e') * n / 2 := by
          have hmul : (1 + δ ^ 2) * n ≤ (1 + e') * n := by nlinarith only [hδe, hn.le]
          have hdiv : (1 + δ ^ 2) * n / 2 ≤ (1 + e') * n / 2 :=
            div_le_div_of_nonneg_right hmul (by norm_num)
          exact hdiv
  have hcntM : ∀ i, cnt y i ≤ M := by
    intro i
    calc cnt y i = (count y (some i) : ℝ) := rfl
      _ ≤ (maxCount y : ℝ) := by exact_mod_cast count_le_maxCount y i
      _ ≤ M := hmax
  have hmu2 : ∀ i, mu y i ≤ M * 2 := by
    intro i
    calc mu y i ≤ 2 * cnt y i := mu_le_two_cnt y i hn
      _ ≤ 2 * M := mul_le_mul_of_nonneg_left (hcntM i) (by norm_num)
      _ = M * 2 := by ring
  have hmu1 : ∀ i, mu y i ≤ M * (1 + e + M / n) := by
    intro i
    have hprod : cnt y i * (cnt y i + 2 * und y) ≤ M * (M + 2 * und y) := by
      have hc := hcntM i
      have hc0 := cnt_nonneg y i
      have hq0 := und_nonneg y
      nlinarith only [hc, hc0, hq0, hM]
    have hlin : M + 2 * und y ≤ (1 + e + M / n) * n := by
      have hMeq : M / n * n = M := div_mul_cancel₀ M hn.ne'
      have hrhs : (1 + e + M / n) * n = (1 + e) * n + M := by
        calc (1 + e + M / n) * n = (1 + e) * n + M / n * n := by ring
          _ = (1 + e) * n + M := by rw [hMeq]
      linarith only [h2hi, hrhs]
    calc mu y i = cnt y i * (cnt y i + 2 * und y) / n := rfl
      _ ≤ M * (M + 2 * und y) / n := div_le_div_of_nonneg_right hprod hn.le
      _ ≤ M * ((1 + e + M / n) * n) / n :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlin hM) hn.le
      _ = M * (1 + e + M / n) := by field_simp
  have hmuMin : ∀ i, mu y i ≤ M * min 2 (1 + e + M / n) := by
    intro i
    rw [mul_min_of_nonneg (2 : ℝ) (1 + e + M / n) hM]
    exact le_min (hmu2 i) (hmu1 i)
  have hdev : ∀ i, dev ℓ (mu y i) ≤ ε * M := by
    intro i
    have h6M' : 6 * ℓ ≤ M * 2 := by simpa [mul_comm] using h6M
    calc dev ℓ (mu y i) ≤ 2 * √(ℓ * (M * 2)) := dev_le hℓ (hmu2 i) h6M'
      _ = 2 * √(2 * ℓ * M) := by rw [show ℓ * (M * 2) = 2 * ℓ * M by ring]
      _ ≤ ε * M := hdevC
  have hcnt : ∀ i, cnt z i ≤ M * (min 2 (1 + e + M / n) + ε) := by
    intro i
    calc cnt z i ≤ mu y i + dev ℓ (mu y i) := hG.1 i
      _ ≤ M * min 2 (1 + e + M / n) + ε * M := add_le_add (hmuMin i) (hdev i)
      _ = M * (min 2 (1 + e + M / n) + ε) := by ring
  have hB0 : 0 ≤ M * (min 2 (1 + e + M / n) + ε) := by
    refine mul_nonneg hM ?_
    refine add_nonneg ?_ hε
    refine le_min (by norm_num) ?_
    have hdiv : 0 ≤ M / n := div_nonneg hM hn.le
    linarith only [he, hdiv]
  exact ⟨cast_maxCount_le hB0 hcnt, hlow, hup⟩

/-- `k ε ≤ 1/100` for the relative colour deviation under `(C k)^6 log n ≤ n` and `C ≥ 8`. -/
lemma colour_eps_small {C k n M0 ℓ ε : ℝ} (hC : (8 : ℝ) ≤ C) (hk : (1 : ℝ) ≤ k) (hn : 0 < n)
    (hlog : 0 < log n) (hM0 : 2 * n / k ^ 2 ≤ M0) (hℓ : ℓ = 3 * log n)
    (hpoly : k ^ 6 * log n ≤ n / C ^ 6) (hε : ε = 2 * √(2 * ℓ / M0)) :
    k * ε ≤ 1 / 100 := by
  have hk0 : 0 ≤ k := by linarith
  have hfrac : 6 * log n / M0 ≤ 3 * k ^ 2 * log n / n := by
    have hden : 2 * n / k ^ 2 ≤ M0 := hM0
    have hinv : 6 * log n / M0 ≤ 6 * log n / (2 * n / k ^ 2) := by
      apply div_le_div_of_nonneg_left (by linarith only [hlog]) _ hden
      positivity
    calc 6 * log n / M0 ≤ 6 * log n / (2 * n / k ^ 2) := hinv
      _ = 3 * k ^ 2 * log n / n := by field_simp; ring
  have hsqrt : √(2 * ℓ / M0) ≤ k * √(3 * log n / n) := by
    have harg : 2 * ℓ / M0 ≤ 3 * k ^ 2 * log n / n := by
      rw [hℓ]
      have : 2 * (3 * log n) / M0 = 6 * log n / M0 := by ring
      linarith only [hfrac, this]
    have hleft : 0 ≤ √(2 * ℓ / M0) := sqrt_nonneg _
    have hright : 0 ≤ √(3 * k ^ 2 * log n / n) := sqrt_nonneg _
    have hsq : 2 * ℓ / M0 ≤ 3 * k ^ 2 * log n / n := harg
    have hsqrt_le : √(2 * ℓ / M0) ≤ √(3 * k ^ 2 * log n / n) := sqrt_le_sqrt hsq
    have heq : √(3 * k ^ 2 * log n / n) = k * √(3 * log n / n) := by
      have h3 : 0 ≤ 3 * log n / n := div_nonneg (by linarith only [hlog]) hn.le
      rw [show 3 * k ^ 2 * log n / n = k ^ 2 * (3 * log n / n) by ring, sqrt_mul (sq_nonneg k),
        sqrt_sq hk0]
    linarith only [hsqrt_le, heq]
  have hεle : ε ≤ 2 * k * √(3 * log n / n) := by
    calc ε = 2 * √(2 * ℓ / M0) := hε
      _ ≤ 2 * (k * √(3 * log n / n)) := mul_le_mul_of_nonneg_left hsqrt (by norm_num)
      _ = 2 * k * √(3 * log n / n) := by ring
  have hke : k * ε ≤ 2 * k ^ 2 * √(3 * log n / n) := by
    calc k * ε ≤ k * (2 * k * √(3 * log n / n)) :=
          mul_le_mul_of_nonneg_left hεle hk0
      _ = 2 * k ^ 2 * √(3 * log n / n) := by ring
  have hsq_le : (k * ε) ^ 2 ≤ 12 * (k ^ 4 * log n / n) := by
    have hnn : 0 ≤ k * ε := mul_nonneg hk0 (by rw [hε]; positivity)
    have htarget : 0 ≤ 2 * k ^ 2 * √(3 * log n / n) := by positivity
    have hsq := sq_le_sq₀ hnn htarget |>.mpr hke
    calc (k * ε) ^ 2 ≤ (2 * k ^ 2 * √(3 * log n / n)) ^ 2 := hsq
      _ = 4 * k ^ 4 * (3 * log n / n) := by
          rw [mul_pow, sq_sqrt (div_nonneg (by linarith only [hlog]) hn.le)]
          ring
      _ = 12 * (k ^ 4 * log n / n) := by ring
  have hpoly' : k ^ 4 * log n / n ≤ 1 / C ^ 6 := by
    have hk4 : (1 : ℝ) ≤ k ^ 2 := by
      have h2 : (1 : ℝ) ≤ k ^ 2 := by nlinarith only [hk]
      exact h2
    rw [div_le_div_iff₀ hn (pow_pos (by linarith : 0 < C) 6)]
    have hmul : k ^ 4 * log n * C ^ 6 ≤ n := by
      have hcomm : k ^ 6 * log n * C ^ 6 ≤ n := by
        rw [le_div_iff₀ (pow_pos (by linarith : 0 < C) 6)] at hpoly
        linarith only [hpoly]
      calc k ^ 4 * log n * C ^ 6 = (k ^ 6 * log n * C ^ 6) / k ^ 2 := by field_simp
        _ ≤ n / k ^ 2 := by
            exact div_le_div_of_nonneg_right hcomm (by positivity)
        _ ≤ n := by
            exact div_le_self (by linarith only [hn.le]) hk4
    linarith only [hmul]
  have h12 : (k * ε) ^ 2 ≤ 12 / C ^ 6 := by
    calc (k * ε) ^ 2 ≤ 12 * (k ^ 4 * log n / n) := hsq_le
      _ ≤ 12 * (1 / C ^ 6) := mul_le_mul_of_nonneg_left hpoly' (by norm_num)
      _ = 12 / C ^ 6 := by ring
  have hden : (120000 : ℝ) ≤ C ^ 6 := by
    have h8 : (8 : ℝ) ^ 6 ≤ C ^ 6 := pow_le_pow_left₀ (by norm_num) hC 6
    have hnum : (120000 : ℝ) ≤ 8 ^ 6 := by norm_num
    exact hnum.trans h8
  have hsmall : 12 / C ^ 6 ≤ (1 / 100) ^ 2 := by
    rw [show (1 / 100 : ℝ) ^ 2 = 1 / 10000 by norm_num]
    rw [div_le_div_iff₀ (pow_pos (by linarith : 0 < C) 6) (by norm_num)]
    nlinarith only [hden]
  have hnn : 0 ≤ k * ε := mul_nonneg hk0 (by rw [hε]; positivity)
  exact (sq_le_sq₀ hnn (by norm_num : (0 : ℝ) ≤ 1 / 100)).mp (h12.trans hsmall)

end Undecided.Plurality
