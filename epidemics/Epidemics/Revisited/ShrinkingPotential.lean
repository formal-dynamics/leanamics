import Epidemics.Revisited.ShrinkingAux
import Epidemics.Revisited.ShrinkingDefs
import Epidemics.Revisited.Growth

/-! # A quadratic potential for the exponential shrinking regime (Theorem 31)

With `u = n - |S|` uninformed nodes, the potential is `Φ_β(S) = u + (β / n) u²`. Under the upper
exponential shrinking conditions, once `u ≤ g₀ n` for a small `g₀`, one round multiplies its
expectation by at most `e^{-ρ} (1 + K / n)` (`apply_shrinkPot_le`):

* `E[u'] ≤ u (e^{-ρ} + a u / n)` by condition (i);
* `E[u'²] = Var[u'] + E[u']² ≤ (1 + c) u + E[u']²` by Lemma 9 with the covariance bound `c / u`;
* the excess `a u² / n` of the first line is paid by the drop of the quadratic term, provided
  `a + β q₀² ≤ β e^{-ρ}` with `q₀ = e^{-ρ} + a g₀`, and the variance term `β (1 + c) u / n` by
  the factor `1 + K / n`, provided `β (1 + c) ≤ e^{-ρ} K`.

Since `Φ_β ≥ 1` while some node is uninformed, Markov's inequality after
`T = ⌈ln n / ρ⌉ + r` rounds gives `P[T(·, n) > T] ≤ e^{-ρ T} (1 + K / n)^T Φ_β(S)`, and
`(1 + K / n)^T` stays bounded because `ln n ≤ n` (`notYet_shrink_stage2`). This replaces the
paper's phase calculus (Lemmas 32-37) for this regime.
-/

namespace Epidemics.Revisited
open Finset Dynamics

variable {n : ℕ}

lemma card_cast_le (T : Finset (Fin n)) : (T.card : ℝ) ≤ n := by
  have h : T.card ≤ n := by simpa [Fintype.card_fin] using card_le_univ (s := T)
  exact_mod_cast h

/-- The potential `u + (β / n) u²` in the number `u = n - |T|` of uninformed nodes. -/
noncomputable def shrinkPot (β : ℝ) (T : Finset (Fin n)) : ℝ :=
  ((n : ℝ) - T.card) + β / n * ((n : ℝ) - T.card) ^ 2

lemma shrinkPot_nonneg {β : ℝ} (hβ : 0 ≤ β) (T : Finset (Fin n)) : 0 ≤ shrinkPot β T := by
  have h1 := sub_nonneg.mpr (card_cast_le T)
  have h2 : 0 ≤ β / n * ((n : ℝ) - T.card) ^ 2 :=
    mul_nonneg (div_nonneg hβ (Nat.cast_nonneg n)) (sq_nonneg _)
  unfold shrinkPot
  linarith only [h1, h2]

/-- While some node is uninformed, the potential is at least one. -/
lemma below_le_shrinkPot {β : ℝ} (hβ : 0 ≤ β) (T : Finset (Fin n)) :
    below (n : ℝ) T ≤ shrinkPot β T := by
  by_cases h : (T.card : ℝ) < n
  · have hb : below (n : ℝ) T = 1 := by simp [below, h]
    have hlt : T.card < n := by exact_mod_cast h
    have hu : (1 : ℝ) ≤ (n : ℝ) - T.card := by
      have hle : ((T.card + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hlt
      push_cast at hle
      linarith only [hle]
    have h2 : 0 ≤ β / n * ((n : ℝ) - T.card) ^ 2 :=
      mul_nonneg (div_nonneg hβ (Nat.cast_nonneg n)) (sq_nonneg _)
    rw [hb]
    unfold shrinkPot
    linarith only [hu, h2]
  · have hb : below (n : ℝ) T = 0 := by simp [below, h]
    rw [hb]
    exact shrinkPot_nonneg hβ T

/-- Expected number of uninformed nodes after one round under condition (i). -/
lemma expect_deficit_le (P : RumorProcess n) {ρ a c g : ℝ} (hUS : P.UpperShrinking ρ a c g)
    (S : Finset (Fin n)) (hS : (n : ℝ) - S.card ≤ g * n) :
    (P.K S).expect (fun T => (n : ℝ) - T.card) ≤
      ((n : ℝ) - S.card) * (Real.exp (-ρ) + a * (((n : ℝ) - S.card) / n)) := by
  rw [expect_deficit]
  have hterm : ∀ x ∈ (univ : Finset (Fin n)) \ S,
      1 - P.informProb S x ≤ Real.exp (-ρ) + a * (((n : ℝ) - S.card) / n) :=
    fun x hx => (hUS S hS).1 x (mem_sdiff.mp hx).2
  have hsum := sum_le_sum hterm
  rw [sum_const, nsmul_eq_mul, card_compl_cast] at hsum
  exact hsum

/-- Second moment of the number of uninformed nodes after one round:
`E[u'²] ≤ (1 + c) u + E[u']²` (Lemma 9 with the covariance bound `c / u`). -/
lemma expect_deficit_sq_le (P : RumorProcess n) {ρ a c g : ℝ} (hc : 0 ≤ c)
    (hUS : P.UpperShrinking ρ a c g) (S : Finset (Fin n)) (hS : (n : ℝ) - S.card ≤ g * n) :
    (P.K S).expect (fun T => ((n : ℝ) - T.card) ^ 2) ≤
      (1 + c) * ((n : ℝ) - S.card) + ((P.K S).expect (fun T => (n : ℝ) - T.card)) ^ 2 := by
  set D := P.K S with hD
  set u : ℝ := (n : ℝ) - S.card with hu
  set μ : ℝ := D.expect (fun T => (n : ℝ) - T.card) with hμ
  set E : ℝ := D.expect (fun T => (T.card : ℝ)) with hE
  have hu0 : 0 ≤ u := sub_nonneg.mpr (card_cast_le S)
  have hμE : μ = (n : ℝ) - E := by
    rw [hμ, Distribution.expect_sub, Distribution.expect_const]
  have hμ0 : 0 ≤ μ := D.expect_nonneg (fun T => sub_nonneg.mpr (card_cast_le T))
  have hvar := variance_card_le P S (div_nonneg hc hu0) (hUS S hS).2
  have hcu : c / u * ((n : ℝ) - S.card) ^ 2 = c * u := by
    rw [← hu]
    rcases eq_or_lt_of_le hu0 with h0 | hpos
    · rw [← h0]
      ring
    · field_simp
  have hcent : D.expect (fun T => ((n : ℝ) - T.card - μ) ^ 2) =
      D.expect (fun T => ((T.card : ℝ) - E) ^ 2) := by
    congr 1
    funext T
    rw [hμE]
    ring
  have hsq := expect_sq_centered D (fun T => (n : ℝ) - T.card)
  rw [← hμ, hcent] at hsq
  have hEu : E - S.card = u - μ := by
    rw [hμE, hu]
    ring
  linarith only [hsq, hvar, hcu, hEu, hμ0]

/-- One round contracts the potential `Φ_β` by `e^{-ρ} (1 + K / n)` once at most `g₀ n` nodes
are uninformed. -/
lemma apply_shrinkPot_le (P : RumorProcess n) {ρ a c g g₀ β K : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hg₀ : g₀ ≤ g) (hβ : 0 ≤ β) (hK : 0 ≤ K)
    (hβq : a + β * (Real.exp (-ρ) + a * g₀) ^ 2 ≤ β * Real.exp (-ρ))
    (hβK : β * (1 + c) ≤ Real.exp (-ρ) * K)
    (hUS : P.UpperShrinking ρ a c g) (hn : 0 < (n : ℝ))
    (S : Finset (Fin n)) (hS : (n : ℝ) - S.card ≤ g₀ * n) :
    P.K.apply (shrinkPot β) S ≤ Real.exp (-ρ) * (1 + K / n) * shrinkPot β S := by
  set D := P.K S with hD
  set u : ℝ := (n : ℝ) - S.card with hu
  set μ : ℝ := D.expect (fun T => (n : ℝ) - T.card) with hμ
  set x : ℝ := Real.exp (-ρ) with hx
  set q₀ : ℝ := x + a * g₀ with hq₀
  have hu0 : 0 ≤ u := sub_nonneg.mpr (card_cast_le S)
  have hSg : u ≤ g * n := le_trans hS (mul_le_mul_of_nonneg_right hg₀ hn.le)
  have hμ0 : 0 ≤ μ := D.expect_nonneg (fun T => sub_nonneg.mpr (card_cast_le T))
  have hμle : μ ≤ u * (x + a * (u / n)) := expect_deficit_le P hUS S hSg
  have hsq : D.expect (fun T => ((n : ℝ) - T.card) ^ 2) ≤ (1 + c) * u + μ ^ 2 :=
    expect_deficit_sq_le P hc hUS S hSg
  have hun : u / n ≤ g₀ := (div_le_iff₀ hn).mpr hS
  have hq : x + a * (u / n) ≤ q₀ := by
    have := mul_le_mul_of_nonneg_left hun ha
    rw [hq₀]
    linarith only [this]
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have hqnn : 0 ≤ x + a * (u / n) := add_nonneg hx0 (mul_nonneg ha (div_nonneg hu0 hn.le))
  have hμq : μ ≤ u * q₀ := le_trans hμle (mul_le_mul_of_nonneg_left hq hu0)
  have hμ2 : μ ^ 2 ≤ u ^ 2 * q₀ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hμ0 hμq 2
  have hEΦ : P.K.apply (shrinkPot β) S =
      μ + β / n * D.expect (fun T => ((n : ℝ) - T.card) ^ 2) := by
    rw [Kernel.apply]
    unfold shrinkPot
    rw [Distribution.expect_add, Distribution.expect_mul]
  have hΦS : shrinkPot β S = u + β / n * u ^ 2 := rfl
  have hβn : 0 ≤ β / n := div_nonneg hβ hn.le
  have hμlin : μ ≤ x * u + a * u ^ 2 / n := by
    have heq : u * (x + a * (u / n)) = x * u + a * u ^ 2 / n := by ring
    linarith only [hμle, heq]
  have hfirst : μ + β / n * D.expect (fun T => ((n : ℝ) - T.card) ^ 2) ≤
      (x * u + a * u ^ 2 / n) + β / n * ((1 + c) * u + u ^ 2 * q₀ ^ 2) := by
    have h2 : β / n * D.expect (fun T => ((n : ℝ) - T.card) ^ 2) ≤
        β / n * ((1 + c) * u + u ^ 2 * q₀ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hβn
      linarith only [hsq, hμ2]
    linarith only [hμlin, h2]
  have hdiff : x * (1 + K / n) * (u + β / n * u ^ 2) -
      ((x * u + a * u ^ 2 / n) + β / n * ((1 + c) * u + u ^ 2 * q₀ ^ 2)) =
      u ^ 2 / n * (β * x - (a + β * q₀ ^ 2)) + u / n * (x * K - β * (1 + c)) +
        x * K * β * u ^ 2 / n ^ 2 := by
    field_simp
    ring
  have ht1 : 0 ≤ u ^ 2 / n * (β * x - (a + β * q₀ ^ 2)) :=
    mul_nonneg (div_nonneg (sq_nonneg u) hn.le) (by linarith only [hβq])
  have ht2 : 0 ≤ u / n * (x * K - β * (1 + c)) :=
    mul_nonneg (div_nonneg hu0 hn.le) (by linarith only [hβK])
  have ht3 : 0 ≤ x * K * β * u ^ 2 / n ^ 2 :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hx0 hK) hβ) (sq_nonneg u)) (sq_nonneg _)
  rw [hEΦ, hΦS]
  linarith only [hfirst, hdiff, ht1, ht2, ht3]

/-- Iterating the contraction: `E[Φ_β(S_t)] ≤ (e^{-ρ} (1 + K / n))^t Φ_β(S)`. -/
lemma iterate_shrinkPot_le (P : RumorProcess n) {ρ a c g g₀ β K : ℝ} (ha : 0 ≤ a)
    (hc : 0 ≤ c) (hg₀ : g₀ ≤ g) (hβ : 0 ≤ β) (hK : 0 ≤ K)
    (hβq : a + β * (Real.exp (-ρ) + a * g₀) ^ 2 ≤ β * Real.exp (-ρ))
    (hβK : β * (1 + c) ≤ Real.exp (-ρ) * K)
    (hUS : P.UpperShrinking ρ a c g) (hn : 0 < (n : ℝ)) (t : ℕ)
    (S : Finset (Fin n)) (hS : (n : ℝ) - S.card ≤ g₀ * n) :
    P.K.iterate t (shrinkPot β) S ≤ (Real.exp (-ρ) * (1 + K / n)) ^ t * shrinkPot β S := by
  have hlam : 0 ≤ Real.exp (-ρ) * (1 + K / n) :=
    mul_nonneg (Real.exp_pos _).le (by have := div_nonneg hK hn.le; linarith only [this])
  induction t generalizing S with
  | zero => simp
  | succ t ih =>
    rw [Kernel.iterate_succ]
    have hpt : ∀ T, S ⊆ T → P.K.iterate t (shrinkPot β) T ≤
        (Real.exp (-ρ) * (1 + K / n)) ^ t * shrinkPot β T := by
      intro T hT
      have hcard : (S.card : ℝ) ≤ T.card := Nat.cast_le.mpr (card_le_card hT)
      exact ih T (by linarith only [hS, hcard])
    have hE := expect_le_of_weight P S hpt
    rw [Distribution.expect_mul] at hE
    have hstep := apply_shrinkPot_le P ha hc hg₀ hβ hK hβq hβK hUS hn S hS
    have hpow : 0 ≤ (Real.exp (-ρ) * (1 + K / n)) ^ t := pow_nonneg hlam t
    calc P.K.apply (P.K.iterate t (shrinkPot β)) S
        ≤ (Real.exp (-ρ) * (1 + K / n)) ^ t * P.K.apply (shrinkPot β) S := hE
      _ ≤ (Real.exp (-ρ) * (1 + K / n)) ^ t *
            (Real.exp (-ρ) * (1 + K / n) * shrinkPot β S) :=
          mul_le_mul_of_nonneg_left hstep hpow
      _ = (Real.exp (-ρ) * (1 + K / n)) ^ (t + 1) * shrinkPot β S := by ring

/-- The exponent after `T = ⌈ln n / ρ⌉ + r` rounds: `-ρ T + T K / n + ln n` is at most
`K / ρlo + K - (ρlo / 2) r`, when `n ≥ 1` and `2 K ≤ ρlo n`. -/
lemma shrink_exponent_le {ρlo ρ K : ℝ} (hρlo : 0 < ρlo) (hρ : ρlo ≤ ρ) (hK : 0 ≤ K)
    (hn1 : 1 ≤ (n : ℝ)) (hnK : 2 * K ≤ ρlo * n) (r : ℕ) :
    -ρ * ((⌈Real.log n / ρ⌉₊ + r : ℕ) : ℝ) + ((⌈Real.log n / ρ⌉₊ + r : ℕ) : ℝ) * (K / n) +
        Real.log n ≤ K / ρlo + K - ρlo / 2 * r := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le hρlo hρ
  have hn0 : 0 < (n : ℝ) := by linarith only [hn1]
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hlogn : Real.log n ≤ n := by
    have := Real.log_le_sub_one_of_pos hn0
    linarith only [this]
  set L : ℝ := (⌈Real.log n / ρ⌉₊ : ℝ) with hL
  have hLge : Real.log n / ρ ≤ L := Nat.le_ceil _
  have hLlt : L < Real.log n / ρ + 1 := Nat.ceil_lt_add_one (div_nonneg hlog0 hρ0.le)
  have hρL : Real.log n ≤ ρ * L := by
    have := (div_le_iff₀ hρ0).mp hLge
    linarith only [this]
  have hlogρ : Real.log n / ρ ≤ n / ρlo := by
    calc Real.log n / ρ ≤ n / ρ := div_le_div_of_nonneg_right hlogn hρ0.le
      _ ≤ n / ρlo := div_le_div_of_nonneg_left hn0.le hρlo hρ
  have hKn : K / n ≤ ρlo / 2 := by
    rw [div_le_iff₀ hn0]
    linarith only [hnK]
  have hLK : L * (K / n) ≤ K / ρlo + K := by
    have hL0 : 0 ≤ L := Nat.cast_nonneg _
    have h1 : L * (K / n) ≤ (n / ρlo + n) * (K / n) :=
      mul_le_mul_of_nonneg_right (by linarith only [hLlt, hlogρ, hn1])
        (div_nonneg hK hn0.le)
    have h2 : (n / ρlo + n) * (K / n) = K / ρlo + K := by
      field_simp
    linarith only [h1, h2]
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hrK : (r : ℝ) * (K / n) ≤ ρlo / 2 * r := by
    have := mul_le_mul_of_nonneg_left hKn hr0
    linarith only [this]
  have hρr : ρlo * r ≤ ρ * r := mul_le_mul_of_nonneg_right hρ hr0
  push_cast
  rw [← hL]
  nlinarith only [hρL, hLK, hrK, hρr]

/-- Stage two of Theorem 31: from at most `g₀ n` uninformed nodes, some node is still
uninformed after `⌈ln n / ρ⌉ + r` rounds with probability at most
`(1 + β g₀) e^{K / ρlo + K} e^{-(ρlo / 2) r}`. -/
lemma notYet_shrink_stage2 (P : RumorProcess n) {ρlo ρ a c g g₀ β K : ℝ} (hρlo : 0 < ρlo)
    (hρ : ρlo ≤ ρ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hg₀0 : 0 ≤ g₀) (hg₀ : g₀ ≤ g) (hβ : 0 ≤ β)
    (hK : 0 ≤ K) (hβq : a + β * (Real.exp (-ρ) + a * g₀) ^ 2 ≤ β * Real.exp (-ρ))
    (hβK : β * (1 + c) ≤ Real.exp (-ρ) * K)
    (hUS : P.UpperShrinking ρ a c g) (hn1 : 1 ≤ (n : ℝ)) (hnK : 2 * K ≤ ρlo * n)
    (S : Finset (Fin n)) (hS : (n : ℝ) - S.card ≤ g₀ * n) (r : ℕ) :
    P.notYet n (⌈Real.log n / ρ⌉₊ + r) S ≤
      (1 + β * g₀) * Real.exp (K / ρlo + K) * Real.exp (-(ρlo / 2) * r) := by
  have hn0 : 0 < (n : ℝ) := by linarith only [hn1]
  set T : ℕ := ⌈Real.log n / ρ⌉₊ + r with hT
  set u : ℝ := (n : ℝ) - S.card with hu
  have hu0 : 0 ≤ u := sub_nonneg.mpr (card_cast_le S)
  have hun : u ≤ n := by
    have := Nat.cast_nonneg (α := ℝ) S.card
    linarith only [this]
  -- Markov: the indicator of an uninformed node is below the potential
  have hmark : P.notYet n T S ≤ P.K.iterate T (shrinkPot β) S := by
    rw [notYet_below]
    exact P.K.iterate_mono T (fun U => below_le_shrinkPot hβ U) S
  have hiter := iterate_shrinkPot_le P ha hc hg₀ hβ hK hβq hβK hUS hn0 T S hS
  -- the potential at the start
  have hΦ : shrinkPot β S ≤ (1 + β * g₀) * n := by
    have hΦS : shrinkPot β S = u + β / n * u ^ 2 := rfl
    have hsq : β / n * u ^ 2 ≤ β * g₀ * u := by
      have h1 : u ^ 2 ≤ g₀ * n * u := by
        rw [sq]
        exact mul_le_mul_of_nonneg_right hS hu0
      have h2 : β / n * u ^ 2 ≤ β / n * (g₀ * n * u) :=
        mul_le_mul_of_nonneg_left h1 (div_nonneg hβ hn0.le)
      have h3 : β / n * (g₀ * n * u) = β * g₀ * u := by
        field_simp
      linarith only [h2, h3]
    have hfac : 0 ≤ 1 + β * g₀ := by have := mul_nonneg hβ hg₀0; linarith only [this]
    have h4 : (1 + β * g₀) * u ≤ (1 + β * g₀) * n := mul_le_mul_of_nonneg_left hun hfac
    rw [hΦS]
    linarith only [hsq, h4]
  -- the contraction factor
  have hpow : (Real.exp (-ρ) * (1 + K / n)) ^ T ≤
      Real.exp (-ρ * T) * Real.exp (T * (K / n)) := by
    rw [mul_pow]
    have h1 : Real.exp (-ρ) ^ T = Real.exp (-ρ * T) := by
      rw [← Real.exp_nat_mul, mul_comm]
    have h2 : (1 + K / n) ^ T ≤ Real.exp (T * (K / n)) := by
      rw [Real.exp_nat_mul]
      apply pow_le_pow_left₀ (by have := div_nonneg hK hn0.le; linarith only [this])
      have := Real.add_one_le_exp (K / n)
      linarith only [this]
    rw [h1]
    exact mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
  have hexp := shrink_exponent_le (n := n) hρlo hρ hK hn1 hnK r
  rw [← hT] at hexp
  have hfac : 0 ≤ 1 + β * g₀ := by have := mul_nonneg hβ hg₀0; linarith only [this]
  have hΦ0 : 0 ≤ shrinkPot β S := shrinkPot_nonneg hβ S
  have hlam0 : 0 ≤ (Real.exp (-ρ) * (1 + K / n)) ^ T :=
    pow_nonneg (mul_nonneg (Real.exp_pos _).le
      (by have := div_nonneg hK hn0.le; linarith only [this])) T
  calc P.notYet n T S
      ≤ (Real.exp (-ρ) * (1 + K / n)) ^ T * shrinkPot β S := le_trans hmark hiter
    _ ≤ (Real.exp (-ρ * T) * Real.exp (T * (K / n))) * ((1 + β * g₀) * n) :=
        mul_le_mul hpow hΦ hΦ0 (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    _ = (1 + β * g₀) * Real.exp (-ρ * T + T * (K / n) + Real.log n) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log hn0]
        ring
    _ ≤ (1 + β * g₀) * Real.exp (K / ρlo + K - ρlo / 2 * r) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hfac
    _ = (1 + β * g₀) * Real.exp (K / ρlo + K) * Real.exp (-(ρlo / 2) * r) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring

end Epidemics.Revisited
