import Epidemics.Revisited.GrowthUpper

/-! # Composing tail bounds (EPI-8, shrinking regime and total time)

Generic finite-time tools for the tails `notYet`, used for Theorem 31 and for the total
spreading time:

* `notYet_add_le`: the Markov property at a fixed time. If from every state with at least `m'`
  informed nodes the tail after `t` more rounds is at most `B`, then the tail after `s + t`
  rounds is at most the tail of reaching `m'` after `s` rounds, plus `B`.
* `tail_compose`: two exponential tails in sequence give an exponential tail, by splitting the
  extra rounds `r` into `r / 2` and `r - r / 2`.
* `sum_notYet_le_of_tail`: an exponential tail after `T₀` rounds bounds every partial sum of the
  tail series `∑_t P[T > t]` by `T₀ + A / (1 - e^{-α})`.
-/

namespace Epidemics.Revisited
open Finset Dynamics

variable {n : ℕ}

lemma notYet_nonneg (P : RumorProcess n) (m : ℝ) (t : ℕ) (S : Finset (Fin n)) :
    0 ≤ P.notYet m t S :=
  P.K.event_nonneg _ t S

lemma notYet_le_one (P : RumorProcess n) (m : ℝ) (t : ℕ) (S : Finset (Fin n)) :
    P.notYet m t S ≤ 1 :=
  P.K.event_le_one _ t S

/-- One more round: `P_S[T > t + 1] = E_{S' ∼ K S}[P_{S'}[T > t]]`. -/
lemma notYet_succ (P : RumorProcess n) (m : ℝ) (t : ℕ) (S : Finset (Fin n)) :
    P.notYet m (t + 1) S = (P.K S).expect (fun T => P.notYet m t T) := by
  rw [notYet_below, Kernel.iterate_succ, Kernel.apply]
  congr 1

lemma notYet_zero (P : RumorProcess n) (m : ℝ) (S : Finset (Fin n)) :
    P.notYet m 0 S = below m S := by
  rw [notYet_below, Kernel.iterate_zero]

/-- Markov property at a fixed time: the tail after `s + t` rounds is at most the tail of
reaching `m'` within `s` rounds plus a bound `B` on the tail after `t` rounds from any state
with at least `m'` informed nodes. -/
lemma notYet_add_le (P : RumorProcess n) {m m' B : ℝ} (hB : 0 ≤ B) (s t : ℕ)
    (hT : ∀ T : Finset (Fin n), m' ≤ (T.card : ℝ) → P.notYet m t T ≤ B)
    (S : Finset (Fin n)) :
    P.notYet m (s + t) S ≤ P.notYet m' s S + B := by
  have hpt : ∀ T, P.K.iterate t (below m) T ≤ below m' T + B := by
    intro T
    rw [← notYet_below]
    by_cases h : (T.card : ℝ) < m'
    · have h1 := notYet_le_one P m t T
      have hb : below m' T = 1 := by simp [below, h]
      linarith only [h1, hb, hB]
    · have hb : below m' T = 0 := by simp [below, h]
      have h2 := hT T (not_lt.mp h)
      linarith only [h2, hb]
  have hmono := P.K.iterate_mono s hpt S
  have hadd : P.K.iterate s (fun T => below m' T + B) S =
      P.K.iterate s (below m') S + B := by
    rw [P.K.iterate_add, P.K.iterate_const]
  rw [notYet_below, P.K.iterate_add_time, notYet_below]
  linarith only [hmono, hadd]

/-- `(1 - p)^r ≤ e^{-p r}`. -/
lemma one_sub_pow_le_exp {p : ℝ} (hp1 : p ≤ 1) (r : ℕ) :
    (1 - p) ^ r ≤ Real.exp (-p * r) := by
  have hbase : 1 - p ≤ Real.exp (-p) := by
    have h := Real.add_one_le_exp (-p)
    linarith only [h]
  have hpow := pow_le_pow_left₀ (sub_nonneg.mpr hp1) hbase r
  calc (1 - p) ^ r ≤ Real.exp (-p) ^ r := hpow
    _ = Real.exp (-p * r) := by rw [← Real.exp_nat_mul, mul_comm]

/-- Splitting `r` extra rounds into `r / 2` and `r - r / 2`: two exponential rates `α₁, α₂`
give the rate `min α₁ α₂ / 2`. -/
lemma exp_split_le {A₁ α₁ A₂ α₂ : ℝ} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (hα₁ : 0 < α₁)
    (hα₂ : 0 < α₂) (r : ℕ) :
    A₁ * Real.exp (-α₁ * ((r / 2 : ℕ) : ℝ)) + A₂ * Real.exp (-α₂ * ((r - r / 2 : ℕ) : ℝ)) ≤
      (A₁ * Real.exp (min α₁ α₂ / 2) + A₂) * Real.exp (-(min α₁ α₂ / 2) * r) := by
  set α := min α₁ α₂ / 2 with hαdef
  have hα0 : 0 ≤ α := by
    have := lt_min hα₁ hα₂
    rw [hαdef]
    linarith only [this]
  have h2α₁ : 2 * α ≤ α₁ := by
    rw [hαdef]
    linarith only [min_le_left α₁ α₂]
  have h2α₂ : 2 * α ≤ α₂ := by
    rw [hαdef]
    linarith only [min_le_right α₁ α₂]
  obtain ⟨hr₁, hr₂⟩ := nat_half_ge r
  have hr₁0 : (0 : ℝ) ≤ ((r / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hr₂0 : (0 : ℝ) ≤ ((r - r / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have he₁ : -α₁ * ((r / 2 : ℕ) : ℝ) ≤ α + -α * r := by
    have hm1 := mul_nonneg (sub_nonneg.mpr h2α₁) hr₁0
    have hm2 : 0 ≤ α * (2 * ((r / 2 : ℕ) : ℝ) - ((r : ℝ) - 1)) :=
      mul_nonneg hα0 (by linarith only [hr₁])
    nlinarith only [hm1, hm2]
  have he₂ : -α₂ * ((r - r / 2 : ℕ) : ℝ) ≤ -α * r := by
    have hm1 := mul_nonneg (sub_nonneg.mpr h2α₂) hr₂0
    have hm2 : 0 ≤ α * (2 * ((r - r / 2 : ℕ) : ℝ) - r) :=
      mul_nonneg hα0 (by linarith only [hr₂])
    nlinarith only [hm1, hm2]
  have hx₁ : A₁ * Real.exp (-α₁ * ((r / 2 : ℕ) : ℝ)) ≤
      A₁ * Real.exp α * Real.exp (-α * r) := by
    rw [mul_assoc, ← Real.exp_add]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he₁) hA₁
  have hx₂ : A₂ * Real.exp (-α₂ * ((r - r / 2 : ℕ) : ℝ)) ≤ A₂ * Real.exp (-α * r) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he₂) hA₂
  have hsum : A₁ * Real.exp α * Real.exp (-α * r) + A₂ * Real.exp (-α * r) =
      (A₁ * Real.exp α + A₂) * Real.exp (-α * r) := by ring
  linarith only [hx₁, hx₂, hsum]

/-- Two exponential tails in sequence: if from `S` the process reaches `m'` informed nodes
within `T₁ + r` rounds except with probability `A₁ e^{-α₁ r}`, and from every state with at
least `m'` informed nodes it reaches `m` within `T₂ + r` rounds except with probability
`A₂ e^{-α₂ r}`, then from `S` it reaches `m` within `T₁ + T₂ + r` rounds except with
probability `(A₁ e^{α} + A₂) e^{-α r}`, where `α = min α₁ α₂ / 2`. -/
lemma tail_compose (P : RumorProcess n) {m m' A₁ α₁ A₂ α₂ : ℝ} (hA₁ : 0 ≤ A₁)
    (hA₂ : 0 ≤ A₂) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) {T₁ T₂ : ℕ} (S : Finset (Fin n))
    (h₁ : ∀ r : ℕ, P.notYet m' (T₁ + r) S ≤ A₁ * Real.exp (-α₁ * r))
    (h₂ : ∀ T : Finset (Fin n), m' ≤ (T.card : ℝ) → ∀ r : ℕ,
      P.notYet m (T₂ + r) T ≤ A₂ * Real.exp (-α₂ * r)) (r : ℕ) :
    P.notYet m (T₁ + T₂ + r) S ≤
      (A₁ * Real.exp (min α₁ α₂ / 2) + A₂) * Real.exp (-(min α₁ α₂ / 2) * r) := by
  have htime : T₁ + T₂ + r = (T₁ + r / 2) + (T₂ + (r - r / 2)) := by omega
  have hB : 0 ≤ A₂ * Real.exp (-α₂ * ((r - r / 2 : ℕ) : ℝ)) :=
    mul_nonneg hA₂ (Real.exp_pos _).le
  have hstep := notYet_add_le P hB (T₁ + r / 2) (T₂ + (r - r / 2))
    (fun T hT => h₂ T hT (r - r / 2)) S
  rw [htime]
  have hfirst := h₁ (r / 2)
  have hsplit := exp_split_le hA₁ hA₂ hα₁ hα₂ r
  linarith only [hstep, hfirst, hsplit]

/-- An exponential tail after `T₀` rounds bounds every partial sum of the tail series:
`∑_{t < R} P[T > t] ≤ T₀ + A / (1 - e^{-α})`. -/
lemma sum_notYet_le_of_tail (P : RumorProcess n) {m A α : ℝ} (hA : 0 ≤ A) (hα : 0 < α)
    (T₀ : ℕ) (S : Finset (Fin n))
    (h : ∀ r : ℕ, P.notYet m (T₀ + r) S ≤ A * Real.exp (-α * r)) (R : ℕ) :
    ∑ t ∈ range R, P.notYet m t S ≤ T₀ + A / (1 - Real.exp (-α)) := by
  have hq : Real.exp (-α) < 1 := by
    have hneg : -α < 0 := by linarith only [hα]
    simpa [Real.exp_zero] using (Real.exp_lt_exp).mpr hneg
  have hden : 0 < 1 - Real.exp (-α) := by linarith only [hq]
  have hsub : ∑ t ∈ range R, P.notYet m t S ≤ ∑ t ∈ range (T₀ + R), P.notYet m t S :=
    sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (Nat.le_add_left R T₀))
      (fun t _ _ => notYet_nonneg P m t S)
  rw [sum_range_add] at hsub
  have hhead : ∑ t ∈ range T₀, P.notYet m t S ≤ (T₀ : ℝ) := by
    have hle := sum_le_sum (fun t (_ : t ∈ range T₀) => notYet_le_one P m t S)
    simpa [sum_const, card_range, nsmul_eq_mul, mul_one] using hle
  have hterm : ∀ i ∈ range R, P.notYet m (T₀ + i) S ≤ A * Real.exp (-α) ^ i := by
    intro i _
    have hi := h i
    rwa [mul_comm (-α), Real.exp_nat_mul] at hi
  have htail := sum_le_sum hterm
  rw [← mul_sum] at htail
  have hgeom := geom_partial_le (Real.exp_nonneg _) hq R
  have hmul := mul_le_mul_of_nonneg_left hgeom hA
  have hinv : A * (1 - Real.exp (-α))⁻¹ = A / (1 - Real.exp (-α)) := by rw [div_eq_mul_inv]
  linarith only [hsub, hhead, htail, hmul, hinv]

end Epidemics.Revisited
