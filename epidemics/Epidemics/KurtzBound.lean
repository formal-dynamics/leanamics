import Epidemics.KurtzMainAux

/-! # Kurtz's law of large numbers for SIR: the probability bound (CRN-2, helpers)

If the tube width `θ` exceeds the deterministic bound of `close_of_good` for a martingale level
`δ`, a deviation larger than `θ` forces one of the three coordinate martingales `±mgIncr β γ j` to
reach `δ` (`fail_indicator_le`), and the maximal Azuma–Hoeffding inequality bounds each of the six
events: `deviationProb ≤ 6 exp(-δ² / (2 n (2/N)²))` (`deviationProb_le_azuma`).
-/

namespace Epidemics.Kurtz

open Dynamics KermackMcKendrick Finset Real

variable {β γ N : ℕ}

/-- Probabilities are nonnegative. -/
lemma deviationProb_nonneg (x₀ : Config N) (x : ℝ → ℝ × ℝ × ℝ) (θ : ℝ) (n : ℕ) :
    0 ≤ deviationProb β γ x₀ x θ n :=
  expList_nonneg fun _ ↦ by split_ifs <;> norm_num

/-- A wider tube is left with smaller probability. -/
lemma deviationProb_anti (x₀ : Config N) (x : ℝ → ℝ × ℝ × ℝ) {θ₁ θ₂ : ℝ} (h : θ₁ ≤ θ₂)
    (n : ℕ) : deviationProb β γ x₀ x θ₂ n ≤ deviationProb β γ x₀ x θ₁ n :=
  expList_le_expList fun _ ↦ ite_one_zero_le_of_imp fun ⟨k, hk, hlt⟩ ↦
    ⟨k, hk, lt_of_le_of_lt h hlt⟩

/-- The indicator that the coordinate-`j` martingale (or its negative, `neg = true`) reaches `δ`
within `n` rounds. -/
noncomputable def mgEvent (β γ : ℕ) {N : ℕ} (x₀ : Config N) (δ : ℝ) (n : ℕ) (j : Fin 3)
    (neg : Bool) (l : List (Round N β γ)) : ℝ :=
  if ∃ k ≤ n, δ ≤ incrementSum (step β γ)
      (fun y a ↦ (if neg then -1 else 1) * mgIncr β γ j y a) x₀ (l.take k)
  then 1 else 0

lemma mgEvent_nonneg (x₀ : Config N) (δ : ℝ) (n : ℕ) (j : Fin 3) (neg : Bool)
    (l : List (Round N β γ)) : 0 ≤ mgEvent β γ x₀ δ n j neg l := by
  unfold mgEvent
  split_ifs <;> norm_num

/-- **Failure forces a martingale deviation.** Along rounds `l` of length `n ≤ T (β + γ) N`, if
the tube width `θ` is at least the bound of `close_of_good` at level `δ`, a deviation larger
than `θ` makes one of the six martingale events happen. -/
lemma fail_indicator_le (hβ : 0 < β) (hγ : 0 < γ) (hN : 0 < N) {x₀ : Config N}
    {s i r : ℝ → ℝ}
    (hx : IsIntegralCurveOn (fun t ↦ (s t, i t, r t)) (fun _ ↦ sirField β γ) (Set.Ici 0))
    (hs : 0 ≤ s 0) (hi : 0 ≤ i 0) (hr : 0 ≤ r 0) (hsum : s 0 + i 0 + r 0 = 1)
    {T δ θ : ℝ} (hδ : 0 ≤ δ) {n : ℕ} (hnT : (n : ℝ) ≤ T * (β + γ) * N)
    (hθ : (dist (scaled x₀) (s 0, i 0, r 0) + δ + T * (2 * β + γ) / N)
      * exp ((2 * β + γ) * T) ≤ θ)
    (l : List (Round N β γ)) (hl : l.length = n) :
    (if ∃ k ≤ n, θ < dist (scaled ((l.take k).foldl (step β γ) x₀))
        ((fun t ↦ (s t, i t, r t)) ((k : ℝ) / ((β + γ) * N))) then (1 : ℝ) else 0)
      ≤ ∑ j : Fin 3, (mgEvent β γ x₀ δ n j false l + mgEvent β γ x₀ δ n j true l) := by
  have hnn (j : Fin 3) : 0 ≤ mgEvent β γ x₀ δ n j false l + mgEvent β γ x₀ δ n j true l :=
    add_nonneg (mgEvent_nonneg _ _ _ _ _ _) (mgEvent_nonneg _ _ _ _ _ _)
  by_cases hbad : ∃ j : Fin 3,
      mgEvent β γ x₀ δ n j false l = 1 ∨ mgEvent β γ x₀ δ n j true l = 1
  · obtain ⟨j, hj⟩ := hbad
    have hone : (1 : ℝ) ≤ mgEvent β γ x₀ δ n j false l + mgEvent β γ x₀ δ n j true l := by
      rcases hj with h | h <;> rw [h] <;> linarith [mgEvent_nonneg x₀ δ n j false l,
        mgEvent_nonneg x₀ δ n j true l]
    calc _ ≤ (1 : ℝ) := by split_ifs <;> norm_num
      _ ≤ _ := hone
      _ ≤ _ := single_le_sum (fun j _ ↦ hnn j) (mem_univ j)
  · push Not at hbad
    have hgood : ∀ j : Fin 3, ∀ k ≤ l.length,
        |incrementSum (step β γ) (mgIncr β γ j) x₀ (l.take k)| ≤ δ := by
      intro j k hk
      have h1 := (hbad j).1
      have h2 := (hbad j).2
      unfold mgEvent at h1 h2
      simp only [Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul] at h1 h2
      have h1' : ¬ δ ≤ incrementSum (step β γ) (mgIncr β γ j) x₀ (l.take k) := fun h ↦
        h1 (if_pos ⟨k, hl ▸ hk, h⟩)
      have h2' : ¬ δ ≤ incrementSum (step β γ) (fun y a ↦ -mgIncr β γ j y a) x₀ (l.take k) :=
        fun h ↦ h2 (if_pos ⟨k, hl ▸ hk, h⟩)
      rw [incrementSum_neg] at h2'
      rw [abs_le]
      constructor <;> linarith
    have hclose := close_of_good hβ hγ hN hx hs hi hr hsum hδ l (hl ▸ hnT) hgood
    rw [if_neg]
    · exact sum_nonneg fun j _ ↦ hnn j
    rintro ⟨k, hk, hlt⟩
    have hk' := hclose k (hl ▸ hk)
    simp only at hlt
    linarith

/-- **The six Azuma bounds.** Under the hypotheses of `fail_indicator_le` with `0 < δ` and
`0 < n`, the probability of a deviation larger than `θ` within `n` steps is at most
`6 exp(-δ² / (2 n (2/N)²))`. -/
lemma deviationProb_le_azuma (hβ : 0 < β) (hγ : 0 < γ) (hN : 0 < N) {x₀ : Config N}
    {s i r : ℝ → ℝ}
    (hx : IsIntegralCurveOn (fun t ↦ (s t, i t, r t)) (fun _ ↦ sirField β γ) (Set.Ici 0))
    (hs : 0 ≤ s 0) (hi : 0 ≤ i 0) (hr : 0 ≤ r 0) (hsum : s 0 + i 0 + r 0 = 1)
    {T δ θ : ℝ} (hδ : 0 ≤ δ) {n : ℕ} (hnT : (n : ℝ) ≤ T * (β + γ) * N)
    (hθ : (dist (scaled x₀) (s 0, i 0, r 0) + δ + T * (2 * β + γ) / N)
      * exp ((2 * β + γ) * T) ≤ θ) :
    deviationProb β γ x₀ (fun t ↦ (s t, i t, r t)) θ n
      ≤ 6 * exp (-(δ ^ 2 / (2 * n * (2 / N) ^ 2))) := by
  have hmean (j : Fin 3) (neg : Bool) (y : Config N) :
      avg (fun a ↦ (if neg then -1 else 1) * mgIncr β γ j y a) = 0 := by
    rw [avg_const_mul, avg_mgIncr hN hβ j y, mul_zero]
  have hbd (j : Fin 3) (neg : Bool) (y : Config N) (a : Round N β γ) :
      |(if neg then -1 else 1) * mgIncr β γ j y a| ≤ 2 / N := by
    rw [abs_mul]
    have : |(if neg then (-1 : ℝ) else 1)| = 1 := by split_ifs <;> norm_num
    rw [this, one_mul]
    exact abs_mgIncr_le hN hβ j y a
  have hev (j : Fin 3) (neg : Bool) : expList (Round N β γ) n (mgEvent β γ x₀ δ n j neg)
      ≤ exp (-(δ ^ 2 / (2 * n * (2 / N) ^ 2))) :=
    expList_azuma _ _ (hmean j neg) (hbd j neg) x₀ n hδ
  unfold deviationProb
  calc expList (Round N β γ) n _
      ≤ expList (Round N β γ) n (fun l ↦ ∑ j : Fin 3,
          (mgEvent β γ x₀ δ n j false l + mgEvent β γ x₀ δ n j true l)) :=
        expList_le_expList_of_length
          (fail_indicator_le hβ hγ hN hx hs hi hr hsum hδ hnT hθ)
    _ = ∑ j : Fin 3, (expList (Round N β γ) n (mgEvent β γ x₀ δ n j false)
          + expList (Round N β γ) n (mgEvent β γ x₀ δ n j true)) := by
        rw [expList_finset_sum]
        exact sum_congr rfl fun j _ ↦ expList_add _ _ _
    _ ≤ ∑ _j : Fin 3, (exp (-(δ ^ 2 / (2 * n * (2 / N) ^ 2)))
          + exp (-(δ ^ 2 / (2 * n * (2 / N) ^ 2)))) :=
        sum_le_sum fun j _ ↦ add_le_add (hev j false) (hev j true)
    _ = 6 * exp (-(δ ^ 2 / (2 * n * (2 / N) ^ 2))) := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end Epidemics.Kurtz
