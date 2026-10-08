import Epidemics.Revisited.DoubleShrinkingStages

/-! # Theorem 43, upper bound (EPI-8, proof)

The three stages of `DoubleShrinkingStages` are composed by the Markov property at fixed times
(`notYet_add_le`), splitting the extra rounds `r` into thirds. The failure probabilities per
phase are polynomially small in `n`, which gives the paper's tail `O(n^{A' - α' r})`; the
number of double exponential phases is `J = ⌊log_ℓ (β ln n / (2 D₀))⌋ ≤ log_ℓ ln n`, and the
factor `2^J` of the phase calculus is a power of `n`.
-/

namespace Epidemics.Revisited
open Finset Dynamics

variable {n : ℕ}

/-! ### Real powers of `n` -/

lemma inv_n_eq : 1 / (n : ℝ) = (n : ℝ) ^ (-1 : ℝ) := by
  rw [Real.rpow_neg_one, one_div]

/-- Failure probability of a geometric phase. -/
lemma q_geom_le (hn : 1 ≤ n) {m m' c α τ τ' : ℝ} (hm : 0 < m) (hm' : 0 < m') (hc : 0 ≤ c)
    (hα : 0 ≤ α) (hτ' : τ' ≤ τ) (hτ'1 : τ' ≤ 1)
    (hB : (1 + c) / m ^ 2 + 1 / m' ≤ (n : ℝ) ^ (τ' / 2)) :
    (1 + c) * n / (m * n) ^ 2 + (n : ℝ) ^ (1 - α) * (n : ℝ) ^ (-τ) / (m' * n) ≤
      (n : ℝ) ^ (-(τ' / 2)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have e1 : (1 + c) * n / (m * n) ^ 2 = (1 + c) / m ^ 2 * (1 / n) := by
    field_simp
  have e2 : (n : ℝ) ^ (1 - α) * (n : ℝ) ^ (-τ) / (m' * n) =
      1 / m' * (n : ℝ) ^ (-α - τ) := by
    have : (n : ℝ) ^ (1 - α) * (n : ℝ) ^ (-τ) = (n : ℝ) ^ (-α - τ) * n := by
      rw [← npow_add hn, ← Real.rpow_add_one hn0.ne']
      congr 1
      ring
    rw [this]
    field_simp
  have h1 : 1 / (n : ℝ) ≤ (n : ℝ) ^ (-τ') := by rw [inv_n_eq]; exact npow_mono hn (by linarith)
  have h2 : (n : ℝ) ^ (-α - τ) ≤ (n : ℝ) ^ (-τ') := npow_mono hn (by linarith)
  have hA : 0 ≤ (1 + c) / m ^ 2 := by positivity
  have hA' : 0 ≤ 1 / m' := by positivity
  have hsplit : (n : ℝ) ^ (τ' / 2) * (n : ℝ) ^ (-τ') = (n : ℝ) ^ (-(τ' / 2)) := by
    rw [← npow_add hn]; congr 1; ring
  rw [e1, e2]
  calc (1 + c) / m ^ 2 * (1 / n) + 1 / m' * (n : ℝ) ^ (-α - τ)
      ≤ (1 + c) / m ^ 2 * (n : ℝ) ^ (-τ') + 1 / m' * (n : ℝ) ^ (-τ') := by
        gcongr
    _ = ((1 + c) / m ^ 2 + 1 / m') * (n : ℝ) ^ (-τ') := by ring
    _ ≤ (n : ℝ) ^ (τ' / 2) * (n : ℝ) ^ (-τ') :=
        mul_le_mul_of_nonneg_right hB (npow_pos hn _).le
    _ = (n : ℝ) ^ (-(τ' / 2)) := hsplit

/-- Failure probability of a double exponential phase, when `ε ≥ n^{-β}`. -/
lemma q_double_le (hn : 1 ≤ n) {ε c α τ τ' β : ℝ} (hε : (n : ℝ) ^ (-β) ≤ ε) (hc : 0 ≤ c)
    (hβα : β ≤ α) (hβ : β ≤ 1 / 4) (hτ' : τ' ≤ τ) (hτ'1 : τ' ≤ 1 / 2)
    (hB : 4 * (1 + c) + 1 ≤ (n : ℝ) ^ (τ' / 2)) :
    (1 + c) * n / (ε * n / 2) ^ 2 + (n : ℝ) ^ (1 - α) * (n : ℝ) ^ (-τ) / (ε * n) ≤
      (n : ℝ) ^ (-(τ' / 2)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hβpos : 0 < (n : ℝ) ^ (-β) := npow_pos hn _
  have hεpos : 0 < ε := lt_of_lt_of_le hβpos hε
  have e1 : (1 + c) * n / (ε * n / 2) ^ 2 = 4 * (1 + c) * (1 / n) / ε ^ 2 := by
    field_simp
    ring
  have e2 : (n : ℝ) ^ (1 - α) * (n : ℝ) ^ (-τ) / (ε * n) = (n : ℝ) ^ (-α - τ) / ε := by
    have : (n : ℝ) ^ (1 - α) * (n : ℝ) ^ (-τ) = (n : ℝ) ^ (-α - τ) * n := by
      rw [← npow_add hn, ← Real.rpow_add_one hn0.ne']
      congr 1
      ring
    rw [this]
    field_simp
  have hsq : (n : ℝ) ^ (-(2 * β)) ≤ ε ^ 2 := by
    have := pow_le_pow_left₀ hβpos.le hε 2
    rwa [npow_pow, show -β * ((2 : ℕ) : ℝ) = -(2 * β) by push_cast; ring] at this
  have h1 : 4 * (1 + c) * (1 / n) / ε ^ 2 ≤ 4 * (1 + c) * (n : ℝ) ^ (-τ') := by
    rw [div_le_iff₀ (by positivity), inv_n_eq]
    have : (n : ℝ) ^ (-1 : ℝ) ≤ (n : ℝ) ^ (-τ') * (n : ℝ) ^ (-(2 * β)) := by
      rw [← npow_add hn]; exact npow_mono hn (by linarith)
    have hm := mul_le_mul_of_nonneg_left hsq (npow_pos hn (-τ')).le
    nlinarith [npow_pos hn (-τ')]
  have h2 : (n : ℝ) ^ (-α - τ) / ε ≤ (n : ℝ) ^ (-τ') := by
    rw [div_le_iff₀ hεpos]
    have : (n : ℝ) ^ (-α - τ) ≤ (n : ℝ) ^ (-τ') * (n : ℝ) ^ (-β) := by
      rw [← npow_add hn]; exact npow_mono hn (by linarith)
    have hm := mul_le_mul_of_nonneg_left hε (npow_pos hn (-τ')).le
    linarith
  have hsplit : (n : ℝ) ^ (τ' / 2) * (n : ℝ) ^ (-τ') = (n : ℝ) ^ (-(τ' / 2)) := by
    rw [← npow_add hn]; congr 1; ring
  rw [e1, e2]
  calc 4 * (1 + c) * (1 / n) / ε ^ 2 + (n : ℝ) ^ (-α - τ) / ε
      ≤ 4 * (1 + c) * (n : ℝ) ^ (-τ') + (n : ℝ) ^ (-τ') := add_le_add h1 h2
    _ = (4 * (1 + c) + 1) * (n : ℝ) ^ (-τ') := by ring
    _ ≤ (n : ℝ) ^ (τ' / 2) * (n : ℝ) ^ (-τ') :=
        mul_le_mul_of_nonneg_right hB (npow_pos hn _).le
    _ = (n : ℝ) ^ (-(τ' / 2)) := hsplit

lemma npow_eq_exp (hn : 1 ≤ n) (x : ℝ) : (n : ℝ) ^ x = Real.exp (Real.log n * x) :=
  Real.rpow_def_of_pos (by exact_mod_cast hn) x

/-- The number of double exponential phases, `J = ⌊log_ℓ (β ln n / (2 D₀))⌋`: the last target
`ε_J` lies between `n^{-β}` and `n^{-β/(2ℓ)}`, and `J ≤ log_ℓ ln n`. -/
lemma J_facts {ℓ κ D₀ β : ℝ} (hℓ : 1 < ℓ) (hκ : 0 ≤ κ) (hD₀ : 0 < D₀) (hβ0 : 0 < β)
    (hβD : β / (2 * D₀) ≤ 1) (hn : 1 ≤ n) (hlog : 2 * D₀ / β + 2 * κ / β ≤ Real.log n)
    (J : ℕ) (hJ : J = ⌊Real.logb ℓ (β * Real.log n / (2 * D₀))⌋₊) :
    (n : ℝ) ^ (-β) ≤ epsSeq ℓ κ D₀ J ∧ epsSeq ℓ κ D₀ J ≤ (n : ℝ) ^ (-(β / (2 * ℓ))) ∧
      (J : ℝ) ≤ Real.logb ℓ (Real.log n) ∧ (J : ℝ) * Real.log ℓ ≤ Real.log n := by
  set L := Real.log n with hL
  set X := β * L / (2 * D₀) with hX
  have hℓ0 : 0 < ℓ := by linarith
  have h2D : 0 < 2 * D₀ := by linarith
  have hDβ : 0 ≤ 2 * D₀ / β := by positivity
  have hκβ : 0 ≤ 2 * κ / β := by positivity
  have hL1 : 2 * D₀ / β ≤ L := by linarith
  have hX1 : 1 ≤ X := by
    rw [hX, le_div_iff₀ h2D]
    have := (div_le_iff₀ hβ0).mp hL1
    linarith
  have hX0 : 0 < X := by linarith
  have hlogbX0 : 0 ≤ Real.logb ℓ X := Real.logb_nonneg hℓ hX1
  have hJle : (J : ℝ) ≤ Real.logb ℓ X := by rw [hJ]; exact Nat.floor_le hlogbX0
  have hJlt : Real.logb ℓ X < (J : ℝ) + 1 := by rw [hJ]; exact Nat.lt_floor_add_one _
  have hℓJ : ℓ ^ J ≤ X := by
    rw [← Real.rpow_natCast]
    calc ℓ ^ (J : ℝ) ≤ ℓ ^ (Real.logb ℓ X) := Real.rpow_le_rpow_of_exponent_le hℓ.le hJle
      _ = X := Real.rpow_logb hℓ0 hℓ.ne' hX0
  have hℓJ1 : X < ℓ * ℓ ^ J := by
    rw [← pow_succ', ← Real.rpow_natCast]
    calc X = ℓ ^ (Real.logb ℓ X) := (Real.rpow_logb hℓ0 hℓ.ne' hX0).symm
      _ < ℓ ^ (((J + 1 : ℕ) : ℝ)) := by
        apply Real.rpow_lt_rpow_of_exponent_lt hℓ
        push_cast
        exact hJlt
  have hXD : X * D₀ = β * L / 2 := by rw [hX]; field_simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [npow_eq_exp hn]
    unfold epsSeq
    apply Real.exp_le_exp.mpr
    have h1 : ℓ ^ J * D₀ ≤ X * D₀ := mul_le_mul_of_nonneg_right hℓJ hD₀.le
    have h2 : κ ≤ β * L / 2 := by
      have := (div_le_iff₀ hβ0).mp (show 2 * κ / β ≤ L by linarith)
      linarith
    rw [← hL]
    linarith
  · rw [npow_eq_exp hn]
    unfold epsSeq
    apply Real.exp_le_exp.mpr
    have h1 : X * D₀ < ℓ * ℓ ^ J * D₀ := mul_lt_mul_of_pos_right hℓJ1 hD₀
    have h2 : β * L / (2 * ℓ) ≤ ℓ ^ J * D₀ := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    rw [← hL]
    have : L * -(β / (2 * ℓ)) = -(β * L / (2 * ℓ)) := by ring
    rw [this]
    linarith
  · have hXL : X ≤ L := by
      rw [hX]
      have hL0 : 0 ≤ L := by linarith
      have : β * L / (2 * D₀) = β / (2 * D₀) * L := by ring
      rw [this]
      nlinarith
    exact le_trans hJle (Real.logb_le_logb_of_le hℓ hX0 hXL)
  · have hXL : X ≤ L := by
      rw [hX]
      have hL0 : 0 ≤ L := by linarith
      have : β * L / (2 * D₀) = β / (2 * D₀) * L := by ring
      rw [this]
      nlinarith
    have hJ' : (J : ℝ) ≤ Real.logb ℓ L := le_trans hJle (Real.logb_le_logb_of_le hℓ hX0 hXL)
    have hlogℓ : 0 < Real.log ℓ := Real.log_pos hℓ
    rw [Real.logb, le_div_iff₀ hlogℓ] at hJ'
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < L)
    linarith

end Epidemics.Revisited
