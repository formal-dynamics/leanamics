import Epidemics.Revisited.ShrinkingPotential

/-! # Exponential shrinking regime, upper bound: constants and proof (Theorem 31)

Two stages, composed by `tail_compose`:

1. From at most `g n` to at most `g₀ n` uninformed nodes: every uninformed node is informed with
   probability at least `p₀ = 1 - e^{-ρlo} - a g > 0`, so Lemma 19 (`connect_tail`) gives the
   tail `(g / g₀) e^{-p₀ r}` (`notYet_shrink_stage1`).
2. From at most `g₀ n` uninformed nodes to none: the potential of `ShrinkingPotential`, with
   `δ = e^{-ρhi} (1 - e^{-ρlo}) / 2`, `g₀ = min g (δ / (3 (a + 1)))`, `β = a / δ` and
   `K = β (1 + c) e^{ρhi}`, gives the tail `(1 + β g₀) e^{K / ρlo + K} e^{-(ρlo / 2) r}` after
   `⌈ln n / ρ⌉ + r` rounds (`notYet_shrink_stage2`).

All constants depend only on `ρlo, ρhi, a, c, g`; the threshold is `n ≥ 2 K / ρlo + 1`.
-/

namespace Epidemics.Revisited
open Finset Dynamics

/-- `δ = e^{-ρhi} (1 - e^{-ρlo}) / 2`, so that `x (1 - x) ≥ 2 δ` for `x = e^{-ρ}`,
`ρ ∈ [ρlo, ρhi]`. -/
noncomputable def shrinkDelta (ρlo ρhi : ℝ) : ℝ := Real.exp (-ρhi) * (1 - Real.exp (-ρlo)) / 2

/-- The fraction `g₀` of uninformed nodes below which the potential contracts. -/
noncomputable def shrinkG0 (ρlo ρhi a g : ℝ) : ℝ := min g (shrinkDelta ρlo ρhi / (3 * (a + 1)))

/-- Weight of the quadratic term of the potential. -/
noncomputable def shrinkBeta (ρlo ρhi a : ℝ) : ℝ := a / shrinkDelta ρlo ρhi

/-- Variance slack: one round multiplies the potential by at most `e^{-ρ} (1 + K / n)`. -/
noncomputable def shrinkK (ρlo ρhi a c : ℝ) : ℝ :=
  shrinkBeta ρlo ρhi a * (1 + c) * Real.exp ρhi

/-- Lower bound `1 - e^{-ρlo} - a g` on the probability to be informed, for at most `g n`
uninformed nodes. -/
noncomputable def shrinkP0 (ρlo a g : ℝ) : ℝ := 1 - Real.exp (-ρlo) - a * g

/-- Prefactor of the first stage. -/
noncomputable def shrinkA1 (ρlo ρhi a g : ℝ) : ℝ := g / shrinkG0 ρlo ρhi a g

/-- Prefactor of the second stage. -/
noncomputable def shrinkA2 (ρlo ρhi a c g : ℝ) : ℝ :=
  (1 + shrinkBeta ρlo ρhi a * shrinkG0 ρlo ρhi a g) *
    Real.exp (shrinkK ρlo ρhi a c / ρlo + shrinkK ρlo ρhi a c)

/-- Rate of the tail bound of Theorem 31. -/
noncomputable def shrinkAlpha (ρlo a g : ℝ) : ℝ := min (shrinkP0 ρlo a g) (ρlo / 2) / 2

/-- Prefactor of the tail bound of Theorem 31. -/
noncomputable def shrinkA (ρlo ρhi a c g : ℝ) : ℝ :=
  shrinkA1 ρlo ρhi a g * Real.exp (shrinkAlpha ρlo a g) + shrinkA2 ρlo ρhi a c g

/-- Threshold on `n` in Theorem 31. -/
noncomputable def shrinkN (ρlo ρhi a c : ℝ) : ℕ := ⌈2 * shrinkK ρlo ρhi a c / ρlo⌉₊ + 1

section Constants
variable {ρlo ρhi a c g : ℝ}

lemma exp_neg_lt_one {x : ℝ} (hx : 0 < x) : Real.exp (-x) < 1 := by
  have hneg : -x < 0 := by linarith only [hx]
  simpa [Real.exp_zero] using (Real.exp_lt_exp).mpr hneg

lemma shrinkDelta_pos (hρlo : 0 < ρlo) : 0 < shrinkDelta ρlo ρhi := by
  have h1 : 0 < 1 - Real.exp (-ρlo) := by linarith only [exp_neg_lt_one hρlo]
  unfold shrinkDelta
  positivity

lemma shrinkDelta_le_half (hρlo : 0 < ρlo) (hρ : ρlo ≤ ρhi) : shrinkDelta ρlo ρhi ≤ 1 / 2 := by
  have h1 : Real.exp (-ρhi) ≤ 1 := le_of_lt (exp_neg_lt_one (lt_of_lt_of_le hρlo hρ))
  have h2 : 1 - Real.exp (-ρlo) ≤ 1 := by linarith only [Real.exp_pos (-ρlo)]
  have h3 : 0 ≤ 1 - Real.exp (-ρlo) := by linarith only [exp_neg_lt_one hρlo]
  have h4 : Real.exp (-ρhi) * (1 - Real.exp (-ρlo)) ≤ 1 * 1 :=
    mul_le_mul h1 h2 h3 zero_le_one
  unfold shrinkDelta
  linarith only [h4]

/-- `x (1 - x) ≥ 2 δ` for `x = e^{-ρ}` with `ρlo ≤ ρ ≤ ρhi`. -/
lemma two_shrinkDelta_le {ρ : ℝ} (hρlo : 0 < ρlo) (hρ1 : ρlo ≤ ρ) (hρ2 : ρ ≤ ρhi) :
    2 * shrinkDelta ρlo ρhi ≤ Real.exp (-ρ) * (1 - Real.exp (-ρ)) := by
  have h1 : Real.exp (-ρhi) ≤ Real.exp (-ρ) := Real.exp_le_exp.mpr (by linarith only [hρ2])
  have h2 : Real.exp (-ρ) ≤ Real.exp (-ρlo) := Real.exp_le_exp.mpr (by linarith only [hρ1])
  have h3 : 0 ≤ 1 - Real.exp (-ρlo) := by linarith only [exp_neg_lt_one hρlo]
  have h4 : Real.exp (-ρhi) * (1 - Real.exp (-ρlo)) ≤ Real.exp (-ρ) * (1 - Real.exp (-ρ)) :=
    mul_le_mul h1 (by linarith only [h2]) h3 (Real.exp_pos _).le
  unfold shrinkDelta
  linarith only [h4]

lemma shrinkG0_pos (hρlo : 0 < ρlo) (ha : 0 ≤ a) (hg0 : 0 < g) : 0 < shrinkG0 ρlo ρhi a g := by
  have hd := shrinkDelta_pos (ρhi := ρhi) hρlo
  unfold shrinkG0
  exact lt_min hg0 (by positivity)

lemma shrinkG0_le : shrinkG0 ρlo ρhi a g ≤ g := min_le_left _ _

lemma a_mul_shrinkG0_le (hρlo : 0 < ρlo) (ha : 0 ≤ a) :
    a * shrinkG0 ρlo ρhi a g ≤ shrinkDelta ρlo ρhi / 3 := by
  have hd := shrinkDelta_pos (ρhi := ρhi) hρlo
  have hle : shrinkG0 ρlo ρhi a g ≤ shrinkDelta ρlo ρhi / (3 * (a + 1)) := min_le_right _ _
  have hmul := mul_le_mul_of_nonneg_left hle ha
  have heq : a * (shrinkDelta ρlo ρhi / (3 * (a + 1))) =
      shrinkDelta ρlo ρhi / 3 * (a / (a + 1)) := by
    field_simp
  have hfrac : a / (a + 1) ≤ 1 := by
    rw [div_le_one (by linarith only [ha])]
    linarith only
  have hfin : shrinkDelta ρlo ρhi / 3 * (a / (a + 1)) ≤ shrinkDelta ρlo ρhi / 3 := by
    have := mul_le_mul_of_nonneg_left hfrac (by linarith only [hd] : 0 ≤ shrinkDelta ρlo ρhi / 3)
    linarith only [this]
  linarith only [hmul, heq, hfin]

lemma shrinkBeta_nonneg (hρlo : 0 < ρlo) (ha : 0 ≤ a) : 0 ≤ shrinkBeta ρlo ρhi a :=
  div_nonneg ha (shrinkDelta_pos hρlo).le

lemma shrinkK_nonneg (hρlo : 0 < ρlo) (ha : 0 ≤ a) (hc : 0 ≤ c) : 0 ≤ shrinkK ρlo ρhi a c := by
  have hβ := shrinkBeta_nonneg (ρhi := ρhi) hρlo ha
  unfold shrinkK
  have : 0 ≤ 1 + c := by linarith only [hc]
  positivity

/-- The drift condition of the quadratic potential: `a + β q₀² ≤ β e^{-ρ}` with
`q₀ = e^{-ρ} + a g₀`. -/
lemma shrink_drift {ρ : ℝ} (hρlo : 0 < ρlo) (hρ : ρlo ≤ ρhi) (hρ1 : ρlo ≤ ρ) (hρ2 : ρ ≤ ρhi)
    (ha : 0 ≤ a) (hg0 : 0 < g) :
    a + shrinkBeta ρlo ρhi a * (Real.exp (-ρ) + a * shrinkG0 ρlo ρhi a g) ^ 2 ≤
      shrinkBeta ρlo ρhi a * Real.exp (-ρ) := by
  set δ := shrinkDelta ρlo ρhi with hδ
  set x := Real.exp (-ρ) with hx
  set y := a * shrinkG0 ρlo ρhi a g with hy
  have hδ0 : 0 < δ := shrinkDelta_pos hρlo
  have hδ1 : δ ≤ 1 / 2 := shrinkDelta_le_half hρlo hρ
  have hx1 : x ≤ 1 := le_of_lt (exp_neg_lt_one (lt_of_lt_of_le hρlo hρ1))
  have hxx : 2 * δ ≤ x * (1 - x) := two_shrinkDelta_le hρlo hρ1 hρ2
  have hy0 : 0 ≤ y := mul_nonneg ha (shrinkG0_pos hρlo ha hg0).le
  have hy3 : y ≤ δ / 3 := a_mul_shrinkG0_le hρlo ha
  have h1 : 0 ≤ y * (1 - x) := mul_nonneg hy0 (sub_nonneg.mpr hx1)
  have h2 : y * y ≤ δ / 3 * (δ / 3) := mul_le_mul hy3 hy3 hy0 (by linarith only [hδ0])
  have h3 : δ * δ ≤ δ * (1 / 2) := mul_le_mul_of_nonneg_left hδ1 hδ0.le
  have hgap : δ ≤ x - (x + y) ^ 2 := by nlinarith only [hxx, h1, h2, h3, hy3, hδ0]
  have hβ0 := shrinkBeta_nonneg (ρhi := ρhi) hρlo ha
  have hβδ : shrinkBeta ρlo ρhi a * δ = a := by
    unfold shrinkBeta
    rw [← hδ]
    field_simp
  have hmul := mul_le_mul_of_nonneg_left hgap hβ0
  have hexp : shrinkBeta ρlo ρhi a * (x - (x + y) ^ 2) =
      shrinkBeta ρlo ρhi a * x - shrinkBeta ρlo ρhi a * (x + y) ^ 2 := by ring
  linarith only [hmul, hβδ, hexp]

/-- The variance condition of the quadratic potential: `β (1 + c) ≤ e^{-ρ} K`. -/
lemma shrink_varK {ρ : ℝ} (hρlo : 0 < ρlo) (hρ2 : ρ ≤ ρhi) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    shrinkBeta ρlo ρhi a * (1 + c) ≤ Real.exp (-ρ) * shrinkK ρlo ρhi a c := by
  have hβ := shrinkBeta_nonneg (ρhi := ρhi) hρlo ha
  have h0 : 0 ≤ shrinkBeta ρlo ρhi a * (1 + c) := mul_nonneg hβ (by linarith only [hc])
  have h1 : 1 ≤ Real.exp (-ρ) * Real.exp ρhi := by
    rw [← Real.exp_add]
    have := Real.add_one_le_exp (-ρ + ρhi)
    linarith only [this, hρ2]
  have heq : Real.exp (-ρ) * shrinkK ρlo ρhi a c =
      shrinkBeta ρlo ρhi a * (1 + c) * (Real.exp (-ρ) * Real.exp ρhi) := by
    unfold shrinkK
    ring
  rw [heq]
  exact le_mul_of_one_le_right h0 h1

lemma shrinkP0_pos (hag : Real.exp (-ρlo) + a * g < 1) : 0 < shrinkP0 ρlo a g := by
  unfold shrinkP0
  linarith only [hag]

lemma shrinkP0_le_one (ha : 0 ≤ a) (hg : 0 ≤ g) : shrinkP0 ρlo a g ≤ 1 := by
  have h1 := Real.exp_pos (-ρlo)
  have h2 := mul_nonneg ha hg
  unfold shrinkP0
  linarith only [h1, h2]

lemma shrinkAlpha_pos (hρlo : 0 < ρlo) (hag : Real.exp (-ρlo) + a * g < 1) :
    0 < shrinkAlpha ρlo a g := by
  have := lt_min (shrinkP0_pos hag) (by linarith only [hρlo] : 0 < ρlo / 2)
  unfold shrinkAlpha
  linarith only [this]

lemma shrinkA1_nonneg (hρlo : 0 < ρlo) (ha : 0 ≤ a) (hg0 : 0 < g) :
    0 ≤ shrinkA1 ρlo ρhi a g :=
  div_nonneg hg0.le (shrinkG0_pos hρlo ha hg0).le

lemma shrinkA2_nonneg (hρlo : 0 < ρlo) (ha : 0 ≤ a) (hg0 : 0 < g) :
    0 ≤ shrinkA2 ρlo ρhi a c g := by
  have hβ := shrinkBeta_nonneg (ρhi := ρhi) hρlo ha
  have hg₀ := (shrinkG0_pos (ρhi := ρhi) hρlo ha hg0).le
  unfold shrinkA2
  have : 0 ≤ 1 + shrinkBeta ρlo ρhi a * shrinkG0 ρlo ρhi a g := by
    have := mul_nonneg hβ hg₀
    linarith only [this]
  positivity

lemma shrinkA_nonneg (hρlo : 0 < ρlo) (ha : 0 ≤ a) (hg0 : 0 < g) :
    0 ≤ shrinkA ρlo ρhi a c g := by
  have h1 := shrinkA1_nonneg (ρhi := ρhi) hρlo ha hg0
  have h2 := shrinkA2_nonneg (ρhi := ρhi) (c := c) hρlo ha hg0
  unfold shrinkA
  positivity

lemma shrinkN_facts {n : ℕ} (hρlo : 0 < ρlo) (hn : shrinkN ρlo ρhi a c ≤ n) :
    1 ≤ (n : ℝ) ∧ 2 * shrinkK ρlo ρhi a c ≤ ρlo * n := by
  have hcast : ((shrinkN ρlo ρhi a c : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
  have hceil : 2 * shrinkK ρlo ρhi a c / ρlo ≤ ⌈2 * shrinkK ρlo ρhi a c / ρlo⌉₊ :=
    Nat.le_ceil _
  have hN : ((shrinkN ρlo ρhi a c : ℕ) : ℝ) = ⌈2 * shrinkK ρlo ρhi a c / ρlo⌉₊ + 1 := by
    unfold shrinkN
    push_cast
    ring
  have hc0 : (0 : ℝ) ≤ ⌈2 * shrinkK ρlo ρhi a c / ρlo⌉₊ := Nat.cast_nonneg _
  refine ⟨by linarith only [hcast, hN, hc0], ?_⟩
  have h1 : 2 * shrinkK ρlo ρhi a c / ρlo ≤ n := by linarith only [hcast, hN, hceil]
  rw [div_le_iff₀ hρlo] at h1
  linarith only [h1]

end Constants

variable {n : ℕ}

/-- Stage one of Theorem 31 (Lemma 19): from at most `g n` uninformed nodes, at most `g₀ n` are
left after `r` rounds except with probability `(g / g₀) e^{-p₀ r}`. -/
lemma notYet_shrink_stage1 (P : RumorProcess n) {ρlo ρ a c g g₀ : ℝ} (hρ1 : ρlo ≤ ρ)
    (ha : 0 ≤ a) (hg : 0 ≤ g) (hg₀ : 0 < g₀) (hag : Real.exp (-ρlo) + a * g < 1)
    (hUS : P.UpperShrinking ρ a c g) (hn : 0 < (n : ℝ))
    (S : Finset (Fin n)) (hS : (n : ℝ) - S.card ≤ g * n) (r : ℕ) :
    P.notYet ((n : ℝ) - g₀ * n) r S ≤ g / g₀ * Real.exp (-shrinkP0 ρlo a g * r) := by
  have hp0 := shrinkP0_pos hag
  have hp1 := shrinkP0_le_one (ρlo := ρlo) ha hg
  have hrhs : 0 ≤ g / g₀ * Real.exp (-shrinkP0 ρlo a g * r) :=
    mul_nonneg (div_nonneg hg hg₀.le) (Real.exp_pos _).le
  by_cases hlt : (S.card : ℝ) < (n : ℝ) - g₀ * n
  · have hmn : (n : ℝ) - g₀ * n < n := by
      have := mul_pos hg₀ hn
      linarith only [this]
    have hp : ∀ T : Finset (Fin n), S.card ≤ T.card → (T.card : ℝ) < (n : ℝ) - g₀ * n →
        ∀ x ∉ T, shrinkP0 ρlo a g ≤ P.informProb T x := by
      intro T hST _ x hx
      have hcard : (S.card : ℝ) ≤ T.card := Nat.cast_le.mpr hST
      have hTg : (n : ℝ) - T.card ≤ g * n := by linarith only [hS, hcard]
      have h1 := (hUS T hTg).1 x hx
      have h2 : Real.exp (-ρ) ≤ Real.exp (-ρlo) := Real.exp_le_exp.mpr (by linarith only [hρ1])
      have h3 : ((n : ℝ) - T.card) / n ≤ g := (div_le_iff₀ hn).mpr hTg
      have h4 := mul_le_mul_of_nonneg_left h3 ha
      unfold shrinkP0
      linarith only [h1, h2, h4]
    have hconn := connect_tail P (ℓ := S.card) hlt hmn hp0.le hp1 hp S le_rfl r
    have hden : (n : ℝ) - ((n : ℝ) - g₀ * n) = g₀ * n := by ring
    rw [hden] at hconn
    have hratio : ((n : ℝ) - S.card) / (g₀ * n) ≤ g / g₀ := by
      rw [div_le_div_iff₀ (mul_pos hg₀ hn) hg₀]
      have := mul_le_mul_of_nonneg_right hS hg₀.le
      linarith only [this, show g * n * g₀ = g * (g₀ * n) by ring]
    have hpow := one_sub_pow_le_exp hp1 r
    exact le_trans hconn (mul_le_mul hratio hpow (pow_nonneg (sub_nonneg.mpr hp1) r)
      (div_nonneg hg hg₀.le))
  · rw [notYet_eq_zero_of_ge P (not_lt.mp hlt) r]
    exact hrhs

/-- Theorem 31, tail bound with explicit constants. -/
lemma notYet_shrink_le {ρlo ρhi a c g : ℝ} (hρlo : 0 < ρlo) (hρ : ρlo ≤ ρhi) (ha : 0 ≤ a)
    (hc : 0 ≤ c) (hg0 : 0 < g) (hag : Real.exp (-ρlo) + a * g < 1)
    (hn : shrinkN ρlo ρhi a c ≤ n) {ρ : ℝ} (hρ1 : ρlo ≤ ρ) (hρ2 : ρ ≤ ρhi)
    (P : RumorProcess n) (hUS : P.UpperShrinking ρ a c g)
    (S : Finset (Fin n)) (hS : (n : ℝ) - S.card ≤ g * n) (r : ℕ) :
    P.notYet n (⌈Real.log n / ρ⌉₊ + r) S ≤
      shrinkA ρlo ρhi a c g * Real.exp (-shrinkAlpha ρlo a g * r) := by
  obtain ⟨hn1, hnK⟩ := shrinkN_facts hρlo hn
  have hn0 : 0 < (n : ℝ) := by linarith only [hn1]
  have hg₀ := shrinkG0_pos (ρhi := ρhi) hρlo ha hg0
  have h₁ : ∀ r : ℕ, P.notYet ((n : ℝ) - shrinkG0 ρlo ρhi a g * n) (0 + r) S ≤
      shrinkA1 ρlo ρhi a g * Real.exp (-shrinkP0 ρlo a g * r) := by
    intro r
    rw [zero_add]
    exact notYet_shrink_stage1 P hρ1 ha hg0.le hg₀ hag hUS hn0 S hS r
  have h₂ : ∀ T : Finset (Fin n), (n : ℝ) - shrinkG0 ρlo ρhi a g * n ≤ (T.card : ℝ) →
      ∀ r : ℕ, P.notYet n (⌈Real.log n / ρ⌉₊ + r) T ≤
        shrinkA2 ρlo ρhi a c g * Real.exp (-(ρlo / 2) * r) := by
    intro T hT r
    exact notYet_shrink_stage2 P hρlo hρ1 ha hc hg₀.le shrinkG0_le
      (shrinkBeta_nonneg hρlo ha) (shrinkK_nonneg hρlo ha hc)
      (shrink_drift hρlo hρ hρ1 hρ2 ha hg0) (shrink_varK hρlo hρ2 ha hc) hUS hn1 hnK T
      (by linarith only [hT]) r
  have hcomp := tail_compose P (shrinkA1_nonneg (ρhi := ρhi) hρlo ha hg0)
    (shrinkA2_nonneg (c := c) hρlo ha hg0) (shrinkP0_pos hag)
    (by linarith only [hρlo] : 0 < ρlo / 2) S h₁ h₂ r
  rw [zero_add] at hcomp
  exact hcomp

/-- Theorem 31, tail bound (proof of `shrinking_upper_tail`). -/
theorem shrinking_upper_tail_proof {ρlo ρhi a c g : ℝ} (hρlo : 0 < ρlo) (hρ : ρlo ≤ ρhi)
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hg0 : 0 < g) (hag : Real.exp (-ρlo) + a * g < 1) :
    ∃ A α : ℝ, 0 < α ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ ρ : ℝ, ρlo ≤ ρ → ρ ≤ ρhi →
      ∀ P : RumorProcess n, P.UpperShrinking ρ a c g →
      ∀ S : Finset (Fin n), (n : ℝ) - S.card ≤ g * n → ∀ r : ℕ,
        P.notYet n (⌈Real.log n / ρ⌉₊ + r) S ≤ A * Real.exp (-α * r) :=
  ⟨shrinkA ρlo ρhi a c g, shrinkAlpha ρlo a g, shrinkAlpha_pos hρlo hag, shrinkN ρlo ρhi a c,
    fun _ hn _ hρ1 hρ2 P hUS S hS r =>
      notYet_shrink_le hρlo hρ ha hc hg0 hag hn hρ1 hρ2 P hUS S hS r⟩

/-- Theorem 31, expectation (proof of `shrinking_upper_expect`). -/
theorem shrinking_upper_expect_proof {ρlo ρhi a c g : ℝ} (hρlo : 0 < ρlo) (hρ : ρlo ≤ ρhi)
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hg0 : 0 < g) (hag : Real.exp (-ρlo) + a * g < 1) :
    ∃ B : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ ρ : ℝ, ρlo ≤ ρ → ρ ≤ ρhi →
      ∀ P : RumorProcess n, P.UpperShrinking ρ a c g →
      ∀ S : Finset (Fin n), (n : ℝ) - S.card ≤ g * n → ∀ R : ℕ,
        ∑ t ∈ range R, P.notYet n t S ≤ Real.log n / ρ + B := by
  refine ⟨1 + shrinkA ρlo ρhi a c g / (1 - Real.exp (-shrinkAlpha ρlo a g)),
    shrinkN ρlo ρhi a c, ?_⟩
  intro n hn ρ hρ1 hρ2 P hUS S hS R
  obtain ⟨hn1, -⟩ := shrinkN_facts hρlo hn
  have hρ0 : 0 < ρ := lt_of_lt_of_le hρlo hρ1
  have hsum := sum_notYet_le_of_tail P (shrinkA_nonneg (ρhi := ρhi) (c := c) hρlo ha hg0)
    (shrinkAlpha_pos hρlo hag) _ S
    (notYet_shrink_le hρlo hρ ha hc hg0 hag hn hρ1 hρ2 P hUS S hS) R
  have hL : (⌈Real.log n / ρ⌉₊ : ℝ) < Real.log n / ρ + 1 :=
    Nat.ceil_lt_add_one (div_nonneg (Real.log_nonneg hn1) hρ0.le)
  linarith only [hsum, hL]

end Epidemics.Revisited
