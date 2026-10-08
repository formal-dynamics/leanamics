import Epidemics.Revisited.ShrinkingUpper

/-! # Total spreading time, upper bound (Theorems 21 and 31 composed through Lemma 19)

Three stages, composed by `tail_compose`:

1. growth from a nonempty set to `f n` informed nodes within `⌈log_{1+γ} n⌉ + r` rounds
   (Theorem 21, `growth_upper_tail`);
2. from `f n` informed nodes to at most `g n` uninformed ones within `r` rounds, when every
   uninformed node is informed with probability at least `p` in between (Lemma 19,
   `notYet_middle_le`, prefactor `(1 - f) / g`);
3. from at most `g n` uninformed nodes to none within `⌈ln n / ρ⌉ + r` rounds (Theorem 31,
   `notYet_shrink_le`).

The expectation follows from the tail by `sum_notYet_le_of_tail`.
-/

namespace Epidemics.Revisited
open Finset Dynamics

variable {n : ℕ}

/-- The middle stage (Lemma 19): from at least `f n` informed nodes, more than `g n` nodes are
still uninformed after `r` rounds with probability at most `((1 - f) / g) e^{-p r}`. -/
lemma notYet_middle_le (P : RumorProcess n) {f g p : ℝ} (hf1 : f < 1) (hg0 : 0 < g)
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hn : 0 < (n : ℝ))
    (hmid : ∀ S : Finset (Fin n), f * n ≤ S.card → g * n < (n : ℝ) - S.card →
      ∀ x ∉ S, p ≤ P.informProb S x)
    (S : Finset (Fin n)) (hS : f * n ≤ S.card) (r : ℕ) :
    P.notYet ((n : ℝ) - g * n) r S ≤ (1 - f) / g * Real.exp (-p * r) := by
  have hfg : 0 ≤ (1 - f) / g := div_nonneg (by linarith only [hf1]) hg0.le
  by_cases hlt : (S.card : ℝ) < (n : ℝ) - g * n
  · have hmn : (n : ℝ) - g * n < n := by
      have := mul_pos hg0 hn
      linarith only [this]
    have hp : ∀ T : Finset (Fin n), S.card ≤ T.card → (T.card : ℝ) < (n : ℝ) - g * n →
        ∀ x ∉ T, p ≤ P.informProb T x := by
      intro T hST hT x hx
      have hcard : (S.card : ℝ) ≤ T.card := Nat.cast_le.mpr hST
      exact hmid T (le_trans hS hcard) (by linarith only [hT]) x hx
    have hconn := connect_tail P (ℓ := S.card) hlt hmn hp0.le hp1 hp S le_rfl r
    have hden : (n : ℝ) - ((n : ℝ) - g * n) = g * n := by ring
    rw [hden] at hconn
    have hratio : ((n : ℝ) - S.card) / (g * n) ≤ (1 - f) / g := by
      rw [div_le_div_iff₀ (mul_pos hg0 hn) hg0]
      have h1 : (n : ℝ) - S.card ≤ (1 - f) * n := by linarith only [hS]
      have h2 := mul_le_mul_of_nonneg_right h1 hg0.le
      linarith only [h2, show (1 - f) * n * g = (1 - f) * (g * n) by ring]
    have hpow := one_sub_pow_le_exp hp1 r
    exact le_trans hconn (mul_le_mul hratio hpow (pow_nonneg (sub_nonneg.mpr hp1) r) hfg)
  · rw [notYet_eq_zero_of_ge P (not_lt.mp hlt) r]
    exact mul_nonneg hfg (Real.exp_pos _).le

/-- Total spreading time, tail bound, with a nonnegative prefactor (proof of
`spreading_upper_tail`). -/
theorem spreading_upper_tail_proof {γlo γhi a b c f ρlo ρhi a' c' g p : ℝ}
    (hγlo : 0 < γlo) (hγ : γlo ≤ γhi) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hf0 : 0 < f)
    (hf1 : f < 1) (haf : a * f < 1) (hρlo : 0 < ρlo) (hρ : ρlo ≤ ρhi) (ha' : 0 ≤ a')
    (hc' : 0 ≤ c') (hg0 : 0 < g) (hag : Real.exp (-ρlo) + a' * g < 1)
    (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∃ A α : ℝ, 0 ≤ A ∧ 0 < α ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ γ : ℝ, γlo ≤ γ → γ ≤ γhi →
      ∀ ρ : ℝ, ρlo ≤ ρ → ρ ≤ ρhi → ∀ P : RumorProcess n,
      P.UpperGrowth γ a b c f → P.UpperShrinking ρ a' c' g →
      (∀ S : Finset (Fin n), f * n ≤ S.card → g * n < (n : ℝ) - S.card →
        ∀ x ∉ S, p ≤ P.informProb S x) →
      ∀ S : Finset (Fin n), S.Nonempty → ∀ r : ℕ,
        P.notYet n (⌈Real.logb (1 + γ) n⌉₊ + ⌈Real.log n / ρ⌉₊ + r) S
          ≤ A * Real.exp (-α * r) := by
  obtain ⟨Ag, αg, hαg, Ng, hgrowth⟩ := growth_upper_tail hγlo hγ ha hb hc hf0 hf1 haf
  -- middle and shrinking stages
  set AM : ℝ := (1 - f) / g with hAM
  set As : ℝ := shrinkA ρlo ρhi a' c' g with hAs
  set αs : ℝ := shrinkAlpha ρlo a' g with hαs
  set A₂ : ℝ := AM * Real.exp (min p αs / 2) + As with hA₂
  set α₂ : ℝ := min p αs / 2 with hα₂
  have hAM0 : 0 ≤ AM := div_nonneg (by linarith only [hf1]) hg0.le
  have hAs0 : 0 ≤ As := shrinkA_nonneg hρlo ha' hg0
  have hαs0 : 0 < αs := shrinkAlpha_pos hρlo hag
  have hA₂0 : 0 ≤ A₂ := add_nonneg (mul_nonneg hAM0 (Real.exp_pos _).le) hAs0
  have hα₂0 : 0 < α₂ := by
    have := lt_min hp0 hαs0
    rw [hα₂]
    linarith only [this]
  set Ag' : ℝ := max Ag 0 with hAg'
  have hAg'0 : 0 ≤ Ag' := le_max_right _ _
  refine ⟨Ag' * Real.exp (min αg α₂ / 2) + A₂, min αg α₂ / 2,
    add_nonneg (mul_nonneg hAg'0 (Real.exp_pos _).le) hA₂0,
    by have := lt_min hαg hα₂0; linarith only [this], max Ng (shrinkN ρlo ρhi a' c'), ?_⟩
  intro n hn γ hγ1 hγ2 ρ hρ1 hρ2 P hUG hUS hmid S hS r
  have hnG : Ng ≤ n := le_trans (le_max_left _ _) hn
  have hnS : shrinkN ρlo ρhi a' c' ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨hn1, -⟩ := shrinkN_facts hρlo hnS
  have hn0 : 0 < (n : ℝ) := by linarith only [hn1]
  -- stage one: growth
  have h₁ : ∀ r : ℕ, P.notYet (f * n) (⌈Real.logb (1 + γ) n⌉₊ + r) S ≤
      Ag' * Real.exp (-αg * r) := by
    intro r
    have h := hgrowth n hnG γ hγ1 hγ2 P hUG S hS r
    exact le_trans h (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  -- stages two and three, from any state with at least `f n` informed nodes
  have h₂ : ∀ T : Finset (Fin n), f * n ≤ (T.card : ℝ) → ∀ r : ℕ,
      P.notYet n (⌈Real.log n / ρ⌉₊ + r) T ≤ A₂ * Real.exp (-α₂ * r) := by
    intro T hT r
    have hm : ∀ r : ℕ, P.notYet ((n : ℝ) - g * n) (0 + r) T ≤ AM * Real.exp (-p * r) := by
      intro r
      rw [zero_add]
      exact notYet_middle_le P hf1 hg0 hp0 hp1 hn0 hmid T hT r
    have hs : ∀ U : Finset (Fin n), (n : ℝ) - g * n ≤ (U.card : ℝ) → ∀ r : ℕ,
        P.notYet n (⌈Real.log n / ρ⌉₊ + r) U ≤ As * Real.exp (-αs * r) := by
      intro U hU r
      exact notYet_shrink_le hρlo hρ ha' hc' hg0 hag hnS hρ1 hρ2 P hUS U
        (by linarith only [hU]) r
    have hcomp := tail_compose P hAM0 hAs0 hp0 hαs0 T hm hs r
    rw [zero_add] at hcomp
    exact hcomp
  exact tail_compose P hAg'0 hA₂0 hαg hα₂0 S h₁ h₂ r

/-- Total spreading time, expectation (proof of `spreading_upper_expect`). -/
theorem spreading_upper_expect_proof {γlo γhi a b c f ρlo ρhi a' c' g p : ℝ}
    (hγlo : 0 < γlo) (hγ : γlo ≤ γhi) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hf0 : 0 < f)
    (hf1 : f < 1) (haf : a * f < 1) (hρlo : 0 < ρlo) (hρ : ρlo ≤ ρhi) (ha' : 0 ≤ a')
    (hc' : 0 ≤ c') (hg0 : 0 < g) (hag : Real.exp (-ρlo) + a' * g < 1)
    (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∃ B : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ γ : ℝ, γlo ≤ γ → γ ≤ γhi →
      ∀ ρ : ℝ, ρlo ≤ ρ → ρ ≤ ρhi → ∀ P : RumorProcess n,
      P.UpperGrowth γ a b c f → P.UpperShrinking ρ a' c' g →
      (∀ S : Finset (Fin n), f * n ≤ S.card → g * n < (n : ℝ) - S.card →
        ∀ x ∉ S, p ≤ P.informProb S x) →
      ∀ S : Finset (Fin n), S.Nonempty → ∀ R : ℕ,
        ∑ t ∈ range R, P.notYet n t S ≤ Real.logb (1 + γ) n + Real.log n / ρ + B := by
  obtain ⟨A, α, hA, hα, N, htail⟩ := spreading_upper_tail_proof hγlo hγ ha hb hc hf0 hf1 haf
    hρlo hρ ha' hc' hg0 hag hp0 hp1
  refine ⟨2 + A / (1 - Real.exp (-α)), max N 1, ?_⟩
  intro n hn γ hγ1 hγ2 ρ hρ1 hρ2 P hUG hUS hmid S hS R
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right N 1) hn
  have hsum := sum_notYet_le_of_tail P hA hα _ S
    (htail n (le_trans (le_max_left N 1) hn) γ hγ1 hγ2 ρ hρ1 hρ2 P hUG hUS hmid S hS) R
  have hb1 : 1 < 1 + γ := by linarith only [hγlo, hγ1]
  have hL1 : (⌈Real.logb (1 + γ) n⌉₊ : ℝ) < Real.logb (1 + γ) n + 1 :=
    Nat.ceil_lt_add_one (Real.logb_nonneg hb1 hn1)
  have hL2 : (⌈Real.log n / ρ⌉₊ : ℝ) < Real.log n / ρ + 1 :=
    Nat.ceil_lt_add_one (div_nonneg (Real.log_nonneg hn1) (lt_of_lt_of_le hρlo hρ1).le)
  push_cast at hsum
  linarith only [hsum, hL1, hL2]

end Epidemics.Revisited
