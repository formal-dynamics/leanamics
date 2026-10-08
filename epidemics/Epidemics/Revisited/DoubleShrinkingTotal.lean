import Epidemics.Revisited.DoubleShrinkingUpper
import Epidemics.Revisited.ShrinkingTotal

/-! # Theorem 43 and the total spreading time with double exponential shrinking (EPI-8, proofs)

* `double_shrinking_upper_tail_proof`: Theorem 43's tail `C n^{A' - α' r}`, from the main case
  (`double_shrinking_tail_main`) and the degenerate cases `g = 0` (nothing to do) and `α = 0`
  (fast finishing everywhere).
* `double_shrinking_exp_tail`: the same tail in the form `A e^{-α' r}` (for `n ≥ 3`), which
  composes with the other regimes by `tail_compose`, and gives the expectation through
  `sum_notYet_le_of_tail`.
* The total spreading time: Theorem 21, Lemma 19 and Theorem 43 composed as in
  `spreading_upper_tail_proof`.
-/

namespace Epidemics.Revisited
open Finset Dynamics

variable {n : ℕ}

/-- Theorem 43 with `α = 0`: every state finishes fast, so the tail is `n^{1 - τ r}`. -/
lemma double_shrinking_tail_alpha_zero {τ : ℝ} (hn : 1 ≤ n) (P : RumorProcess n)
    (hFF : P.FastFinishing 0 τ) (S : Finset (Fin n)) (T₀ r : ℕ) :
    P.notYet n (T₀ + r) S ≤ 1 * (n : ℝ) ^ (1 - τ * r) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hU : (n : ℝ) - S.card ≤ n := by have : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _; linarith
  have hfin := notYet_finish_le P (U := n) (npow_pos hn (-τ)).le
    (fun T hT x hx => hFF T (by rw [sub_zero, Real.rpow_one]; exact hT) x hx) S hU r
  have hmono := notYet_antitone P n (Nat.le_add_left r T₀) S
  have hu := mul_le_mul_of_nonneg_left hU (pow_nonneg (npow_pos hn (-τ)).le r)
  rw [npow_pow] at hfin hu
  have heq : (n : ℝ) ^ (-τ * (r : ℝ)) * n = (n : ℝ) ^ (1 - τ * r) := by
    rw [← Real.rpow_add_one hn0.ne']
    congr 1
    ring
  rw [one_mul, ← heq]
  linarith

/-- Theorem 43, tail (proof of `double_shrinking_upper_tail`, with `1 ≤ C` and `0 ≤ A'`). -/
theorem double_shrinking_upper_tail_proof {ℓ a c g α τ : ℝ} (hℓ : 1 < ℓ) (ha : 0 ≤ a)
    (hc : 0 ≤ c) (hg0 : 0 ≤ g) (hα0 : 0 ≤ α) (hag : a * g ^ (ℓ - 1) < 1) (hτ : 0 < τ) :
    ∃ C A' α' : ℝ, 1 ≤ C ∧ 0 ≤ A' ∧ 0 < α' ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ P : RumorProcess n, P.UpperDoubleShrinking ℓ a c g α → P.FastFinishing α τ →
      ∀ S : Finset (Fin n), (n : ℝ) - S.card ≤ g * n → ∀ r : ℕ,
        P.notYet n (⌈Real.logb ℓ (Real.log n)⌉₊ + r) S ≤ C * (n : ℝ) ^ (A' - α' * r) := by
  rcases hg0.eq_or_lt with hg | hg
  · -- `g = 0`: all nodes are informed from the start
    refine ⟨1, 0, 1, le_rfl, le_rfl, one_pos, 1, ?_⟩
    intro n hn P _ _ S hS r
    rw [← hg, zero_mul] at hS
    rw [notYet_eq_zero_of_ge P (by linarith) _]
    exact mul_nonneg zero_le_one (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  rcases hα0.eq_or_lt with hα | hα
  · -- `α = 0`: fast finishing everywhere
    refine ⟨1, 1, τ, le_rfl, zero_le_one, hτ, 1, ?_⟩
    intro n hn P _ hFF S _ r
    rw [← hα] at hFF
    exact double_shrinking_tail_alpha_zero hn P hFF S _ r
  exact double_shrinking_tail_main hℓ ha hc hg hα hag hτ

/-- A polynomial tail `C n^{A' - α' r}` is an exponential tail `C e^{A'} e^{-α' r}` once
`ln n ≥ 1`. -/
lemma exp_tail_of_poly (P : RumorProcess n) {m C A' α' : ℝ} (hC : 1 ≤ C) (hn : 3 ≤ n) (T₀ : ℕ)
    (S : Finset (Fin n))
    (h : ∀ r : ℕ, P.notYet m (T₀ + r) S ≤ C * (n : ℝ) ^ (A' - α' * r)) (r : ℕ) :
    P.notYet m (T₀ + r) S ≤ C * Real.exp A' * Real.exp (-α' * r) := by
  have hn1 : 1 ≤ n := by omega
  have hlog : 1 ≤ Real.log n := by
    have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have he : Real.exp 1 ≤ 3 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (le_trans he h3)
  have hsplit : C * Real.exp A' * Real.exp (-α' * r) = C * Real.exp (A' - α' * r) := by
    rw [mul_assoc, ← Real.exp_add]; ring_nf
  rw [hsplit]
  by_cases hx : A' - α' * r ≤ 0
  · refine le_trans (h r) (mul_le_mul_of_nonneg_left ?_ (by linarith))
    rw [npow_eq_exp hn1]
    apply Real.exp_le_exp.mpr
    nlinarith
  · rw [not_le] at hx
    have h1 := notYet_le_one P m (T₀ + r) S
    have h2 : 1 ≤ Real.exp (A' - α' * r) := Real.one_le_exp hx.le
    nlinarith [Real.exp_pos (A' - α' * r)]

/-- Theorem 43, exponential form of the tail. -/
theorem double_shrinking_exp_tail {ℓ a c g α τ : ℝ} (hℓ : 1 < ℓ) (ha : 0 ≤ a)
    (hc : 0 ≤ c) (hg0 : 0 ≤ g) (hα0 : 0 ≤ α) (hag : a * g ^ (ℓ - 1) < 1) (hτ : 0 < τ) :
    ∃ A α' : ℝ, 0 ≤ A ∧ 0 < α' ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ P : RumorProcess n, P.UpperDoubleShrinking ℓ a c g α → P.FastFinishing α τ →
      ∀ S : Finset (Fin n), (n : ℝ) - S.card ≤ g * n → ∀ r : ℕ,
        P.notYet n (⌈Real.logb ℓ (Real.log n)⌉₊ + r) S ≤ A * Real.exp (-α' * r) := by
  obtain ⟨C, A', α', hC, -, hα', N, h⟩ :=
    double_shrinking_upper_tail_proof hℓ ha hc hg0 hα0 hag hτ
  refine ⟨C * Real.exp A', α', by have := Real.exp_pos A'; positivity, hα', max N 3,
    le_max_right _ _, ?_⟩
  intro n hn P hDES hFF S hS r
  exact exp_tail_of_poly P hC (le_trans (le_max_right _ _) hn) _ S
    (h n (le_trans (le_max_left _ _) hn) P hDES hFF S hS) r

/-- Theorem 43, expectation (proof of `double_shrinking_upper_expect`). -/
theorem double_shrinking_upper_expect_proof {ℓ a c g α τ : ℝ} (hℓ : 1 < ℓ) (ha : 0 ≤ a)
    (hc : 0 ≤ c) (hg0 : 0 ≤ g) (hα0 : 0 ≤ α) (hag : a * g ^ (ℓ - 1) < 1) (hτ : 0 < τ) :
    ∃ B : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ P : RumorProcess n,
      P.UpperDoubleShrinking ℓ a c g α → P.FastFinishing α τ →
      ∀ S : Finset (Fin n), (n : ℝ) - S.card ≤ g * n → ∀ R : ℕ,
        ∑ t ∈ range R, P.notYet n t S ≤ Real.logb ℓ (Real.log n) + B := by
  obtain ⟨A, α', hA, hα', N, hN3, h⟩ := double_shrinking_exp_tail hℓ ha hc hg0 hα0 hag hτ
  refine ⟨1 + A / (1 - Real.exp (-α')), N, ?_⟩
  intro n hn P hDES hFF S hS R
  have hsum := sum_notYet_le_of_tail P hA hα' _ S (h n hn P hDES hFF S hS) R
  have hlog1 : 1 ≤ Real.log n := by
    have h3 : (3 : ℝ) ≤ n := by exact_mod_cast le_trans hN3 hn
    have he : Real.exp 1 ≤ 3 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (le_trans he h3)
  have hL : (⌈Real.logb ℓ (Real.log n)⌉₊ : ℝ) < Real.logb ℓ (Real.log n) + 1 :=
    Nat.ceil_lt_add_one (Real.logb_nonneg hℓ hlog1)
  linarith

/-- Total spreading time with double exponential shrinking, tail (proof of
`spreading_upper_tail_double`). -/
theorem spreading_upper_tail_double_proof {γlo γhi a b c f ℓ a' c' g α τ p : ℝ}
    (hγlo : 0 < γlo) (hγ : γlo ≤ γhi) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hf0 : 0 < f)
    (hf1 : f < 1) (haf : a * f < 1) (hℓ : 1 < ℓ) (ha' : 0 ≤ a') (hc' : 0 ≤ c') (hg0 : 0 < g)
    (hα0 : 0 ≤ α) (hag : a' * g ^ (ℓ - 1) < 1) (hτ : 0 < τ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∃ A κ : ℝ, 0 ≤ A ∧ 0 < κ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ γ : ℝ, γlo ≤ γ → γ ≤ γhi →
      ∀ P : RumorProcess n,
      P.UpperGrowth γ a b c f → P.UpperDoubleShrinking ℓ a' c' g α → P.FastFinishing α τ →
      (∀ S : Finset (Fin n), f * n ≤ S.card → g * n < (n : ℝ) - S.card →
        ∀ x ∉ S, p ≤ P.informProb S x) →
      ∀ S : Finset (Fin n), S.Nonempty → ∀ r : ℕ,
        P.notYet n (⌈Real.logb (1 + γ) n⌉₊ + ⌈Real.logb ℓ (Real.log n)⌉₊ + r) S
          ≤ A * Real.exp (-κ * r) := by
  obtain ⟨Ag, αg, hαg, Ng, hgrowth⟩ := growth_upper_tail hγlo hγ ha hb hc hf0 hf1 haf
  obtain ⟨As, αs, hAs0, hαs0, Ns, hNs3, hshrink⟩ :=
    double_shrinking_exp_tail hℓ ha' hc' hg0.le hα0 hag hτ
  set AM : ℝ := (1 - f) / g with hAM
  set A₂ : ℝ := AM * Real.exp (min p αs / 2) + As with hA₂
  set α₂ : ℝ := min p αs / 2 with hα₂
  have hAM0 : 0 ≤ AM := div_nonneg (by linarith only [hf1]) hg0.le
  have hA₂0 : 0 ≤ A₂ := add_nonneg (mul_nonneg hAM0 (Real.exp_pos _).le) hAs0
  have hα₂0 : 0 < α₂ := by
    have := lt_min hp0 hαs0
    rw [hα₂]
    linarith only [this]
  set Ag' : ℝ := max Ag 0 with hAg'
  have hAg'0 : 0 ≤ Ag' := le_max_right _ _
  refine ⟨Ag' * Real.exp (min αg α₂ / 2) + A₂, min αg α₂ / 2,
    add_nonneg (mul_nonneg hAg'0 (Real.exp_pos _).le) hA₂0,
    by have := lt_min hαg hα₂0; linarith only [this], max Ng Ns, ?_⟩
  intro n hn γ hγ1 hγ2 P hUG hDES hFF hmid S hS r
  have hnG : Ng ≤ n := le_trans (le_max_left _ _) hn
  have hnS : Ns ≤ n := le_trans (le_max_right _ _) hn
  have hn0 : 0 < (n : ℝ) := by
    have : 3 ≤ n := le_trans hNs3 hnS
    exact_mod_cast (show 0 < n by omega)
  have h₁ : ∀ r : ℕ, P.notYet (f * n) (⌈Real.logb (1 + γ) n⌉₊ + r) S ≤
      Ag' * Real.exp (-αg * r) := by
    intro r
    have h := hgrowth n hnG γ hγ1 hγ2 P hUG S hS r
    exact le_trans h (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  have h₂ : ∀ T : Finset (Fin n), f * n ≤ (T.card : ℝ) → ∀ r : ℕ,
      P.notYet n (⌈Real.logb ℓ (Real.log n)⌉₊ + r) T ≤ A₂ * Real.exp (-α₂ * r) := by
    intro T hT r
    have hm : ∀ r : ℕ, P.notYet ((n : ℝ) - g * n) (0 + r) T ≤ AM * Real.exp (-p * r) := by
      intro r
      rw [zero_add]
      exact notYet_middle_le P hf1 hg0 hp0 hp1 hn0 hmid T hT r
    have hs : ∀ U : Finset (Fin n), (n : ℝ) - g * n ≤ (U.card : ℝ) → ∀ r : ℕ,
        P.notYet n (⌈Real.logb ℓ (Real.log n)⌉₊ + r) U ≤ As * Real.exp (-αs * r) := by
      intro U hU r
      exact hshrink n hnS P hDES hFF U (by linarith only [hU]) r
    have hcomp := tail_compose P hAM0 hAs0 hp0 hαs0 T hm hs r
    rw [zero_add] at hcomp
    exact hcomp
  exact tail_compose P hAg'0 hA₂0 hαg hα₂0 S h₁ h₂ r

/-- Total spreading time with double exponential shrinking, expectation (proof of
`spreading_upper_expect_double`). -/
theorem spreading_upper_expect_double_proof {γlo γhi a b c f ℓ a' c' g α τ p : ℝ}
    (hγlo : 0 < γlo) (hγ : γlo ≤ γhi) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hf0 : 0 < f)
    (hf1 : f < 1) (haf : a * f < 1) (hℓ : 1 < ℓ) (ha' : 0 ≤ a') (hc' : 0 ≤ c') (hg0 : 0 < g)
    (hα0 : 0 ≤ α) (hag : a' * g ^ (ℓ - 1) < 1) (hτ : 0 < τ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∃ B : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ γ : ℝ, γlo ≤ γ → γ ≤ γhi →
      ∀ P : RumorProcess n,
      P.UpperGrowth γ a b c f → P.UpperDoubleShrinking ℓ a' c' g α → P.FastFinishing α τ →
      (∀ S : Finset (Fin n), f * n ≤ S.card → g * n < (n : ℝ) - S.card →
        ∀ x ∉ S, p ≤ P.informProb S x) →
      ∀ S : Finset (Fin n), S.Nonempty → ∀ R : ℕ,
        ∑ t ∈ range R, P.notYet n t S ≤
          Real.logb (1 + γ) n + Real.logb ℓ (Real.log n) + B := by
  obtain ⟨A, κ, hA, hκ, N, htail⟩ := spreading_upper_tail_double_proof hγlo hγ ha hb hc hf0
    hf1 haf hℓ ha' hc' hg0 hα0 hag hτ hp0 hp1
  refine ⟨2 + A / (1 - Real.exp (-κ)), max N 3, ?_⟩
  intro n hn γ hγ1 hγ2 P hUG hDES hFF hmid S hS R
  have hn1 : (1 : ℝ) ≤ n := by
    have : 3 ≤ n := le_trans (le_max_right N 3) hn
    exact_mod_cast (show 1 ≤ n by omega)
  have hlog1 : 1 ≤ Real.log n := by
    have h3 : (3 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right N 3) hn
    have he : Real.exp 1 ≤ 3 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (le_trans he h3)
  have hsum := sum_notYet_le_of_tail P hA hκ _ S
    (htail n (le_trans (le_max_left N 3) hn) γ hγ1 hγ2 P hUG hDES hFF hmid S hS) R
  have hb1 : 1 < 1 + γ := by linarith only [hγlo, hγ1]
  have hL1 : (⌈Real.logb (1 + γ) n⌉₊ : ℝ) < Real.logb (1 + γ) n + 1 :=
    Nat.ceil_lt_add_one (Real.logb_nonneg hb1 hn1)
  have hL2 : (⌈Real.logb ℓ (Real.log n)⌉₊ : ℝ) < Real.logb ℓ (Real.log n) + 1 :=
    Nat.ceil_lt_add_one (Real.logb_nonneg hℓ hlog1)
  push_cast at hsum
  linarith only [hsum, hL1, hL2]

end Epidemics.Revisited
