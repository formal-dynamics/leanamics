import Epidemics.Revisited.DoubleShrinkingRound

/-! # The three stages of Theorem 43, for one value of `n` (EPI-8)

1. **Geometric stage** (`stage_geom`): from at most `g n` uninformed nodes to at most `g₀ n`,
   with targets `g μ^j n`, `μ = (1 + a g^{ℓ-1}) / 2 < 1`, in a constant number `K` of phases.
   The paper uses Lemma 19 here, which gives the expectation `O(1)` but a tail whose rate does
   not depend on `n`; the per-round Chebyshev bound gives failure probability `O(1/n)` per phase.
2. **Double exponential stage** (`stage_double`): targets `ε_{j+1} = 2 a₁ ε_j^ℓ`, written in
   closed form `ε_j = exp (-(κ + ℓ^j D₀))` with `κ (ℓ - 1) = ln (2 a₁)`, for `J` phases
   (Observation 3, Corollary 46 and Lemma 47 of the paper).
3. **Finishing stage** (`stage_finish`): below `ε_J n` uninformed nodes every uninformed node
   stays uninformed with probability at most `θ`, so all are informed after `t` rounds except
   with probability `θ^t n`.
-/

namespace Epidemics.Revisited
open Finset Dynamics

variable {n : ℕ}

/-- Stage 1: geometric targets `g μ^j n`. -/
lemma stage_geom (P : RumorProcess n) {ℓ a c g α τ lam μ δ : ℝ} (K : ℕ) (hℓ : 1 < ℓ)
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hg : 0 < g) (hlam : a * g ^ (ℓ - 1) ≤ lam) (hlamμ : lam < μ)
    (hμ1 : μ ≤ 1) (hδ : 0 < δ) (hn : 1 ≤ n) (h2 : 2 ≤ (n : ℝ) ^ (δ / 2))
    (hq : (1 + c) * n / (g * μ ^ K * (μ - lam) * n) ^ 2 +
        (n : ℝ) ^ (1 - α) * (n : ℝ) ^ (-τ) / (g * μ ^ K * n) ≤ (n : ℝ) ^ (-(2 * δ)))
    (hDES : P.UpperDoubleShrinking ℓ a c g α) (hFF : P.FastFinishing α τ)
    (S : Finset (Fin n)) (hS : (n : ℝ) - S.card ≤ g * n) (s : ℕ) :
    P.notYet ((n : ℝ) - g * μ ^ K * n) (K + s) S ≤ 2 ^ K * (n : ℝ) ^ (-(δ / 2) * s) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlam0 : 0 ≤ lam := le_trans (mul_nonneg ha (Real.rpow_nonneg hg.le _)) hlam
  have hμ0 : 0 < μ := lt_of_le_of_lt hlam0 hlamμ
  have hy := notYet_phase_npow P (fun j => g * μ ^ j * n) K hδ hn h2 ?_ S (by simpa using hS) s
  · simpa using hy
  intro j hj T hT
  have hμj : μ ^ j ≤ 1 := pow_le_one₀ hμ0.le hμ1
  have hμK : μ ^ K ≤ μ ^ j := pow_le_pow_of_le_one hμ0.le hμ1 hj.le
  have hμK1 : μ ^ K ≤ μ ^ (j + 1) := pow_le_pow_of_le_one hμ0.le hμ1 hj
  have hμjpos : 0 < μ ^ j := pow_pos hμ0 j
  have hu0 : 0 ≤ (n : ℝ) - T.card := by have := card_cast_le T; linarith
  have hTg : (n : ℝ) - T.card ≤ g * n := by
    have : g * μ ^ j * n ≤ g * n := by
      have := mul_le_mul_of_nonneg_left hμj hg.le
      nlinarith
    linarith
  have hs : (n : ℝ) ^ (1 - α) ≤ (n : ℝ) - T.card →
      a * (((n : ℝ) - T.card) / n) ^ (ℓ - 1) ≤ lam := by
    intro _
    have hfrac : ((n : ℝ) - T.card) / n ≤ g := by rw [div_le_iff₀ hn0]; exact hTg
    have := Real.rpow_le_rpow (div_nonneg hu0 hn0.le) hfrac (by linarith : (0 : ℝ) ≤ ℓ - 1)
    exact le_trans (mul_le_mul_of_nonneg_left this ha) hlam
  have hz0 : 0 < g * μ ^ (j + 1) * n := by positivity
  have hzgap : g * μ ^ j * n * (μ - lam) ≤ g * μ ^ (j + 1) * n - ((n : ℝ) - T.card) * lam := by
    have := mul_le_mul_of_nonneg_right hT hlam0
    rw [pow_succ]
    nlinarith
  have hgap0 : 0 < g * μ ^ j * n * (μ - lam) := by
    have : 0 < μ - lam := by linarith
    positivity
  have hz : ((n : ℝ) - T.card) * lam < g * μ ^ (j + 1) * n := by linarith
  have hround := round_fail_le P hc hDES hFF hn T hTg hs hz hz0
  have hgapK : g * μ ^ K * (μ - lam) * n ≤ g * μ ^ (j + 1) * n - ((n : ℝ) - T.card) * lam := by
    have : g * μ ^ K * (μ - lam) * n ≤ g * μ ^ j * n * (μ - lam) := by
      have h1 : 0 ≤ μ - lam := by linarith
      have := mul_le_mul_of_nonneg_left hμK hg.le
      have := mul_le_mul_of_nonneg_right this (mul_nonneg h1 hn0.le)
      nlinarith
    linarith
  have hK0 : 0 < g * μ ^ K * (μ - lam) * n := by
    have : 0 < μ - lam := by linarith
    have := pow_pos hμ0 K
    positivity
  have ht1 : (1 + c) * n / (g * μ ^ (j + 1) * n - ((n : ℝ) - T.card) * lam) ^ 2 ≤
      (1 + c) * n / (g * μ ^ K * (μ - lam) * n) ^ 2 := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_left₀ hK0.le hgapK 2
  have ht2 : (n : ℝ) ^ (1 - α) * (n : ℝ) ^ (-τ) / (g * μ ^ (j + 1) * n) ≤
      (n : ℝ) ^ (1 - α) * (n : ℝ) ^ (-τ) / (g * μ ^ K * n) := by
    apply div_le_div_of_nonneg_left
      (mul_nonneg (npow_pos hn _).le (npow_pos hn _).le) (by have := pow_pos hμ0 K; positivity)
    have := mul_le_mul_of_nonneg_left hμK1 hg.le
    nlinarith
  linarith

/-- The closed form of the double exponential targets. -/
noncomputable def epsSeq (ℓ κ D₀ : ℝ) (j : ℕ) : ℝ := Real.exp (-(κ + ℓ ^ j * D₀))

lemma epsSeq_pos (ℓ κ D₀ : ℝ) (j : ℕ) : 0 < epsSeq ℓ κ D₀ j := Real.exp_pos _

lemma epsSeq_anti {ℓ κ D₀ : ℝ} (hℓ : 1 ≤ ℓ) (hD₀ : 0 ≤ D₀) {j k : ℕ} (hjk : j ≤ k) :
    epsSeq ℓ κ D₀ k ≤ epsSeq ℓ κ D₀ j := by
  unfold epsSeq
  apply Real.exp_le_exp.mpr
  have := pow_le_pow_right₀ hℓ hjk
  nlinarith

/-- `ε_{j+1} = 2 a₁ ε_j^ℓ`. -/
lemma epsSeq_succ {ℓ κ D₀ a₁ : ℝ} (ha₁ : 0 < a₁) (hκ : Real.log (2 * a₁) = κ * (ℓ - 1))
    (j : ℕ) : epsSeq ℓ κ D₀ (j + 1) = 2 * a₁ * epsSeq ℓ κ D₀ j ^ ℓ := by
  unfold epsSeq
  rw [← Real.exp_mul, ← Real.exp_log (by positivity : (0 : ℝ) < 2 * a₁), hκ, ← Real.exp_add,
    pow_succ]
  congr 1
  ring

/-- Stage 2: double exponential targets `ε_j n`, `J` phases. -/
lemma stage_double (P : RumorProcess n) {ℓ a c g α τ a₁ κ D₀ δ : ℝ} (J : ℕ) (hℓ : 1 < ℓ)
    (ha₁ : a ≤ a₁) (ha₁0 : 0 < a₁) (hc : 0 ≤ c)
    (hκ : Real.log (2 * a₁) = κ * (ℓ - 1)) (hD₀ : 0 ≤ D₀) (hε0 : epsSeq ℓ κ D₀ 0 ≤ g)
    (hδ : 0 < δ) (hn : 1 ≤ n) (h2 : 2 ≤ (n : ℝ) ^ (δ / 2))
    (hq : (1 + c) * n / (epsSeq ℓ κ D₀ J * n / 2) ^ 2 +
        (n : ℝ) ^ (1 - α) * (n : ℝ) ^ (-τ) / (epsSeq ℓ κ D₀ J * n) ≤ (n : ℝ) ^ (-(2 * δ)))
    (hDES : P.UpperDoubleShrinking ℓ a c g α) (hFF : P.FastFinishing α τ)
    (S : Finset (Fin n)) (hS : (n : ℝ) - S.card ≤ epsSeq ℓ κ D₀ 0 * n) (s : ℕ) :
    P.notYet ((n : ℝ) - epsSeq ℓ κ D₀ J * n) (J + s) S ≤ 2 ^ J * (n : ℝ) ^ (-(δ / 2) * s) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set ε := epsSeq ℓ κ D₀ with hεdef
  refine notYet_phase_npow P (fun j => ε j * n) J hδ hn h2 ?_ S hS s
  intro j hj T hT
  have hεj := epsSeq_pos ℓ κ D₀ j
  have hu0 : 0 ≤ (n : ℝ) - T.card := by have := card_cast_le T; linarith
  have hεjg : ε j ≤ g := le_trans (epsSeq_anti hℓ.le hD₀ (Nat.zero_le j)) hε0
  have hTg : (n : ℝ) - T.card ≤ g * n := by
    have := mul_le_mul_of_nonneg_right hεjg hn0.le
    linarith
  have hfrac : ((n : ℝ) - T.card) / n ≤ ε j := by rw [div_le_iff₀ hn0]; exact hT
  have hs : (n : ℝ) ^ (1 - α) ≤ (n : ℝ) - T.card →
      a * (((n : ℝ) - T.card) / n) ^ (ℓ - 1) ≤ a₁ * ε j ^ (ℓ - 1) := by
    intro _
    have := Real.rpow_le_rpow (div_nonneg hu0 hn0.le) hfrac (by linarith : (0 : ℝ) ≤ ℓ - 1)
    exact mul_le_mul ha₁ this (Real.rpow_nonneg (div_nonneg hu0 hn0.le) _) ha₁0.le
  have hpow : ε j * ε j ^ (ℓ - 1) = ε j ^ ℓ := by
    rw [← Real.rpow_one_add' hεj.le (by linarith)]
    congr 1
    ring
  have hsucc : ε (j + 1) = 2 * a₁ * ε j ^ ℓ := epsSeq_succ ha₁0 hκ j
  have hus : ((n : ℝ) - T.card) * (a₁ * ε j ^ (ℓ - 1)) ≤ ε (j + 1) * n / 2 := by
    have hnn : 0 ≤ a₁ * ε j ^ (ℓ - 1) := mul_nonneg ha₁0.le (Real.rpow_nonneg hεj.le _)
    have := mul_le_mul_of_nonneg_right hT hnn
    rw [hsucc]
    calc ((n : ℝ) - T.card) * (a₁ * ε j ^ (ℓ - 1)) ≤ ε j * n * (a₁ * ε j ^ (ℓ - 1)) := this
      _ = a₁ * (ε j * ε j ^ (ℓ - 1)) * n := by ring
      _ = 2 * a₁ * ε j ^ ℓ * n / 2 := by rw [hpow]; ring
  have hεJ : ε J ≤ ε (j + 1) := epsSeq_anti hℓ.le hD₀ hj
  have hεJpos := epsSeq_pos ℓ κ D₀ J
  have hz0 : 0 < ε (j + 1) * n := mul_pos (epsSeq_pos ℓ κ D₀ _) hn0
  have hz : ((n : ℝ) - T.card) * (a₁ * ε j ^ (ℓ - 1)) < ε (j + 1) * n := by linarith
  have hround := round_fail_le P hc hDES hFF hn T hTg hs hz hz0
  have hgap : ε J * n / 2 ≤ ε (j + 1) * n - ((n : ℝ) - T.card) * (a₁ * ε j ^ (ℓ - 1)) := by
    have := mul_le_mul_of_nonneg_right hεJ hn0.le
    linarith
  have ht1 : (1 + c) * n / (ε (j + 1) * n - ((n : ℝ) - T.card) * (a₁ * ε j ^ (ℓ - 1))) ^ 2 ≤
      (1 + c) * n / (ε J * n / 2) ^ 2 := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_left₀ (by positivity) hgap 2
  have ht2 : (n : ℝ) ^ (1 - α) * (n : ℝ) ^ (-τ) / (ε (j + 1) * n) ≤
      (n : ℝ) ^ (1 - α) * (n : ℝ) ^ (-τ) / (ε J * n) :=
    div_le_div_of_nonneg_left (mul_nonneg (npow_pos hn _).le (npow_pos hn _).le)
      (by positivity) (mul_le_mul_of_nonneg_right hεJ hn0.le)
  linarith

/-- Stage 3: finishing below `U` uninformed nodes, `U ≤ g n`, when the stay probability is at
most `θ` both under Definition 13 (where `a (u/n)^{ℓ-1} ≤ θ`) and under fast finishing. -/
lemma stage_finish (P : RumorProcess n) {ℓ a c g α τ U θ : ℝ}
    (hU : U ≤ g * n) (hθ : 0 ≤ θ)
    (hθd : ∀ u : ℝ, 0 ≤ u → u ≤ U → a * (u / n) ^ (ℓ - 1) ≤ θ)
    (hθf : (n : ℝ) ^ (-τ) ≤ θ)
    (hDES : P.UpperDoubleShrinking ℓ a c g α) (hFF : P.FastFinishing α τ)
    (S : Finset (Fin n)) (hS : (n : ℝ) - S.card ≤ U) (t : ℕ) :
    P.notYet n t S ≤ θ ^ t * n := by
  have hfin := notYet_finish_le P hθ (U := U) ?_ S hS t
  · have hu : (n : ℝ) - S.card ≤ n := by have : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _; linarith
    exact le_trans hfin (mul_le_mul_of_nonneg_left hu (pow_nonneg hθ t))
  intro T hT x hx
  have hu0 : 0 ≤ (n : ℝ) - T.card := by have := card_cast_le T; linarith
  by_cases h : (n : ℝ) ^ (1 - α) ≤ (n : ℝ) - T.card
  · exact le_trans ((hDES T h (le_trans hT hU)).1 x hx) (hθd _ hu0 hT)
  · rw [not_le] at h
    exact le_trans (hFF T h.le x hx) hθf

end Epidemics.Revisited
