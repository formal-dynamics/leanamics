import Dynamics.DriftHittingStop

/-!
# Helpers for the hitting-time bound (Claim 2.9 of Doerr et al., SPAA 2011)

The proof of `Dynamics.Kernel.drift_hitting` (the paper omits it) applies the geometric drift
bound `one_sub_hitProb_le_of_drift` to a potential `V = g ∘ X` off the target (`V = 0` on it):

* `g` is antitone with values in `(0, 1]`. On the low levels `x < x₀`, where one step only
  guarantees `X' ≥ x + 1` with probability `p = min c₃ (1 - e^{-c₂})`, it is
  `g x = 1 - η (θ^x - 1)` with `θ = p⁻¹`: this is the shape that makes
  `p g(x + 1) + (1 - p) ≤ ρ g x` hold with a single `ρ < 1`, however small `p` is. From the level
  `x₀` on, where the growth `X' ≥ c₁ x` fails only with probability `e^{-c₂ x}`, it is
  `g x = (1/2) e^{-(c₂/2)(x - x₀)}` (`exists_potential`).
* One step of the chain decreases `V` by the factor `ρ` off the target (`apply_potential_le`),
  by the elementary bound `expect_le_of_prob` on a two-valued majorant.
* `V ≤ 1` and `V ≥ (1/2) e^{-(c₂/2) c₄ log q} = (1/2) q^{-c₂ c₄/2}` off the target, so the
  non-hitting probability after `t` steps is at most `2 ρ^t q^{c₂ c₄/2}`, which is below
  `q^{-c₆}` after `O(log q)` steps (`two_mul_pow_mul_exp_le`).
-/

namespace Dynamics

namespace Distribution
variable {α : Type*} [Fintype α]

/-- Probabilities are monotone in the event. -/
lemma prob_mono (μ : Distribution α) {E F : α → Prop} (h : ∀ b, E b → F b) :
    μ.prob E ≤ μ.prob F := by
  classical
  unfold prob
  refine μ.expect_mono fun b => ?_
  by_cases hE : E b
  · simp [hE, h b hE]
  · by_cases hF : F b <;> simp [hE, hF]

/-- If `f ≤ M` everywhere and `f ≤ m ≤ M` on an event of probability at least `s`, then
`𝔼 f ≤ M - (M - m) s`. -/
lemma expect_le_of_prob (μ : Distribution α) {f : α → ℝ} {E : α → Prop} {m M s : ℝ}
    (hf : ∀ b, f b ≤ M) (hE : ∀ b, E b → f b ≤ m) (hmM : m ≤ M) (hs : s ≤ μ.prob E) :
    μ.expect f ≤ M - (M - m) * s := by
  classical
  have h (b : α) : f b ≤ M - (M - m) * (if E b then 1 else 0) := by
    by_cases hb : E b
    · rw [if_pos hb]
      linarith [hE b hb]
    · rw [if_neg hb]
      linarith [hf b]
  calc μ.expect f ≤ μ.expect (fun b => M - (M - m) * (if E b then 1 else 0)) := μ.expect_mono h
    _ = M - (M - m) * μ.prob E := by
        rw [expect_sub, expect_const, expect_mul]
        rfl
    _ ≤ M - (M - m) * s := by nlinarith [sub_nonneg.mpr hmM]

end Distribution

namespace Kernel
open Real

/-- `e^{-u} ≤ 1/4` for `u ≥ 3` (from `e^u ≥ 1 + u`). -/
lemma exp_neg_le_quarter {u : ℝ} (hu : 3 ≤ u) : exp (-u) ≤ 1 / 4 := by
  rw [exp_neg, inv_le_comm₀ (exp_pos u) (by norm_num)]
  norm_num
  linarith [add_one_le_exp u]

/-- A threshold level `x₀ ≥ 1` with `θ^x₀ ≥ 2`, `e^{-β (c₁ - 1) x₀} ≤ 1/4` and
`e^{-2 β x₀} ≤ 1/4`. -/
lemma exists_threshold {θ β c₁ : ℝ} (hθ : 1 < θ) (hβ : 0 < β) (hc₁ : 1 < c₁) :
    ∃ x₀ : ℕ, 1 ≤ x₀ ∧ 2 ≤ θ ^ x₀ ∧ exp (-(β * (c₁ - 1) * x₀)) ≤ 1 / 4 ∧
      exp (-(2 * β * x₀)) ≤ 1 / 4 := by
  have hβc : 0 < β * (c₁ - 1) := mul_pos hβ (by linarith)
  obtain ⟨N₁, hN₁⟩ := pow_unbounded_of_one_lt (2 : ℝ) hθ
  obtain ⟨N₂, hN₂⟩ := exists_nat_ge (3 / (β * (c₁ - 1)) + 3 / (2 * β))
  have hθx₀ : 2 ≤ θ ^ max N₁ N₂ := hN₁.le.trans (pow_le_pow_right₀ hθ.le (le_max_left _ _))
  have hN : 3 / (β * (c₁ - 1)) + 3 / (2 * β) ≤ ((max N₁ N₂ : ℕ) : ℝ) :=
    hN₂.trans (Nat.cast_le.mpr (le_max_right _ _))
  generalize max N₁ N₂ = x₀ at hθx₀ hN
  have h1 : 0 ≤ 3 / (β * (c₁ - 1)) := by positivity
  have h2 : 0 ≤ 3 / (2 * β) := by positivity
  refine ⟨x₀, ?_, hθx₀, exp_neg_le_quarter ?_, exp_neg_le_quarter ?_⟩
  · rcases Nat.eq_zero_or_pos x₀ with h | h
    · rw [h, pow_zero] at hθx₀
      norm_num at hθx₀
    · exact h
  · have h3 : 3 / (β * (c₁ - 1)) ≤ x₀ := by linarith
    rw [div_le_iff₀ hβc] at h3
    linarith
  · have h3 : 3 / (2 * β) ≤ x₀ := by linarith
    rw [div_le_iff₀ (by positivity)] at h3
    linarith

/-- Low levels: with `θ = p⁻¹`, `T = θ^x ≥ 1` and `ρ = 1 - (1 - p) η / 2`, the potential
`g x = 1 - η (θ^x - 1)` satisfies `p g(x + 1) + (1 - p) ≤ ρ g x`. The slack is
`(1 - p) η (1 + η (T - 1)) / 2`. -/
lemma low_drift_ineq {p η θ T : ℝ} (hp1 : p < 1) (hη : 0 ≤ η) (hpθ : p * θ = 1) (hT : 1 ≤ T) :
    p * (1 - η * (T * θ - 1)) + (1 - p) ≤ (1 - (1 - p) * η / 2) * (1 - η * (T - 1)) := by
  have h3 : p * (η * (T * θ)) = η * T := by
    rw [show p * (η * (T * θ)) = η * T * (p * θ) by ring, hpθ, mul_one]
  have h4 : 0 ≤ (1 - p) * η * (η * (T - 1)) :=
    mul_nonneg (mul_nonneg (by linarith) hη) (mul_nonneg hη (by linarith))
  have h5 : 0 ≤ (1 - p) * η := mul_nonneg (by linarith) hη
  nlinarith

/-- High levels: for `x₀ ≤ x` and `y ≥ c₁ x`, the growth step lowers
`(1/2) e^{-β (· - x₀)}` by `e^{-β (c₁ - 1) x₀} ≤ 1/4`, and the failure probability `e^{-2 β x}`
is at most `e^{-2 β x₀} ≤ 1/4` times `e^{-β (x - x₀)}`; so the expected potential is at most
`3/8 e^{-β (x - x₀)} ≤ ρ g x` once `ρ ≥ 3/4`. -/
lemma high_drift_ineq {β c₁ ρ x₀ x y : ℝ} (hβ : 0 ≤ β) (hc₁ : 1 ≤ c₁) (hρ : 3 / 4 ≤ ρ)
    (hx : x₀ ≤ x) (hy : c₁ * x ≤ y)
    (hq1 : exp (-(β * (c₁ - 1) * x₀)) ≤ 1 / 4) (hq2 : exp (-(2 * β * x₀)) ≤ 1 / 4) :
    1 / 2 * exp (-(β * (y - x₀))) + exp (-(2 * β * x)) ≤
      ρ * (1 / 2 * exp (-(β * (x - x₀)))) := by
  have hE := exp_pos (-(β * (x - x₀)))
  have h1 : exp (-(β * (y - x₀))) ≤ exp (-(β * (x - x₀))) * exp (-(β * (c₁ - 1) * x₀)) := by
    rw [← exp_add, exp_le_exp]
    nlinarith [mul_nonneg hβ (sub_nonneg.mpr hy),
      mul_nonneg (mul_nonneg hβ (sub_nonneg.mpr hc₁)) (sub_nonneg.mpr hx)]
  have h2 : exp (-(2 * β * x)) ≤ exp (-(β * (x - x₀))) * exp (-(2 * β * x₀)) := by
    rw [← exp_add, exp_le_exp]
    nlinarith [mul_nonneg hβ (sub_nonneg.mpr hx)]
  have h3 := mul_le_mul_of_nonneg_left hq1 hE.le
  have h4 := mul_le_mul_of_nonneg_left hq2 hE.le
  have h5 := mul_le_mul_of_nonneg_right hρ hE.le
  nlinarith

/-- **The potential.** Let `c₁ > 1`, `c₂ > 0`, `0 < p < 1`. There are `ρ ∈ (0, 1)` and an
antitone `g : ℕ → ℝ` with `(1/2) e^{-(c₂/2) x} ≤ g x ≤ 1`, such that at every level `x` one of
two drift inequalities holds: the low-level one `p g(x + 1) + (1 - p) ≤ ρ g x` (a step up by one
with probability `≥ p`, anything otherwise), or, for `x ≥ 1`, the high-level one
`g y + e^{-c₂ x} ≤ ρ g x` for every `y ≥ c₁ x` (growth by `c₁` except with probability
`e^{-c₂ x}`). -/
lemma exists_potential {c₁ c₂ p : ℝ} (hc₁ : 1 < c₁) (hc₂ : 0 < c₂) (hp : 0 < p) (hp1 : p < 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∃ g : ℕ → ℝ, Antitone g ∧ (∀ x, g x ≤ 1) ∧
      (∀ x : ℕ, 1 / 2 * exp (-(c₂ / 2 * x)) ≤ g x) ∧
      ∀ x : ℕ, p * g (x + 1) + (1 - p) ≤ ρ * g x ∨
        (1 ≤ x ∧ ∀ y : ℕ, c₁ * x ≤ y → g y + exp (-(c₂ * x)) ≤ ρ * g x) := by
  obtain ⟨β, hβ⟩ : ∃ β, c₂ / 2 = β := ⟨_, rfl⟩
  have hβ0 : 0 < β := by rw [← hβ]; positivity
  have hc₂β : c₂ = 2 * β := by rw [← hβ]; ring
  rw [hβ, hc₂β]
  obtain ⟨θ, hθ⟩ : ∃ θ, p⁻¹ = θ := ⟨_, rfl⟩
  have hθ1 : 1 < θ := hθ ▸ (one_lt_inv₀ hp).mpr hp1
  have hpθ : p * θ = 1 := hθ ▸ mul_inv_cancel₀ hp.ne'
  obtain ⟨x₀, hx₀1, hθx₀, hq1, hq2⟩ := exists_threshold hθ1 hβ0 hc₁
  -- the slope `η` of the low part, with `g x₀ = 1/2`
  obtain ⟨η, hη⟩ : ∃ η, 1 / (2 * (θ ^ x₀ - 1)) = η := ⟨_, rfl⟩
  have hθ1' : 0 < θ ^ x₀ - 1 := by linarith
  have hη0 : 0 < η := by rw [← hη]; positivity
  have hηx₀ : η * (θ ^ x₀ - 1) = 1 / 2 := by
    rw [← hη]
    field_simp
  have hη2 : η ≤ 1 / 2 := by nlinarith
  have hρ34 : 3 / 4 ≤ 1 - (1 - p) * η / 2 := by nlinarith [mul_nonneg hp.le hη0.le]
  refine ⟨1 - (1 - p) * η / 2, by linarith, by nlinarith [mul_pos (sub_pos.mpr hp1) hη0], ?_⟩
  -- the potential
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ, ∀ x, g x =
      if x ≤ x₀ then 1 - η * (θ ^ x - 1) else 1 / 2 * exp (-(β * ((x : ℝ) - x₀))) :=
    ⟨_, fun _ => rfl⟩
  have g_low (x : ℕ) (hx : x ≤ x₀) : g x = 1 - η * (θ ^ x - 1) := by rw [hg, if_pos hx]
  have g_high (x : ℕ) (hx : x₀ ≤ x) : g x = 1 / 2 * exp (-(β * ((x : ℝ) - x₀))) := by
    rcases hx.lt_or_eq with h | h
    · rw [hg, if_neg (not_le.mpr h)]
    · subst h
      rw [g_low _ le_rfl, hηx₀, sub_self, mul_zero, neg_zero, exp_zero]
      norm_num
  have g_low_ge (x : ℕ) (hx : x ≤ x₀) : 1 / 2 ≤ g x := by
    rw [g_low x hx]
    have := pow_le_pow_right₀ hθ1.le hx
    nlinarith
  have g_high_le (x : ℕ) (hx : x₀ ≤ x) : g x ≤ 1 / 2 := by
    rw [g_high x hx]
    have hxx : (x₀ : ℝ) ≤ x := Nat.cast_le.mpr hx
    have : exp (-(β * ((x : ℝ) - x₀))) ≤ 1 := by
      rw [exp_le_one_iff, neg_nonpos]
      nlinarith
    linarith
  refine ⟨g, antitone_nat_of_succ_le fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_⟩
  · -- antitone
    rcases lt_or_ge x x₀ with hx | hx
    · rw [g_low (x + 1) hx, g_low x hx.le, pow_succ]
      have := one_le_pow₀ (n := x) hθ1.le
      have h : 0 ≤ η * (θ ^ x * (θ - 1)) :=
        mul_nonneg hη0.le (mul_nonneg (by linarith) (by linarith))
      nlinarith
    · rw [g_high (x + 1) (by omega), g_high x hx,
        mul_le_mul_iff_right₀ (by norm_num : (0 : ℝ) < 1 / 2), exp_le_exp]
      push_cast
      nlinarith
  · -- at most one
    rcases le_or_gt x x₀ with hx | hx
    · rw [g_low x hx]
      have := one_le_pow₀ (n := x) hθ1.le
      nlinarith
    · linarith [g_high_le x hx.le]
  · -- lower bound
    rcases le_or_gt x x₀ with hx | hx
    · have : exp (-(β * x)) ≤ 1 := by
        rw [exp_le_one_iff, neg_nonpos]
        positivity
      linarith [g_low_ge x hx]
    · rw [g_high x hx.le, mul_le_mul_iff_right₀ (by norm_num : (0 : ℝ) < 1 / 2), exp_le_exp]
      have : (0 : ℝ) ≤ x₀ := Nat.cast_nonneg _
      nlinarith
  · -- drift
    rcases lt_or_ge x x₀ with hx | hx
    · left
      rw [g_low (x + 1) hx, g_low x hx.le, pow_succ]
      exact low_drift_ineq hp1 hη0.le hpθ (one_le_pow₀ hθ1.le)
    · right
      refine ⟨hx₀1.trans hx, fun y hy => ?_⟩
      have hxx₀ : (x₀ : ℝ) ≤ x := Nat.cast_le.mpr hx
      have hxc : (x : ℝ) ≤ c₁ * x := by
        have : (0 : ℝ) ≤ x := Nat.cast_nonneg _
        nlinarith
      rw [g_high y (Nat.cast_le.mp (hxx₀.trans (hxc.trans hy))), g_high x hx]
      exact high_drift_ineq hβ0.le hc₁.le hρ34 hxx₀ hy hq1 hq2

variable {α : Type*} [Fintype α]

/-- **One step of the potential.** Let `V = g ∘ X` off the target `L ≤ X` and `V = 0` on it,
for a potential `g` as in `exists_potential`, and let the chain satisfy the hypotheses of
Claim 2.9 below the target `L ≤ q`. Then `𝔼[V(X_{t+1}) | X_t = a] ≤ ρ g(X a)` from every state
`a` below the target. At a low level the step goes up by one with probability at least
`p ≤ min c₃ (1 - e^{-c₂})` (by the escape hypothesis at `0`, by growth at `X a ≥ 1`); at a
high level growth fails with probability at most `e^{-c₂ X a}`. -/
lemma apply_potential_le (K : Dynamics.Kernel α) (X : α → ℕ) (q : ℕ) {c₁ c₂ c₃ p ρ L : ℝ}
    {g : ℕ → ℝ} (hc₁ : 1 < c₁) (hc₂ : 0 ≤ c₂) (hpc₃ : p ≤ c₃) (hpc₂ : p ≤ 1 - exp (-c₂))
    (hρ : ρ ≤ 1) (hg : Antitone g) (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1)
    (hdrift : ∀ x : ℕ, p * g (x + 1) + (1 - p) ≤ ρ * g x ∨
      (1 ≤ x ∧ ∀ y : ℕ, c₁ * x ≤ y → g y + exp (-(c₂ * x)) ≤ ρ * g x))
    (hLq : L ≤ q)
    (hgrow : ∀ a, (X a : ℝ) < L →
      1 - exp (-(c₂ * X a)) ≤ (K a).prob (fun b => min (c₁ * X a) q ≤ X b))
    (hzero : ∀ a, X a = 0 → c₃ ≤ (K a).prob (fun b => 1 ≤ X b))
    {a : α} (ha : (X a : ℝ) < L) :
    K.apply (fun b => if L ≤ X b then 0 else g (X b)) a ≤ ρ * g (X a) := by
  have hV1 (b : α) : (if L ≤ X b then 0 else g (X b)) ≤ 1 := by
    split_ifs
    · norm_num
    · exact hg1 _
  have hxq : (X a : ℝ) < q := ha.trans_le hLq
  show (K a).expect _ ≤ _
  rcases hdrift (X a) with hlow | ⟨hx1, hhigh⟩
  · -- low level: one step up with probability at least `p`
    have hE (b : α) (hb : X a + 1 ≤ X b) : (if L ≤ X b then 0 else g (X b)) ≤ g (X a + 1) := by
      split_ifs
      · exact hg0 _
      · exact hg hb
    have hs : p ≤ (K a).prob (fun b => X a + 1 ≤ X b) := by
      rcases Nat.eq_zero_or_pos (X a) with h0 | hpos
      · refine hpc₃.trans ((hzero a h0).trans ((K a).prob_mono fun b hb => ?_))
        omega
      · have hx1 : (1 : ℝ) ≤ X a := by exact_mod_cast hpos
        have hexp : exp (-(c₂ * X a)) ≤ exp (-c₂) := by
          rw [exp_le_exp]
          nlinarith
        refine (hpc₂.trans (by linarith)).trans ((hgrow a ha).trans ((K a).prob_mono ?_))
        intro b hb
        have hlt : (X a : ℝ) < X b := by
          rcases min_le_iff.mp hb with h | h
          · nlinarith
          · linarith
        exact_mod_cast hlt
    have := (K a).expect_le_of_prob hV1 hE (hg1 _) hs
    linarith
  · -- high level: growth by `c₁` except with probability `e^{-c₂ X a}`
    set e := exp (-(c₂ * X a)) with he
    have he0 : 0 ≤ e := (exp_pos _).le
    have hm0 : 0 ≤ ρ * g (X a) - e := by
      have := hhigh ⌈c₁ * X a⌉₊ (Nat.le_ceil _)
      linarith [hg0 ⌈c₁ * X a⌉₊]
    have hE (b : α) (hb : min (c₁ * X a) q ≤ X b) :
        (if L ≤ X b then 0 else g (X b)) ≤ ρ * g (X a) - e := by
      split_ifs with hL
      · exact hm0
      · have hbq : (X b : ℝ) < q := (not_le.mp hL).trans_le hLq
        rcases min_le_iff.mp hb with h | h
        · linarith [hhigh (X b) h]
        · linarith
    have hm1 : ρ * g (X a) - e ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hρ (hg0 (X a))
      linarith [hg1 (X a)]
    have := (K a).expect_le_of_prob hV1 hE hm1 (hgrow a ha)
    nlinarith [mul_nonneg hm0 he0]

/-- **The final estimate.** If `ρ ∈ (0, 1)`, `ℓ ≥ log 2`, `D ≥ 0` and
`t ≥ ((1 + b + c) / log (1/ρ) + D / log 2) ℓ - D`, then `2 ρ^t e^{b ℓ} ≤ e^{-c ℓ}`. With
`ℓ = log q` this is `2 ρ^t q^b ≤ q^{-c}`. -/
lemma two_mul_pow_mul_exp_le {ρ b c ℓ D : ℝ} {t : ℕ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hℓ : log 2 ≤ ℓ) (hD : 0 ≤ D) (ht : ((1 + b + c) / (-log ρ) + D / log 2) * ℓ - D ≤ t) :
    2 * ρ ^ t * exp (b * ℓ) ≤ exp (-(c * ℓ)) := by
  have hlam : 0 < -log ρ := neg_pos.mpr (log_neg hρ0 hρ1)
  have hl2 : 0 < log 2 := log_pos one_lt_two
  have h1 : D ≤ D / log 2 * ℓ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
    nlinarith
  rw [add_mul] at ht
  have h2 : (1 + b + c) / (-log ρ) * ℓ ≤ t := by linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ hlam] at h2
  calc 2 * ρ ^ t * exp (b * ℓ) = exp (log 2 + t * log ρ + b * ℓ) := by
        rw [exp_add, exp_add, exp_log two_pos, exp_nat_mul, exp_log hρ0]
    _ ≤ exp (-(c * ℓ)) := exp_le_exp.mpr (by nlinarith)

end Kernel
end Dynamics
