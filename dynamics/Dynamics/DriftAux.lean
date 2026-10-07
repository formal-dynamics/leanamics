import Dynamics.DriftSeq

/-!
# Helpers for the drift theorems

Pointwise facts about a nonnegative potential `Ψ` and its survival indicator `1_{Ψ > 0}`, and the
two inductions on `𝔼[Ψ_t]` behind `Dynamics.Kernel.drift_absorption_seq` and
`Dynamics.Kernel.multiplicative_drift_seq` (Lemmas 2.2 and 2.4 of Berenbrink, Giakkoupis,
Kermarrec, Mallmann-Trenn, ICALP 2016).

The paper handles the drift `c / Ψ` with Jensen's inequality,
`𝔼[1_{Ψ > 0} / Ψ] ≥ P(Ψ > 0)² / 𝔼[Ψ]`. We linearize instead: `1 / y ≥ 2 λ - λ² y` for `y > 0`
and every `λ` (from `(1 - λ y)² ≥ 0`), so the drift hypothesis gives the pointwise bound
`K Ψ ≤ (1 + c λ²) Ψ - 2 c λ 1_{Ψ > 0}` (`apply_le_lin`), which only needs monotonicity and
linearity of `iterateSeq`. Jensen's bound is the optimum `λ = P(Ψ > 0) / 𝔼[Ψ]`; the proof uses
the fixed `λ = q / Ψ(x₀)`, with `q` the survival probability at the final time.
-/

namespace Dynamics.Kernel
open Finset
variable {α : Type*}

/-- The indicator of `Ψ = 0` is one minus the indicator of `Ψ > 0` when `Ψ ≥ 0`. -/
lemma ind_eq_zero_eq (Ψ : α → ℝ) (hΨ : ∀ x, 0 ≤ Ψ x) :
    (fun x => if Ψ x = 0 then (1 : ℝ) else 0) = fun x => 1 - (if 0 < Ψ x then 1 else 0) := by
  funext x
  rcases (hΨ x).eq_or_lt with h | h
  · simp [← h]
  · simp [h, h.ne']

/-- **Markov's inequality** for the survival indicator: `1_{Ψ > 0} ≤ Ψ / Ψmin` when every
positive value of `Ψ ≥ 0` is at least `Ψmin > 0`. -/
lemma ind_pos_le_div (Ψ : α → ℝ) {Ψmin : ℝ} (hΨ : ∀ x, 0 ≤ Ψ x) (hmin : 0 < Ψmin)
    (hgap : ∀ x, 0 < Ψ x → Ψmin ≤ Ψ x) (x : α) :
    (if 0 < Ψ x then (1 : ℝ) else 0) ≤ Ψmin⁻¹ * Ψ x := by
  split_ifs with hx
  · rw [← div_eq_inv_mul, one_le_div hmin]
    exact hgap x hx
  · exact mul_nonneg (inv_nonneg.mpr hmin.le) (hΨ x)

variable [Fintype α]

/-- On a finite type the positive values of a nonnegative `Ψ` are bounded below by some
`m > 0`, i.e. `m · 1_{Ψ > 0} ≤ Ψ`. -/
lemma exists_pos_mul_ind_le (Ψ : α → ℝ) (hΨ : ∀ x, 0 ≤ Ψ x) :
    ∃ m : ℝ, 0 < m ∧ ∀ x, m * (if 0 < Ψ x then 1 else 0) ≤ Ψ x := by
  by_cases hne : (univ.filter fun x => 0 < Ψ x).Nonempty
  · obtain ⟨y, hy, hmin⟩ := exists_min_image _ Ψ hne
    refine ⟨Ψ y, (mem_filter.mp hy).2, fun x => ?_⟩
    split_ifs with hx
    · simpa using hmin x (mem_filter.mpr ⟨mem_univ x, hx⟩)
    · simpa using hΨ x
  · refine ⟨1, one_pos, fun x => ?_⟩
    split_ifs with hx
    · exact absurd ⟨x, mem_filter.mpr ⟨mem_univ x, hx⟩⟩ hne
    · simpa using hΨ x

/-- A kernel that keeps a nonnegative `Ψ` at zero from the zeros of `Ψ` does not increase the
indicator of `Ψ > 0`. -/
lemma apply_ind_pos_le (K : Dynamics.Kernel α) (Ψ : α → ℝ) (hΨ : ∀ x, 0 ≤ Ψ x)
    (habs : ∀ x, Ψ x = 0 → K.apply Ψ x = 0) (x : α) :
    K.apply (fun y => if 0 < Ψ y then 1 else 0) x ≤ if 0 < Ψ x then 1 else 0 := by
  split_ifs with hx
  · calc K.apply (fun y => if 0 < Ψ y then 1 else 0) x ≤ (K x).expect fun _ => 1 :=
          (K x).expect_mono fun y => by split_ifs <;> norm_num
      _ = 1 := (K x).expect_const 1
  · obtain ⟨m, hm, hle⟩ := exists_pos_mul_ind_le Ψ hΨ
    have h1 : m * K.apply (fun y => if 0 < Ψ y then 1 else 0) x ≤ K.apply Ψ x := by
      have h := (K x).expect_mono hle
      rwa [Distribution.expect_mul] at h
    rw [habs x (le_antisymm (not_lt.mp hx) (hΨ x))] at h1
    nlinarith

/-- **Survival is antitone** up to time `T` when the zeros of `Ψ` are absorbing:
`P_T(Ψ > 0) ≤ P_t(Ψ > 0)` for `t ≤ T`. -/
lemma iterateSeq_ind_pos_antitone (K : ℕ → Dynamics.Kernel α) (Ψ : α → ℝ)
    (hΨ : ∀ x, 0 ≤ Ψ x) (T : ℕ) (habs : ∀ t < T, ∀ x, Ψ x = 0 → (K t).apply Ψ x = 0)
    (x₀ : α) {t : ℕ} (ht : t ≤ T) :
    iterateSeq K T (fun x => if 0 < Ψ x then 1 else 0) x₀ ≤
      iterateSeq K t (fun x => if 0 < Ψ x then 1 else 0) x₀ := by
  induction T, ht using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih =>
    rw [iterateSeq_succ]
    calc _ ≤ iterateSeq K n (fun x => if 0 < Ψ x then 1 else 0) x₀ :=
          iterateSeq_mono K n (apply_ind_pos_le (K n) Ψ hΨ (habs n (Nat.lt_succ_self n))) x₀
      _ ≤ _ := ih fun s hs => habs s (by omega)

/-- **Linearized drift.** The drift `c / Ψ`, bounded with `1 / Ψ ≥ 2 λ - λ² Ψ`: pointwise,
`K Ψ ≤ (1 + c λ²) Ψ - 2 c λ 1_{Ψ > 0}`, for every `λ`. -/
lemma apply_le_lin (K : Dynamics.Kernel α) (Ψ : α → ℝ) (c lam : ℝ) (hc : 0 ≤ c)
    (hΨ : ∀ x, 0 ≤ Ψ x) (hdrift : ∀ x, 0 < Ψ x → K.apply Ψ x ≤ Ψ x - c / Ψ x)
    (habs : ∀ x, Ψ x = 0 → K.apply Ψ x = 0) (x : α) :
    K.apply Ψ x ≤
      (1 + c * lam ^ 2) * Ψ x + -(2 * c * lam) * (if 0 < Ψ x then 1 else 0) := by
  split_ifs with hx
  · have hinv : 2 * lam - lam ^ 2 * Ψ x ≤ 1 / Ψ x := by
      rw [le_div_iff₀ hx]
      nlinarith [sq_nonneg (1 - lam * Ψ x)]
    have h1 := hdrift x hx
    have h2 := mul_le_mul_of_nonneg_left hinv hc
    rw [mul_one_div] at h2
    linarith
  · have h0 := le_antisymm (not_lt.mp hx) (hΨ x)
    rw [habs x h0, h0]
    simp

/-- **Iterated linearized drift.** Let `lam, q ≥ 0` with `lam² Ψ(x₀) = lam q`, and let the
survival probability stay at least `q` before time `T`. Then for `t ≤ T`,
`𝔼[Ψ_t] ≤ Ψ(x₀) - lam q ∑_{s < t} c s`: each step lowers `𝔼[Ψ]` by at least `c_t lam q`. -/
lemma iterateSeq_le_sub_of_drift (K : ℕ → Dynamics.Kernel α) (Ψ : α → ℝ) (c : ℕ → ℝ)
    (T : ℕ) (hΨ : ∀ x, 0 ≤ Ψ x) (hc : ∀ t < T, 0 ≤ c t)
    (hdrift : ∀ t < T, ∀ x, 0 < Ψ x → (K t).apply Ψ x ≤ Ψ x - c t / Ψ x)
    (habs : ∀ t < T, ∀ x, Ψ x = 0 → (K t).apply Ψ x = 0)
    (x₀ : α) {lam q : ℝ} (hlam : 0 ≤ lam) (hq : 0 ≤ q) (hid : lam ^ 2 * Ψ x₀ = lam * q)
    (hsurv : ∀ t < T, q ≤ iterateSeq K t (fun x => if 0 < Ψ x then 1 else 0) x₀) :
    ∀ t ≤ T, iterateSeq K t Ψ x₀ ≤ Ψ x₀ - lam * q * ∑ s ∈ range t, c s := by
  intro t ht
  induction t with
  | zero => simp
  | succ t ih =>
    have ht' : t < T := ht
    have he := ih ht'.le
    have hS : 0 ≤ ∑ s ∈ range t, c s :=
      sum_nonneg fun s hs => hc s ((mem_range.mp hs).trans ht')
    have hct := hc t ht'
    have hp := hsurv t ht'
    have hstep : iterateSeq K (t + 1) Ψ x₀ ≤ (1 + c t * lam ^ 2) * iterateSeq K t Ψ x₀ +
        -(2 * c t * lam) * iterateSeq K t (fun x => if 0 < Ψ x then 1 else 0) x₀ := by
      rw [iterateSeq_succ, ← iterateSeq_lin]
      exact iterateSeq_mono K t
        (apply_le_lin (K t) Ψ (c t) lam hct hΨ (hdrift t ht') (habs t ht')) x₀
    have h1 : c t * lam ^ 2 * iterateSeq K t Ψ x₀ ≤ c t * lam ^ 2 * Ψ x₀ :=
      mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg (mul_nonneg hlam hq) hS])
        (by positivity)
    have h2 : c t * lam * q ≤
        c t * lam * iterateSeq K t (fun x => if 0 < Ψ x then 1 else 0) x₀ :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg hct hlam)
    have h3 : c t * lam ^ 2 * Ψ x₀ = c t * lam * q := by
      rw [mul_assoc, hid, ← mul_assoc]
    rw [sum_range_succ]
    linarith

/-- **Iterated multiplicative drift.** If `K t Ψ ≤ (1 - δ t) Ψ` with `1 - δ t ≥ 0` for every
step `t < T`, then `𝔼[Ψ_t] ≤ ∏_{s < t} (1 - δ s) Ψ(x₀)` for `t ≤ T`. -/
lemma iterateSeq_le_prod_of_drift (K : ℕ → Dynamics.Kernel α) (Ψ : α → ℝ) (δ : ℕ → ℝ)
    (T : ℕ) (hδ : ∀ t < T, 0 ≤ 1 - δ t)
    (hdrift : ∀ t < T, ∀ x, (K t).apply Ψ x ≤ (1 - δ t) * Ψ x) (x₀ : α) :
    ∀ t ≤ T, iterateSeq K t Ψ x₀ ≤ (∏ s ∈ range t, (1 - δ s)) * Ψ x₀ := by
  intro t ht
  induction t with
  | zero => simp
  | succ t ih =>
    have ht' : t < T := ht
    rw [iterateSeq_succ]
    calc iterateSeq K t ((K t).apply Ψ) x₀
        ≤ iterateSeq K t (fun x => (1 - δ t) * Ψ x) x₀ :=
          iterateSeq_mono K t (hdrift t ht') x₀
      _ = (1 - δ t) * iterateSeq K t Ψ x₀ := by rw [iterateSeq_mul]
      _ ≤ (1 - δ t) * ((∏ s ∈ range t, (1 - δ s)) * Ψ x₀) :=
          mul_le_mul_of_nonneg_left (ih ht'.le) (hδ t ht')
      _ = (∏ s ∈ range (t + 1), (1 - δ s)) * Ψ x₀ := by rw [prod_range_succ]; ring

end Dynamics.Kernel
