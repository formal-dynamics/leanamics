import Epidemics.KermackMcKendrickCalculus
import Epidemics.KermackMcKendrickDefs

/-! # Kurtz's law of large numbers for SIR: the ODE side (CRN-2, helpers)

For a solution `x(t) = (s t, i t, r t)` of the Kermack–McKendrick system on `[0, ∞)`, given only as
an integral curve of `sirField β γ` (no `IsSolution`: the initial point is any point of the
simplex):

* the simplex is invariant: `s, i, r ≥ 0` and `s + i + r = 1` on `[0, ∞)` (first integral
  `s exp((β/γ) r)` for `s`, integrating factor `i exp(-∫ (β s - γ))` for `i`, monotonicity for
  `r`), so `‖x(t)‖ ≤ 1` in the sup norm of `ℝ × ℝ × ℝ`;
* on the unit ball, `sirField β γ` is `(2β + γ)`-Lipschitz and bounded by `β + γ`;
* the Euler step error `‖x(t+h) - x(t) - h F(x(t))‖ ≤ (2β + γ)(β + γ) h²` (mean value inequality).
-/

namespace Epidemics.Kurtz

open Set Real KermackMcKendrick

variable {β γ : ℝ} {s i r : ℝ → ℝ}

/-! ### Components of an integral curve -/

section Curve

variable (hx : IsIntegralCurveOn (fun t ↦ (s t, i t, r t)) (fun _ ↦ sirField β γ) (Ici 0))
include hx

lemma sir_hasDerivWithinAt_s {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt s (-(β * s t * i t)) (Ici 0) t := by
  have h2 := hasFDerivAt_fst.comp_hasDerivWithinAt t (hx t ht)
  simpa [sirField, Function.comp_def] using h2

lemma sir_hasDerivWithinAt_i {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt i (β * s t * i t - γ * i t) (Ici 0) t := by
  have h2 := (hasFDerivAt_fst.comp _ hasFDerivAt_snd).comp_hasDerivWithinAt t (hx t ht)
  simpa [sirField, Function.comp_def] using h2

lemma sir_hasDerivWithinAt_r {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt r (γ * i t) (Ici 0) t := by
  have h2 := (hasFDerivAt_snd.comp _ hasFDerivAt_snd).comp_hasDerivWithinAt t (hx t ht)
  simpa [sirField, Function.comp_def] using h2

/-- Conservation: `s + i + r` is constant on `[0, ∞)`. -/
lemma sir_sum_eq {t : ℝ} (ht : 0 ≤ t) :
    s t + i t + r t = s 0 + i 0 + r 0 := by
  have hd : ∀ u, 0 ≤ u → HasDerivWithinAt (fun u ↦ s u + i u + r u) 0 (Ici 0) u := by
    intro u hu
    refine ((((sir_hasDerivWithinAt_s hx) hu).add ((sir_hasDerivWithinAt_i hx) hu)).add
      ((sir_hasDerivWithinAt_r hx) hu)).congr_deriv ?_
    ring
  exact eq_of_hasDerivWithinAt_zero hd ht

/-- The first integral `s · exp((β/γ) r)` is constant on `[0, ∞)` (Kermack–McKendrick 1927). -/
lemma sir_s_mul_exp (hγ : γ ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    s t * exp (β / γ * r t) = s 0 * exp (β / γ * r 0) := by
  have hd : ∀ u, 0 ≤ u →
      HasDerivWithinAt (fun u ↦ s u * exp (β / γ * r u)) 0 (Ici 0) u := by
    intro u hu
    refine (((sir_hasDerivWithinAt_s hx) hu).mul
      (((sir_hasDerivWithinAt_r hx) hu).const_mul (β / γ)).exp).congr_deriv ?_
    field_simp
    ring
  exact eq_of_hasDerivWithinAt_zero hd ht

/-- `s ≥ 0` on `[0, ∞)` if `s 0 ≥ 0`. -/
lemma sir_s_nonneg (hγ : γ ≠ 0) (hs : 0 ≤ s 0) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ s t := by
  have h := (sir_s_mul_exp hx) hγ ht
  have he := exp_pos (β / γ * r t)
  have h0 : 0 ≤ s 0 * exp (β / γ * r 0) := mul_nonneg hs (exp_pos _).le
  by_contra hneg
  have : s t * exp (β / γ * r t) < 0 := mul_neg_of_neg_of_pos (not_le.mp hneg) he
  linarith

/-- `i ≥ 0` on `[0, ∞)` if `i 0 ≥ 0`: with `G t = ∫₀ᵗ (β s - γ)` (for `s` extended by `s 0` to
negative times), `i · exp(-G)` is constant. -/
lemma sir_i_nonneg (hi : 0 ≤ i 0) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ i t := by
  have hcs : ContinuousOn s (Ici 0) :=
    continuousOn_of_hasDerivWithinAt fun _ hu ↦ (sir_hasDerivWithinAt_s hx) hu
  have hcont : Continuous fun u ↦ β * s (max u 0) - γ := by
    have : Continuous fun u ↦ s (max u 0) :=
      hcs.comp_continuous (continuous_id.max continuous_const) fun u ↦ le_max_right u 0
    exact (continuous_const.mul this).sub continuous_const
  set G : ℝ → ℝ := fun t ↦ ∫ u in (0 : ℝ)..t, (β * s (max u 0) - γ) with hG
  have hGd (u : ℝ) : HasDerivAt G (β * s (max u 0) - γ) u :=
    (hcont.integral_hasStrictDerivAt 0 u).hasDerivAt
  have hd : ∀ u, 0 ≤ u → HasDerivWithinAt (fun u ↦ i u * exp (-G u)) 0 (Ici 0) u := by
    intro u hu
    refine (((sir_hasDerivWithinAt_i hx) hu).mul
      ((hGd u).neg.exp.hasDerivWithinAt)).congr_deriv ?_
    rw [max_eq_left hu]
    ring
  have h := eq_of_hasDerivWithinAt_zero hd ht
  have hG0 : G 0 = 0 := by simp [hG]
  rw [hG0, neg_zero, exp_zero, mul_one] at h
  have he := exp_pos (-G t)
  by_contra hneg
  have : i t * exp (-G t) < 0 := mul_neg_of_neg_of_pos (not_le.mp hneg) he
  linarith

/-- `r ≥ r 0` on `[0, ∞)` when `i ≥ 0` there and `γ ≥ 0` (`r' = γ i ≥ 0`). -/
lemma sir_r_ge (hγ : 0 ≤ γ) (hi : 0 ≤ i 0) {t : ℝ} (ht : 0 ≤ t) :
    r 0 ≤ r t := by
  have hmono : MonotoneOn r (Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun u ↦ γ * i u) (convex_Ici 0)
      (continuousOn_of_hasDerivWithinAt fun _ hu ↦ (sir_hasDerivWithinAt_r hx) hu)
      (fun u hu ↦ ?_) (fun u hu ↦ ?_)
    · rw [interior_Ici] at hu ⊢
      exact ((sir_hasDerivWithinAt_r hx) (le_of_lt hu)).mono Ioi_subset_Ici_self
    · rw [interior_Ici] at hu
      exact mul_nonneg hγ ((sir_i_nonneg hx) hi (le_of_lt hu))
  exact hmono self_mem_Ici ht ht

/-- **Invariance of the simplex**: a solution started in the simplex stays in the sup-norm unit
ball (indeed in the simplex) on `[0, ∞)`. -/
lemma sir_norm_le_one (hγ : 0 < γ) (hs : 0 ≤ s 0)
    (hi : 0 ≤ i 0) (hr : 0 ≤ r 0) (hsum : s 0 + i 0 + r 0 = 1) {t : ℝ} (ht : 0 ≤ t) :
    ‖(s t, i t, r t)‖ ≤ 1 := by
  have h1 := (sir_s_nonneg hx) hγ.ne' hs ht
  have h2 := (sir_i_nonneg hx) hi ht
  have h3 := (sir_r_ge hx) hγ.le hi ht
  have h4 := (sir_sum_eq hx) ht
  simp only [Prod.norm_def, Real.norm_eq_abs]
  refine max_le ?_ (max_le ?_ ?_) <;> rw [abs_le] <;> constructor <;> linarith

end Curve

/-! ### The field on the unit ball -/

/-- `|a b - c d| ≤ |b - d| + |a - c|` when `|a|, |d| ≤ 1`. -/
lemma abs_mul_sub_mul_le {a b c d : ℝ} (ha : |a| ≤ 1) (hd : |d| ≤ 1) :
    |a * b - c * d| ≤ |b - d| + |a - c| := by
  have e : a * b - c * d = a * (b - d) + d * (a - c) := by ring
  rw [e]
  calc |a * (b - d) + d * (a - c)| ≤ |a * (b - d)| + |d * (a - c)| := abs_add_le _ _
    _ = |a| * |b - d| + |d| * |a - c| := by rw [abs_mul, abs_mul]
    _ ≤ 1 * |b - d| + 1 * |a - c| := by gcongr
    _ = |b - d| + |a - c| := by ring

lemma abs_fst_le_norm (p : ℝ × ℝ × ℝ) : |p.1| ≤ ‖p‖ := by
  simp only [Prod.norm_def, Real.norm_eq_abs]
  exact le_max_left _ _

lemma abs_snd_fst_le_norm (p : ℝ × ℝ × ℝ) : |p.2.1| ≤ ‖p‖ := by
  simp only [Prod.norm_def, Real.norm_eq_abs]
  exact (le_max_left _ _).trans (le_max_right _ _)

lemma abs_snd_snd_le_norm (p : ℝ × ℝ × ℝ) : |p.2.2| ≤ ‖p‖ := by
  simp only [Prod.norm_def, Real.norm_eq_abs]
  exact (le_max_right _ _).trans (le_max_right _ _)

/-- A point of `ℝ × ℝ × ℝ` whose three coordinates are bounded by `δ` has sup norm at most `δ`. -/
lemma norm_le_of_abs_le {p : ℝ × ℝ × ℝ} {δ : ℝ} (h1 : |p.1| ≤ δ) (h2 : |p.2.1| ≤ δ)
    (h3 : |p.2.2| ≤ δ) : ‖p‖ ≤ δ := by
  simp only [Prod.norm_def, Real.norm_eq_abs]
  exact max_le h1 (max_le h2 h3)

/-- On the unit ball, the Kermack–McKendrick field is `(2β + γ)`-Lipschitz (sup norm). -/
lemma norm_sirField_sub_le (hβ : 0 ≤ β) (hγ : 0 ≤ γ) {p q : ℝ × ℝ × ℝ} (hp : ‖p‖ ≤ 1)
    (hq : ‖q‖ ≤ 1) : ‖sirField β γ p - sirField β γ q‖ ≤ (2 * β + γ) * ‖p - q‖ := by
  have hp1 := (abs_fst_le_norm p).trans hp
  have hq2 := (abs_snd_fst_le_norm q).trans hq
  have d1 := abs_fst_le_norm (p - q)
  have d2 := abs_snd_fst_le_norm (p - q)
  simp only [Prod.fst_sub, Prod.snd_sub] at d1 d2
  have hm := abs_mul_sub_mul_le (b := p.2.1) (c := q.1) hp1 hq2
  have hpq : 0 ≤ ‖p - q‖ := norm_nonneg _
  have key : |p.1 * p.2.1 - q.1 * q.2.1| ≤ 2 * ‖p - q‖ := by linarith
  refine norm_le_of_abs_le ?_ ?_ ?_ <;> simp only [sirField, Prod.fst_sub, Prod.snd_sub]
  · calc |-(β * p.1 * p.2.1) - -(β * q.1 * q.2.1)| = β * |p.1 * p.2.1 - q.1 * q.2.1| := by
          have e : -(β * p.1 * p.2.1) - -(β * q.1 * q.2.1)
              = -(β * (p.1 * p.2.1 - q.1 * q.2.1)) := by ring
          rw [e, abs_neg, abs_mul, abs_of_nonneg hβ]
      _ ≤ β * (2 * ‖p - q‖) := by gcongr
      _ ≤ (2 * β + γ) * ‖p - q‖ := by nlinarith
  · calc |β * p.1 * p.2.1 - γ * p.2.1 - (β * q.1 * q.2.1 - γ * q.2.1)|
        = |β * (p.1 * p.2.1 - q.1 * q.2.1) - γ * (p.2.1 - q.2.1)| := by ring_nf
      _ ≤ |β * (p.1 * p.2.1 - q.1 * q.2.1)| + |γ * (p.2.1 - q.2.1)| := abs_sub _ _
      _ = β * |p.1 * p.2.1 - q.1 * q.2.1| + γ * |p.2.1 - q.2.1| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hβ, abs_of_nonneg hγ]
      _ ≤ β * (2 * ‖p - q‖) + γ * ‖p - q‖ := by gcongr
      _ = (2 * β + γ) * ‖p - q‖ := by ring
  · calc |γ * p.2.1 - γ * q.2.1| = γ * |p.2.1 - q.2.1| := by
          rw [← mul_sub, abs_mul, abs_of_nonneg hγ]
      _ ≤ γ * ‖p - q‖ := by gcongr
      _ ≤ (2 * β + γ) * ‖p - q‖ := by nlinarith

/-- On the unit ball, the Kermack–McKendrick field is bounded by `β + γ` (sup norm). -/
lemma norm_sirField_le (hβ : 0 ≤ β) (hγ : 0 ≤ γ) {p : ℝ × ℝ × ℝ} (hp : ‖p‖ ≤ 1) :
    ‖sirField β γ p‖ ≤ β + γ := by
  have h1 := (abs_fst_le_norm p).trans hp
  have h2 := (abs_snd_fst_le_norm p).trans hp
  have h12 : |p.1 * p.2.1| ≤ 1 := by
    rw [abs_mul]
    exact mul_le_one₀ h1 (abs_nonneg _) h2
  refine norm_le_of_abs_le ?_ ?_ ?_ <;> simp only [sirField]
  · rw [abs_neg, mul_assoc, abs_mul, abs_of_nonneg hβ]
    nlinarith [abs_nonneg (p.1 * p.2.1)]
  · calc |β * p.1 * p.2.1 - γ * p.2.1| ≤ |β * p.1 * p.2.1| + |γ * p.2.1| := abs_sub _ _
      _ = β * |p.1 * p.2.1| + γ * |p.2.1| := by
          have e1 : |β * p.1 * p.2.1| = β * |p.1 * p.2.1| := by
            rw [mul_assoc, abs_mul, abs_of_nonneg hβ]
          have e2 : |γ * p.2.1| = γ * |p.2.1| := by rw [abs_mul, abs_of_nonneg hγ]
          rw [e1, e2]
      _ ≤ β * 1 + γ * 1 := by gcongr
      _ = β + γ := by ring
  · rw [abs_mul, abs_of_nonneg hγ]
    nlinarith [abs_nonneg p.2.1]

/-! ### Euler step error -/

/-- **Euler step error.** If the solution stays in the unit ball on `[t, t + h]`, then
`‖x(t + h) - x(t) - h F(x(t))‖ ≤ (2β + γ)(β + γ) h²`. -/
lemma sir_euler_le
    (hx : IsIntegralCurveOn (fun t ↦ (s t, i t, r t)) (fun _ ↦ sirField β γ) (Ici 0))
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) {t h : ℝ} (ht : 0 ≤ t) (hh : 0 ≤ h)
    (hball : ∀ u ∈ Icc t (t + h), ‖(s u, i u, r u)‖ ≤ 1) :
    ‖(s (t + h), i (t + h), r (t + h)) - (s t, i t, r t) - h • sirField β γ (s t, i t, r t)‖
      ≤ (2 * β + γ) * (β + γ) * h ^ 2 := by
  set x : ℝ → ℝ × ℝ × ℝ := fun u ↦ (s u, i u, r u) with hxdef
  have hsub : Icc t (t + h) ⊆ Ici 0 := fun u hu ↦ ht.trans hu.1
  have hder : ∀ u ∈ Icc t (t + h), HasDerivWithinAt x (sirField β γ (x u)) (Icc t (t + h)) u :=
    fun u hu ↦ (hx u (hsub hu)).mono hsub
  -- the solution moves at speed at most `β + γ`
  have hmove : ∀ u ∈ Icc t (t + h), ‖x u - x t‖ ≤ (β + γ) * (u - t) :=
    norm_image_sub_le_of_norm_deriv_le_segment' hder
      fun u hu ↦ norm_sirField_le hβ hγ (hball u (Ico_subset_Icc_self hu))
  -- `g u = x u - (u - t) F(x t)` has derivative `F(x u) - F(x t)`
  have hg : ∀ u ∈ Icc t (t + h), HasDerivWithinAt (fun u ↦ x u - (u - t) • sirField β γ (x t))
      (sirField β γ (x u) - sirField β γ (x t)) (Icc t (t + h)) u := by
    intro u hu
    refine ((hder u hu).sub (((hasDerivWithinAt_id u _).sub_const t).smul_const
      (sirField β γ (x t)))).congr_deriv ?_
    simp
  have hgb : ∀ u ∈ Ico t (t + h), ‖sirField β γ (x u) - sirField β γ (x t)‖
      ≤ (2 * β + γ) * (β + γ) * h := by
    intro u hu
    have hu' := Ico_subset_Icc_self hu
    have hL : 0 ≤ 2 * β + γ := by linarith
    have hM : 0 ≤ β + γ := by linarith
    calc ‖sirField β γ (x u) - sirField β γ (x t)‖ ≤ (2 * β + γ) * ‖x u - x t‖ :=
          norm_sirField_sub_le hβ hγ (hball u hu') (hball t ⟨le_rfl, by linarith⟩)
      _ ≤ (2 * β + γ) * ((β + γ) * (u - t)) := mul_le_mul_of_nonneg_left (hmove u hu') hL
      _ ≤ (2 * β + γ) * ((β + γ) * h) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith [hu.2]) hM) hL
      _ = (2 * β + γ) * (β + γ) * h := by ring
  have := norm_image_sub_le_of_norm_deriv_le_segment' hg hgb (t + h) ⟨by linarith, le_rfl⟩
  simp only [sub_self, zero_smul, sub_zero, add_sub_cancel_left] at this
  calc ‖x (t + h) - x t - h • sirField β γ (x t)‖
      = ‖x (t + h) - h • sirField β γ (x t) - x t‖ := by congr 1; abel
    _ ≤ (2 * β + γ) * (β + γ) * h * h := this
    _ = (2 * β + γ) * (β + γ) * h ^ 2 := by ring

end Epidemics.Kurtz
