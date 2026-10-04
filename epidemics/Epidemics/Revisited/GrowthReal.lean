import Epidemics.Revisited.GrowthConnect

/-! # Real estimates for the exponential-growth targets

Round target `E0(k) = E(k) - A k^{3/4}`, with `k^{3/4}` written as `Real.sqrt` so that no
real exponentiation is required, and the phase thresholds `k_{j+1} = k_j + E0(k_j)`.
Every constant below depends only on `γlo, γhi, a, b, c, f`.
-/

namespace Epidemics.Revisited
open Finset

noncomputable def fourthRoot (x : ℝ) : ℝ := Real.sqrt (Real.sqrt x)

noncomputable def threeFourth (x : ℝ) : ℝ := Real.sqrt x * fourthRoot x

lemma fourthRoot_nonneg (x : ℝ) : 0 ≤ fourthRoot x := by
  unfold fourthRoot
  exact Real.sqrt_nonneg _

lemma threeFourth_nonneg (x : ℝ) : 0 ≤ threeFourth x :=
  mul_nonneg (Real.sqrt_nonneg _) (fourthRoot_nonneg _)

lemma fourthRoot_sq (x : ℝ) : fourthRoot x ^ 2 = Real.sqrt x := by
  unfold fourthRoot
  rw [sq, Real.mul_self_sqrt (Real.sqrt_nonneg _)]

lemma fourthRoot_four {x : ℝ} (hx : 0 ≤ x) : fourthRoot x ^ 4 = x := by
  have h2 := fourthRoot_sq x
  calc fourthRoot x ^ 4 = (fourthRoot x ^ 2) ^ 2 := by ring
    _ = Real.sqrt x ^ 2 := by rw [h2]
    _ = x := Real.sq_sqrt hx

lemma threeFourth_eq_pow3 (x : ℝ) : threeFourth x = fourthRoot x ^ 3 := by
  have h2 := fourthRoot_sq x
  calc threeFourth x = Real.sqrt x * fourthRoot x := rfl
    _ = fourthRoot x ^ 2 * fourthRoot x := by rw [← h2]
    _ = fourthRoot x ^ 3 := by ring

lemma fourthRoot_one : fourthRoot 1 = 1 := by
  simp [fourthRoot]

lemma fourthRoot_ge_one {x : ℝ} (hx : 1 ≤ x) : 1 ≤ fourthRoot x := by
  have hsqrt : 1 ≤ Real.sqrt x := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hx
  unfold fourthRoot
  rw [← Real.sqrt_one]
  exact Real.sqrt_le_sqrt hsqrt

lemma fourthRoot_mul {u : ℝ} (hu : 0 ≤ u) (v : ℝ) :
    fourthRoot (u * v) = fourthRoot u * fourthRoot v := by
  unfold fourthRoot
  rw [Real.sqrt_mul hu]
  rw [Real.sqrt_mul (Real.sqrt_nonneg u) (Real.sqrt v)]

lemma fourthRoot_pow (ρ : ℝ) (hρ : 0 ≤ ρ) (i : ℕ) :
    fourthRoot (ρ ^ i) = fourthRoot ρ ^ i := by
  induction i with
  | zero => simp [fourthRoot_one]
  | succ i ih =>
    rw [pow_succ, pow_succ, fourthRoot_mul (pow_nonneg hρ i) ρ, ih]

lemma threeFourth_mul {u : ℝ} (hu : 0 ≤ u) (v : ℝ) :
    threeFourth (u * v) = threeFourth u * threeFourth v := by
  unfold threeFourth
  rw [Real.sqrt_mul hu, fourthRoot_mul hu v]
  ring

lemma threeFourth_le_self {x : ℝ} (hx : 1 ≤ x) : threeFourth x ≤ x := by
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hfr : 0 ≤ fourthRoot x := fourthRoot_nonneg x
  have hfr1 : 1 ≤ fourthRoot x := fourthRoot_ge_one hx
  have h3 := threeFourth_eq_pow3 x
  have h4 := fourthRoot_four hx0
  have hsplit : x = threeFourth x * fourthRoot x := by
    calc x = fourthRoot x ^ 4 := h4.symm
      _ = fourthRoot x ^ 3 * fourthRoot x := by ring
      _ = threeFourth x * fourthRoot x := by rw [← h3]
  calc threeFourth x = threeFourth x * 1 := by ring
    _ ≤ threeFourth x * fourthRoot x := mul_le_mul_of_nonneg_left hfr1 (threeFourth_nonneg x)
    _ = x := hsplit.symm

lemma threeFourth_split {x : ℝ} (hx : 1 ≤ x) :
    threeFourth x * fourthRoot x = x := by
  have hx0 : 0 ≤ x := by linarith only [hx]
  calc threeFourth x * fourthRoot x
      = fourthRoot x ^ 3 * fourthRoot x := by rw [threeFourth_eq_pow3 x]
    _ = fourthRoot x ^ 4 := by ring
    _ = x := fourthRoot_four hx0

lemma threeFourth_div_self {x : ℝ} (hx : 1 ≤ x) :
    threeFourth x / x = 1 / fourthRoot x := by
  have hpos : 0 < x := by linarith only [hx]
  have hfr : 0 < fourthRoot x := by
    have h1 : 1 ≤ fourthRoot x := fourthRoot_ge_one hx
    linarith only [h1]
  rw [div_eq_div_iff hpos.ne' hfr.ne']
  simpa [one_mul] using threeFourth_split hx

/-- `3 s^4 - 4 s^3 + 1 = (s - 1)^2 (3 s^2 + 2 s + 1) ≥ 0` for `s ≥ 1`. -/
lemma three_poly_nonneg {s : ℝ} (hs : 1 ≤ s) : 0 ≤ 3 * s ^ 4 - 4 * s ^ 3 + 1 := by
  have h : 3 * s ^ 4 - 4 * s ^ 3 + 1 = (s - 1) ^ 2 * (3 * s ^ 2 + 2 * s + 1) := by ring
  have h1 : 0 ≤ (s - 1) ^ 2 := sq_nonneg _
  have h2 : 0 ≤ 3 * s ^ 2 + 2 * s + 1 := by nlinarith only [hs]
  rw [h]
  exact mul_nonneg h1 h2

lemma threeFourth_increment {t : ℝ} (ht : 1 ≤ t) :
    threeFourth t - 1 ≤ (3 / 4) * (t - 1) := by
  have ht0 : 0 ≤ t := by linarith only [ht]
  let s : ℝ := fourthRoot t
  have hs1 : 1 ≤ s := fourthRoot_ge_one ht
  have hpoly := three_poly_nonneg hs1
  have h4 : s ^ 4 = t := fourthRoot_four ht0
  have h3 : s ^ 3 = threeFourth t := (threeFourth_eq_pow3 t).symm
  have hstep : 4 * (s ^ 3 - 1) ≤ 3 * (s ^ 4 - 1) := by linarith only [hpoly]
  have h4pos : (0 : ℝ) < 4 := by norm_num
  have hdiv : s ^ 3 - 1 ≤ (3 * (s ^ 4 - 1)) / 4 := by
    rw [le_div_iff₀ h4pos]
    linarith only [hstep]
  have hform : (3 * (s ^ 4 - 1)) / 4 = (3 / 4) * (s ^ 4 - 1) := by ring
  rw [hform] at hdiv
  rw [h3, h4] at hdiv
  exact hdiv

lemma threeFourth_diff {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    threeFourth y - threeFourth x ≤ (3 / 4) * (y - x) := by
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hy0 : 0 ≤ y := by linarith only [hx, hxy]
  have hxpos : 0 < x := by linarith only [hx]
  let t : ℝ := y / x
  have ht : 1 ≤ t := by
    rw [le_div_iff₀ hxpos]
    simpa [one_mul] using hxy
  have ht0 : 0 ≤ t := by linarith only [ht]
  have hy : y = t * x := by
    simp [t, div_mul_cancel₀ _ hxpos.ne']
  have hprod : threeFourth y = threeFourth t * threeFourth x := by
    rw [hy, threeFourth_mul ht0 x]
  have hinc := threeFourth_increment ht
  have hxself := threeFourth_le_self hx
  have ht3 : 0 ≤ threeFourth t - 1 := by
    have h1 : 1 ≤ threeFourth t := by
      have hfr : 1 ≤ fourthRoot t := fourthRoot_ge_one ht
      have hsq : 1 ≤ Real.sqrt t := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt ht
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ Real.sqrt t * fourthRoot t :=
            mul_le_mul hsq hfr (by norm_num) (Real.sqrt_nonneg _)
        _ = threeFourth t := rfl
    linarith only [h1]
  have hnonnegx : 0 ≤ threeFourth x := threeFourth_nonneg x
  calc threeFourth y - threeFourth x
      = threeFourth x * (threeFourth t - 1) := by rw [hprod]; ring
    _ ≤ threeFourth x * ((3 / 4) * (t - 1)) :=
        mul_le_mul_of_nonneg_left hinc hnonnegx
    _ ≤ x * ((3 / 4) * (t - 1)) := by
        have h34 : 0 ≤ (3 / 4) * (t - 1) := by
          have : 0 ≤ t - 1 := by linarith only [ht]
          positivity
        exact mul_le_mul_of_nonneg_right hxself h34
    _ = (3 / 4) * (y - x) := by rw [hy]; ring

/-- `exp(-2x) ≤ 1 - x` on `[0, 1/2]`, from `y + 1 ≤ exp y`. -/
lemma exp_neg_two_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    Real.exp (-(2 * x)) ≤ 1 - x := by
  have hy0 : 0 ≤ 2 * x := by linarith only [hx0]
  have hy1 : 2 * x ≤ 1 := by linarith only [hx1]
  have hden : 0 < 1 - (2 * x) / 2 := by linarith only [hy1]
  have hhalf : 1 - (2 * x) / 2 = 1 - x := by ring
  have hfrac : (2 * x) / 2 ≤ (2 * x) * (1 - (2 * x) / 2) := by
    nlinarith only [hy0, hy1]
  have hsum : (1 : ℝ) ≤ ((2 * x) + 1) * (1 - (2 * x) / 2) := by
    nlinarith only [hfrac, hy0, hy1]
  have hexp : (2 * x) + 1 ≤ Real.exp (2 * x) := Real.add_one_le_exp (2 * x)
  have hcomp : 1 ≤ (1 - (2 * x) / 2) * Real.exp (2 * x) := by
    have hmul := mul_le_mul_of_nonneg_right hexp hden.le
    calc (1 : ℝ) ≤ ((2 * x) + 1) * (1 - (2 * x) / 2) := hsum
      _ ≤ Real.exp (2 * x) * (1 - (2 * x) / 2) := hmul
      _ = (1 - (2 * x) / 2) * Real.exp (2 * x) := by ring
  have hneg : Real.exp (-(2 * x)) ≤ 1 - (2 * x) / 2 := by
    rw [Real.exp_neg]
    have hpos : 0 < Real.exp (2 * x) := Real.exp_pos _
    calc (Real.exp (2 * x))⁻¹
        = (Real.exp (2 * x))⁻¹ * 1 := by ring
      _ ≤ (Real.exp (2 * x))⁻¹ * ((1 - (2 * x) / 2) * Real.exp (2 * x)) :=
          mul_le_mul_of_nonneg_left hcomp (inv_nonneg.mpr hpos.le)
      _ = 1 - (2 * x) / 2 := by
          have hassoc :
              (Real.exp (2 * x))⁻¹ * ((1 - (2 * x) / 2) * Real.exp (2 * x)) =
                (1 - (2 * x) / 2) *
                  ((Real.exp (2 * x))⁻¹ * Real.exp (2 * x)) := by ring
          rw [hassoc, inv_mul_cancel₀ hpos.ne', mul_one]
  rwa [hhalf] at hneg

lemma log_one_sub_ge {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    -2 * x ≤ Real.log (1 - x) := by
  have hexp := exp_neg_two_le hx0 hx1
  have hlog := Real.log_le_log (Real.exp_pos _) hexp
  rw [Real.log_exp] at hlog
  have hneg : -(2 * x) = -2 * x := by ring
  rwa [hneg] at hlog

noncomputable def fShrink (a f : ℝ) : ℝ := min (f / 2) (1 / (8 * (a + 1)))

lemma fShrink_pos {a f : ℝ} (hf : 0 < f) (ha : 0 ≤ a) : 0 < fShrink a f := by
  have ha1 : 0 < a + 1 := by linarith only [ha]
  have h1 : 0 < f / 2 := by linarith only [hf]
  have h2 : 0 < 1 / (8 * (a + 1)) := by positivity
  exact lt_min h1 h2

lemma fShrink_le_half {a f : ℝ} : fShrink a f ≤ f / 2 := min_le_left _ _

lemma fShrink_le_f {a f : ℝ} (hf : 0 < f) : fShrink a f ≤ f := by
  have hhalf : f / 2 ≤ f := by linarith only [hf]
  exact le_trans fShrink_le_half hhalf

lemma fShrink_a_le {a f : ℝ} (ha : 0 ≤ a) : (a + 1) * fShrink a f ≤ 1 / 8 := by
  have ha1 : 0 ≤ a + 1 := by linarith only [ha]
  have hle : fShrink a f ≤ 1 / (8 * (a + 1)) := min_le_right _ _
  have hpos : 0 < a + 1 := by linarith only [ha]
  calc (a + 1) * fShrink a f
      ≤ (a + 1) * (1 / (8 * (a + 1))) := mul_le_mul_of_nonneg_left hle ha1
    _ = 1 / 8 := by field_simp [hpos.ne']

noncomputable def growthE (γ a b : ℝ) (n : ℕ) (k : ℝ) : ℝ :=
  γ * k * (1 - (a + 1) * k / n - b / Real.log n)

noncomputable def growthE0 (γ a b A : ℝ) (n : ℕ) (k : ℝ) : ℝ :=
  growthE γ a b n k - A * threeFourth k

lemma growthE_le_linear {γ a b : ℝ} {n : ℕ} {k : ℝ} (hγ : 0 ≤ γ) (hk : 0 ≤ k)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : 0 < (n : ℝ)) (hlog : 0 < Real.log n) :
    growthE γ a b n k ≤ γ * k := by
  have hparen : 1 - (a + 1) * k / n - b / Real.log n ≤ 1 := by
    have h1 : 0 ≤ (a + 1) * k / n := by positivity
    have h2 : 0 ≤ b / Real.log n := div_nonneg hb hlog.le
    linarith only [h1, h2]
  unfold growthE
  have hmul : γ * k * (1 - (a + 1) * k / n - b / Real.log n) ≤ γ * k * 1 :=
    mul_le_mul_of_nonneg_left hparen (mul_nonneg hγ hk)
  simpa [mul_one] using hmul

lemma sqrt_pow {ρ : ℝ} (hρ : 0 ≤ ρ) (i : ℕ) : Real.sqrt (ρ ^ i) = Real.sqrt ρ ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ, pow_succ, Real.sqrt_mul (pow_nonneg hρ i), ih]

lemma fourthRoot_pos {x : ℝ} (hx : 0 < x) : 0 < fourthRoot x := by
  unfold fourthRoot
  exact Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hx)

lemma fourthRoot_mono {x y : ℝ} (hxy : x ≤ y) : fourthRoot x ≤ fourthRoot y := by
  unfold fourthRoot
  exact Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hxy)

lemma geom_sum_le_div {ρ : ℝ} (hρ : 1 < ρ) (j : ℕ) :
    ∑ i ∈ range j, ρ ^ i ≤ ρ ^ j / (ρ - 1) := by
  have hne : ρ ≠ 1 := ne_of_gt hρ
  rw [geom_sum_eq hne]
  have hden : 0 < ρ - 1 := sub_pos.mpr hρ
  rw [div_le_div_iff_of_pos_right hden]
  linarith

lemma prod_one_sub_ge {η : ℕ → ℝ} {m : ℕ}
    (h0 : ∀ i ∈ range m, 0 ≤ η i) (h1 : ∀ i ∈ range m, η i ≤ 1)
    (hsum : ∑ i ∈ range m, η i ≤ 1) :
    1 - ∑ i ∈ range m, η i ≤ ∏ i ∈ range m, (1 - η i) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hη0 : 0 ≤ η m := h0 m (mem_range.mpr (Nat.lt_succ_self m))
    have hη1 : η m ≤ 1 := h1 m (mem_range.mpr (Nat.lt_succ_self m))
    have h0' : ∀ i ∈ range m, 0 ≤ η i := fun i hi => h0 i (mem_range.mpr (Nat.lt_succ_of_lt (mem_range.mp hi)))
    have h1' : ∀ i ∈ range m, η i ≤ 1 := fun i hi => h1 i (mem_range.mpr (Nat.lt_succ_of_lt (mem_range.mp hi)))
    have hsum' : ∑ i ∈ range m, η i ≤ 1 := by
      have hle : ∑ i ∈ range m, η i ≤ ∑ i ∈ range (m + 1), η i := by
        rw [sum_range_succ]
        linarith only [hη0]
      exact le_trans hle hsum
    have hIH := ih h0' h1' hsum'
    have hfactor : 0 ≤ 1 - η m := by linarith only [hη1]
    have hcross : 0 ≤ η m * ∑ i ∈ range m, η i :=
      mul_nonneg hη0 (sum_nonneg h0')
    have hbase : 1 - (∑ i ∈ range m, η i + η m) ≤
        (1 - ∑ i ∈ range m, η i) * (1 - η m) := by
      nlinarith only [hcross]
    have hmul := mul_le_mul_of_nonneg_right hIH hfactor
    rw [prod_range_succ, sum_range_succ]
    exact le_trans hbase hmul

/-- `E(y) - E(x) ≥ (γ/2) (y - x)` on `1 ≤ x ≤ y ≤ f' n`, once `b / log n ≤ 1/4` and
`(a + 1) f' ≤ 1/8`. -/
lemma growthE_diff {γ a b : ℝ} {n : ℕ} {x y f' : ℝ} (hγ : 0 ≤ γ) (hxy : x ≤ y)
    (hy : y ≤ f' * n) (ha : 0 ≤ a) (hn : 0 < (n : ℝ)) (hlog : 0 < Real.log n)
    (hblog : b / Real.log n ≤ 1 / 4) (hf' : (a + 1) * f' ≤ 1 / 8) :
    γ * (y - x) * (1 / 2) ≤ growthE γ a b n y - growthE γ a b n x := by
  have ha1 : 0 ≤ a + 1 := by linarith only [ha]
  have hxy2 : x + y ≤ 2 * y := by linarith only [hxy]
  have hy2 : 2 * y ≤ 2 * (f' * n) := mul_le_mul_of_nonneg_left hy (by norm_num)
  have hsumle : x + y ≤ 2 * f' * n := by
    have hassoc : 2 * (f' * n) = 2 * f' * n := by ring
    linarith only [hxy2, hy2, hassoc]
  have havg : (x + y) / n ≤ 2 * f' := by
    rw [div_le_iff₀ hn]
    simpa [mul_comm] using hsumle
  have hcoef : (a + 1) * (x + y) / n ≤ 1 / 4 := by
    have hmul : (a + 1) * ((x + y) / n) ≤ (a + 1) * (2 * f') :=
      mul_le_mul_of_nonneg_left havg ha1
    have htwo : (a + 1) * (2 * f') = 2 * ((a + 1) * f') := by ring
    have hident : (a + 1) * (x + y) / n = (a + 1) * ((x + y) / n) := by ring
    linarith only [hmul, htwo, hf', hident]
  have hbr : 1 / 2 ≤ 1 - b / Real.log n - (a + 1) * (x + y) / n := by
    linarith only [hblog, hcoef]
  have hEq : growthE γ a b n y - growthE γ a b n x =
      γ * (y - x) * (1 - b / Real.log n - (a + 1) * (x + y) / n) := by
    unfold growthE
    field_simp [hn.ne', hlog.ne']
    ring
  have hnonneg : 0 ≤ γ * (y - x) := mul_nonneg hγ (by linarith only [hxy])
  calc γ * (y - x) * (1 / 2)
      ≤ γ * (y - x) * (1 - b / Real.log n - (a + 1) * (x + y) / n) :=
        mul_le_mul_of_nonneg_left hbr hnonneg
    _ = growthE γ a b n y - growthE γ a b n x := hEq.symm

lemma growthE_lower {γ a b : ℝ} {n : ℕ} {k f' : ℝ} (hγ : 0 ≤ γ) (hk : 0 ≤ k)
    (hkf : k ≤ f' * n) (ha : 0 ≤ a) (hn : 0 < (n : ℝ))
    (hblog : b / Real.log n ≤ 1 / 4) (hf' : (a + 1) * f' ≤ 1 / 8) :
    γ * k * (5 / 8) ≤ growthE γ a b n k := by
  have ha1 : 0 ≤ a + 1 := by linarith only [ha]
  have hdiv : k / n ≤ f' := by
    rw [div_le_iff₀ hn]
    simpa [mul_comm] using hkf
  have hcoef : (a + 1) * k / n ≤ 1 / 8 := by
    have hmul : (a + 1) * (k / n) ≤ (a + 1) * f' := mul_le_mul_of_nonneg_left hdiv ha1
    have hident : (a + 1) * k / n = (a + 1) * (k / n) := by ring
    linarith only [hmul, hf', hident]
  have hbr : 5 / 8 ≤ 1 - (a + 1) * k / n - b / Real.log n := by
    linarith only [hcoef, hblog]
  unfold growthE
  have hnonneg : 0 ≤ γ * k := mul_nonneg hγ hk
  exact mul_le_mul_of_nonneg_left hbr hnonneg

lemma growthE0_diff {γ a b A : ℝ} {n : ℕ} {x y f' : ℝ} (hγ : 0 ≤ γ) (hx : 1 ≤ x) (hxy : x ≤ y)
    (hy : y ≤ f' * n) (ha : 0 ≤ a) (hA : A ≤ γ / 6) (hn : 0 < (n : ℝ))
    (hlog : 0 < Real.log n) (hblog : b / Real.log n ≤ 1 / 4) (hf' : (a + 1) * f' ≤ 1 / 8) :
    γ * (y - x) * (3 / 8) ≤ growthE0 γ a b A n y - growthE0 γ a b A n x := by
  have hE := growthE_diff hγ hxy hy ha hn hlog hblog hf'
  have h3 := threeFourth_diff hx hxy
  have hAy : A * (threeFourth y - threeFourth x) ≤ (γ / 6) * ((3 / 4) * (y - x)) := by
    have hdiff : 0 ≤ threeFourth y - threeFourth x := by
      have hmono : threeFourth x ≤ threeFourth y := by
        unfold threeFourth
        exact mul_le_mul (Real.sqrt_le_sqrt hxy) (fourthRoot_mono hxy)
          (fourthRoot_nonneg x) (Real.sqrt_nonneg y)
      linarith only [hmono]
    exact mul_le_mul hA h3 hdiff (by linarith only [hγ, hA])
  have hsub : growthE0 γ a b A n y - growthE0 γ a b A n x =
      (growthE γ a b n y - growthE γ a b n x) -
        A * (threeFourth y - threeFourth x) := by
    unfold growthE0
    ring
  have hrate : (γ / 6) * ((3 / 4) * (y - x)) ≤ γ * (y - x) * (1 / 8) := by
    nlinarith only [hγ, hxy]
  have hhalf : γ * (y - x) * (3 / 8) ≤
      γ * (y - x) * (1 / 2) - γ * (y - x) * (1 / 8) := by
    nlinarith only [hγ, hxy]
  calc γ * (y - x) * (3 / 8)
      ≤ γ * (y - x) * (1 / 2) - γ * (y - x) * (1 / 8) := hhalf
    _ ≤ (growthE γ a b n y - growthE γ a b n x) - A * (threeFourth y - threeFourth x) := by
        have hdrop : A * (threeFourth y - threeFourth x) ≤ γ * (y - x) * (1 / 8) :=
          le_trans hAy hrate
        linarith only [hE, hdrop]
    _ = growthE0 γ a b A n y - growthE0 γ a b A n x := hsub.symm

lemma growthE0_lower {γ a b A : ℝ} {n : ℕ} {k f' : ℝ} (hγ : 0 ≤ γ) (hk : 1 ≤ k)
    (hkf : k ≤ f' * n) (ha : 0 ≤ a) (hA : A ≤ γ / 6) (hn : 0 < (n : ℝ))
    (hblog : b / Real.log n ≤ 1 / 4) (hf' : (a + 1) * f' ≤ 1 / 8) :
    γ * k * (11 / 24) ≤ growthE0 γ a b A n k := by
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hE := growthE_lower hγ hk0 hkf ha hn hblog hf'
  have h3 := threeFourth_le_self hk
  have hsub : A * threeFourth k ≤ (γ / 6) * k := by
    have hAk : A * threeFourth k ≤ (γ / 6) * threeFourth k :=
      mul_le_mul_of_nonneg_right hA (threeFourth_nonneg k)
    have htk : (γ / 6) * threeFourth k ≤ (γ / 6) * k :=
      mul_le_mul_of_nonneg_left h3 (by linarith only [hγ, hA])
    exact le_trans hAk htk
  unfold growthE0
  linarith only [hE, hsub]

noncomputable def alpha0 (b γlo : ℝ) : ℝ := Real.exp (-2 * b / Real.log (1 + γlo))

noncomputable def alphaSeq (b γlo : ℝ) : ℝ := alpha0 b γlo / 2

noncomputable def fourthGap (γlo : ℝ) : ℝ := 1 - (fourthRoot (1 + γlo))⁻¹

noncomputable def growthA (γlo b : ℝ) : ℝ :=
  min (γlo / 6) ((1 / 8) * fourthRoot (alphaSeq b γlo) * fourthGap γlo)

lemma alpha0_pos (b γlo : ℝ) : 0 < alpha0 b γlo := by
  unfold alpha0
  exact Real.exp_pos _

lemma alpha0_le_one {b γlo : ℝ} (hb : 0 ≤ b) (hγlo : 0 < γlo) : alpha0 b γlo ≤ 1 := by
  have hlog : 0 < Real.log (1 + γlo) := Real.log_pos (by linarith only [hγlo])
  have harg : -2 * b / Real.log (1 + γlo) ≤ 0 := by
    have hnum : -2 * b ≤ 0 := by linarith only [hb]
    exact div_nonpos_of_nonpos_of_nonneg hnum hlog.le
  have hexp := (Real.exp_le_exp).mpr harg
  rw [Real.exp_zero] at hexp
  simpa [alpha0] using hexp

lemma alphaSeq_pos (b γlo : ℝ) : 0 < alphaSeq b γlo := by
  unfold alphaSeq
  exact div_pos (alpha0_pos b γlo) (by norm_num)

lemma alphaSeq_le_one {b γlo : ℝ} (hb : 0 ≤ b) (hγlo : 0 < γlo) : alphaSeq b γlo ≤ 1 := by
  have hhalf : alpha0 b γlo / 2 ≤ 1 / 2 := by
    have h2 : (0 : ℝ) < 2 := by norm_num
    rw [div_le_div_iff_of_pos_right h2]
    have h := alpha0_le_one hb hγlo
    linarith only [h]
  have h12 : (1 : ℝ) / 2 ≤ 1 := by norm_num
  exact le_trans (by simpa [alphaSeq] using hhalf) h12

lemma fourthGap_pos {γlo : ℝ} (hγlo : 0 < γlo) : 0 < fourthGap γlo := by
  have h1 : 1 < 1 + γlo := by linarith only [hγlo]
  have hfr : 1 < fourthRoot (1 + γlo) := by
    have hge : 1 ≤ fourthRoot (1 + γlo) := fourthRoot_ge_one h1.le
    have hne : fourthRoot (1 + γlo) ≠ 1 := by
      intro h
      have h4 := fourthRoot_four (x := 1 + γlo) (by linarith only [hγlo])
      rw [h] at h4
      have : (1 : ℝ) ^ 4 = 1 := by norm_num
      linarith only [h4, this, hγlo]
    exact lt_of_le_of_ne hge (Ne.symm hne)
  have hinv : (fourthRoot (1 + γlo))⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]
    right
    exact hfr
  unfold fourthGap
  linarith only [hinv]

lemma growthA_pos {b γlo : ℝ} (hγlo : 0 < γlo) : 0 < growthA γlo b := by
  have h1 : 0 < γlo / 6 := by
    have h6 : (0 : ℝ) < 6 := by norm_num
    exact div_pos hγlo h6
  have h2 : 0 < (1 / 8) * fourthRoot (alphaSeq b γlo) * fourthGap γlo := by
    have h8 : (0 : ℝ) < 1 / 8 := by norm_num
    exact mul_pos (mul_pos h8 (fourthRoot_pos (alphaSeq_pos b γlo))) (fourthGap_pos hγlo)
  unfold growthA
  exact lt_min h1 h2

lemma growthA_le_gamma {b γlo : ℝ} : growthA γlo b ≤ γlo / 6 := min_le_left _ _

lemma growthA_le_series {b γlo : ℝ} :
    growthA γlo b ≤ (1 / 8) * fourthRoot (alphaSeq b γlo) * fourthGap γlo := min_le_right _ _

lemma growthA_le_eighth {b γlo : ℝ} (hb : 0 ≤ b) (hγlo : 0 < γlo) : growthA γlo b ≤ 1 / 8 := by
  have hfr : fourthRoot (alphaSeq b γlo) ≤ 1 := by
    have hα : alphaSeq b γlo ≤ 1 := alphaSeq_le_one hb hγlo
    have h1 : fourthRoot (alphaSeq b γlo) ≤ fourthRoot 1 := fourthRoot_mono hα
    simpa [fourthRoot_one] using h1
  have hgap : fourthGap γlo ≤ 1 := by
    unfold fourthGap
    have : 0 ≤ (fourthRoot (1 + γlo))⁻¹ := inv_nonneg.mpr (fourthRoot_nonneg _)
    linarith only [this]
  have hmul : (1 / 8) * fourthRoot (alphaSeq b γlo) * fourthGap γlo ≤ 1 / 8 := by
    have h18 : (0 : ℝ) ≤ 1 / 8 := by norm_num
    have hprod : fourthRoot (alphaSeq b γlo) * fourthGap γlo ≤ 1 := by
      have hgap0 : 0 ≤ fourthGap γlo := by
        have hpos := fourthGap_pos hγlo
        linarith only [hpos]
      calc fourthRoot (alphaSeq b γlo) * fourthGap γlo
          ≤ 1 * fourthGap γlo :=
            mul_le_mul_of_nonneg_right hfr hgap0
        _ = fourthGap γlo := by ring
        _ ≤ 1 := hgap
    calc (1 / 8) * fourthRoot (alphaSeq b γlo) * fourthGap γlo
        = (1 / 8) * (fourthRoot (alphaSeq b γlo) * fourthGap γlo) := by ring
      _ ≤ (1 / 8) * 1 := mul_le_mul_of_nonneg_left hprod h18
      _ = 1 / 8 := by ring
  exact le_trans growthA_le_series hmul

noncomputable def logNeed (a b f : ℝ) : ℝ :=
  max (4 * b) (max (2 * b / (1 - a * f)) 1)

noncomputable def growthN (a b f : ℝ) : ℕ :=
  max 3 (max (Nat.ceil (Real.exp (logNeed a b f)))
    (max (Nat.ceil ((fShrink a f)⁻¹)) (Nat.ceil (2 / f) + 1)))

lemma log_ge_need {a b f : ℝ} {n : ℕ} (hn : growthN a b f ≤ n) :
    logNeed a b f ≤ Real.log (n : ℝ) := by
  have hceil : Nat.ceil (Real.exp (logNeed a b f)) ≤ n :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn)
  have hcast : Real.exp (logNeed a b f) ≤ (n : ℝ) := (Nat.ceil_le).mp hceil
  have hlog := Real.log_le_log (Real.exp_pos _) hcast
  rw [Real.log_exp] at hlog
  exact hlog

lemma log_pos_of_large {a b f : ℝ} {n : ℕ} (hn : growthN a b f ≤ n) :
    0 < Real.log (n : ℝ) := by
  have h1 : (1 : ℝ) ≤ Real.log n := by
    have hneed : (1 : ℝ) ≤ logNeed a b f :=
      le_trans (le_max_right (2 * b / (1 - a * f)) 1) (le_max_right (4 * b) _)
    exact le_trans hneed (log_ge_need hn)
  linarith only [h1]

lemma n_cast_pos {a b f : ℝ} {n : ℕ} (hn : growthN a b f ≤ n) : 0 < (n : ℝ) := by
  have h3 : (3 : ℕ) ≤ n := le_trans (Nat.le_max_left _ _) hn
  exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 3) h3)

lemma blog_quarter {a b f : ℝ} {n : ℕ} (hn : growthN a b f ≤ n) :
    b / Real.log n ≤ 1 / 4 := by
  have hpos := log_pos_of_large hn
  have h4 : 4 * b ≤ Real.log n := le_trans (le_max_left _ _) (log_ge_need hn)
  rw [div_le_iff₀ hpos]
  linarith only [h4]

lemma blog_connect {a b f : ℝ} {n : ℕ} (haf : a * f < 1) (hn : growthN a b f ≤ n) :
    b / Real.log n ≤ (1 - a * f) / 2 := by
  have hpos := log_pos_of_large hn
  have hden : 0 < 1 - a * f := by linarith only [haf]
  have hneed : 2 * b / (1 - a * f) ≤ Real.log n :=
    le_trans (le_max_left (2 * b / (1 - a * f)) 1)
      (le_trans (le_max_right (4 * b) _) (log_ge_need hn))
  have hmul : 2 * b ≤ Real.log n * (1 - a * f) := by
    rwa [div_le_iff₀ hden] at hneed
  rw [div_le_iff₀ hpos]
  linarith only [hmul]

lemma shrink_n_ge_one {a b f : ℝ} {n : ℕ} (hf0 : 0 < f) (ha : 0 ≤ a)
    (hn : growthN a b f ≤ n) : 1 ≤ fShrink a f * n := by
  have hceil : Nat.ceil ((fShrink a f)⁻¹) ≤ n := by
    calc Nat.ceil ((fShrink a f)⁻¹)
        ≤ max (Nat.ceil ((fShrink a f)⁻¹)) (Nat.ceil (2 / f) + 1) := le_max_left _ _
      _ ≤ max (Nat.ceil (Real.exp (logNeed a b f)))
            (max (Nat.ceil ((fShrink a f)⁻¹)) (Nat.ceil (2 / f) + 1)) := le_max_right _ _
      _ ≤ growthN a b f := le_max_right _ _
      _ ≤ n := hn
  have hinv : (fShrink a f)⁻¹ ≤ (n : ℝ) := (Nat.ceil_le).mp hceil
  have hf' : 0 < fShrink a f := fShrink_pos hf0 ha
  calc (1 : ℝ) = fShrink a f * (fShrink a f)⁻¹ := (mul_inv_cancel₀ hf'.ne').symm
    _ ≤ fShrink a f * n := mul_le_mul_of_nonneg_left hinv hf'.le

lemma n_gt_two_div_f {a b f : ℝ} {n : ℕ} (hn : growthN a b f ≤ n) : 2 / f < (n : ℝ) := by
  have hceil : Nat.ceil (2 / f) + 1 ≤ n := by
    calc Nat.ceil (2 / f) + 1
        ≤ max (Nat.ceil ((fShrink a f)⁻¹)) (Nat.ceil (2 / f) + 1) := le_max_right _ _
      _ ≤ max (Nat.ceil (Real.exp (logNeed a b f)))
            (max (Nat.ceil ((fShrink a f)⁻¹)) (Nat.ceil (2 / f) + 1)) := le_max_right _ _
      _ ≤ growthN a b f := le_max_right _ _
      _ ≤ n := hn
  have hle : 2 / f ≤ (Nat.ceil (2 / f) : ℝ) := Nat.le_ceil _
  have hcast : ((Nat.ceil (2 / f) + 1 : ℕ) : ℝ) ≤ n := Nat.cast_le.mpr hceil
  have hlt : (Nat.ceil (2 / f) : ℝ) < ((Nat.ceil (2 / f) + 1 : ℕ) : ℝ) :=
    Nat.cast_lt.mpr (Nat.lt_succ_self _)
  linarith only [hle, hlt, hcast]

lemma shrink_slack {a b f : ℝ} {n : ℕ} (hf0 : 0 < f) (hn : growthN a b f ≤ n) :
    fShrink a f * n + 1 < f * n := by
  have hlt := n_gt_two_div_f (a := a) (b := b) hn
  have hmul : fShrink a f * n ≤ (f / 2) * n :=
    mul_le_mul_of_nonneg_right (fShrink_le_half (a := a) (f := f)) (Nat.cast_nonneg n)
  have hhalf : (f / 2) * n + 1 < f * n := by
    have htwo : (2 : ℝ) < f * n := by
      rw [div_lt_iff₀ hf0] at hlt
      simpa [mul_comm] using hlt
    linarith only [htwo]
  linarith only [hmul, hhalf]

lemma pow_le_of_logb {ρ x : ℝ} {j : ℕ} (hρ : 1 < ρ) (hx : 0 < x)
    (hj : (j : ℝ) ≤ Real.logb ρ x) : ρ ^ j ≤ x := by
  have hlog : 0 < Real.log ρ := Real.log_pos hρ
  rw [Real.logb, le_div_iff₀ hlog] at hj
  have hexp := (Real.exp_le_exp).mpr hj
  rwa [Real.exp_nat_mul (Real.log ρ) j, Real.exp_log (by linarith only [hρ] : 0 < ρ),
    Real.exp_log hx] at hexp

lemma lt_pow_of_logb {ρ x : ℝ} {j : ℕ} (hρ : 1 < ρ) (hx : 0 < x)
    (hj : Real.logb ρ x < (j : ℝ)) : x < ρ ^ j := by
  have hlog : 0 < Real.log ρ := Real.log_pos hρ
  rw [Real.logb, div_lt_iff₀ hlog] at hj
  have hexp := (Real.exp_lt_exp).mpr hj
  rwa [Real.exp_nat_mul (Real.log ρ) j, Real.exp_log (by linarith only [hρ] : 0 < ρ),
    Real.exp_log hx] at hexp

lemma logb_nonneg_of_one_le {ρ x : ℝ} (hρ : 1 < ρ) (hx : 1 ≤ x) : 0 ≤ Real.logb ρ x := by
  have hlogρ : 0 < Real.log ρ := Real.log_pos hρ
  have hlogx : 0 ≤ Real.log x := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1) hx
    simpa using h
  exact div_nonneg hlogx hlogρ.le

noncomputable def phaseCount (γ a f : ℝ) (n : ℕ) : ℕ :=
  Nat.floor (Real.logb (1 + γ) (fShrink a f * n))

lemma phaseCount_pow_le {γ a f : ℝ} {n : ℕ} (hγ : 0 < γ) (hfn : 1 ≤ fShrink a f * n) :
    (1 + γ) ^ phaseCount γ a f n ≤ fShrink a f * n := by
  have hρ : 1 < 1 + γ := by linarith only [hγ]
  have hlog0 : 0 ≤ Real.logb (1 + γ) (fShrink a f * n) := logb_nonneg_of_one_le hρ hfn
  have hj : (phaseCount γ a f n : ℝ) ≤ Real.logb (1 + γ) (fShrink a f * n) :=
    Nat.floor_le hlog0
  exact pow_le_of_logb hρ (by linarith only [hfn]) hj

lemma phaseCount_succ_gt {γ a f : ℝ} {n : ℕ} (hγ : 0 < γ) (hfn : 1 ≤ fShrink a f * n) :
    fShrink a f * n < (1 + γ) ^ (phaseCount γ a f n + 1) := by
  have hρ : 1 < 1 + γ := by linarith only [hγ]
  have hx : 0 < fShrink a f * n := by linarith only [hfn]
  have hlt : Real.logb (1 + γ) (fShrink a f * n) < (phaseCount γ a f n + 1 : ℝ) := by
    have hEq : (phaseCount γ a f n : ℝ) + 1 = (phaseCount γ a f n + 1 : ℝ) := by
      rw [Nat.cast_add, Nat.cast_one]
    rw [← hEq]
    simpa [phaseCount] using Nat.lt_floor_add_one (Real.logb (1 + γ) (fShrink a f * n))
  exact lt_pow_of_logb hρ hx hlt

noncomputable def gammaFactor (γ b : ℝ) (n : ℕ) : ℝ :=
  1 + γ - γ * b / Real.log n

lemma gammaFactor_ge_one {γ b : ℝ} {n : ℕ} (hγ : 0 ≤ γ)
    (hblog : b / Real.log n ≤ 1 / 4) : 1 ≤ gammaFactor γ b n := by
  unfold gammaFactor
  have hsub : γ * b / Real.log n ≤ γ / 4 := by
    have hident : γ * b / Real.log n = γ * (b / Real.log n) := by ring
    have hmul := mul_le_mul_of_nonneg_left hblog hγ
    linarith only [hident, hmul]
  linarith only [hsub, hγ]

lemma gammaFactor_ratio {γ b : ℝ} {n : ℕ} (hγ : 0 ≤ γ)
    (hblog : b / Real.log n ≤ 1 / 4) : γ ≤ (4 / 3) * gammaFactor γ b n := by
  have hsub : γ * b / Real.log n ≤ γ / 4 := by
    have hident : γ * b / Real.log n = γ * (b / Real.log n) := by ring
    have hmul := mul_le_mul_of_nonneg_left hblog hγ
    linarith only [hident, hmul]
  have hthree : (3 / 4) * γ ≤ gammaFactor γ b n := by
    unfold gammaFactor
    linarith only [hsub]
  have h43 : (0 : ℝ) ≤ 4 / 3 := by norm_num
  have hmul := mul_le_mul_of_nonneg_left hthree h43
  have hform : (4 / 3) * ((3 / 4) * γ) = γ := by ring
  linarith only [hmul, hform]

noncomputable def etaTerm (γ a b A : ℝ) (n : ℕ) (k : ℝ) : ℝ :=
  γ * (a + 1) * k / (gammaFactor γ b n * n) +
    A / (gammaFactor γ b n * fourthRoot k)

lemma k_div_fourthRoot {k : ℝ} (hk : 1 ≤ k) : k / fourthRoot k = threeFourth k := by
  have hfr : fourthRoot k ≠ 0 := by
    have h1 := fourthRoot_ge_one hk
    linarith only [h1]
  rw [div_eq_iff hfr]
  exact (threeFourth_split hk).symm

lemma growthStep_factor {γ a b A : ℝ} {n : ℕ} {k : ℝ} (hk : 1 ≤ k)
    (hΓ : gammaFactor γ b n ≠ 0) (hn : (n : ℝ) ≠ 0) (hlog : Real.log n ≠ 0) :
    k + growthE0 γ a b A n k =
      gammaFactor γ b n * k * (1 - etaTerm γ a b A n k) := by
  have hthree := k_div_fourthRoot hk
  have hfr : fourthRoot k ≠ 0 := by
    have h1 := fourthRoot_ge_one hk
    linarith only [h1]
  have hL : k + growthE0 γ a b A n k =
      gammaFactor γ b n * k - γ * (a + 1) * k ^ 2 / n - A * threeFourth k := by
    unfold growthE0 growthE gammaFactor
    field_simp [hn, hlog]
    ring
  have hR : gammaFactor γ b n * k * (1 - etaTerm γ a b A n k) =
      gammaFactor γ b n * k - γ * (a + 1) * k ^ 2 / n - A * (k / fourthRoot k) := by
    unfold etaTerm
    field_simp [hΓ, hn, hlog, hfr]
    ring
  rw [hL, hR, hthree]

noncomputable def kSeq (γ a b A : ℝ) (n : ℕ) : ℕ → ℝ
  | 0 => 1
  | j + 1 => kSeq γ a b A n j + growthE0 γ a b A n (kSeq γ a b A n j)

lemma kSeq_in_range {γlo γ a b f : ℝ} {n : ℕ} (hγlo : 0 < γlo) (hγ : γlo ≤ γ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hf0 : 0 < f) (hn : growthN a b f ≤ n) (j : ℕ)
    (hj : j ≤ phaseCount γ a f n) :
    1 ≤ kSeq γ a b (growthA γlo b) n j ∧
      kSeq γ a b (growthA γlo b) n j ≤ (1 + γ) ^ j := by
  have hγ0 : 0 ≤ γ := le_trans hγlo.le hγ
  have hγpos : 0 < γ := lt_of_lt_of_le hγlo hγ
  have hAγ : growthA γlo b ≤ γ / 6 := by
    have h6 : (0 : ℝ) ≤ 6 := by norm_num
    exact le_trans growthA_le_gamma (div_le_div_of_nonneg_right hγ h6)
  have hA0 : 0 ≤ growthA γlo b := (growthA_pos (b := b) hγlo).le
  have hfn := shrink_n_ge_one hf0 ha hn
  have hJ := phaseCount_pow_le hγpos hfn
  have hblog := blog_quarter (a := a) (b := b) (f := f) hn
  have hlog := log_pos_of_large (a := a) (b := b) (f := f) hn
  have hnpos := n_cast_pos (a := a) (b := b) (f := f) hn
  have hf' := fShrink_a_le (a := a) (f := f) ha
  induction j with
  | zero =>
    simp [kSeq]
  | succ j ih =>
    have hj' : j ≤ phaseCount γ a f n := Nat.le_of_succ_le hj
    obtain ⟨hk1, hkρ⟩ := ih hj'
    have hpow : (1 + γ) ^ j ≤ (1 + γ) ^ phaseCount γ a f n :=
      pow_le_pow_right₀ (by linarith only [hγpos]) hj'
    have hkf : kSeq γ a b (growthA γlo b) n j ≤ fShrink a f * n :=
      le_trans hkρ (le_trans hpow hJ)
    have hElow := growthE0_lower hγ0 hk1 hkf ha hAγ hnpos hblog hf'
    have hElin := growthE_le_linear hγ0 (by linarith only [hk1]) ha hb hnpos hlog
    have hE0le : growthE0 γ a b (growthA γlo b) n (kSeq γ a b (growthA γlo b) n j) ≤
        γ * kSeq γ a b (growthA γlo b) n j := by
      have hnn : 0 ≤ growthA γlo b * threeFourth (kSeq γ a b (growthA γlo b) n j) :=
        mul_nonneg hA0 (threeFourth_nonneg _)
      unfold growthE0
      linarith only [hElin, hnn]
    refine ⟨?_, ?_⟩
    · have hdef : kSeq γ a b (growthA γlo b) n (j + 1) =
          kSeq γ a b (growthA γlo b) n j +
            growthE0 γ a b (growthA γlo b) n (kSeq γ a b (growthA γlo b) n j) := rfl
      have hpos : 0 ≤ growthE0 γ a b (growthA γlo b) n (kSeq γ a b (growthA γlo b) n j) := by
        have h11 : 0 ≤ γ * kSeq γ a b (growthA γlo b) n j * (11 / 24) :=
          mul_nonneg (mul_nonneg hγ0 (by linarith only [hk1])) (by norm_num)
        linarith only [hElow, h11]
      linarith only [hk1, hpos, hdef]
    · have hdef : kSeq γ a b (growthA γlo b) n (j + 1) =
          kSeq γ a b (growthA γlo b) n j +
            growthE0 γ a b (growthA γlo b) n (kSeq γ a b (growthA γlo b) n j) := rfl
      have hstep : kSeq γ a b (growthA γlo b) n j +
            growthE0 γ a b (growthA γlo b) n (kSeq γ a b (growthA γlo b) n j) ≤
          (1 + γ) * kSeq γ a b (growthA γlo b) n j := by
        linarith only [hE0le]
      have hmul : (1 + γ) * kSeq γ a b (growthA γlo b) n j ≤ (1 + γ) * (1 + γ) ^ j :=
        mul_le_mul_of_nonneg_left hkρ (by linarith only [hγpos])
      have hpow' : (1 + γ) * (1 + γ) ^ j = (1 + γ) ^ (j + 1) := by ring
      linarith only [hdef, hstep, hmul, hpow']

end Epidemics.Revisited
