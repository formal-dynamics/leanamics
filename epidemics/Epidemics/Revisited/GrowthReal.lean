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
  -- `(k + 1 : ℝ)` elaborates as `↑k + 1`, while `lt_pow_of_logb` needs `↑(k + 1)`.
  have hlt : Real.logb (1 + γ) (fShrink a f * n) < (phaseCount γ a f n : ℝ) + 1 := by
    simpa [phaseCount] using Nat.lt_floor_add_one (Real.logb (1 + γ) (fShrink a f * n))
  rw [← Nat.cast_add_one] at hlt
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

lemma fShrink_le_one {a f : ℝ} (ha : 0 ≤ a) : fShrink a f ≤ 1 := by
  have hle : fShrink a f ≤ 1 / (8 * (a + 1)) := min_le_right _ _
  have ha1 : (1 : ℝ) ≤ a + 1 := by linarith only [ha]
  have hden : (8 : ℝ) ≤ 8 * (a + 1) := by nlinarith only [ha1]
  have hpos : (0 : ℝ) < 8 := by norm_num
  have hdiv : 1 / (8 * (a + 1)) ≤ 1 / 8 :=
    div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) hpos hden
  have h18 : (1 : ℝ) / 8 ≤ 1 := by norm_num
  exact le_trans (le_trans hle hdiv) h18

lemma gammaFactor_ge_scaled {γ b : ℝ} {n : ℕ} (hb : 0 ≤ b) (hlog : 0 < Real.log n) :
    (1 + γ) * (1 - b / Real.log n) ≤ gammaFactor γ b n := by
  have hL : (1 + γ) * (1 - b / Real.log n) =
      1 + γ - (1 + γ) * b / Real.log n := by field_simp [hlog.ne']
  have hγ : γ ≤ 1 + γ := by linarith
  have hmul := mul_le_mul_of_nonneg_right hγ (div_nonneg hb hlog.le)
  have hidentL : γ * b / Real.log n = γ * (b / Real.log n) := by ring
  have hidentR : (1 + γ) * b / Real.log n = (1 + γ) * (b / Real.log n) := by ring
  unfold gammaFactor
  linarith only [hL, hmul, hidentL, hidentR]

lemma one_sub_blog_pow_ge {γlo γ a b f : ℝ} {n j : ℕ} (hγlo : 0 < γlo) (hγ : γlo ≤ γ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hf0 : 0 < f) (hn : growthN a b f ≤ n)
    (hj : j ≤ phaseCount γ a f n) :
    alpha0 b γlo ≤ (1 - b / Real.log n) ^ j := by
  have hlog := log_pos_of_large (a := a) (b := b) (f := f) hn
  have hxle := blog_quarter (a := a) (b := b) (f := f) hn
  have hx0 : 0 ≤ b / Real.log n := div_nonneg hb hlog.le
  have hx12 : b / Real.log n ≤ 1 / 2 := by linarith only [hxle]
  have h1x : 0 < 1 - b / Real.log n := by linarith only [hxle]
  have hlog1x := log_one_sub_ge hx0 hx12
  have hγpos : 0 < γ := lt_of_lt_of_le hγlo hγ
  have hρlo : 1 < 1 + γlo := by linarith only [hγlo]
  have hρ : 1 < 1 + γ := by linarith only [hγpos]
  have hlogρlo : 0 < Real.log (1 + γlo) := Real.log_pos hρlo
  have hlogρ : 0 < Real.log (1 + γ) := Real.log_pos hρ
  have hfn := shrink_n_ge_one hf0 ha hn
  have hjlog : (j : ℝ) ≤ Real.log n / Real.log (1 + γlo) := by
    have hpc : (j : ℝ) ≤ (phaseCount γ a f n : ℝ) := Nat.cast_le.mpr hj
    have hfloor : (phaseCount γ a f n : ℝ) ≤ Real.logb (1 + γ) (fShrink a f * n) := by
      exact Nat.floor_le (logb_nonneg_of_one_le hρ hfn)
    have hmuln : fShrink a f * n ≤ n := by
      have h := mul_le_mul_of_nonneg_right (fShrink_le_one (f := f) ha) (Nat.cast_nonneg n)
      simpa [one_mul] using h
    have hlogle : Real.log (fShrink a f * n) ≤ Real.log n :=
      Real.log_le_log (by linarith only [hfn]) hmuln
    have hblog1 : Real.log (fShrink a f * n) / Real.log (1 + γ) ≤
        Real.log n / Real.log (1 + γ) :=
      div_le_div_of_nonneg_right hlogle hlogρ.le
    have hlogn0 : 0 ≤ Real.log n := by
      have h3 : (3 : ℕ) ≤ n := le_trans (le_max_left _ _) hn
      have h1n : (1 : ℝ) ≤ n := by exact_mod_cast le_trans (show (1 : ℕ) ≤ 3 by norm_num) h3
      have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1) h1n
      simpa using h
    have hlogργ : Real.log (1 + γlo) ≤ Real.log (1 + γ) :=
      Real.log_le_log (by linarith only [hγlo]) (by linarith only [hγ])
    have hblog2 : Real.log n / Real.log (1 + γ) ≤ Real.log n / Real.log (1 + γlo) :=
      div_le_div_of_nonneg_left hlogn0 hlogρlo hlogργ
    have hlogb_eq : Real.logb (1 + γ) (fShrink a f * n) =
        Real.log (fShrink a f * n) / Real.log (1 + γ) := rfl
    linarith only [hpc, hfloor, hblog1, hblog2, hlogb_eq]
  have hjx : (j : ℝ) * (b / Real.log n) ≤ b / Real.log (1 + γlo) := by
    have hmul := mul_le_mul_of_nonneg_right hjlog hx0
    have hcancel : Real.log n / Real.log (1 + γlo) * (b / Real.log n) =
        b / Real.log (1 + γlo) := by field_simp [hlog.ne', hlogρlo.ne']
    linarith only [hmul, hcancel]
  have hneg : -2 * (b / Real.log (1 + γlo)) ≤ -2 * ((j : ℝ) * (b / Real.log n)) := by
    have hneg2 : -(2 : ℝ) ≤ 0 := by norm_num
    have hmul := mul_le_mul_of_nonpos_left hjx hneg2
    linarith only [hmul]
  have hlogj : (j : ℝ) * (-2 * (b / Real.log n)) ≤
      (j : ℝ) * Real.log (1 - b / Real.log n) :=
    mul_le_mul_of_nonneg_left hlog1x (Nat.cast_nonneg j)
  have hassoc : (j : ℝ) * (-2 * (b / Real.log n)) = -2 * ((j : ℝ) * (b / Real.log n)) := by
    ring
  have hpow : (1 - b / Real.log n) ^ j =
      Real.exp ((j : ℝ) * Real.log (1 - b / Real.log n)) :=
    (congrArg (fun t => t ^ j) (Real.exp_log h1x)).symm.trans
      (Real.exp_nat_mul (Real.log (1 - b / Real.log n)) j).symm
  calc alpha0 b γlo
      = Real.exp (-2 * b / Real.log (1 + γlo)) := rfl
    _ = Real.exp (-2 * (b / Real.log (1 + γlo))) := by
        congr 1
        ring
    _ ≤ Real.exp (-2 * ((j : ℝ) * (b / Real.log n))) := (Real.exp_le_exp).mpr hneg
    _ ≤ Real.exp ((j : ℝ) * Real.log (1 - b / Real.log n)) := by
        rw [← hassoc]
        exact (Real.exp_le_exp).mpr hlogj
    _ = (1 - b / Real.log n) ^ j := hpow.symm

lemma phaseCount_pow_ge {γ a f : ℝ} {n : ℕ} (hγ : 0 < γ) (hfn : 1 ≤ fShrink a f * n) :
    fShrink a f * n / (1 + γ) ≤ (1 + γ) ^ phaseCount γ a f n := by
  have hρ : 1 < 1 + γ := by linarith only [hγ]
  have hlogρ : 0 < Real.log (1 + γ) := Real.log_pos hρ
  have hx : 0 < fShrink a f * n := by linarith only [hfn]
  have hJ : Real.logb (1 + γ) (fShrink a f * n) - 1 ≤ (phaseCount γ a f n : ℝ) := by
    have hlt := Nat.lt_floor_add_one (Real.logb (1 + γ) (fShrink a f * n))
    have hEq : (phaseCount γ a f n : ℝ) = Nat.floor (Real.logb (1 + γ) (fShrink a f * n)) := rfl
    linarith only [hlt, hEq]
  have hprod : (Real.logb (1 + γ) (fShrink a f * n) - 1) * Real.log (1 + γ) ≤
      (phaseCount γ a f n : ℝ) * Real.log (1 + γ) :=
    mul_le_mul_of_nonneg_right hJ hlogρ.le
  have hleft : (Real.logb (1 + γ) (fShrink a f * n) - 1) * Real.log (1 + γ) =
      Real.log (fShrink a f * n / (1 + γ)) := by
    rw [Real.logb, sub_mul, div_mul_cancel₀ _ hlogρ.ne', Real.log_div hx.ne' (by linarith only [hρ])]
    ring
  have hright : Real.exp ((phaseCount γ a f n : ℝ) * Real.log (1 + γ)) =
      (1 + γ) ^ phaseCount γ a f n := by
    rw [Real.exp_nat_mul, Real.exp_log (by linarith only [hρ])]
  have hexp := (Real.exp_le_exp).mpr hprod
  rw [hleft, Real.exp_log (by
    have : 0 < 1 + γ := by linarith only [hρ]
    exact div_pos hx this), hright] at hexp
  exact hexp

lemma kSeq_le_shrink {γlo γ a b f : ℝ} {n : ℕ} (hγlo : 0 < γlo) (hγ : γlo ≤ γ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hf0 : 0 < f) (hn : growthN a b f ≤ n)
    (j : ℕ) (hj : j ≤ phaseCount γ a f n) :
    kSeq γ a b (growthA γlo b) n j ≤ fShrink a f * n := by
  have hγpos : 0 < γ := lt_of_lt_of_le hγlo hγ
  have hfn := shrink_n_ge_one hf0 ha hn
  obtain ⟨_, hk⟩ := kSeq_in_range hγlo hγ ha hb hf0 hn j hj
  have hpow : (1 + γ) ^ j ≤ (1 + γ) ^ phaseCount γ a f n :=
    pow_le_pow_right₀ (by linarith only [hγpos]) hj
  exact le_trans hk (le_trans hpow (phaseCount_pow_le hγpos hfn))

lemma kSeq_eq_prod {γlo γ a b f : ℝ} {n : ℕ} (hγlo : 0 < γlo) (hγ : γlo ≤ γ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hf0 : 0 < f) (hn : growthN a b f ≤ n) :
    ∀ m, m ≤ phaseCount γ a f n →
      kSeq γ a b (growthA γlo b) n m =
        gammaFactor γ b n ^ m *
          ∏ i ∈ range m, (1 - etaTerm γ a b (growthA γlo b) n
            (kSeq γ a b (growthA γlo b) n i)) := by
  have hlog := log_pos_of_large (a := a) (b := b) (f := f) hn
  have hnpos := n_cast_pos (a := a) (b := b) (f := f) hn
  have hblog := blog_quarter (a := a) (b := b) (f := f) hn
  have hγ0 : 0 ≤ γ := le_trans hγlo.le hγ
  have hΓ1 : 1 ≤ gammaFactor γ b n := gammaFactor_ge_one hγ0 hblog
  have hΓ : gammaFactor γ b n ≠ 0 := by linarith only [hΓ1]
  intro m
  induction m with
  | zero =>
    intro _
    simp [kSeq]
  | succ m ih =>
    intro hm
    have hm' : m ≤ phaseCount γ a f n := Nat.le_of_succ_le hm
    have hrec := ih hm'
    obtain ⟨hk1, _⟩ := kSeq_in_range hγlo hγ ha hb hf0 hn m hm'
    have hstep : kSeq γ a b (growthA γlo b) n (m + 1) =
        gammaFactor γ b n * kSeq γ a b (growthA γlo b) n m *
          (1 - etaTerm γ a b (growthA γlo b) n (kSeq γ a b (growthA γlo b) n m)) := by
      have hdef : kSeq γ a b (growthA γlo b) n (m + 1) =
          kSeq γ a b (growthA γlo b) n m +
            growthE0 γ a b (growthA γlo b) n (kSeq γ a b (growthA γlo b) n m) := rfl
      rw [hdef]
      exact growthStep_factor hk1 hΓ hnpos.ne' hlog.ne'
    rw [hstep, prod_range_succ, hrec]
    ring

lemma etaTerm_nonneg {γ a b A : ℝ} {n : ℕ} {k : ℝ} (hγ : 0 ≤ γ) (ha : 0 ≤ a)
    (hA : 0 ≤ A) (hΓ : 0 < gammaFactor γ b n) (hn : 0 < (n : ℝ)) (hk0 : 0 < k) :
    0 ≤ etaTerm γ a b A n k := by
  have hfr : 0 < fourthRoot k := fourthRoot_pos hk0
  have hden1 : 0 < gammaFactor γ b n * n := mul_pos hΓ hn
  have hden2 : 0 < gammaFactor γ b n * fourthRoot k := mul_pos hΓ hfr
  have h1 : 0 ≤ γ * (a + 1) * k / (gammaFactor γ b n * n) := by positivity
  have h2 : 0 ≤ A / (gammaFactor γ b n * fourthRoot k) := div_nonneg hA hden2.le
  unfold etaTerm
  linarith only [h1, h2]

lemma etaTerm_le_half {γ a b A : ℝ} {n : ℕ} {k f' : ℝ} (hγ : 0 ≤ γ) (hk : 1 ≤ k)
    (hkf : k ≤ f' * n) (ha : 0 ≤ a) (hA0 : 0 ≤ A) (hA : A ≤ 1 / 8) (hn : 0 < (n : ℝ))
    (hblog : b / Real.log n ≤ 1 / 4) (hf' : (a + 1) * f' ≤ 1 / 8) :
    etaTerm γ a b A n k ≤ 1 / 2 := by
  have hΓ : 1 ≤ gammaFactor γ b n := gammaFactor_ge_one hγ hblog
  have hΓpos : 0 < gammaFactor γ b n := by linarith only [hΓ]
  have hratio := gammaFactor_ratio hγ hblog
  have ha1 : 0 ≤ a + 1 := by linarith only [ha]
  have hdiv : k / n ≤ f' := by
    rw [div_le_iff₀ hn]
    simpa [mul_comm] using hkf
  have hcoef : (a + 1) * k / n ≤ 1 / 8 := by
    have hmul := mul_le_mul_of_nonneg_left hdiv ha1
    have hident : (a + 1) * k / n = (a + 1) * (k / n) := by ring
    linarith only [hmul, hf', hident]
  have hγΓ : γ / gammaFactor γ b n ≤ 4 / 3 := (div_le_iff₀ hΓpos).mpr hratio
  have hcoef0 : 0 ≤ (a + 1) * k / n := by positivity
  have hfirstId : γ * (a + 1) * k / (gammaFactor γ b n * n) =
      (γ / gammaFactor γ b n) * ((a + 1) * k / n) := by
    field_simp [hΓpos.ne', hn.ne']
  have hfirst : γ * (a + 1) * k / (gammaFactor γ b n * n) ≤ (4 / 3) * (1 / 8) := by
    rw [hfirstId]
    exact mul_le_mul hγΓ hcoef hcoef0 (by norm_num)
  have hfr : 1 ≤ fourthRoot k := fourthRoot_ge_one hk
  have hden : 1 ≤ gammaFactor γ b n * fourthRoot k := by
    have hΓ0 : 0 ≤ gammaFactor γ b n := by linarith only [hΓ]
    have hmul := mul_le_mul hΓ hfr (by norm_num : (0 : ℝ) ≤ 1) hΓ0
    simpa [one_mul] using hmul
  have hsecond : A / (gammaFactor γ b n * fourthRoot k) ≤ 1 / 8 := by
    have hposden : 0 < gammaFactor γ b n * fourthRoot k := by linarith only [hden]
    have hAle : A / (gammaFactor γ b n * fourthRoot k) ≤ A / 1 :=
      div_le_div_of_nonneg_left hA0 (by norm_num : (0 : ℝ) < 1) hden
    have hA1 : A / 1 = A := by ring
    linarith only [hAle, hA1, hA]
  have hnum : (4 / 3) * (1 / 8) + 1 / 8 ≤ 1 / 2 := by norm_num
  unfold etaTerm
  linarith only [hfirst, hsecond, hnum]

lemma sum_eta_linear_le {γlo γ a b f : ℝ} {n : ℕ} (hγlo : 0 < γlo) (hγ : γlo ≤ γ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hf0 : 0 < f) (hn : growthN a b f ≤ n)
    (m : ℕ) (hm : m ≤ phaseCount γ a f n) :
    ∑ i ∈ range m, γ * (a + 1) * kSeq γ a b (growthA γlo b) n i / n ≤ 1 / 8 := by
  have hγpos : 0 < γ := lt_of_lt_of_le hγlo hγ
  have hρ : 1 < 1 + γ := by linarith only [hγpos]
  have hfn := shrink_n_ge_one hf0 ha hn
  have hnpos := n_cast_pos (a := a) (b := b) (f := f) hn
  have hf' := fShrink_a_le (a := a) (f := f) ha
  have hsumρ : ∑ i ∈ range m, (1 + γ) ^ i ≤ (1 + γ) ^ m / γ := by
    have h := geom_sum_le_div hρ m
    simpa [show (1 + γ) - 1 = γ by ring] using h
  have hk : ∀ i ∈ range m, kSeq γ a b (growthA γlo b) n i ≤ (1 + γ) ^ i := by
    intro i hi
    have hiP : i ≤ phaseCount γ a f n := le_trans (Nat.le_of_lt (mem_range.mp hi)) hm
    exact (kSeq_in_range hγlo hγ ha hb hf0 hn i hiP).2
  have hsumk : ∑ i ∈ range m, kSeq γ a b (growthA γlo b) n i ≤
      ∑ i ∈ range m, (1 + γ) ^ i := sum_le_sum hk
  have hpow : (1 + γ) ^ m ≤ fShrink a f * n := by
    have hle : (1 + γ) ^ m ≤ (1 + γ) ^ phaseCount γ a f n :=
      pow_le_pow_right₀ (by linarith only [hγpos]) hm
    exact le_trans hle (phaseCount_pow_le hγpos hfn)
  have ha1 : 0 ≤ a + 1 := by linarith only [ha]
  have hfactor : 0 ≤ γ * (a + 1) / n := by positivity
  have hsumId : ∑ i ∈ range m, γ * (a + 1) * kSeq γ a b (growthA γlo b) n i / n =
      (γ * (a + 1) / n) * ∑ i ∈ range m, kSeq γ a b (growthA γlo b) n i := by
    rw [mul_sum]
    refine sum_congr rfl ?_
    intro i _
    field_simp [hnpos.ne']
  have hbound : (γ * (a + 1) / n) * ∑ i ∈ range m, kSeq γ a b (growthA γlo b) n i ≤
      (γ * (a + 1) / n) * ((1 + γ) ^ m / γ) :=
    mul_le_mul_of_nonneg_left (le_trans hsumk hsumρ) hfactor
  have hcancel : (γ * (a + 1) / n) * ((1 + γ) ^ m / γ) = (a + 1) * (1 + γ) ^ m / n := by
    field_simp [hγpos.ne', hnpos.ne']
  have hlast : (a + 1) * (1 + γ) ^ m / n ≤ (a + 1) * fShrink a f := by
    rw [div_le_iff₀ hnpos]
    have hmul := mul_le_mul_of_nonneg_left hpow ha1
    linarith only [hmul]
  linarith only [hsumId, hbound, hcancel, hlast, hf']

lemma sum_eta_fourth_le {γlo γ a b : ℝ} {n : ℕ} (hγlo : 0 < γlo) (hγ : γlo ≤ γ)
    (m : ℕ)
    (hk : ∀ i < m, alphaSeq b γlo * (1 + γ) ^ i ≤ kSeq γ a b (growthA γlo b) n i) :
    ∑ i ∈ range m,
      growthA γlo b / fourthRoot (kSeq γ a b (growthA γlo b) n i) ≤ 1 / 8 := by
  have hγpos : 0 < γ := lt_of_lt_of_le hγlo hγ
  have hρ0 : 0 ≤ 1 + γ := by linarith only [hγpos]
  have hA0 : 0 ≤ growthA γlo b := (growthA_pos (b := b) hγlo).le
  have hα : 0 < alphaSeq b γlo := alphaSeq_pos b γlo
  have hfrα : 0 < fourthRoot (alphaSeq b γlo) := fourthRoot_pos hα
  have hr1 : (fourthRoot (1 + γlo))⁻¹ < 1 := by
    have h1 : 1 < 1 + γlo := by linarith only [hγlo]
    have hge : 1 ≤ fourthRoot (1 + γlo) := fourthRoot_ge_one h1.le
    have hne : fourthRoot (1 + γlo) ≠ 1 := by
      intro h
      have h4 := fourthRoot_four (x := 1 + γlo) (by linarith only [hγlo])
      rw [h] at h4
      have hone : (1 : ℝ) ^ 4 = 1 := by norm_num
      linarith only [h4, hone, hγlo]
    rw [inv_lt_one_iff₀]
    right
    exact lt_of_le_of_ne hge (Ne.symm hne)
  have hr0 : 0 ≤ (fourthRoot (1 + γlo))⁻¹ := inv_nonneg.mpr (fourthRoot_nonneg _)
  have hterm : ∀ i ∈ range m, growthA γlo b / fourthRoot (kSeq γ a b (growthA γlo b) n i) ≤
      (growthA γlo b * (fourthRoot (alphaSeq b γlo))⁻¹) *
        (fourthRoot (1 + γlo))⁻¹ ^ i := by
    intro i hi
    have hi' : i < m := mem_range.mp hi
    have hki := hk i hi'
    have hlow0 : 0 < alphaSeq b γlo * (1 + γ) ^ i :=
      mul_pos hα (pow_pos (by linarith only [hγpos]) i)
    have hfrle : fourthRoot (alphaSeq b γlo * (1 + γ) ^ i) ≤
        fourthRoot (kSeq γ a b (growthA γlo b) n i) := fourthRoot_mono hki
    have hsplit : fourthRoot (alphaSeq b γlo * (1 + γ) ^ i) =
        fourthRoot (alphaSeq b γlo) * fourthRoot (1 + γ) ^ i := by
      rw [fourthRoot_mul hα.le, fourthRoot_pow (1 + γ) hρ0 i]
    have hposLow : 0 < fourthRoot (alphaSeq b γlo * (1 + γ) ^ i) := by
      rw [hsplit]
      exact mul_pos hfrα (pow_pos (fourthRoot_pos (by linarith only [hγpos])) i)
    have hposK : 0 < fourthRoot (kSeq γ a b (growthA γlo b) n i) :=
      lt_of_lt_of_le hposLow hfrle
    have hinv : (fourthRoot (kSeq γ a b (growthA γlo b) n i))⁻¹ ≤
        (fourthRoot (alphaSeq b γlo * (1 + γ) ^ i))⁻¹ :=
      (inv_le_inv₀ hposK hposLow).mpr hfrle
    have hinvSplit : (fourthRoot (alphaSeq b γlo * (1 + γ) ^ i))⁻¹ =
        (fourthRoot (alphaSeq b γlo))⁻¹ * (fourthRoot (1 + γ))⁻¹ ^ i := by
      rw [hsplit, mul_inv, ← inv_pow]
    have hrγ : (fourthRoot (1 + γ))⁻¹ ≤ (fourthRoot (1 + γlo))⁻¹ :=
      (inv_le_inv₀ (fourthRoot_pos (by linarith only [hγpos]))
        (fourthRoot_pos (by linarith only [hγlo]))).mpr
        (fourthRoot_mono (by linarith only [hγ]))
    have hrpow : (fourthRoot (1 + γ))⁻¹ ^ i ≤ (fourthRoot (1 + γlo))⁻¹ ^ i :=
      pow_le_pow_left₀ (inv_nonneg.mpr (fourthRoot_nonneg _)) hrγ i
    have hAle : growthA γlo b * (fourthRoot (kSeq γ a b (growthA γlo b) n i))⁻¹ ≤
        growthA γlo b * ((fourthRoot (alphaSeq b γlo))⁻¹ * (fourthRoot (1 + γ))⁻¹ ^ i) :=
      mul_le_mul_of_nonneg_left (by rw [← hinvSplit]; exact hinv) hA0
    have hAle2 : growthA γlo b *
          ((fourthRoot (alphaSeq b γlo))⁻¹ * (fourthRoot (1 + γ))⁻¹ ^ i) ≤
        growthA γlo b * ((fourthRoot (alphaSeq b γlo))⁻¹ * (fourthRoot (1 + γlo))⁻¹ ^ i) := by
      have hc : 0 ≤ (fourthRoot (alphaSeq b γlo))⁻¹ := inv_nonneg.mpr (fourthRoot_nonneg _)
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrpow hc) hA0
    have hdiv : growthA γlo b / fourthRoot (kSeq γ a b (growthA γlo b) n i) =
        growthA γlo b * (fourthRoot (kSeq γ a b (growthA γlo b) n i))⁻¹ := by
      rw [div_eq_mul_inv]
    have hring : (growthA γlo b * (fourthRoot (alphaSeq b γlo))⁻¹) *
          (fourthRoot (1 + γlo))⁻¹ ^ i =
        growthA γlo b * ((fourthRoot (alphaSeq b γlo))⁻¹ * (fourthRoot (1 + γlo))⁻¹ ^ i) := by
      ring
    linarith only [hdiv, hAle, hAle2, hring]
  have hsum := sum_le_sum hterm
  have hfactor : ∑ i ∈ range m, (growthA γlo b * (fourthRoot (alphaSeq b γlo))⁻¹) *
        (fourthRoot (1 + γlo))⁻¹ ^ i =
      (growthA γlo b * (fourthRoot (alphaSeq b γlo))⁻¹) *
        ∑ i ∈ range m, (fourthRoot (1 + γlo))⁻¹ ^ i := by
    rw [← mul_sum]
  have hgeom := geom_partial_le hr0 hr1 m
  have hc0 : 0 ≤ growthA γlo b * (fourthRoot (alphaSeq b γlo))⁻¹ :=
    mul_nonneg hA0 (inv_nonneg.mpr (fourthRoot_nonneg _))
  have hmul := mul_le_mul_of_nonneg_left hgeom hc0
  have hgap : 1 - (fourthRoot (1 + γlo))⁻¹ = fourthGap γlo := rfl
  have hconst : growthA γlo b * (fourthRoot (alphaSeq b γlo))⁻¹ * (fourthGap γlo)⁻¹ ≤ 1 / 8 := by
    have hden : 0 < fourthRoot (alphaSeq b γlo) * fourthGap γlo :=
      mul_pos hfrα (fourthGap_pos hγlo)
    rw [show growthA γlo b * (fourthRoot (alphaSeq b γlo))⁻¹ * (fourthGap γlo)⁻¹ =
        growthA γlo b / (fourthRoot (alphaSeq b γlo) * fourthGap γlo) by
      rw [div_eq_mul_inv, mul_inv]; ring]
    rw [div_le_iff₀ hden]
    have hseries := growthA_le_series (b := b) (γlo := γlo)
    have hassoc : (1 / 8) * fourthRoot (alphaSeq b γlo) * fourthGap γlo =
        (1 / 8) * (fourthRoot (alphaSeq b γlo) * fourthGap γlo) := by ring
    linarith only [hseries, hassoc]
  have hgeom' : (growthA γlo b * (fourthRoot (alphaSeq b γlo))⁻¹) *
        ∑ i ∈ range m, (fourthRoot (1 + γlo))⁻¹ ^ i ≤
      growthA γlo b * (fourthRoot (alphaSeq b γlo))⁻¹ * (fourthGap γlo)⁻¹ := by
    rw [hgap] at hmul
    exact hmul
  linarith only [hsum, hfactor, hgeom', hconst]

lemma eta_sum_le {γlo γ a b f : ℝ} {n : ℕ} (hγlo : 0 < γlo) (hγ : γlo ≤ γ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hf0 : 0 < f) (hn : growthN a b f ≤ n)
    (m : ℕ) (hm : m ≤ phaseCount γ a f n)
    (hk : ∀ i < m, alphaSeq b γlo * (1 + γ) ^ i ≤ kSeq γ a b (growthA γlo b) n i) :
    ∑ i ∈ range m, etaTerm γ a b (growthA γlo b) n (kSeq γ a b (growthA γlo b) n i) ≤
      1 / 4 := by
  have hγ0 : 0 ≤ γ := le_trans hγlo.le hγ
  have hblog := blog_quarter (a := a) (b := b) (f := f) hn
  have hnpos := n_cast_pos (a := a) (b := b) (f := f) hn
  have hΓ : 1 ≤ gammaFactor γ b n := gammaFactor_ge_one hγ0 hblog
  have hsplit : ∀ i ∈ range m, etaTerm γ a b (growthA γlo b) n
      (kSeq γ a b (growthA γlo b) n i) ≤
      γ * (a + 1) * kSeq γ a b (growthA γlo b) n i / n +
        growthA γlo b / fourthRoot (kSeq γ a b (growthA γlo b) n i) := by
    intro i hi
    have hiP : i ≤ phaseCount γ a f n := le_trans (Nat.le_of_lt (mem_range.mp hi)) hm
    obtain ⟨hk1, _⟩ := kSeq_in_range hγlo hγ ha hb hf0 hn i hiP
    have hfr : 0 < fourthRoot (kSeq γ a b (growthA γlo b) n i) := by
      have h1 := fourthRoot_ge_one hk1
      linarith only [h1]
    have hA0 : 0 ≤ growthA γlo b := (growthA_pos (b := b) hγlo).le
    have h1 : γ * (a + 1) * kSeq γ a b (growthA γlo b) n i /
        (gammaFactor γ b n * n) ≤
        γ * (a + 1) * kSeq γ a b (growthA γlo b) n i / n := by
      have ha1 : 0 ≤ a + 1 := by linarith only [ha]
      have hnum : 0 ≤ γ * (a + 1) * kSeq γ a b (growthA γlo b) n i := by positivity
      have hden : n ≤ gammaFactor γ b n * n := by
        have hone : (n : ℝ) = 1 * n := by ring
        have hmul := mul_le_mul_of_nonneg_right hΓ hnpos.le
        linarith only [hone, hmul]
      exact div_le_div_of_nonneg_left hnum hnpos hden
    have h2 : growthA γlo b /
        (gammaFactor γ b n * fourthRoot (kSeq γ a b (growthA γlo b) n i)) ≤
        growthA γlo b / fourthRoot (kSeq γ a b (growthA γlo b) n i) := by
      have hden : fourthRoot (kSeq γ a b (growthA γlo b) n i) ≤
          gammaFactor γ b n * fourthRoot (kSeq γ a b (growthA γlo b) n i) := by
        have hone : fourthRoot (kSeq γ a b (growthA γlo b) n i) =
            1 * fourthRoot (kSeq γ a b (growthA γlo b) n i) := by ring
        have hmul := mul_le_mul_of_nonneg_right hΓ
          (fourthRoot_nonneg (kSeq γ a b (growthA γlo b) n i))
        linarith only [hone, hmul]
      exact div_le_div_of_nonneg_left hA0 hfr hden
    unfold etaTerm
    linarith only [h1, h2]
  have hsum := sum_le_sum hsplit
  rw [sum_add_distrib] at hsum
  have hlin := sum_eta_linear_le hγlo hγ ha hb hf0 hn m hm
  have hfour := sum_eta_fourth_le hγlo hγ m hk
  linarith only [hsum, hlin, hfour]

lemma kSeq_lower {γlo γ a b f : ℝ} {n : ℕ} (hγlo : 0 < γlo) (hγ : γlo ≤ γ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hf0 : 0 < f) (hn : growthN a b f ≤ n) (m : ℕ)
    (hm : m ≤ phaseCount γ a f n) :
    alphaSeq b γlo * (1 + γ) ^ m ≤ kSeq γ a b (growthA γlo b) n m := by
  have hγ0 : 0 ≤ γ := le_trans hγlo.le hγ
  have hγpos : 0 < γ := lt_of_lt_of_le hγlo hγ
  have hblog := blog_quarter (a := a) (b := b) (f := f) hn
  have hlog := log_pos_of_large (a := a) (b := b) (f := f) hn
  have h1x : 0 ≤ 1 - b / Real.log n := by linarith only [hblog]
  have hΓ := gammaFactor_ge_scaled (γ := γ) (b := b) (n := n) hb hlog
  have hprodFormula := kSeq_eq_prod hγlo hγ ha hb hf0 hn
  suffices ∀ m, m ≤ phaseCount γ a f n → ∀ i, i ≤ m →
      alphaSeq b γlo * (1 + γ) ^ i ≤ kSeq γ a b (growthA γlo b) n i from
    this m hm m le_rfl
  intro m
  induction m with
  | zero =>
    intro _ i hi
    have hi0 : i = 0 := Nat.le_zero.mp hi
    subst hi0
    simp [kSeq, pow_zero]
    exact alphaSeq_le_one hb hγlo
  | succ m ih =>
    intro hm i hi
    by_cases hle : i ≤ m
    · exact ih (Nat.le_of_succ_le hm) i hle
    · have heq : i = m + 1 := le_antisymm hi (Nat.succ_le_of_lt (lt_of_not_ge hle))
      subst heq
      have hprev : ∀ j < m + 1, alphaSeq b γlo * (1 + γ) ^ j ≤
          kSeq γ a b (growthA γlo b) n j := by
        intro j hj
        exact ih (Nat.le_of_succ_le hm) j (Nat.le_of_lt_succ hj)
      have hsum := eta_sum_le hγlo hγ ha hb hf0 hn (m + 1) hm hprev
      have hη0 : ∀ i ∈ range (m + 1), 0 ≤ etaTerm γ a b (growthA γlo b) n
          (kSeq γ a b (growthA γlo b) n i) := by
        intro i hi
        have hiP : i ≤ phaseCount γ a f n := le_trans (Nat.le_of_lt (mem_range.mp hi)) hm
        obtain ⟨hk1, _⟩ := kSeq_in_range hγlo hγ ha hb hf0 hn i hiP
        have hΓ1 : 1 ≤ gammaFactor γ b n := gammaFactor_ge_one hγ0 hblog
        have hnpos := n_cast_pos (a := a) (b := b) (f := f) hn
        exact etaTerm_nonneg hγ0 ha (growthA_pos (b := b) hγlo).le
          (by linarith only [hΓ1]) hnpos (by linarith only [hk1])
      have hη1 : ∀ i ∈ range (m + 1), etaTerm γ a b (growthA γlo b) n
          (kSeq γ a b (growthA γlo b) n i) ≤ 1 := by
        intro i hi
        have hiP : i ≤ phaseCount γ a f n := le_trans (Nat.le_of_lt (mem_range.mp hi)) hm
        obtain ⟨hk1, _⟩ := kSeq_in_range hγlo hγ ha hb hf0 hn i hiP
        have hkf := kSeq_le_shrink hγlo hγ ha hb hf0 hn i hiP
        have hhalf := etaTerm_le_half hγ0 hk1 hkf ha (growthA_pos (b := b) hγlo).le
          (growthA_le_eighth hb hγlo) (n_cast_pos (a := a) (b := b) (f := f) hn) hblog
          (fShrink_a_le ha)
        linarith only [hhalf]
      have hsum1 : ∑ i ∈ range (m + 1), etaTerm γ a b (growthA γlo b) n
          (kSeq γ a b (growthA γlo b) n i) ≤ 1 := by linarith only [hsum]
      have hprod := prod_one_sub_ge hη0 hη1 hsum1
      have hhalf : (1 : ℝ) / 2 ≤ ∏ i ∈ range (m + 1), (1 - etaTerm γ a b (growthA γlo b) n
          (kSeq γ a b (growthA γlo b) n i)) := by linarith only [hsum, hprod]
      have hpowΓ : ((1 + γ) * (1 - b / Real.log n)) ^ (m + 1) ≤
          gammaFactor γ b n ^ (m + 1) :=
        pow_le_pow_left₀ (mul_nonneg (by linarith only [hγpos]) h1x) hΓ _
      have hblogpow := one_sub_blog_pow_ge hγlo hγ ha hb hf0 hn hm
      have hformula := hprodFormula (m + 1) hm
      have hbase : 0 ≤ (1 + γ) ^ (m + 1) := pow_nonneg (by linarith only [hγpos]) _
      have hΓ0 : 0 ≤ gammaFactor γ b n := by
        have hbase0 : 0 ≤ (1 + γ) * (1 - b / Real.log n) :=
          mul_nonneg (by linarith only [hγpos]) h1x
        linarith only [hbase0, hΓ]
      have hprodLe : ((1 + γ) * (1 - b / Real.log n)) ^ (m + 1) * (1 / 2) ≤
          gammaFactor γ b n ^ (m + 1) *
            ∏ i ∈ range (m + 1), (1 - etaTerm γ a b (growthA γlo b) n
              (kSeq γ a b (growthA γlo b) n i)) :=
        mul_le_mul hpowΓ hhalf (by norm_num) (pow_nonneg hΓ0 _)
      have hident : ((1 + γ) * (1 - b / Real.log n)) ^ (m + 1) =
          (1 + γ) ^ (m + 1) * (1 - b / Real.log n) ^ (m + 1) := mul_pow _ _ _
      have hαdef : alphaSeq b γlo = alpha0 b γlo * (1 / 2) := by unfold alphaSeq; ring
      have hmul := mul_le_mul_of_nonneg_right hblogpow
        (mul_nonneg hbase (by norm_num : (0 : ℝ) ≤ 1 / 2))
      have hgoal : alphaSeq b γlo * (1 + γ) ^ (m + 1) ≤
          ((1 + γ) * (1 - b / Real.log n)) ^ (m + 1) * (1 / 2) := by
        rw [hident]
        calc alphaSeq b γlo * (1 + γ) ^ (m + 1)
            = (alpha0 b γlo * (1 / 2)) * (1 + γ) ^ (m + 1) := by rw [hαdef]
          _ = alpha0 b γlo * ((1 + γ) ^ (m + 1) * (1 / 2)) := by ring
          _ ≤ (1 - b / Real.log n) ^ (m + 1) * ((1 + γ) ^ (m + 1) * (1 / 2)) := hmul
          _ = (1 + γ) ^ (m + 1) * (1 - b / Real.log n) ^ (m + 1) * (1 / 2) := by ring
      calc alphaSeq b γlo * (1 + γ) ^ (m + 1)
          ≤ ((1 + γ) * (1 - b / Real.log n)) ^ (m + 1) * (1 / 2) := hgoal
        _ ≤ gammaFactor γ b n ^ (m + 1) *
              ∏ i ∈ range (m + 1), (1 - etaTerm γ a b (growthA γlo b) n
                (kSeq γ a b (growthA γlo b) n i)) := hprodLe
        _ = kSeq γ a b (growthA γlo b) n (m + 1) := hformula.symm

lemma kSeq_phase_ge {γlo γ a b f : ℝ} {n : ℕ} (hγlo : 0 < γlo) (hγ : γlo ≤ γ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hf0 : 0 < f) (hn : growthN a b f ≤ n) :
    alphaSeq b γlo * fShrink a f * n / (1 + γ) ≤
      kSeq γ a b (growthA γlo b) n (phaseCount γ a f n) := by
  have hγpos : 0 < γ := lt_of_lt_of_le hγlo hγ
  have hfn := shrink_n_ge_one hf0 ha hn
  have hpow := phaseCount_pow_ge hγpos hfn
  have hlow := kSeq_lower hγlo hγ ha hb hf0 hn (phaseCount γ a f n) le_rfl
  have hα0 : 0 ≤ alphaSeq b γlo := (alphaSeq_pos b γlo).le
  have hmul := mul_le_mul_of_nonneg_left hpow hα0
  have hident : alphaSeq b γlo * (fShrink a f * n / (1 + γ)) =
      alphaSeq b γlo * fShrink a f * n / (1 + γ) := by
    field_simp [(by linarith only [hγpos] : (1 + γ) ≠ 0)]
  linarith only [hmul, hlow, hident]

lemma kSeq_div_ge {γlo γhi γ a b f : ℝ} {n : ℕ} (hγlo : 0 < γlo) (hγ : γlo ≤ γ)
    (hγhi : γ ≤ γhi) (ha : 0 ≤ a) (hb : 0 ≤ b) (hf0 : 0 < f) (hn : growthN a b f ≤ n) :
    alphaSeq b γlo * fShrink a f / (1 + γhi) ≤
      kSeq γ a b (growthA γlo b) n (phaseCount γ a f n) / n := by
  have hγpos : 0 < γ := lt_of_lt_of_le hγlo hγ
  have hphase := kSeq_phase_ge hγlo hγ ha hb hf0 hn
  have hnpos := n_cast_pos (a := a) (b := b) (f := f) hn
  have hdiv := div_le_div_of_nonneg_right hphase hnpos.le
  have hcancel : alphaSeq b γlo * fShrink a f * n / (1 + γ) / n =
      alphaSeq b γlo * fShrink a f / (1 + γ) := by
    field_simp [hnpos.ne', (by linarith only [hγpos] : (1 + γ) ≠ 0)]
  have hnum : 0 ≤ alphaSeq b γlo * fShrink a f :=
    mul_nonneg (alphaSeq_pos b γlo).le (fShrink_pos hf0 ha).le
  have hρ : 0 < 1 + γ := by linarith only [hγpos]
  have hργ : 1 + γ ≤ 1 + γhi := by linarith only [hγhi]
  have hshrink := div_le_div_of_nonneg_left hnum hρ hργ
  linarith only [hdiv, hcancel, hshrink]

lemma phaseCount_le_ceil {γ a b f : ℝ} {n : ℕ} (hγ : 0 < γ) (ha : 0 ≤ a) (hf0 : 0 < f)
    (hn : growthN a b f ≤ n) :
    phaseCount γ a f n ≤ Nat.ceil (Real.logb (1 + γ) (n : ℝ)) := by
  have hρ : 1 < 1 + γ := by linarith only [hγ]
  have hfn := shrink_n_ge_one hf0 ha hn
  have hmul : fShrink a f * n ≤ n := by
    have h := mul_le_mul_of_nonneg_right (fShrink_le_one (f := f) ha) (Nat.cast_nonneg n)
    simpa [one_mul] using h
  have hlog := Real.logb_le_logb_of_le hρ (by linarith only [hfn]) hmul
  simpa [phaseCount] using
    le_trans (Nat.floor_le_floor hlog) (Nat.floor_le_ceil (Real.logb (1 + γ) (n : ℝ)))

lemma nat_half_ge (r : ℕ) :
    ((r / 2 : ℕ) : ℝ) ≥ ((r : ℝ) - 1) / 2 ∧ ((r - r / 2 : ℕ) : ℝ) ≥ (r : ℝ) / 2 := by
  have hdiv : 2 * (r / 2) + r % 2 = r := Nat.div_add_mod r 2
  have hmod : r % 2 ≤ 1 := by
    have hlt : r % 2 < 2 := Nat.mod_lt r (by norm_num)
    omega
  have hcast : (r : ℝ) = 2 * ((r / 2 : ℕ) : ℝ) + ((r % 2 : ℕ) : ℝ) := by
    exact_mod_cast hdiv.symm
  have hs : ((r / 2 : ℕ) : ℝ) = ((r : ℝ) - ((r % 2 : ℕ) : ℝ)) / 2 := by
    have h2 : (2 : ℝ) ≠ 0 := by norm_num
    rw [eq_div_iff h2]
    have hcomm : ((r / 2 : ℕ) : ℝ) * 2 = 2 * ((r / 2 : ℕ) : ℝ) := by ring
    linarith only [hcast, hcomm]
  have hsub : (r : ℝ) - ((r / 2 : ℕ) : ℝ) = ((r - r / 2 : ℕ) : ℝ) :=
    (Nat.cast_sub (Nat.div_le_self r 2)).symm
  have ht : ((r - r / 2 : ℕ) : ℝ) = ((r : ℝ) + ((r % 2 : ℕ) : ℝ)) / 2 := by
    have h2 : (2 : ℝ) ≠ 0 := by norm_num
    rw [← hsub, eq_div_iff h2]
    have hcomm : ((r : ℝ) - ((r / 2 : ℕ) : ℝ)) * 2 =
        2 * ((r : ℝ) - ((r / 2 : ℕ) : ℝ)) := by ring
    linarith only [hcast, hcomm]
  have hmodR : ((r % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hmod
  constructor
  · rw [hs, ge_iff_le]
    have hden : (0 : ℝ) < 2 := by norm_num
    rw [div_le_div_iff_of_pos_right hden]
    linarith only [hmodR]
  · rw [ht, ge_iff_le]
    have hden : (0 : ℝ) < 2 := by norm_num
    rw [div_le_div_iff_of_pos_right hden]
    have hmod0 : (0 : ℝ) ≤ ((r % 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith only [hmod0]

noncomputable def sqrtGap (γlo : ℝ) : ℝ := 1 - (Real.sqrt (1 + γlo))⁻¹

lemma sqrtGap_pos {γlo : ℝ} (hγlo : 0 < γlo) : 0 < sqrtGap γlo := by
  have hsqrt : 1 < Real.sqrt (1 + γlo) := by
    simpa [Real.sqrt_one] using Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)
      (by linarith only [hγlo] : (1 : ℝ) < 1 + γlo)
  have hinv : (Real.sqrt (1 + γlo))⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]
    right
    exact hsqrt
  unfold sqrtGap
  linarith only [hinv]

noncomputable def qCap (γlo γhi b c : ℝ) : ℝ := (γhi + c) / (growthA γlo b) ^ 2

lemma qCap_pos {γlo γhi b c : ℝ} (hγlo : 0 < γlo) (hγ : γlo ≤ γhi) (hc : 0 ≤ c) :
    0 < qCap γlo γhi b c := by
  have hnum : 0 < γhi + c := by linarith only [hγlo, hγ, hc]
  have hden : 0 < (growthA γlo b) ^ 2 := pow_pos (growthA_pos (b := b) hγlo) 2
  exact div_pos hnum hden

noncomputable def qTerm (γ c A k : ℝ) : ℝ := (γ + c) / (A ^ 2 * Real.sqrt k)

lemma qTerm_nonneg {γ c A k : ℝ} (hγ : 0 ≤ γ) (hc : 0 ≤ c) :
    0 ≤ qTerm γ c A k := by
  have hden : 0 ≤ A ^ 2 * Real.sqrt k :=
    mul_nonneg (sq_nonneg A) (Real.sqrt_nonneg k)
  have hnum : 0 ≤ γ + c := by linarith only [hγ, hc]
  exact div_nonneg hnum hden

lemma qTerm_le_scaled {γ γhi c A k : ℝ} (hγ : γ ≤ γhi) (hA : A ≠ 0) (hk : 0 < k) :
    qTerm γ c A k ≤ ((γhi + c) / A ^ 2) * (Real.sqrt k)⁻¹ := by
  have hsqrt : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk
  have hA2 : 0 < A ^ 2 := by
    have hne : A ^ 2 ≠ 0 := fun h => hA (sq_eq_zero_iff.mp h)
    exact lt_of_le_of_ne (sq_nonneg A) hne.symm
  have hden : 0 < A ^ 2 * Real.sqrt k := mul_pos hA2 hsqrt
  have hnum : γ + c ≤ γhi + c := by linarith only [hγ]
  unfold qTerm
  have hle := div_le_div_of_nonneg_right hnum hden.le
  have hident : (γhi + c) / (A ^ 2 * Real.sqrt k) =
      ((γhi + c) / A ^ 2) * (Real.sqrt k)⁻¹ := by
    field_simp [hA2.ne', hsqrt.ne']
  linarith only [hle, hident]

noncomputable def tailQSum (γlo γhi b c : ℝ) : ℝ :=
  qCap γlo γhi b c * (Real.sqrt (alphaSeq b γlo))⁻¹ * (sqrtGap γlo)⁻¹

lemma inv_sqrt_kSeq_le {γlo γ a b f : ℝ} {n : ℕ} (hγlo : 0 < γlo) (hγ : γlo ≤ γ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hf0 : 0 < f) (hn : growthN a b f ≤ n)
    (j : ℕ) (hj : j ≤ phaseCount γ a f n) :
    (Real.sqrt (kSeq γ a b (growthA γlo b) n j))⁻¹ ≤
      (Real.sqrt (alphaSeq b γlo))⁻¹ * (Real.sqrt (1 + γ))⁻¹ ^ j := by
  have hγpos : 0 < γ := lt_of_lt_of_le hγlo hγ
  have hα := alphaSeq_pos b γlo
  have hlow := kSeq_lower hγlo hγ ha hb hf0 hn j hj
  have hpos : 0 < alphaSeq b γlo * (1 + γ) ^ j :=
    mul_pos hα (pow_pos (by linarith only [hγpos]) j)
  have hsqrt := Real.sqrt_le_sqrt hlow
  rw [Real.sqrt_mul hα.le, sqrt_pow (by linarith only [hγpos]) j] at hsqrt
  have hleft : 0 < Real.sqrt (alphaSeq b γlo) * Real.sqrt (1 + γ) ^ j := by
    have hrewrite : Real.sqrt (alphaSeq b γlo) * Real.sqrt (1 + γ) ^ j =
        Real.sqrt (alphaSeq b γlo * (1 + γ) ^ j) := by
      rw [Real.sqrt_mul hα.le, sqrt_pow (by linarith only [hγpos]) j]
    rw [hrewrite]
    exact Real.sqrt_pos.mpr hpos
  have hright : 0 < Real.sqrt (kSeq γ a b (growthA γlo b) n j) := lt_of_lt_of_le hleft hsqrt
  have hinv := (inv_le_inv₀ hright hleft).mpr hsqrt
  rw [mul_inv, ← inv_pow] at hinv
  exact hinv

lemma sum_inv_sqrt_kSeq_le {γlo γ a b f : ℝ} {n : ℕ} (hγlo : 0 < γlo) (hγ : γlo ≤ γ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hf0 : 0 < f) (hn : growthN a b f ≤ n)
    (m : ℕ) (hm : m ≤ phaseCount γ a f n) :
    ∑ i ∈ range m, (Real.sqrt (kSeq γ a b (growthA γlo b) n i))⁻¹ ≤
      (Real.sqrt (alphaSeq b γlo))⁻¹ * (sqrtGap γlo)⁻¹ := by
  have hγpos : 0 < γ := lt_of_lt_of_le hγlo hγ
  have hr0 : 0 ≤ (Real.sqrt (1 + γlo))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hr1 : (Real.sqrt (1 + γlo))⁻¹ < 1 := by
    have hgap := sqrtGap_pos hγlo
    unfold sqrtGap at hgap
    linarith only [hgap]
  have hterm : ∀ i ∈ range m, (Real.sqrt (kSeq γ a b (growthA γlo b) n i))⁻¹ ≤
      (Real.sqrt (alphaSeq b γlo))⁻¹ * (Real.sqrt (1 + γlo))⁻¹ ^ i := by
    intro i hi
    have hiP : i ≤ phaseCount γ a f n := le_trans (Nat.le_of_lt (mem_range.mp hi)) hm
    have hinv := inv_sqrt_kSeq_le hγlo hγ ha hb hf0 hn i hiP
    have hr : (Real.sqrt (1 + γ))⁻¹ ≤ (Real.sqrt (1 + γlo))⁻¹ := by
      have hmono : Real.sqrt (1 + γlo) ≤ Real.sqrt (1 + γ) :=
        Real.sqrt_le_sqrt (by linarith only [hγ])
      exact (inv_le_inv₀ (Real.sqrt_pos.mpr (by linarith only [hγpos]))
        (Real.sqrt_pos.mpr (by linarith only [hγlo]))).mpr hmono
    have hrpow : (Real.sqrt (1 + γ))⁻¹ ^ i ≤ (Real.sqrt (1 + γlo))⁻¹ ^ i :=
      pow_le_pow_left₀ (inv_nonneg.mpr (Real.sqrt_nonneg (1 + γ))) hr i
    have hc : 0 ≤ (Real.sqrt (alphaSeq b γlo))⁻¹ :=
      inv_nonneg.mpr (Real.sqrt_nonneg _)
    have hmul := mul_le_mul_of_nonneg_left hrpow hc
    linarith only [hinv, hmul]
  have hsum := sum_le_sum hterm
  have hfactor : ∑ i ∈ range m, (Real.sqrt (alphaSeq b γlo))⁻¹ * (Real.sqrt (1 + γlo))⁻¹ ^ i =
      (Real.sqrt (alphaSeq b γlo))⁻¹ * ∑ i ∈ range m, (Real.sqrt (1 + γlo))⁻¹ ^ i := by
    rw [← mul_sum]
  have hgeom := geom_partial_le hr0 hr1 m
  have hc0 : 0 ≤ (Real.sqrt (alphaSeq b γlo))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left hgeom hc0
  have hgap : (sqrtGap γlo)⁻¹ = (1 - (Real.sqrt (1 + γlo))⁻¹)⁻¹ := rfl
  calc ∑ i ∈ range m, (Real.sqrt (kSeq γ a b (growthA γlo b) n i))⁻¹
      ≤ ∑ i ∈ range m, (Real.sqrt (alphaSeq b γlo))⁻¹ * (Real.sqrt (1 + γlo))⁻¹ ^ i := hsum
    _ = (Real.sqrt (alphaSeq b γlo))⁻¹ * ∑ i ∈ range m, (Real.sqrt (1 + γlo))⁻¹ ^ i := hfactor
    _ ≤ (Real.sqrt (alphaSeq b γlo))⁻¹ * (1 - (Real.sqrt (1 + γlo))⁻¹)⁻¹ := hmul
    _ = (Real.sqrt (alphaSeq b γlo))⁻¹ * (sqrtGap γlo)⁻¹ := by rw [hgap]

lemma sum_qTerm_le {γlo γhi γ a b c f : ℝ} {n : ℕ} (hγlo : 0 < γlo) (hγ : γlo ≤ γ)
    (hγhi : γ ≤ γhi) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hf0 : 0 < f)
    (hn : growthN a b f ≤ n) :
    ∑ i ∈ range (phaseCount γ a f n),
        qTerm γ c (growthA γlo b) (kSeq γ a b (growthA γlo b) n i) ≤
      tailQSum γlo γhi b c := by
  have hA := growthA_pos (b := b) hγlo
  have hscale : (γ + c) / (growthA γlo b) ^ 2 ≤ qCap γlo γhi b c := by
    have hnum : γ + c ≤ γhi + c := by linarith only [hγhi]
    have hden : 0 < (growthA γlo b) ^ 2 := pow_pos hA 2
    have hdiv := div_le_div_of_nonneg_right hnum hden.le
    simpa [qCap] using hdiv
  have hsumInv := sum_inv_sqrt_kSeq_le hγlo hγ ha hb hf0 hn (phaseCount γ a f n) le_rfl
  have hfactor0 : 0 ≤ (γ + c) / (growthA γlo b) ^ 2 :=
    div_nonneg (by linarith only [hγlo, hγ, hc]) (pow_pos hA 2).le
  have hsumId : ∑ i ∈ range (phaseCount γ a f n),
        qTerm γ c (growthA γlo b) (kSeq γ a b (growthA γlo b) n i) =
      ((γ + c) / (growthA γlo b) ^ 2) *
        ∑ i ∈ range (phaseCount γ a f n),
          (Real.sqrt (kSeq γ a b (growthA γlo b) n i))⁻¹ := by
    rw [mul_sum]
    refine sum_congr rfl ?_
    intro i hi
    have hiP : i ≤ phaseCount γ a f n := Nat.le_of_lt (mem_range.mp hi)
    have hk1 := (kSeq_in_range hγlo hγ ha hb hf0 hn i hiP).1
    have hk0 : 0 < kSeq γ a b (growthA γlo b) n i := by linarith only [hk1]
    have hsqrt : 0 < Real.sqrt (kSeq γ a b (growthA γlo b) n i) := Real.sqrt_pos.mpr hk0
    unfold qTerm
    field_simp [hA.ne', hsqrt.ne']
  have hmul := mul_le_mul_of_nonneg_left hsumInv hfactor0
  have hnonneg : 0 ≤ (Real.sqrt (alphaSeq b γlo))⁻¹ * (sqrtGap γlo)⁻¹ :=
    mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg (alphaSeq b γlo)))
      (inv_nonneg.mpr (sqrtGap_pos hγlo).le)
  have hcap := mul_le_mul_of_nonneg_right hscale hnonneg
  calc ∑ i ∈ range (phaseCount γ a f n),
        qTerm γ c (growthA γlo b) (kSeq γ a b (growthA γlo b) n i)
      = ((γ + c) / (growthA γlo b) ^ 2) *
          ∑ i ∈ range (phaseCount γ a f n),
            (Real.sqrt (kSeq γ a b (growthA γlo b) n i))⁻¹ := hsumId
    _ ≤ ((γ + c) / (growthA γlo b) ^ 2) *
          ((Real.sqrt (alphaSeq b γlo))⁻¹ * (sqrtGap γlo)⁻¹) := hmul
    _ ≤ qCap γlo γhi b c * ((Real.sqrt (alphaSeq b γlo))⁻¹ * (sqrtGap γlo)⁻¹) := hcap
    _ = tailQSum γlo γhi b c := by
        unfold tailQSum
        ring

noncomputable def xDecay (γlo γhi b c : ℝ) : ℝ := 1 + 1 / (2 * qCap γlo γhi b c)

noncomputable def Qstar (γlo γhi b c : ℝ) : ℝ :=
  qCap γlo γhi b c / (1 + qCap γlo γhi b c)

lemma xDecay_gt_one {γlo γhi b c : ℝ} (hγlo : 0 < γlo) (hγ : γlo ≤ γhi) (hc : 0 ≤ c) :
    1 < xDecay γlo γhi b c := by
  have hq : 0 < qCap γlo γhi b c := qCap_pos hγlo hγ hc
  have hden : 0 < 2 * qCap γlo γhi b c := mul_pos (by norm_num) hq
  have hdiv : 0 < 1 / (2 * qCap γlo γhi b c) := div_pos (by norm_num) hden
  unfold xDecay
  linarith only [hdiv]

lemma Qstar_bounds {γlo γhi b c : ℝ} (hγlo : 0 < γlo) (hγ : γlo ≤ γhi) (hc : 0 ≤ c) :
    0 < Qstar γlo γhi b c ∧ Qstar γlo γhi b c < 1 := by
  have hq : 0 < qCap γlo γhi b c := qCap_pos hγlo hγ hc
  have hden : 0 < 1 + qCap γlo γhi b c := by linarith only [hq]
  refine ⟨div_pos hq hden, ?_⟩
  rw [Qstar, div_lt_one hden]
  linarith only [hq]

lemma xDecay_Qstar_lt_one {γlo γhi b c : ℝ} (hγlo : 0 < γlo) (hγ : γlo ≤ γhi) (hc : 0 ≤ c) :
    xDecay γlo γhi b c * Qstar γlo γhi b c < 1 := by
  have hq : 0 < qCap γlo γhi b c := qCap_pos hγlo hγ hc
  have h1 : 0 < 1 + qCap γlo γhi b c := by linarith only [hq]
  have h2 : 0 < 2 * qCap γlo γhi b c := mul_pos (by norm_num) hq
  have hden : 0 < 2 * (1 + qCap γlo γhi b c) := mul_pos (by norm_num) h1
  have hL : xDecay γlo γhi b c * Qstar γlo γhi b c =
      (2 * qCap γlo γhi b c + 1) / (2 * (1 + qCap γlo γhi b c)) := by
    unfold xDecay Qstar
    field_simp [hq.ne', h1.ne', h2.ne']
  have hlt : (2 * qCap γlo γhi b c + 1) / (2 * (1 + qCap γlo γhi b c)) < 1 := by
    rw [div_lt_one hden]
    linarith only [hq]
  linarith only [hL, hlt]

lemma Qof_mono {q Qs : ℝ} (hq0 : 0 ≤ q) (hQ : q ≤ Qs) :
    q / (1 + q) ≤ Qs / (1 + Qs) := by
  have h1 : 0 < 1 + q := by linarith only [hq0]
  have h2 : 0 < 1 + Qs := by linarith only [hq0, hQ]
  rw [div_le_div_iff₀ h1 h2]
  nlinarith only [hQ]

lemma ratio_le_exp {Q x Qs : ℝ} (hx : 1 ≤ x) (hxQ : x * Qs < 1)
    (hQ0 : 0 ≤ Q) (hQ : Q ≤ Qs) :
    (1 - Q) / (1 - x * Q) ≤ Real.exp (((x - 1) / (1 - x * Qs)) * Q) := by
  have hxQ' : x * Q ≤ x * Qs := mul_le_mul_of_nonneg_left hQ (by linarith only [hx])
  have hden : 0 < 1 - x * Q := by linarith only [hxQ', hxQ]
  have hdenS : 0 < 1 - x * Qs := by linarith only [hxQ]
  have hQ1 : Q ≤ x * Q := by
    have hmul := mul_le_mul_of_nonneg_left hx hQ0
    have hone : Q = Q * 1 := by ring
    linarith only [hmul, hone]
  have hy : (x - 1) * Q / (1 - x * Q) ≤ ((x - 1) / (1 - x * Qs)) * Q := by
    have hdenle : 1 - x * Qs ≤ 1 - x * Q := by linarith only [hxQ']
    have hnum0 : 0 ≤ (x - 1) * Q := mul_nonneg (by linarith only [hx]) hQ0
    have hdiv := div_le_div_of_nonneg_left hnum0 hdenS hdenle
    have hident : (x - 1) * Q / (1 - x * Qs) = ((x - 1) / (1 - x * Qs)) * Q := by
      field_simp [hdenS.ne']
    linarith only [hdiv, hident]
  have hEq : (1 - Q) / (1 - x * Q) = 1 + (x - 1) * Q / (1 - x * Q) := by
    have hnum : 1 - Q = (1 - x * Q) + (x - 1) * Q := by ring
    calc (1 - Q) / (1 - x * Q)
        = ((1 - x * Q) + (x - 1) * Q) / (1 - x * Q) := by rw [hnum]
      _ = (1 - x * Q) / (1 - x * Q) + (x - 1) * Q / (1 - x * Q) := by
          rw [add_div]
      _ = 1 + (x - 1) * Q / (1 - x * Q) := by rw [div_self hden.ne']
  have hExp : 1 + (x - 1) * Q / (1 - x * Q) ≤
      Real.exp ((x - 1) * Q / (1 - x * Q)) := by
    simpa [add_comm] using Real.add_one_le_exp ((x - 1) * Q / (1 - x * Q))
  calc (1 - Q) / (1 - x * Q)
      = 1 + (x - 1) * Q / (1 - x * Q) := hEq
    _ ≤ Real.exp ((x - 1) * Q / (1 - x * Q)) := hExp
    _ ≤ Real.exp (((x - 1) / (1 - x * Qs)) * Q) := (Real.exp_le_exp).mpr hy

lemma prod_ratio_le_exp {Q : ℕ → ℝ} {J : ℕ} {x Qs : ℝ}
    (hx : 1 ≤ x) (hxQ : x * Qs < 1)
    (hQ0 : ∀ i ∈ range J, 0 ≤ Q i) (hQ : ∀ i ∈ range J, Q i ≤ Qs) :
    ∏ i ∈ range J, ((1 - Q i) / (1 - x * Q i)) ≤
      Real.exp (((x - 1) / (1 - x * Qs)) * ∑ i ∈ range J, Q i) := by
  have hterm : ∀ i ∈ range J, (1 - Q i) / (1 - x * Q i) ≤
      Real.exp (((x - 1) / (1 - x * Qs)) * Q i) := by
    intro i hi
    exact ratio_le_exp hx hxQ (hQ0 i hi) (hQ i hi)
  have hpos : ∀ i ∈ range J, 0 ≤ (1 - Q i) / (1 - x * Q i) := by
    intro i hi
    have hden : 0 < 1 - x * Q i := by
      have hxQ' : x * Q i ≤ x * Qs :=
        mul_le_mul_of_nonneg_left (hQ i hi) (by linarith only [hx])
      linarith only [hxQ', hxQ]
    have hQ1 : Q i < 1 := by
      have hle : Q i ≤ x * Q i := by
        have hmul := mul_le_mul_of_nonneg_left hx (hQ0 i hi)
        have hone : Q i = Q i * 1 := by ring
        linarith only [hmul, hone]
      have hxQi : x * Q i ≤ x * Qs :=
        mul_le_mul_of_nonneg_left (hQ i hi) (by linarith only [hx])
      linarith only [hle, hxQi, hxQ]
    exact div_nonneg (by linarith only [hQ1]) hden.le
  have hprod := prod_le_prod hpos hterm
  rw [← Real.exp_sum] at hprod
  have hsum : ∑ i ∈ range J, ((x - 1) / (1 - x * Qs)) * Q i =
      ((x - 1) / (1 - x * Qs)) * ∑ i ∈ range J, Q i := by rw [mul_sum]
  rw [hsum] at hprod
  exact hprod

lemma inv_pow_half_le {x : ℝ} (hx : 1 < x) (r : ℕ) :
    (x⁻¹) ^ (r / 2) ≤ Real.sqrt x * Real.exp (-(Real.log x / 2) * r) := by
  have hx0 : 0 < x := by linarith only [hx]
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hs := (nat_half_ge r).1
  have hneg : -((r / 2 : ℕ) : ℝ) * Real.log x ≤
      -(((r : ℝ) - 1) / 2) * Real.log x :=
    mul_le_mul_of_nonneg_right (neg_le_neg hs) hlog.le
  have hpow : (x⁻¹) ^ (r / 2) = Real.exp (-((r / 2 : ℕ) : ℝ) * Real.log x) := by
    have hxexp : x⁻¹ = Real.exp (-Real.log x) := by
      calc x⁻¹
          = (Real.exp (Real.log x))⁻¹ := by rw [Real.exp_log hx0]
        _ = Real.exp (-Real.log x) := (Real.exp_neg _).symm
    calc (x⁻¹) ^ (r / 2)
        = Real.exp (-Real.log x) ^ (r / 2) := congrArg (fun t => t ^ (r / 2)) hxexp
      _ = Real.exp (((r / 2 : ℕ) : ℝ) * (-Real.log x)) := (Real.exp_nat_mul _ _).symm
      _ = Real.exp (-((r / 2 : ℕ) : ℝ) * Real.log x) := by
          congr 1
          ring
  have hsqrt : Real.sqrt x = Real.exp (Real.log x / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0]
    congr 1
    ring
  have hsplit : -(((r : ℝ) - 1) / 2) * Real.log x =
      Real.log x / 2 + -(Real.log x / 2) * r := by ring
  calc (x⁻¹) ^ (r / 2)
      = Real.exp (-((r / 2 : ℕ) : ℝ) * Real.log x) := hpow
    _ ≤ Real.exp (-(((r : ℝ) - 1) / 2) * Real.log x) := (Real.exp_le_exp).mpr hneg
    _ = Real.exp (Real.log x / 2) * Real.exp (-(Real.log x / 2) * r) := by
        rw [hsplit, Real.exp_add]
    _ = Real.sqrt x * Real.exp (-(Real.log x / 2) * r) := by rw [hsqrt]

lemma one_sub_pow_half {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (r : ℕ) :
    (1 - p) ^ (r - r / 2) ≤ Real.exp (-(-Real.log (1 - p) / 2) * r) := by
  have h1p : 0 < 1 - p := by linarith only [hp0, hp1]
  have hlog : Real.log (1 - p) < 0 := by
    rw [← Real.log_one]
    exact Real.log_lt_log h1p (by linarith only [hp0])
  have ht := (nat_half_ge r).2
  have hpow : (1 - p) ^ (r - r / 2) =
      Real.exp (((r - r / 2 : ℕ) : ℝ) * Real.log (1 - p)) := by
    calc (1 - p) ^ (r - r / 2)
        = Real.exp (Real.log (1 - p)) ^ (r - r / 2) :=
          congrArg (fun t => t ^ (r - r / 2)) (Real.exp_log h1p).symm
      _ = Real.exp (((r - r / 2 : ℕ) : ℝ) * Real.log (1 - p)) :=
          (Real.exp_nat_mul _ _).symm
  have hcmp : ((r - r / 2 : ℕ) : ℝ) * Real.log (1 - p) ≤
      ((r : ℝ) / 2) * Real.log (1 - p) :=
    mul_le_mul_of_nonpos_right ht hlog.le
  have hident : (r : ℝ) / 2 * Real.log (1 - p) = -(-Real.log (1 - p) / 2) * r := by ring
  calc (1 - p) ^ (r - r / 2)
      = Real.exp (((r - r / 2 : ℕ) : ℝ) * Real.log (1 - p)) := hpow
    _ ≤ Real.exp ((r : ℝ) / 2 * Real.log (1 - p)) := (Real.exp_le_exp).mpr hcmp
    _ = Real.exp (-(-Real.log (1 - p) / 2) * r) := by rw [hident]

end Epidemics.Revisited
