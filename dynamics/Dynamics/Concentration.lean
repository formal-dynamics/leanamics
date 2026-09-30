import Dynamics.Uniform

/-!
# Hoeffding and Bernstein bounds on finite product spaces

Concentration for a sum `∑ i, Y i (ω i)` of independent coordinates, where
`ω : Fin n → γ` is drawn uniformly (so the coordinates `ω i` are independent
uniform draws from the finite type `γ`). As everywhere in this library the
probability of an event is the average of its indicator, and independence is
`avg_prod_pi`; no measure theory is used.

* `one_sub_add_mul_exp_le`: **Hoeffding's lemma** for a Bernoulli variable,
  `1 - p + p eᵗ ≤ exp(p t + t²/8)`, proved by two monotonicity arguments.
* `avg_hoeffding`: **Hoeffding's inequality** for `{0,1}`-valued coordinates,
  `P(X ≥ 𝔼X + λ) ≤ exp(-2λ²/n)`.
* `exp_le_bernstein`: the scalar inequality behind Bernstein's bound,
  `e^y ≤ 1 + y + y² / (2(1 - u/3))` for `y ≤ u < 3`, from the monotonicity
  of `(1 + y + y²/(2(1 - y/3))) e^{-y}` on either side of `0`.
* `avg_bernstein`: **Bernstein's inequality**, `P(X ≥ 𝔼X + λ) ≤
  exp(-λ² / (2σ²(1 + bλ/(3σ²))))` whenever every coordinate satisfies
  `Yᵢ - 𝔼Yᵢ ≤ b` and `σ²` bounds the variance of `X`.
-/

namespace Dynamics

open Finset Real

/-! ### Scalar inequalities -/

/-- `e^x ≤ 1 + x + x² / (2(1 - x/3))` for every `x < 3`. -/
lemma exp_le_one_add_add_sq_div {x : ℝ} (hx3 : x < 3) :
    exp x ≤ 1 + x + x ^ 2 / (2 * (1 - x / 3)) := by
  -- `F y = P y * e^{-y}` has `F' = e^{-y} y³ / (2(3-y)²)`, of the sign of `y`,
  -- so `F` is minimal at `y = 0`, where it equals `1`.
  have hF (y : ℝ) (hy : y < 3) :
      HasDerivAt (fun y => (1 + y + 3 * y ^ 2 / (2 * (3 - y))) * exp (-y))
        (exp (-y) * y ^ 3 / (2 * (3 - y) ^ 2)) y := by
    have hden : 2 * (3 - y) ≠ 0 := by linarith
    have h1 : HasDerivAt (fun y : ℝ => 3 * y ^ 2) (6 * y) y :=
      ((hasDerivAt_pow 2 y).const_mul 3).congr_deriv (by norm_num; ring)
    have h2 : HasDerivAt (fun y : ℝ => 2 * (3 - y)) (-2) y :=
      (((hasDerivAt_id' y).const_sub 3).const_mul 2).congr_deriv (by norm_num)
    have hP := ((hasDerivAt_id' y).const_add 1).fun_add (h1.fun_div h2 hden)
    have he : HasDerivAt (fun y => exp (-y)) (-exp (-y)) y := by
      simpa using (hasDerivAt_neg y).exp
    refine (hP.fun_mul he).congr_deriv ?_
    have h3 : (3 - y) ≠ 0 := by linarith
    field_simp
    ring
  have hF0 : (fun y => (1 + y + 3 * y ^ 2 / (2 * (3 - y))) * exp (-y)) 0 = 1 := by simp
  have hFx : 1 ≤ (1 + x + 3 * x ^ 2 / (2 * (3 - x))) * exp (-x) := by
    rcases le_total 0 x with hx0 | hx0
    · have hmono : MonotoneOn (fun y => (1 + y + 3 * y ^ 2 / (2 * (3 - y))) * exp (-y))
          (Set.Ico 0 3) := by
        apply monotoneOn_of_deriv_nonneg (convex_Ico 0 3)
        · exact fun y hy => (hF y hy.2).continuousAt.continuousWithinAt
        · intro y hy
          rw [interior_Ico] at hy
          exact (hF y hy.2).differentiableAt.differentiableWithinAt
        · intro y hy
          rw [interior_Ico] at hy
          rw [(hF y hy.2).deriv]
          have : 0 < 3 - y := by linarith [hy.2]
          have hy0 : 0 ≤ y := hy.1.le
          positivity
      have h := hmono ⟨le_refl 0, by norm_num⟩ ⟨hx0, hx3⟩ hx0
      rw [hF0] at h
      exact h
    · have hanti : AntitoneOn (fun y => (1 + y + 3 * y ^ 2 / (2 * (3 - y))) * exp (-y))
          (Set.Iic 0) := by
        apply antitoneOn_of_deriv_nonpos (convex_Iic 0)
        · exact fun y hy =>
            (hF y (by linarith [Set.mem_Iic.mp hy])).continuousAt.continuousWithinAt
        · intro y hy
          rw [interior_Iic] at hy
          exact (hF y (by linarith [Set.mem_Iio.mp hy])).differentiableAt.differentiableWithinAt
        · intro y hy
          rw [interior_Iic] at hy
          have hy0 : y < 0 := hy
          rw [(hF y (by linarith)).deriv]
          have h3 : 0 < 2 * (3 - y) ^ 2 := by nlinarith
          apply div_nonpos_of_nonpos_of_nonneg _ h3.le
          apply mul_nonpos_of_nonneg_of_nonpos (exp_pos _).le
          have : y ^ 3 = y * y ^ 2 := by ring
          rw [this]
          exact mul_nonpos_of_nonpos_of_nonneg hy0.le (sq_nonneg y)
      have h := hanti (Set.mem_Iic.mpr hx0) (Set.mem_Iic.mpr le_rfl) hx0
      rw [hF0] at h
      exact h
  rw [exp_neg] at hFx
  have hpos := exp_pos x
  have heq : x ^ 2 / (2 * (1 - x / 3)) = 3 * x ^ 2 / (2 * (3 - x)) := by
    have : (3 : ℝ) - x ≠ 0 := by linarith
    field_simp
  rw [heq]
  rwa [le_mul_inv_iff₀ hpos, one_mul] at hFx

/-- **The Bernstein scalar inequality**: for `y ≤ u < 3`,
`e^y ≤ 1 + y + y² / (2(1 - u/3))`. -/
lemma exp_le_bernstein {y u : ℝ} (hyu : y ≤ u) (hu3 : u < 3) :
    exp y ≤ 1 + y + y ^ 2 / (2 * (1 - u / 3)) := by
  calc exp y ≤ 1 + y + y ^ 2 / (2 * (1 - y / 3)) :=
        exp_le_one_add_add_sq_div (lt_of_le_of_lt hyu hu3)
    _ ≤ 1 + y + y ^ 2 / (2 * (1 - u / 3)) := by
        have h1 : 0 < 2 * (1 - u / 3) := by linarith
        have h2 : 2 * (1 - u / 3) ≤ 2 * (1 - y / 3) := by linarith
        have := div_le_div_of_nonneg_left (sq_nonneg y) h1 h2
        linarith

/-- **Hoeffding's lemma** for a Bernoulli variable: for `p ∈ [0,1]` and every
real `t`, `1 - p + p eᵗ ≤ exp(p t + t²/8)`. -/
lemma one_sub_add_mul_exp_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ) :
    1 - p + p * exp t ≤ exp (p * t + t ^ 2 / 8) := by
  have hDpos (s : ℝ) : 0 < 1 - p + p * exp s := by
    rcases hp1.lt_or_eq with hp | hp
    · have := exp_pos s
      nlinarith
    · rw [hp]
      simpa using exp_pos s
  have hD (s : ℝ) : HasDerivAt (fun s => 1 - p + p * exp s) (p * exp s) s :=
    ((hasDerivAt_exp s).const_mul p).const_add (1 - p)
  -- `q s = p eˢ / (1 - p + p eˢ)` satisfies `q' = q (1 - q) ≤ 1/4`
  have hq (s : ℝ) : HasDerivAt (fun s => p * exp s / (1 - p + p * exp s))
      (p * exp s / (1 - p + p * exp s) * (1 - p * exp s / (1 - p + p * exp s))) s := by
    refine (((hasDerivAt_exp s).const_mul p).fun_div (hD s) (hDpos s).ne').congr_deriv ?_
    have := (hDpos s).ne'
    field_simp
  -- `h s = p + s/4 - q s` is monotone and vanishes at `0`
  have hh (s : ℝ) : HasDerivAt (fun s => p + s / 4 - p * exp s / (1 - p + p * exp s))
      (1 / 4 - p * exp s / (1 - p + p * exp s) * (1 - p * exp s / (1 - p + p * exp s))) s :=
    (((hasDerivAt_id' s).div_const 4).const_add p).fun_sub (hq s)
  have hhmono : Monotone (fun s => p + s / 4 - p * exp s / (1 - p + p * exp s)) := by
    apply monotone_of_deriv_nonneg (fun s => (hh s).differentiableAt)
    intro s
    rw [(hh s).deriv]
    nlinarith [sq_nonneg (p * exp s / (1 - p + p * exp s) - 1 / 2)]
  have hh0 : (fun s => p + s / 4 - p * exp s / (1 - p + p * exp s)) 0 = 0 := by simp
  -- `g s = p s + s²/8 - log(1 - p + p eˢ)` has `g' = h`, so it is minimal at `0`
  have hg (s : ℝ) : HasDerivAt (fun s => p * s + s ^ 2 / 8 - Real.log (1 - p + p * exp s))
      (p + s / 4 - p * exp s / (1 - p + p * exp s)) s := by
    have hlog := (hD s).log (hDpos s).ne'
    refine ((((hasDerivAt_id' s).const_mul p).fun_add
      ((hasDerivAt_pow 2 s).div_const 8)).fun_sub hlog).congr_deriv ?_
    norm_num
    ring
  have hg0 : (fun s => p * s + s ^ 2 / 8 - Real.log (1 - p + p * exp s)) 0 = 0 := by simp
  have hgt : 0 ≤ p * t + t ^ 2 / 8 - Real.log (1 - p + p * exp t) := by
    rcases le_total 0 t with ht | ht
    · have hmono : MonotoneOn (fun s => p * s + s ^ 2 / 8 - Real.log (1 - p + p * exp s))
          (Set.Ici 0) := by
        apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
        · exact fun s _ => (hg s).continuousAt.continuousWithinAt
        · exact fun s _ => (hg s).differentiableAt.differentiableWithinAt
        · intro s hs
          rw [interior_Ici] at hs
          rw [(hg s).deriv]
          have := hhmono (le_of_lt (Set.mem_Ioi.mp hs))
          simp only at this
          linarith [hh0]
      have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
      simp only at this
      linarith [hg0]
    · have hanti : AntitoneOn (fun s => p * s + s ^ 2 / 8 - Real.log (1 - p + p * exp s))
          (Set.Iic 0) := by
        apply antitoneOn_of_deriv_nonpos (convex_Iic 0)
        · exact fun s _ => (hg s).continuousAt.continuousWithinAt
        · exact fun s _ => (hg s).differentiableAt.differentiableWithinAt
        · intro s hs
          rw [interior_Iic] at hs
          rw [(hg s).deriv]
          have := hhmono (le_of_lt (Set.mem_Iio.mp hs))
          simp only at this
          linarith [hh0]
      have := hanti (Set.mem_Iic.mpr ht) (Set.mem_Iic.mpr le_rfl) ht
      simp only at this
      linarith [hg0]
  calc 1 - p + p * exp t = exp (Real.log (1 - p + p * exp t)) := (exp_log (hDpos t)).symm
    _ ≤ exp (p * t + t ^ 2 / 8) := exp_le_exp.mpr (by linarith)

/-! ### Tail bounds for sums of independent coordinates -/

variable {n : ℕ} {γ : Type*} [Fintype γ]

/-- Markov's inequality applied to `exp (t (X - k))`: an exponential-moment
bound turns into a tail bound. -/
lemma avg_tail_le_of_mgf (X : (Fin n → γ) → ℝ) {t : ℝ} (ht : 0 ≤ t) (k : ℝ) :
    avg (fun ω => if k ≤ X ω then (1 : ℝ) else 0)
      ≤ avg (fun ω => exp (t * X ω)) * exp (-(t * k)) := by
  have hpt (ω : Fin n → γ) :
      (if k ≤ X ω then (1 : ℝ) else 0) ≤ exp (-(t * k)) * exp (t * X ω) := by
    rw [← exp_add]
    split_ifs with h
    · have h0 : (0 : ℝ) ≤ -(t * k) + t * X ω := by nlinarith
      calc (1 : ℝ) = exp 0 := by simp
        _ ≤ _ := exp_le_exp.mpr h0
    · exact (exp_pos _).le
  calc avg (fun ω => if k ≤ X ω then (1 : ℝ) else 0)
      ≤ avg (fun ω => exp (-(t * k)) * exp (t * X ω)) := avg_le_avg hpt
    _ = _ := by rw [avg_const_mul, mul_comm]

/-- The exponential moment of a sum of independent coordinates factors. -/
lemma avg_exp_sum (Y : Fin n → γ → ℝ) (t : ℝ) :
    avg (fun ω : Fin n → γ => exp (t * ∑ i, Y i (ω i)))
      = ∏ i, avg (fun y => exp (t * Y i y)) := by
  have h (ω : Fin n → γ) : exp (t * ∑ i, Y i (ω i)) = ∏ i, exp (t * Y i (ω i)) := by
    rw [mul_sum, exp_sum]
  simp_rw [h]
  exact avg_prod_pi n (fun i y => exp (t * Y i y))

/-- **Hoeffding's inequality** for independent `{0,1}`-valued coordinates:
`P(X ≥ 𝔼X + λ) ≤ exp(-2λ²/n)`. -/
theorem avg_hoeffding [Nonempty γ] (Y : Fin n → γ → ℝ) (hY : ∀ i x, Y i x = 0 ∨ Y i x = 1)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    avg (fun ω : Fin n → γ =>
        if (∑ i, avg (Y i)) + lam ≤ ∑ i, Y i (ω i) then (1 : ℝ) else 0)
      ≤ exp (-(2 * lam ^ 2 / n)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, div_zero, neg_zero, exp_zero]
    calc _ ≤ avg (fun _ : Fin 0 → γ => (1 : ℝ)) := avg_le_avg fun ω => by split <;> norm_num
      _ = 1 := avg_const 1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set t : ℝ := 4 * lam / n with htdef
  have ht : 0 ≤ t := by positivity
  set μ : ℝ := ∑ i, avg (Y i)
  have hbound := avg_tail_le_of_mgf (fun ω : Fin n → γ => ∑ i, Y i (ω i)) ht (μ + lam)
  rw [avg_exp_sum] at hbound
  have hone (i : Fin n) : avg (fun y => exp (t * Y i y)) ≤ exp (t * avg (Y i) + t ^ 2 / 8) := by
    have hpt (y : γ) : exp (t * Y i y) = 1 + (exp t - 1) * Y i y := by
      rcases hY i y with h | h <;> simp [h]
    simp_rw [hpt]
    have hsplit : avg (fun y => 1 + (exp t - 1) * Y i y) = 1 + (exp t - 1) * avg (Y i) := by
      rw [avg_add, avg_const, avg_const_mul]
    rw [hsplit]
    have hp0 : 0 ≤ avg (Y i) := avg_nonneg fun y => by rcases hY i y with h | h <;> simp [h]
    have hp1 : avg (Y i) ≤ 1 := by
      calc avg (Y i) ≤ avg (fun _ : γ => (1 : ℝ)) :=
            avg_le_avg fun y => by rcases hY i y with h | h <;> simp [h]
        _ = 1 := avg_const 1
    have := one_sub_add_mul_exp_le hp0 hp1 t
    rw [mul_comm t (avg (Y i))]
    linarith
  have hprod : ∏ i, avg (fun y => exp (t * Y i y)) ≤ exp (t * μ + n * (t ^ 2 / 8)) := by
    calc ∏ i, avg (fun y => exp (t * Y i y))
        ≤ ∏ i : Fin n, exp (t * avg (Y i) + t ^ 2 / 8) :=
          prod_le_prod (fun i _ => avg_nonneg fun y => (exp_pos _).le) (fun i _ => hone i)
      _ = exp (t * μ + n * (t ^ 2 / 8)) := by
          rw [← exp_sum, sum_add_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin,
            nsmul_eq_mul]
  calc _ ≤ (∏ i, avg (fun y => exp (t * Y i y))) * exp (-(t * (μ + lam))) := hbound
    _ ≤ exp (t * μ + n * (t ^ 2 / 8)) * exp (-(t * (μ + lam))) :=
        mul_le_mul_of_nonneg_right hprod (exp_pos _).le
    _ = exp (-(2 * lam ^ 2 / n)) := by
        rw [← exp_add]
        congr 1
        rw [htdef]
        field_simp
        ring

/-- The variance of a coordinate, `𝔼[(Y - 𝔼Y)²]`. -/
noncomputable def variance (f : γ → ℝ) : ℝ := avg (fun y => (f y - avg f) ^ 2)

lemma variance_nonneg (f : γ → ℝ) : 0 ≤ variance f :=
  avg_nonneg fun _ => sq_nonneg _

/-- The variance is at most the second moment. -/
lemma variance_le_avg_sq [Nonempty γ] (f : γ → ℝ) : variance f ≤ avg (fun y => f y ^ 2) := by
  unfold variance
  have h (y : γ) : (f y - avg f) ^ 2 = f y ^ 2 + (-(2 * avg f) * f y + avg f ^ 2) := by ring
  simp_rw [h]
  rw [avg_add, avg_add, avg_const_mul, avg_const]
  nlinarith [sq_nonneg (avg f)]

/-- **Bernstein's inequality** (Dubhashi–Panconesi): if every coordinate
satisfies `Yᵢ - 𝔼Yᵢ ≤ b` and `σ²` is at least the variance of
`X = ∑ᵢ Yᵢ`, then `P(X ≥ 𝔼X + λ) ≤ exp(-λ² / (2σ²(1 + bλ/(3σ²))))`. -/
theorem avg_bernstein [Nonempty γ] (Y : Fin n → γ → ℝ) {b σ2 lam : ℝ} (hb : 0 < b)
    (hYb : ∀ i x, Y i x - avg (Y i) ≤ b) (hσ : ∑ i, variance (Y i) ≤ σ2) (hσ0 : 0 < σ2)
    (hlam : 0 ≤ lam) :
    avg (fun ω : Fin n → γ =>
        if (∑ i, avg (Y i)) + lam ≤ ∑ i, Y i (ω i) then (1 : ℝ) else 0)
      ≤ exp (-(lam ^ 2 / (2 * σ2 * (1 + b * lam / (3 * σ2))))) := by
  set μ : ℝ := ∑ i, avg (Y i)
  set t : ℝ := lam / (σ2 + b * lam / 3) with htdef
  have hden : 0 < σ2 + b * lam / 3 := by positivity
  have ht : 0 ≤ t := by positivity
  have htb : t * b < 3 := by
    rw [htdef, div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith
  set u : ℝ := t * b
  have hK : 0 < 2 * (1 - u / 3) := by linarith
  -- one coordinate: `𝔼 exp(t(Yᵢ - 𝔼Yᵢ)) ≤ exp(t² Var / (2(1 - u/3)))`
  have hone (i : Fin n) :
      avg (fun y => exp (t * Y i y))
        ≤ exp (t * avg (Y i) + t ^ 2 * variance (Y i) / (2 * (1 - u / 3))) := by
    have hpt (y : γ) : exp (t * Y i y) ≤ exp (t * avg (Y i)) *
        (1 + t * (Y i y - avg (Y i)) + t ^ 2 * (Y i y - avg (Y i)) ^ 2 / (2 * (1 - u / 3))) := by
      have hyu : t * (Y i y - avg (Y i)) ≤ u := mul_le_mul_of_nonneg_left (hYb i y) ht
      have := exp_le_bernstein hyu htb
      have hsplit : exp (t * Y i y) = exp (t * avg (Y i)) * exp (t * (Y i y - avg (Y i))) := by
        rw [← exp_add]; congr 1; ring
      rw [hsplit]
      apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
      have e : t ^ 2 * (Y i y - avg (Y i)) ^ 2 / (2 * (1 - u / 3))
          = (t * (Y i y - avg (Y i))) ^ 2 / (2 * (1 - u / 3)) := by ring
      rw [e]
      exact this
    calc avg (fun y => exp (t * Y i y))
        ≤ avg (fun y => exp (t * avg (Y i)) *
            (1 + t * (Y i y - avg (Y i)) + t ^ 2 * (Y i y - avg (Y i)) ^ 2 / (2 * (1 - u / 3)))) :=
          avg_le_avg hpt
      _ = exp (t * avg (Y i)) * (1 + t ^ 2 * variance (Y i) / (2 * (1 - u / 3))) := by
          rw [avg_const_mul]
          congr 1
          have hc : avg (fun y => Y i y - avg (Y i)) = 0 := by
            rw [avg_sub, avg_const, sub_self]
          have h2 (y : γ) : 1 + t * (Y i y - avg (Y i))
              + t ^ 2 * (Y i y - avg (Y i)) ^ 2 / (2 * (1 - u / 3))
              = 1 + (t * (Y i y - avg (Y i))
                + (t ^ 2 / (2 * (1 - u / 3))) * (Y i y - avg (Y i)) ^ 2) := by ring
          simp_rw [h2]
          rw [avg_add, avg_const, avg_add, avg_const_mul, hc, avg_const_mul]
          unfold variance
          ring
      _ ≤ exp (t * avg (Y i)) * exp (t ^ 2 * variance (Y i) / (2 * (1 - u / 3))) := by
          apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
          linarith [add_one_le_exp (t ^ 2 * variance (Y i) / (2 * (1 - u / 3)))]
      _ = _ := by rw [← exp_add]
  have hprod : ∏ i, avg (fun y => exp (t * Y i y))
      ≤ exp (t * μ + t ^ 2 * σ2 / (2 * (1 - u / 3))) := by
    calc ∏ i, avg (fun y => exp (t * Y i y))
        ≤ ∏ i : Fin n, exp (t * avg (Y i) + t ^ 2 * variance (Y i) / (2 * (1 - u / 3))) :=
          prod_le_prod (fun i _ => avg_nonneg fun y => (exp_pos _).le) (fun i _ => hone i)
      _ = exp (t * μ + t ^ 2 * (∑ i, variance (Y i)) / (2 * (1 - u / 3))) := by
          rw [← exp_sum]
          congr 1
          simp only [μ, sum_add_distrib, mul_sum, sum_div]
      _ ≤ exp (t * μ + t ^ 2 * σ2 / (2 * (1 - u / 3))) := by
          apply exp_le_exp.mpr
          have := mul_le_mul_of_nonneg_left hσ (sq_nonneg t)
          have := div_le_div_of_nonneg_right this hK.le
          linarith
  have hbound := avg_tail_le_of_mgf (fun ω : Fin n → γ => ∑ i, Y i (ω i)) ht (μ + lam)
  rw [avg_exp_sum] at hbound
  calc _ ≤ (∏ i, avg (fun y => exp (t * Y i y))) * exp (-(t * (μ + lam))) := hbound
    _ ≤ exp (t * μ + t ^ 2 * σ2 / (2 * (1 - u / 3))) * exp (-(t * (μ + lam))) :=
        mul_le_mul_of_nonneg_right hprod (exp_pos _).le
    _ = exp (-(lam ^ 2 / (2 * σ2 * (1 + b * lam / (3 * σ2))))) := by
        rw [← exp_add]
        congr 1
        simp only [u, htdef]
        have hD : σ2 + b * lam / 3 ≠ 0 := hden.ne'
        have hσne : σ2 ≠ 0 := hσ0.ne'
        have h1 : 1 - lam / (σ2 + b * lam / 3) * b / 3 = σ2 / (σ2 + b * lam / 3) := by
          field_simp
          ring
        rw [h1]
        field_simp
        ring

end Dynamics
