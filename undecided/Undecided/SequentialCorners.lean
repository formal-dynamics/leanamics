import Undecided.SequentialPotentials

/-! # The three corners of the configuration space

The corners of [AAE08, Fig. 1]: mostly blank (`8v ≤ n`), mostly `x` (`8x ≥ 7n`), mostly `y`.
In each corner a potential drops by a factor `1 - Θ(1/n)` per interaction (an epidemic in the
blank corner, a coupon collector in the `x` and `y` corners, cf. [AAE08, Lemmas 6 and 7]).
Outside its corner the potential can only rise at state-changing interactions, by a factor at
most `1 + 20/n`, which the weight charges to the counters `I_xy` or `I_ch` (`n ≥ 16`):

* `stepB`: weight `(5/(16n)) (R_b - 64 I_xy)`, potential `1 / v`;
* `stepX`: weight `(5/(32n)) (R_x - 128 I_ch)`, potential `3y + b + 1` ([AAE08, §4.7]);
* `stepY`: the mirror image, potential `3x + b + 1`.
-/

namespace Undecided.Sequential
open Dynamics Real

variable {n : ℕ}

/-! ### PB: the blank corner -/

/-- The blank corner: at most `n/8` decided agents. -/
def BlankR (s : Config n) : Prop := 8 * (count s .a + count s .b) ≤ n

instance (s : Config n) : Decidable (BlankR s) := by unfold BlankR; infer_instance

/-- Weight of PB: `(5/(16n)) (R_b - 64 I_xy)`. -/
noncomputable def wB (n : ℕ) (s : Config n) (i r : Op) : ℝ :=
  5 / (16 * n) * ((if BlankR s then 1 else 0) - 64 * xyI i r)

/-- Potential of PB: `1 / v`, with `v = x + y` the number of decided agents. -/
noncomputable def fB (x y _b : ℝ) : ℝ := 1 / (x + y)

/-- The `xb`/`yb` part of the one-step formula of PB: `-E b / (v + 1)`. -/
lemma blank_vb (x y b E : ℝ) (hv : 0 < x + y) :
    x * b * (E * (1 / (x + 1 + y)) - E * (1 / (x + y))) +
      y * b * (E * (1 / (x + (y + 1))) - E * (1 / (x + y))) = -(E * b / (x + y + 1)) := by
  have h1 : x + 1 + y = x + y + 1 := by ring
  have h2 : x + (y + 1) = x + y + 1 := by ring
  rw [h1, h2]
  field_simp
  ring

/-- The `xy`/`yx` part of the one-step formula of PB, inside the corner: at most `E`. -/
lemma blank_xy_le (x y E e : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x * y = 0 ∨ 2 ≤ x + y)
    (hE : 0 ≤ E) (he1 : e ≤ 1) :
    x * y * (E * e * (1 / (x + (y - 1))) - E * (1 / (x + y))) +
      x * y * (E * e * (1 / (x - 1 + y)) - E * (1 / (x + y))) ≤ E := by
  rcases hxy with h | h
  · rw [h]; linarith
  · have h1 : x + (y - 1) = x + y - 1 := by ring
    have h2 : x - 1 + y = x + y - 1 := by ring
    rw [h1, h2]
    have hv1 : 0 < x + y - 1 := by linarith
    have hv : 0 < x + y := by linarith
    have hxy0 : 0 ≤ x * y := mul_nonneg hx hy
    have hA : 0 ≤ 1 / (x + y - 1) := by positivity
    have step1 : x * y * (E * e * (1 / (x + y - 1)) - E * (1 / (x + y))) ≤
        x * y * (E * (1 / (x + y - 1)) - E * (1 / (x + y))) := by
      apply mul_le_mul_of_nonneg_left _ hxy0
      have : E * e * (1 / (x + y - 1)) ≤ E * (1 / (x + y - 1)) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hA he1) hE
      linarith
    have step2 : 2 * (x * y * (E * (1 / (x + y - 1)) - E * (1 / (x + y)))) ≤ E := by
      have : 2 * (x * y * (E * (1 / (x + y - 1)) - E * (1 / (x + y)))) =
          E * (2 * (x * y) / ((x + y) * (x + y - 1))) := by
        field_simp
        ring
      rw [this]
      apply mul_le_of_le_one_right hE
      rw [div_le_one (by positivity)]
      nlinarith [sq_nonneg (x - y)]
    linarith

/-- **PB inside the blank corner**: the potential `1/v` drops by the factor `1 - 5/(16m)`. -/
lemma blank_inside (x y b m E e : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hb : 0 ≤ b)
    (hs : x + y + b = m) (hm : 2 ≤ m) (hcorner : 8 * (x + y) ≤ m)
    (hv : x + y = 0 ∨ 1 ≤ x + y) (hxy : x * y = 0 ∨ 2 ≤ x + y) (hE : 0 < E)
    (hE1 : E * (1 - 5 / (16 * m)) ≤ 1) (he1 : e ≤ 1) :
    E * (1 / (x + y)) + (x * b * (E * (1 / (x + 1 + y)) - E * (1 / (x + y))) +
      y * b * (E * (1 / (x + (y + 1))) - E * (1 / (x + y))) +
      x * y * (E * e * (1 / (x + (y - 1))) - E * (1 / (x + y))) +
      x * y * (E * e * (1 / (x - 1 + y)) - E * (1 / (x + y)))) / (m * (m - 1)) ≤
      1 / (x + y) := by
  have hD : 0 < m * (m - 1) := by nlinarith
  rcases hv with hv | hv
  · -- no decided agent: nothing changes
    have hx0 : x = 0 := by linarith
    have hy0 : y = 0 := by linarith
    subst hx0 hy0
    simp
  have hv0 : 0 < x + y := by linarith
  have hT1 := blank_vb x y b E hv0
  have hT2 := blank_xy_le x y E e hx hy hxy hE.le he1
  -- the numerator is at most `E (1 - b / (2v)) ≤ -5 m E / (16 v)`
  have hT1' : -(E * b / (x + y + 1)) ≤ -(E * b / (2 * (x + y))) := by
    rw [neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have hN : x * b * (E * (1 / (x + 1 + y)) - E * (1 / (x + y))) +
      y * b * (E * (1 / (x + (y + 1))) - E * (1 / (x + y))) +
      x * y * (E * e * (1 / (x + (y - 1))) - E * (1 / (x + y))) +
      x * y * (E * e * (1 / (x - 1 + y)) - E * (1 / (x + y))) ≤
      -(5 * m * E / (16 * (x + y))) := by
    have hkey : -(E * b / (2 * (x + y))) + E ≤ -(5 * m * E / (16 * (x + y))) := by
      have : -(E * b / (2 * (x + y))) + E + 5 * m * E / (16 * (x + y)) =
          E * (16 * (x + y) - 8 * b + 5 * m) / (16 * (x + y)) := by
        field_simp
        ring
      have hneg : E * (16 * (x + y) - 8 * b + 5 * m) / (16 * (x + y)) ≤ 0 := by
        apply div_nonpos_iff.mpr
        right
        exact ⟨mul_nonpos_of_nonneg_of_nonpos hE.le (by nlinarith), by positivity⟩
      linarith
    linarith
  calc E * (1 / (x + y)) + (x * b * (E * (1 / (x + 1 + y)) - E * (1 / (x + y))) +
        y * b * (E * (1 / (x + (y + 1))) - E * (1 / (x + y))) +
        x * y * (E * e * (1 / (x + (y - 1))) - E * (1 / (x + y))) +
        x * y * (E * e * (1 / (x - 1 + y)) - E * (1 / (x + y)))) / (m * (m - 1))
      ≤ E * (1 / (x + y)) + -(5 * m * E / (16 * (x + y))) / (m * (m - 1)) := by
        gcongr
    _ = E * (1 - 5 / (16 * (m - 1))) * (1 / (x + y)) := by
        field_simp
        ring
    _ ≤ E * (1 - 5 / (16 * m)) * (1 / (x + y)) := by
        gcongr
        · nlinarith
        · nlinarith
    _ ≤ 1 * (1 / (x + y)) := by gcongr
    _ = 1 / (x + y) := one_mul _

/-- **PB outside the blank corner**: the potential `1/v` does not increase in expectation, the
rise at `xy` interactions being paid by the weight `e = exp(-20/m)`. -/
lemma blank_outside (x y b m e : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hb : 0 ≤ b)
    (hm : 16 ≤ m) (hout : m < 8 * (x + y)) (hxy : x * y = 0 ∨ 2 ≤ x + y) (he0 : 0 ≤ e)
    (he : e * (1 + 20 / m) ≤ 1) :
    1 * (1 / (x + y)) + (x * b * (1 * (1 / (x + 1 + y)) - 1 * (1 / (x + y))) +
      y * b * (1 * (1 / (x + (y + 1))) - 1 * (1 / (x + y))) +
      x * y * (1 * e * (1 / (x + (y - 1))) - 1 * (1 / (x + y))) +
      x * y * (1 * e * (1 / (x - 1 + y)) - 1 * (1 / (x + y)))) / (m * (m - 1)) ≤
      1 / (x + y) := by
  have hv0 : 0 < x + y := by linarith
  have hT1 := blank_vb x y b 1 hv0
  have hT1' : -(1 * b / (x + y + 1)) ≤ 0 := by
    have : 0 ≤ 1 * b / (x + y + 1) := by positivity
    linarith
  have hT2 : x * y * (1 * e * (1 / (x + (y - 1))) - 1 * (1 / (x + y))) ≤ 0 ∧
      x * y * (1 * e * (1 / (x - 1 + y)) - 1 * (1 / (x + y))) ≤ 0 := by
    rcases hxy with h | h
    · rw [h]; simp
    · have h1 : x + (y - 1) = x + y - 1 := by ring
      have h2 : x - 1 + y = x + y - 1 := by ring
      rw [h1, h2]
      have hv1 : 0 < x + y - 1 := by linarith
      have hxy0 : 0 ≤ x * y := mul_nonneg hx hy
      have hc : 1 ≤ (x + y - 1) * (20 / m) := by
        rw [mul_div_assoc', le_div_iff₀ (by linarith)]
        linarith
      have hlt : e * (1 / (x + y - 1)) ≤ 1 / (x + y) := by
        rw [mul_one_div, div_le_div_iff₀ hv1 hv0, one_mul]
        nlinarith
      have : 1 * e * (1 / (x + y - 1)) - 1 * (1 / (x + y)) ≤ 0 := by linarith
      exact ⟨mul_nonpos_of_nonneg_of_nonpos hxy0 this, mul_nonpos_of_nonneg_of_nonpos hxy0 this⟩
  have key : ∀ N : ℝ, N ≤ 0 → 1 * (1 / (x + y)) + N / (m * (m - 1)) ≤ 1 / (x + y) :=
    fun N hN => by
      have := add_div_le_self (Φ := 1 / (x + y)) hN (by linarith : (2 : ℝ) ≤ m)
      linarith
  apply key
  linarith [hT2.1, hT2.2]

/-- **PB, one step** (cf. [AAE08, Lemma 6]). -/
theorem stepB (hn : 16 ≤ n) (s : Config n) :
    avg (fun p : Interaction n => exp (wB n s (s p.1.1) (s p.1.2)) * cpot fB (step s p)) ≤
      cpot fB s := by
  unfold cpot
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = if BlankR s then 1 else 0 := ⟨_, rfl⟩
  rw [avg_step_counts (by omega) s (wB n s) (5 / (16 * n) * R)
    (fun i r h => by simp [wB, xyI_idle h, hR]) fB]
  have hm : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hau : wB n s .a .u = 5 / (16 * n) * R := by rw [wB, ← hR]; simp [xyI]
  have hbu : wB n s .b .u = 5 / (16 * n) * R := by rw [wB, ← hR]; simp [xyI]
  have hab : wB n s .a .b = 5 / (16 * n) * R + -(20 / n) := by
    rw [wB, ← hR]; simp [xyI]; field_simp; ring
  have hba : wB n s .b .a = 5 / (16 * n) * R + -(20 / n) := by
    rw [wB, ← hR]; simp [xyI]; field_simp; ring
  rw [hau, hbu, hab, hba, exp_add]
  simp only [fB]
  have hs := count_add s
  have hxy : (count s .a : ℝ) * count s .b = 0 ∨ 2 ≤ (count s .a : ℝ) + count s .b := by
    rcases Nat.eq_zero_or_pos (count s .a) with h | h
    · left; simp [h]
    rcases Nat.eq_zero_or_pos (count s .b) with h' | h'
    · left; simp [h']
    right
    have : 2 ≤ count s .a + count s .b := by omega
    exact_mod_cast this
  have he := exp_neg_mul_one_add_le (20 / (n : ℝ))
  by_cases hc : BlankR s
  · have hR1 : R = 1 := by simp [hR, hc]
    rw [hR1, mul_one]
    have hv : (count s .a : ℝ) + count s .b = 0 ∨ 1 ≤ (count s .a : ℝ) + count s .b := by
      rcases Nat.eq_zero_or_pos (count s .a + count s .b) with h | h
      · left; exact_mod_cast h
      · right; exact_mod_cast h
    refine blank_inside _ _ _ _ _ _ (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      hs (by linarith) (by exact_mod_cast hc) hv hxy (exp_pos _) ?_ ?_
    · exact exp_mul_one_sub_le _
    · exact exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  · have hR0 : R = 0 := by simp [hR, hc]
    rw [hR0, mul_zero, exp_zero]
    have hout : (n : ℝ) < 8 * ((count s .a : ℝ) + count s .b) := by
      have : n < 8 * (count s .a + count s .b) := by unfold BlankR at hc; omega
      exact_mod_cast this
    exact blank_outside _ _ _ _ _ (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      hm hout hxy (exp_pos _).le he

/-! ### PX and PY: the `x` and `y` corners -/

/-- The `x` corner without consensus: at least `7n/8` agents hold `x`, not all of them. -/
def XR (s : Config n) : Prop := 7 * n ≤ 8 * count s .a ∧ count s .a < n

/-- The `y` corner without consensus. -/
def YR (s : Config n) : Prop := 7 * n ≤ 8 * count s .b ∧ count s .b < n

instance (s : Config n) : Decidable (XR s) := by unfold XR; infer_instance
instance (s : Config n) : Decidable (YR s) := by unfold YR; infer_instance

/-- Weight of PX: `(5/(32n)) (R_x - 128 I_ch)`. -/
noncomputable def wX (n : ℕ) (s : Config n) (i r : Op) : ℝ :=
  5 / (32 * n) * ((if XR s then 1 else 0) - 128 * (vbI i r + xyI i r))

/-- Weight of PY: `(5/(32n)) (R_y - 128 I_ch)`. -/
noncomputable def wY (n : ℕ) (s : Config n) (i r : Op) : ℝ :=
  5 / (32 * n) * ((if YR s then 1 else 0) - 128 * (vbI i r + xyI i r))

/-- Potential of PX: `3y + b + 1` [AAE08, §4.7]. -/
def fX (_x y b : ℝ) : ℝ := 3 * y + b + 1

/-- Potential of PY: `3x + b + 1`. -/
def fY (x _y b : ℝ) : ℝ := 3 * x + b + 1

/-- The one-step formula of PX for majority count `p`, minority count `q` and `b` blanks, with
weights `E` (idle) and `E e` (state-changing). -/
noncomputable def cornerForm (p q b m E e : ℝ) : ℝ :=
  E * (3 * q + b + 1) + (p * b * (E * e * (3 * q + b) - E * (3 * q + b + 1)) +
    q * b * (E * e * (3 * q + b + 3) - E * (3 * q + b + 1)) +
    p * q * (E * e * (3 * q + b - 1) - E * (3 * q + b + 1)) +
    p * q * (E * e * (3 * q + b + 2) - E * (3 * q + b + 1))) / (m * (m - 1))

/-- **PX inside the `x` corner**: `3y + b + 1` drops by the factor `1 - 5/(32m)`. -/
lemma corner_inside (p q b m E e : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hb : 0 ≤ b)
    (hs : p + q + b = m) (hpm : 7 * m ≤ 8 * p) (hqb : 1 ≤ q + b) (hE : 0 < E)
    (hE1 : E * (1 - 5 / (32 * m)) ≤ 1) (he1 : e ≤ 1) :
    cornerForm p q b m E e ≤ 3 * q + b + 1 := by
  unfold cornerForm
  have hD : 0 < m * (m - 1) := by nlinarith
  have hpb : 0 ≤ p * b := mul_nonneg hp hb
  have hqb' : 0 ≤ q * b := mul_nonneg hq hb
  have hpq : 0 ≤ p * q := mul_nonneg hp hq
  have t1 : p * b * (E * e * (3 * q + b) - E * (3 * q + b + 1)) ≤ p * b * (-E) := by
    apply mul_le_mul_of_nonneg_left _ hpb
    have : E * e * (3 * q + b) ≤ E * (3 * q + b) := by
      have := mul_le_mul_of_nonneg_left he1 hE.le
      nlinarith
    linarith
  have t2 : q * b * (E * e * (3 * q + b + 3) - E * (3 * q + b + 1)) ≤ q * b * (2 * E) := by
    apply mul_le_mul_of_nonneg_left _ hqb'
    have : E * e * (3 * q + b + 3) ≤ E * (3 * q + b + 3) := by
      have := mul_le_mul_of_nonneg_left he1 hE.le
      nlinarith
    linarith
  have t3 : p * q * (E * e * (3 * q + b - 1) - E * (3 * q + b + 1)) +
      p * q * (E * e * (3 * q + b + 2) - E * (3 * q + b + 1)) ≤ p * q * (-E) := by
    rw [← mul_add]
    apply mul_le_mul_of_nonneg_left _ hpq
    have : E * e * (6 * q + 2 * b + 1) ≤ E * (6 * q + 2 * b + 1) := by
      have := mul_le_mul_of_nonneg_left he1 hE.le
      nlinarith
    nlinarith
  -- `-pb + 2qb - pq ≤ -(5m/8)(q + b)`
  have hcore : p * b * (-E) + q * b * (2 * E) + p * q * (-E) ≤ -(E * (5 * m / 8) * (q + b)) := by
    nlinarith [mul_le_mul_of_nonneg_left (show 5 * m / 8 ≤ p - 2 * q by linarith) hb,
      mul_le_mul_of_nonneg_left (show 5 * m / 8 ≤ p by linarith) hq]
  have hN := add_le_add (add_le_add t1 t2) t3
  have hfrac : (5 / (32 * m)) * (3 * q + b + 1) ≤ (5 * m / 8) * (q + b) / (m * (m - 1)) := by
    rw [le_div_iff₀ hD]
    have : (3 * q + b + 1) * (m - 1) ≤ 4 * (q + b) * m := by nlinarith
    have hm0 : 0 < m := by linarith
    field_simp
    nlinarith
  calc _ ≤ E * (3 * q + b + 1) + -(E * (5 * m / 8) * (q + b)) / (m * (m - 1)) := by
        gcongr
        linarith
    _ = E * ((3 * q + b + 1) - (5 * m / 8) * (q + b) / (m * (m - 1))) := by ring
    _ ≤ E * ((3 * q + b + 1) - (5 / (32 * m)) * (3 * q + b + 1)) := by gcongr
    _ = E * (1 - 5 / (32 * m)) * (3 * q + b + 1) := by ring
    _ ≤ 1 * (3 * q + b + 1) := by gcongr
    _ = 3 * q + b + 1 := one_mul _

/-- **PX outside the `x` corner**: `3y + b + 1 ≥ n/8`, so its rise at a state-changing
interaction (at most `+2`) is paid by the weight `e = exp(-20/m)`. -/
lemma corner_outside (p q b m e : ℝ) (hq : 0 ≤ q) (hb : 0 ≤ b) (hs : p + q + b = m)
    (hm : 1 ≤ m) (hpm : 8 * p < 7 * m) (hp : 0 ≤ p) (he0 : 0 ≤ e) (he : e * (1 + 20 / m) ≤ 1) :
    cornerForm p q b m 1 e ≤ 3 * q + b + 1 := by
  unfold cornerForm
  have hm0 : 0 < m := by linarith
  have hD : 0 ≤ m * (m - 1) := by nlinarith
  have hΦ : m / 10 ≤ 3 * q + b + 1 := by linarith
  have h2 : e * (3 * q + b + 3) ≤ 3 * q + b + 1 := by
    have h20 : 2 ≤ (3 * q + b + 1) * (20 / m) := by
      rw [mul_div_assoc', le_div_iff₀ hm0]; linarith
    nlinarith
  have hpb : 0 ≤ p * b := mul_nonneg hp hb
  have hqb' : 0 ≤ q * b := mul_nonneg hq hb
  have hpq : 0 ≤ p * q := mul_nonneg hp hq
  have hN : p * b * (1 * e * (3 * q + b) - 1 * (3 * q + b + 1)) +
      q * b * (1 * e * (3 * q + b + 3) - 1 * (3 * q + b + 1)) +
      p * q * (1 * e * (3 * q + b - 1) - 1 * (3 * q + b + 1)) +
      p * q * (1 * e * (3 * q + b + 2) - 1 * (3 * q + b + 1)) ≤ 0 := by
    have a1 : 1 * e * (3 * q + b) - 1 * (3 * q + b + 1) ≤ 0 := by nlinarith
    have a2 : 1 * e * (3 * q + b + 3) - 1 * (3 * q + b + 1) ≤ 0 := by nlinarith
    have a3 : 1 * e * (3 * q + b - 1) - 1 * (3 * q + b + 1) ≤ 0 := by nlinarith
    have a4 : 1 * e * (3 * q + b + 2) - 1 * (3 * q + b + 1) ≤ 0 := by nlinarith
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hpb a1, mul_nonpos_of_nonneg_of_nonpos hqb' a2,
      mul_nonpos_of_nonneg_of_nonpos hpq a3, mul_nonpos_of_nonneg_of_nonpos hpq a4]
  have : (p * b * (1 * e * (3 * q + b) - 1 * (3 * q + b + 1)) +
      q * b * (1 * e * (3 * q + b + 3) - 1 * (3 * q + b + 1)) +
      p * q * (1 * e * (3 * q + b - 1) - 1 * (3 * q + b + 1)) +
      p * q * (1 * e * (3 * q + b + 2) - 1 * (3 * q + b + 1))) / (m * (m - 1)) ≤ 0 :=
    div_nonpos_iff.mpr (Or.inr ⟨hN, hD⟩)
  linarith

/-- The one-step bound of PX in all three cases: inside the corner, outside it, and at
consensus (`q = b = 0`, where every interaction is idle). -/
lemma corner_step (p q b m E e : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hb : 0 ≤ b)
    (hs : p + q + b = m) (hm : 16 ≤ m) (R : ℝ)
    (hR : (R = 1 ∧ 7 * m ≤ 8 * p ∧ 1 ≤ q + b) ∨ (R = 0 ∧ 8 * p < 7 * m) ∨
      (R = 0 ∧ q = 0 ∧ b = 0))
    (hE : E = exp (5 / (32 * m) * R)) (he : e = exp (-(20 / m))) :
    cornerForm p q b m E e ≤ 3 * q + b + 1 := by
  have he1 := exp_neg_mul_one_add_le (20 / m)
  have he0 : 0 ≤ e := by rw [he]; exact (exp_pos _).le
  rcases hR with ⟨hR1, hc, hpq⟩ | ⟨hR0, hc⟩ | ⟨hR0, hq0, hb0⟩
  · rw [hR1, mul_one] at hE
    refine corner_inside p q b m E e hp hq hb hs hc hpq (by rw [hE]; exact exp_pos _)
      (by rw [hE]; exact exp_mul_one_sub_le _) ?_
    rw [he]
    have hm0 : 0 < m := by linarith
    exact exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  · rw [hR0, mul_zero, exp_zero] at hE
    rw [hE]
    exact corner_outside p q b m e hq hb hs (by linarith) hc hp he0 (by rw [he]; exact he1)
  · rw [hR0, mul_zero, exp_zero] at hE
    subst hq0 hb0
    rw [hE]
    unfold cornerForm
    simp

/-- The three cases of `corner_step` for a configuration, with `o` the corner's opinion. -/
lemma corner_cases (s : Config n) {o o' : Op}
    (hs : count s o + count s o' + count s .u = n) (P : Prop) [Decidable P]
    (hP : P ↔ 7 * n ≤ 8 * count s o ∧ count s o < n) :
    ((if P then (1 : ℝ) else 0) = 1 ∧ 7 * (n : ℝ) ≤ 8 * count s o ∧
        1 ≤ (count s o' : ℝ) + count s .u) ∨
      ((if P then (1 : ℝ) else 0) = 0 ∧ 8 * (count s o : ℝ) < 7 * n) ∨
      ((if P then (1 : ℝ) else 0) = 0 ∧ (count s o' : ℝ) = 0 ∧ (count s .u : ℝ) = 0) := by
  by_cases h : P
  · obtain ⟨h1, h2⟩ := hP.mp h
    left
    refine ⟨by simp [h], by exact_mod_cast h1, ?_⟩
    have : 1 ≤ count s o' + count s .u := by omega
    exact_mod_cast this
  · rw [hP] at h
    right
    by_cases h8 : 8 * count s o < 7 * n
    · left; exact ⟨by simp [hP, h], by exact_mod_cast h8⟩
    · right
      have h1 : count s o' = 0 := by omega
      have h2 : count s .u = 0 := by omega
      refine ⟨by simp [hP, h], by simp [h1], by simp [h2]⟩

/-- **PX, one step** (cf. [AAE08, Lemma 7]). -/
theorem stepX (hn : 16 ≤ n) (s : Config n) :
    avg (fun p : Interaction n => exp (wX n s (s p.1.1) (s p.1.2)) * cpot fX (step s p)) ≤
      cpot fX s := by
  unfold cpot
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = if XR s then 1 else 0 := ⟨_, rfl⟩
  rw [avg_step_counts (by omega) s (wX n s) (5 / (32 * n) * R)
    (fun i r h => by simp [wX, vbI_idle h, xyI_idle h, hR]) fX]
  have hm : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hch : ∀ i r : Op, ¬ Idle i r → wX n s i r = 5 / (32 * n) * R + -(20 / n) := by
    intro i r h
    rw [wX, ← hR]
    cases i <;> cases r <;> simp [Idle] at h <;> simp [vbI, xyI] <;> field_simp <;> ring
  rw [hch .a .u (by simp [Idle]), hch .b .u (by simp [Idle]), hch .a .b (by simp [Idle]),
    hch .b .a (by simp [Idle]), exp_add]
  have hcases := corner_cases s (o := .a) (o' := .b) (count_add_nat s) (XR s)
    (by rfl)
  rw [← hR] at hcases
  have hform := corner_step (count s .a) (count s .b) (count s .u) n
    (exp (5 / (32 * n) * R)) (exp (-(20 / n))) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (count_add s) hm R hcases rfl rfl
  refine le_trans (le_of_eq ?_) hform
  unfold cornerForm fX
  ring

/-- **PY, one step**: the mirror image of `stepX`. -/
theorem stepY (hn : 16 ≤ n) (s : Config n) :
    avg (fun p : Interaction n => exp (wY n s (s p.1.1) (s p.1.2)) * cpot fY (step s p)) ≤
      cpot fY s := by
  unfold cpot
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = if YR s then 1 else 0 := ⟨_, rfl⟩
  rw [avg_step_counts (by omega) s (wY n s) (5 / (32 * n) * R)
    (fun i r h => by simp [wY, vbI_idle h, xyI_idle h, hR]) fY]
  have hm : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hch : ∀ i r : Op, ¬ Idle i r → wY n s i r = 5 / (32 * n) * R + -(20 / n) := by
    intro i r h
    rw [wY, ← hR]
    cases i <;> cases r <;> simp [Idle] at h <;> simp [vbI, xyI] <;> field_simp <;> ring
  rw [hch .a .u (by simp [Idle]), hch .b .u (by simp [Idle]), hch .a .b (by simp [Idle]),
    hch .b .a (by simp [Idle]), exp_add]
  have hs' : count s .b + count s .a + count s .u = n := by
    have := count_add_nat s; omega
  have hcases := corner_cases s (o := .b) (o' := .a) hs' (YR s) (by rfl)
  rw [← hR] at hcases
  have hform := corner_step (count s .b) (count s .a) (count s .u) n
    (exp (5 / (32 * n) * R)) (exp (-(20 / n))) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (by have := count_add s; linarith) hm R hcases rfl rfl
  refine le_trans (le_of_eq ?_) hform
  unfold cornerForm fY
  ring

end Undecided.Sequential
