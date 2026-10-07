import Undecided.SequentialCounts
import Undecided.SequentialMartingale

/-! # One-step supermartingale inequalities

Each bound of the proof is a weight `φ` (per interaction) and a potential `F` (a function of the
counts `x, y, b`) with `avg_p exp (φ s p) * F (step s p) ≤ F s` for every configuration `s`, the
hypothesis of `expList_exp_pathSum_le`. Writing `u = x - y`, `v = x + y`:

* `stepSC` (state-changing interactions, as in [AAE08, §4.4, Lemmas 2–4]): weight
  `(I_vb / 5 - I_xy / 6) / n`, potential `1 / (u² + 4n)`;
* `stepC` (central region, where a constant fraction of interactions changes the state):
  weight `(R_c - 256 I_ch) / 256`, potential `1`.

The one-step expectation is `avg_step_counts`; what remains are inequalities between reals.
-/

namespace Undecided.Sequential
open Dynamics Real

variable {n : ℕ}

/-! ### Elementary bounds -/

lemma exp_mul_one_sub_le (a : ℝ) : exp a * (1 - a) ≤ 1 := by
  have h1 := add_one_le_exp (-a)
  have h2 : exp a * exp (-a) = 1 := by rw [← exp_add]; simp
  nlinarith [exp_pos a]

lemma exp_neg_mul_one_add_le (a : ℝ) : exp (-a) * (1 + a) ≤ 1 := by
  have h1 := add_one_le_exp a
  have h2 : exp (-a) * exp a = 1 := by rw [← exp_add]; simp
  nlinarith [exp_pos (-a)]

/-- A nonpositive numerator in the one-step formula: the potential does not increase. -/
lemma add_div_le_self {Φ N m : ℝ} (hN : N ≤ 0) (hm : 2 ≤ m) : Φ + N / (m * (m - 1)) ≤ Φ := by
  have hD : 0 < m * (m - 1) := by nlinarith
  have : N / (m * (m - 1)) ≤ 0 := div_nonpos_iff.mpr (Or.inr ⟨hN, hD.le⟩)
  linarith

/-- A potential depending on the counts only. -/
noncomputable def cpot (Φ : ℝ → ℝ → ℝ → ℝ) (s : Config n) : ℝ :=
  Φ (count s .a) (count s .b) (count s .u)

lemma two_le_cast {n : ℕ} (hn : 2 ≤ n) : (2 : ℝ) ≤ n := by exact_mod_cast hn

/-! ### P1: state-changing interactions -/

/-- Weight of P1: `(I_vb / 5 - I_xy / 6) / n`. -/
noncomputable def wSC (n : ℕ) (i r : Op) : ℝ := (vbI i r / 5 - xyI i r / 6) / n

/-- Potential of P1: `1 / ((x - y)² + 4n)` ([AAE08, §4.4] uses `1 / (u² + 2n)`). -/
noncomputable def fSC (n : ℕ) (x y _b : ℝ) : ℝ := 1 / ((x - y) ^ 2 + 4 * n)

/-- The polynomial core of P1 for `xb`/`yb` interactions (the `I_vb` part of [AAE08, Lemma 2]). -/
lemma sc_vb_poly (x y m : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y ≤ m) (hm : 1 ≤ m) :
    5 * m * (x * ((x - y - 1) ^ 2 + 4 * m) + y * ((x - y + 1) ^ 2 + 4 * m)) *
        ((x - y) ^ 2 + 4 * m) ≤
      (5 * m - 1) * (x + y) * (((x - y + 1) ^ 2 + 4 * m) * ((x - y - 1) ^ 2 + 4 * m)) := by
  have hz : 0 ≤ (x - y) ^ 2 := sq_nonneg _
  have key : (5 * m - 1) * (x + y) * (((x - y + 1) ^ 2 + 4 * m) * ((x - y - 1) ^ 2 + 4 * m)) -
      5 * m * (x * ((x - y - 1) ^ 2 + 4 * m) + y * ((x - y + 1) ^ 2 + 4 * m)) *
        ((x - y) ^ 2 + 4 * m) =
      (x + y) * (4 * m ^ 2 - 3 * m - 1 + 17 * m * (x - y) ^ 2 + 9 * ((x - y) ^ 2) ^ 2 +
        2 * (x - y) ^ 2) + 10 * ((x - y) ^ 2 + 4 * m) * (x - y) ^ 2 * (m - (x + y)) := by ring
  have h1 : 0 ≤ 4 * m ^ 2 - 3 * m - 1 + 17 * m * (x - y) ^ 2 + 9 * ((x - y) ^ 2) ^ 2 +
      2 * (x - y) ^ 2 := by nlinarith
  have h2 := mul_nonneg (by linarith : 0 ≤ x + y) h1
  have h3 : 0 ≤ 10 * ((x - y) ^ 2 + 4 * m) * (x - y) ^ 2 * (m - (x + y)) :=
    mul_nonneg (mul_nonneg (by positivity) hz) (by linarith)
  linarith

/-- The polynomial core of P1 for `xy`/`yx` interactions ([AAE08, Lemma 3]). -/
lemma sc_xy_poly (u m : ℝ) (hm : 1 ≤ m) :
    6 * m * (((u - 1) ^ 2 + 4 * m) + ((u + 1) ^ 2 + 4 * m)) * (u ^ 2 + 4 * m) ≤
      2 * (6 * m + 1) * (((u + 1) ^ 2 + 4 * m) * ((u - 1) ^ 2 + 4 * m)) := by
  nlinarith [sq_nonneg (u ^ 2 - 5 * m - 1), sq_nonneg u,
    mul_nonneg (by linarith : (0 : ℝ) ≤ m) (sq_nonneg u)]

/-- Numerator of the one-step formula of P1 is nonpositive. -/
lemma sc_numerator (x y b m : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hb : 0 ≤ b) (hxy : x + y ≤ m)
    (hm : 1 ≤ m) :
    x * b * (exp (1 / (5 * m)) * (1 / ((x + 1 - y) ^ 2 + 4 * m)) -
        1 / ((x - y) ^ 2 + 4 * m)) +
      y * b * (exp (1 / (5 * m)) * (1 / ((x - (y + 1)) ^ 2 + 4 * m)) -
        1 / ((x - y) ^ 2 + 4 * m)) +
      x * y * (exp (-(1 / (6 * m))) * (1 / ((x - (y - 1)) ^ 2 + 4 * m)) -
        1 / ((x - y) ^ 2 + 4 * m)) +
      x * y * (exp (-(1 / (6 * m))) * (1 / ((x - 1 - y) ^ 2 + 4 * m)) -
        1 / ((x - y) ^ 2 + 4 * m)) ≤ 0 := by
  set f := (x - y) ^ 2 + 4 * m with hf
  set fp := (x - y + 1) ^ 2 + 4 * m with hfp
  set fm := (x - y - 1) ^ 2 + 4 * m with hfm
  have e1 : (x + 1 - y) ^ 2 + 4 * m = fp := by rw [hfp]; ring
  have e2 : (x - (y + 1)) ^ 2 + 4 * m = fm := by rw [hfm]; ring
  have e3 : (x - (y - 1)) ^ 2 + 4 * m = fp := by rw [hfp]; ring
  have e4 : (x - 1 - y) ^ 2 + 4 * m = fm := by rw [hfm]; ring
  rw [e1, e2, e3, e4]
  have hf0 : 0 < f := by positivity
  have hfp0 : 0 < fp := by positivity
  have hfm0 : 0 < fm := by positivity
  have hm0 : 0 < m := by linarith
  -- `xb`/`yb`: the potential drops by the factor `1 - 1/(5m)`
  have hA : x * (1 / fp) + y * (1 / fm) ≤ (1 - 1 / (5 * m)) * ((x + y) * (1 / f)) := by
    have hp := sc_vb_poly x y m hx hy hxy hm
    rw [← hf, ← hfp, ← hfm] at hp
    have lhs : x * (1 / fp) + y * (1 / fm) = (x * fm + y * fp) / (fp * fm) := by
      field_simp
    have rhs : (1 - 1 / (5 * m)) * ((x + y) * (1 / f)) = (5 * m - 1) * (x + y) / (5 * m * f) := by
      field_simp
    rw [lhs, rhs, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hA' : exp (1 / (5 * m)) * (x * (1 / fp) + y * (1 / fm)) ≤ (x + y) * (1 / f) := by
    have h0 : 0 ≤ (x + y) * (1 / f) := by positivity
    calc exp (1 / (5 * m)) * (x * (1 / fp) + y * (1 / fm))
        ≤ exp (1 / (5 * m)) * ((1 - 1 / (5 * m)) * ((x + y) * (1 / f))) :=
          mul_le_mul_of_nonneg_left hA (exp_pos _).le
      _ = (exp (1 / (5 * m)) * (1 - 1 / (5 * m))) * ((x + y) * (1 / f)) := by ring
      _ ≤ 1 * ((x + y) * (1 / f)) :=
          mul_le_mul_of_nonneg_right (exp_mul_one_sub_le _) h0
      _ = (x + y) * (1 / f) := one_mul _
  -- `xy`/`yx`: the potential rises by at most the factor `1 + 1/(6m)`
  have hB : 1 / fp + 1 / fm ≤ (1 + 1 / (6 * m)) * (2 * (1 / f)) := by
    have hp := sc_xy_poly (x - y) m hm
    rw [← hf, ← hfp, ← hfm] at hp
    have lhs : 1 / fp + 1 / fm = (fm + fp) / (fp * fm) := by field_simp
    have rhs : (1 + 1 / (6 * m)) * (2 * (1 / f)) = 2 * (6 * m + 1) / (6 * m * f) := by
      field_simp
    rw [lhs, rhs, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hB' : exp (-(1 / (6 * m))) * (1 / fp + 1 / fm) ≤ 2 * (1 / f) := by
    have h0 : 0 ≤ 2 * (1 / f) := by positivity
    calc exp (-(1 / (6 * m))) * (1 / fp + 1 / fm)
        ≤ exp (-(1 / (6 * m))) * ((1 + 1 / (6 * m)) * (2 * (1 / f))) :=
          mul_le_mul_of_nonneg_left hB (exp_pos _).le
      _ = (exp (-(1 / (6 * m))) * (1 + 1 / (6 * m))) * (2 * (1 / f)) := by ring
      _ ≤ 1 * (2 * (1 / f)) := mul_le_mul_of_nonneg_right (exp_neg_mul_one_add_le _) h0
      _ = 2 * (1 / f) := one_mul _
  have hxyb : 0 ≤ x * y := mul_nonneg hx hy
  nlinarith [mul_le_mul_of_nonneg_left hA' hb, mul_le_mul_of_nonneg_left hB' hxyb]

/-- **P1, one step** (cf. [AAE08, Lemmas 2–4]). -/
theorem stepSC (hn : 2 ≤ n) (s : Config n) :
    avg (fun p : Interaction n => exp (wSC n (s p.1.1) (s p.1.2)) * cpot (fSC n) (step s p)) ≤
      cpot (fSC n) s := by
  unfold cpot
  rw [avg_step_counts hn s (wSC n) 0 (fun i r h => by simp [wSC, vbI_idle h, xyI_idle h])]
  have hau : wSC n .a .u = 1 / (5 * n) := by simp [wSC, vbI, xyI]; ring
  have hbu : wSC n .b .u = 1 / (5 * n) := by simp [wSC, vbI, xyI]; ring
  have hab : wSC n .a .b = -(1 / (6 * n)) := by simp [wSC, vbI, xyI]; ring
  have hba : wSC n .b .a = -(1 / (6 * n)) := by simp [wSC, vbI, xyI]; ring
  rw [hau, hbu, hab, hba, exp_zero, one_mul]
  refine add_div_le_self ?_ (two_le_cast hn)
  have hs := count_add s
  simp only [fSC]
  exact sc_numerator _ _ _ _ (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (by linarith [(Nat.cast_nonneg (count s .u) : (0 : ℝ) ≤ _)])
    (by linarith [two_le_cast hn])

/-! ### PC: the central region -/

/-- The central region: more than `n/8` decided agents, and fewer than `7n/8` of each opinion. -/
def CentralR (s : Config n) : Prop :=
  n < 8 * (count s .a + count s .b) ∧ 8 * count s .a < 7 * n ∧ 8 * count s .b < 7 * n

instance (s : Config n) : Decidable (CentralR s) := by unfold CentralR; infer_instance

/-- Weight of PC: `(R_c - 256 I_ch) / 256`. -/
noncomputable def wC (s : Config n) (i r : Op) : ℝ :=
  ((if CentralR s then 1 else 0) - 256 * (vbI i r + xyI i r)) / 256

/-- In the central region, a constant fraction of interactions changes the state. -/
lemma central_pairs (x y b m : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hb : 0 ≤ b) (hs : x + y + b = m)
    (h1 : m < 8 * (x + y)) (h2 : 8 * x < 7 * m) (h3 : 8 * y < 7 * m) :
    m ^ 2 ≤ 128 * (x * b + y * b + 2 * (x * y)) := by
  rcases le_or_gt (m / 16) b with hb' | hb'
  · nlinarith
  · have hx' : m / 16 < x := by linarith
    have hy' : m / 16 < y := by linarith
    nlinarith [mul_pos (sub_pos.mpr hx') (sub_pos.mpr hy')]

/-- **PC, one step.** -/
theorem stepC (hn : 2 ≤ n) (s : Config n) :
    avg (fun p : Interaction n => exp (wC s (s p.1.1) (s p.1.2)) *
      cpot (fun _ _ _ => 1) (step s p)) ≤ cpot (fun _ _ _ => 1) s := by
  unfold cpot
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = if CentralR s then 1 else 0 := ⟨_, rfl⟩
  rw [avg_step_counts hn s (wC s) (R / 256)
    (fun i r h => by simp [wC, vbI_idle h, xyI_idle h, hR])
    (fun _ _ _ => 1)]
  have hch : ∀ i r : Op, ¬ Idle i r → wC s i r = R / 256 - 1 := by
    intro i r h
    unfold Idle at h
    cases i <;> cases r <;> simp_all [wC, vbI, xyI] <;> ring
  rw [hch .a .u (by simp [Idle]), hch .b .u (by simp [Idle]), hch .a .b (by simp [Idle]),
    hch .b .a (by simp [Idle])]
  simp only [mul_one]
  have hm := two_le_cast hn
  have hD : 0 < (n : ℝ) * (n - 1) := by nlinarith
  set x : ℝ := (count s .a : ℝ) with hxd
  set y : ℝ := (count s .b : ℝ) with hyd
  set b : ℝ := (count s .u : ℝ) with hbd
  have hx : 0 ≤ x := Nat.cast_nonneg _
  have hy : 0 ≤ y := Nat.cast_nonneg _
  have hb : 0 ≤ b := Nat.cast_nonneg _
  set P := (x * b + y * b + 2 * (x * y)) / (n * (n - 1)) with hP
  have hP0 : 0 ≤ P := by positivity
  have he : exp (R / 256 - 1) = exp (R / 256) * exp (-1) := by rw [← exp_add]; ring_nf
  have hform : exp (R / 256) + (x * b * (exp (R / 256 - 1) - exp (R / 256)) +
      y * b * (exp (R / 256 - 1) - exp (R / 256)) +
      x * y * (exp (R / 256 - 1) - exp (R / 256)) +
      x * y * (exp (R / 256 - 1) - exp (R / 256))) / (n * (n - 1)) =
      exp (R / 256) * (1 - P * (1 - exp (-1))) := by
    rw [he, hP]; field_simp; ring
  rw [hform]
  have hq : 1 - exp (-1) ≥ 1 / 2 := by
    have := Real.exp_neg_one_lt_half
    linarith
  by_cases hc : CentralR s
  · have hR1 : R = 1 := by simp [hR, hc]
    obtain ⟨h1, h2, h3⟩ := hc
    have hs := count_add s
    have hpairs := central_pairs x y b n hx hy hb hs (by rw [hxd, hyd]; exact_mod_cast h1)
      (by rw [hxd]; exact_mod_cast h2) (by rw [hyd]; exact_mod_cast h3)
    have hP1 : 1 / 128 ≤ P := by
      rw [hP, le_div_iff₀ hD]
      nlinarith
    rw [hR1]
    have h4 : 1 - P * (1 - exp (-1)) ≤ 1 - 1 / 256 := by nlinarith
    calc exp (1 / 256) * (1 - P * (1 - exp (-1))) ≤ exp (1 / 256) * (1 - 1 / 256) :=
          mul_le_mul_of_nonneg_left h4 (exp_pos _).le
      _ ≤ 1 := exp_mul_one_sub_le _
  · have hR0 : R = 0 := by simp [hR, hc]
    rw [hR0]
    have h4 : 1 - P * (1 - exp (-1)) ≤ 1 := by nlinarith
    simpa using h4

end Undecided.Sequential
