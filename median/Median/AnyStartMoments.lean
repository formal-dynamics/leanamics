import Median.BinaryAux

/-! # Moments of one round of the binary median dynamics

The number of `true` nodes after one round is a sum of independent `{0,1}`
coordinates. This file records the variance (`3 n p² (1-p)²`), a fourth-moment
bound, the resulting lower bound on the mean absolute deviation, and the
Hoeffding mgf, together with the symmetry that flips both opinions.
-/

namespace Median
open Finset Real Dynamics

variable {n : ℕ} {γ : Type*} [Fintype γ]

/-! ### Averages of independent coordinates -/

lemma avg_cauchy (f g : γ → ℝ) :
    (avg (fun y => f y * g y)) ^ 2 ≤ avg (fun y => f y ^ 2) * avg (fun y => g y ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq univ f g
  have hN : (0 : ℝ) ≤ (Fintype.card γ : ℝ) := by positivity
  have hdiv : ((∑ y, f y * g y) / (Fintype.card γ : ℝ)) ^ 2
      ≤ ((∑ y, f y ^ 2) / (Fintype.card γ : ℝ)) * ((∑ y, g y ^ 2) / (Fintype.card γ : ℝ)) := by
    rw [div_pow, div_mul_div_comm]
    refine div_le_div_of_nonneg_right ?_ (mul_nonneg hN hN)
    simpa [sq] using h
  simpa [avg] using hdiv

/-- Pull one distinguished coordinate out of a product average. -/
lemma avg_cons_mul [Nonempty γ] (F : γ → ℝ) (G : (Fin n → γ) → ℝ) :
    avg (fun ω : Fin (n + 1) → γ => F (ω 0) * G (fun i : Fin n => ω i.succ))
      = avg F * avg G := by
  have hfun : (fun ω : Fin (n + 1) → γ => F (ω 0) * G (fun i => ω i.succ))
      = fun ω => (fun p : γ × (Fin n → γ) => F p.1 * G p.2)
          ((Fin.consEquiv (fun _ : Fin (n + 1) => γ)).symm ω) := by
    funext ω
    rfl
  rw [hfun,
    avg_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => γ)).symm
      (fun p : γ × (Fin n → γ) => F p.1 * G p.2),
    avg_mul_prod F G]

lemma avg_sum_coord (f : Fin n → γ → ℝ) :
    avg (fun ω : Fin n → γ => ∑ i, f i (ω i)) = ∑ i, avg (f i) := by
  rw [avg_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simpa using avg_eval n i (f i)

lemma avg_sum_sq_indep (f : Fin n → γ → ℝ) (hf0 : ∀ i, avg (f i) = 0) :
    avg (fun ω : Fin n → γ => (∑ i, f i (ω i)) ^ 2) = ∑ i, avg (fun y => (f i y) ^ 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hG0 : avg (fun t : Fin n → γ => ∑ i, f i.succ (t i)) = 0 := by
        rw [avg_sum_coord]
        simp [hf0]
      have htail := ih (fun i => f i.succ) (fun i => hf0 i.succ)
      have hsplit : ∀ ω : Fin (n + 1) → γ,
          (∑ i, f i (ω i)) ^ 2
            = (f 0 (ω 0) + ∑ i : Fin n, f i.succ (ω i.succ)) ^ 2 := by
        intro ω
        congr 1
        rw [Fin.sum_univ_succ]
      simp_rw [hsplit]
      have hexp : ∀ a : ℝ, ∀ b : ℝ, (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := by
        intro a b; ring
      simp_rw [hexp]
      have h1 : avg (fun ω : Fin (n + 1) → γ => (f 0 (ω 0)) ^ 2)
          = avg (fun y => (f 0 y) ^ 2) := by
        simpa using avg_eval (n + 1) (0 : Fin (n + 1)) (fun y => (f 0 y) ^ 2)
      have h2 : avg (fun ω : Fin (n + 1) → γ =>
          (∑ i : Fin n, f i.succ (ω i.succ)) ^ 2)
          = ∑ i : Fin n, avg (fun y => (f i.succ y) ^ 2) := by
        have hfun : (fun ω : Fin (n + 1) → γ =>
            (∑ i : Fin n, f i.succ (ω i.succ)) ^ 2)
            = fun ω => (fun _ : γ => (1 : ℝ)) (ω 0)
                * (fun t : Fin n → γ => (∑ i, f i.succ (t i)) ^ 2) (fun i => ω i.succ) := by
          funext ω; simp
        rw [hfun, avg_cons_mul, avg_const, one_mul, htail]
      have h3 : avg (fun ω : Fin (n + 1) → γ =>
          2 * f 0 (ω 0) * ∑ i : Fin n, f i.succ (ω i.succ)) = 0 := by
        have hfun : (fun ω : Fin (n + 1) → γ =>
            2 * f 0 (ω 0) * ∑ i : Fin n, f i.succ (ω i.succ))
            = fun ω => (fun y => 2 * f 0 y) (ω 0)
                * (fun t : Fin n → γ => ∑ i, f i.succ (t i)) (fun i => ω i.succ) := by
          funext ω; ring
        rw [hfun, avg_cons_mul, hG0, mul_zero]
        rw [avg_const_mul, hf0 0, mul_zero]
      have hadd := avg_add
        (fun ω : Fin (n + 1) → γ => (f 0 (ω 0)) ^ 2
            + (∑ i : Fin n, f i.succ (ω i.succ)) ^ 2)
        (fun ω : Fin (n + 1) → γ => 2 * f 0 (ω 0) * ∑ i : Fin n, f i.succ (ω i.succ))
      rw [← hadd]
      have hsum : avg (fun ω : Fin (n + 1) → γ =>
          (f 0 (ω 0)) ^ 2 + (∑ i : Fin n, f i.succ (ω i.succ)) ^ 2)
          = avg (fun y => (f 0 y) ^ 2) + ∑ i : Fin n, avg (fun y => (f i.succ y) ^ 2) := by
        rw [avg_add, h1, h2]
      rw [hsum, h3, add_zero, Fin.sum_univ_succ]
      simp

/-- Fourth moment of a sum of independent centered coordinates bounded by `1`. -/
lemma avg_sum_fourth_indep (f : Fin n → γ → ℝ) (hf0 : ∀ i, avg (f i) = 0)
    (hfb : ∀ i y, |f i y| ≤ 1) :
    avg (fun ω : Fin n → γ => (∑ i, f i (ω i)) ^ 4)
      ≤ (∑ i, avg (fun y => (f i y) ^ 2))
        + 3 * (∑ i, avg (fun y => (f i y) ^ 2)) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hG0 : avg (fun t : Fin n → γ => ∑ i, f i.succ (t i)) = 0 := by
        rw [avg_sum_coord]; simp [hf0]
      have hGsq := avg_sum_sq_indep (fun i => f i.succ) (fun i => hf0 i.succ)
      have hG4 := ih (fun i => f i.succ) (fun i => hf0 i.succ) (fun i y => hfb i.succ y)
      set σt : ℝ := ∑ i : Fin n, avg (fun y => (f i.succ y) ^ 2) with hσt
      have hfb2 : ∀ y, (f 0 y) ^ 4 ≤ (f 0 y) ^ 2 := by
        intro y
        have h1 : (f 0 y) ^ 2 ≤ 1 := by
          have := hfb 0 y
          nlinarith [sq_nonneg (f 0 y)]
        have h4 : (f 0 y) ^ 4 = (f 0 y) ^ 2 * (f 0 y) ^ 2 := by ring
        nlinarith
      have hE4 : avg (fun y => (f 0 y) ^ 4) ≤ avg (fun y => (f 0 y) ^ 2) :=
        avg_le_avg hfb2
      have hsplit : ∀ ω : Fin (n + 1) → γ,
          (∑ i, f i (ω i)) ^ 4
            = (f 0 (ω 0) + ∑ i : Fin n, f i.succ (ω i.succ)) ^ 4 := by
        intro ω; congr 1; rw [Fin.sum_univ_succ]
      simp_rw [hsplit]
      have hexp : ∀ a b : ℝ,
          (a + b) ^ 4 = a ^ 4 + b ^ 4 + 4 * a ^ 3 * b + 6 * a ^ 2 * b ^ 2 + 4 * a * b ^ 3 := by
        intro a b; ring
      simp_rw [hexp]
      -- factor each average
      have hA : avg (fun ω : Fin (n + 1) → γ => (f 0 (ω 0)) ^ 4)
          = avg (fun y => (f 0 y) ^ 4) := by
        simpa using avg_eval (n + 1) (0 : Fin (n + 1)) (fun y => (f 0 y) ^ 4)
      have hB : avg (fun ω : Fin (n + 1) → γ =>
          (∑ i : Fin n, f i.succ (ω i.succ)) ^ 4)
          = avg (fun t : Fin n → γ => (∑ i, f i.succ (t i)) ^ 4) := by
        have hfun : (fun ω : Fin (n + 1) → γ =>
            (∑ i : Fin n, f i.succ (ω i.succ)) ^ 4)
            = fun ω => (fun _ : γ => (1 : ℝ)) (ω 0)
                * (fun t => (∑ i, f i.succ (t i)) ^ 4) (fun i => ω i.succ) := by
          funext ω; simp
        rw [hfun, avg_cons_mul, avg_const, one_mul]
      have hC : avg (fun ω : Fin (n + 1) → γ =>
          4 * (f 0 (ω 0)) ^ 3 * ∑ i : Fin n, f i.succ (ω i.succ)) = 0 := by
        have hfun : (fun ω : Fin (n + 1) → γ =>
            4 * (f 0 (ω 0)) ^ 3 * ∑ i : Fin n, f i.succ (ω i.succ))
            = fun ω => (fun y => 4 * (f 0 y) ^ 3) (ω 0)
                * (fun t => ∑ i, f i.succ (t i)) (fun i => ω i.succ) := by
          funext ω; ring
        rw [hfun, avg_cons_mul, hG0, mul_zero]
      have hD : avg (fun ω : Fin (n + 1) → γ =>
          6 * (f 0 (ω 0)) ^ 2 * (∑ i : Fin n, f i.succ (ω i.succ)) ^ 2)
          = 6 * avg (fun y => (f 0 y) ^ 2) * σt := by
        have hfun : (fun ω : Fin (n + 1) → γ =>
            6 * (f 0 (ω 0)) ^ 2 * (∑ i : Fin n, f i.succ (ω i.succ)) ^ 2)
            = fun ω => (fun y => 6 * (f 0 y) ^ 2) (ω 0)
                * (fun t => (∑ i, f i.succ (t i)) ^ 2) (fun i => ω i.succ) := by
          funext ω; ring
        rw [hfun, avg_cons_mul, avg_const_mul, hGsq, hσt]
        ring
      have hE : avg (fun ω : Fin (n + 1) → γ =>
          4 * f 0 (ω 0) * (∑ i : Fin n, f i.succ (ω i.succ)) ^ 3) = 0 := by
        have hfun : (fun ω : Fin (n + 1) → γ =>
            4 * f 0 (ω 0) * (∑ i : Fin n, f i.succ (ω i.succ)) ^ 3)
            = fun ω => (fun y => 4 * f 0 y) (ω 0)
                * (fun t => (∑ i, f i.succ (t i)) ^ 3) (fun i => ω i.succ) := by
          funext ω; ring
        rw [hfun, avg_cons_mul, avg_const_mul, hf0 0]
        ring
      -- reassemble the sum of the five terms
      have hsum := avg_add
        (fun ω : Fin (n + 1) → γ => (f 0 (ω 0)) ^ 4
            + (∑ i : Fin n, f i.succ (ω i.succ)) ^ 4
            + 4 * (f 0 (ω 0)) ^ 3 * ∑ i : Fin n, f i.succ (ω i.succ))
        (fun ω : Fin (n + 1) → γ =>
            6 * (f 0 (ω 0)) ^ 2 * (∑ i : Fin n, f i.succ (ω i.succ)) ^ 2
            + 4 * f 0 (ω 0) * (∑ i : Fin n, f i.succ (ω i.succ)) ^ 3)
      -- pointwise the expanded polynomial equals the sum of those groups
      have hpt : ∀ ω : Fin (n + 1) → γ,
          (f 0 (ω 0) + ∑ i : Fin n, f i.succ (ω i.succ)) ^ 4
            = ((f 0 (ω 0)) ^ 4 + (∑ i : Fin n, f i.succ (ω i.succ)) ^ 4
                + 4 * (f 0 (ω 0)) ^ 3 * ∑ i : Fin n, f i.succ (ω i.succ))
              + (6 * (f 0 (ω 0)) ^ 2 * (∑ i : Fin n, f i.succ (ω i.succ)) ^ 2
                + 4 * f 0 (ω 0) * (∑ i : Fin n, f i.succ (ω i.succ)) ^ 3) := by
        intro ω; ring
      simp_rw [hpt]
      rw [hsum]
      have hL : avg (fun ω : Fin (n + 1) → γ => (f 0 (ω 0)) ^ 4
            + (∑ i : Fin n, f i.succ (ω i.succ)) ^ 4
            + 4 * (f 0 (ω 0)) ^ 3 * ∑ i : Fin n, f i.succ (ω i.succ))
          = avg (fun y => (f 0 y) ^ 4)
            + avg (fun t : Fin n → γ => (∑ i, f i.succ (t i)) ^ 4) := by
        rw [avg_add, avg_add, hA, hB, hC, add_zero]
      have hR : avg (fun ω : Fin (n + 1) → γ =>
            6 * (f 0 (ω 0)) ^ 2 * (∑ i : Fin n, f i.succ (ω i.succ)) ^ 2
            + 4 * f 0 (ω 0) * (∑ i : Fin n, f i.succ (ω i.succ)) ^ 3)
          = 6 * avg (fun y => (f 0 y) ^ 2) * σt := by
        rw [avg_add, hD, hE, add_zero]
      rw [hL, hR]
      -- compare with σ² + 3 σ⁴ for the whole sum
      set a : ℝ := avg (fun y => (f 0 y) ^ 2) with ha
      have hσ : ∑ i : Fin (n + 1), avg (fun y => (f i y) ^ 2) = a + σt := by
        rw [Fin.sum_univ_succ, ha, hσt]
      rw [hσ]
      have htail : avg (fun t : Fin n → γ => (∑ i, f i.succ (t i)) ^ 4) ≤ σt + 3 * σt ^ 2 := hG4
      have hhead : avg (fun y => (f 0 y) ^ 4) ≤ a := hE4
      have hnonneg_a : 0 ≤ a := avg_nonneg fun y => sq_nonneg _
      have hnonneg_t : 0 ≤ σt := by
        rw [hσt]; exact Finset.sum_nonneg fun i _ => avg_nonneg fun y => sq_nonneg _
      nlinarith [hhead, htail, sq_nonneg a, sq_nonneg σt, mul_nonneg hnonneg_a hnonneg_t]

/-! ### Mean absolute deviation from the second and fourth moments -/

lemma avg_abs_ge_of_moments (Z : γ → ℝ) (h0 : avg Z = 0) :
    avg (fun y => |Z y|) ≥ (avg (fun y => Z y ^ 2)) ^ 2
      / Real.sqrt (avg (fun y => Z y ^ 2) * avg (fun y => Z y ^ 4)) := by
  have hsq : (avg (fun y => Z y ^ 2)) ^ 2
      ≤ avg (fun y => |Z y|) * avg (fun y => |Z y| ^ 3) := by
    have h := avg_cauchy (fun y => Real.sqrt |Z y|) (fun y => |Z y| ^ (3 / 2 : ℝ))
    -- fallback: Cauchy in the form (E[|Z| * |Z|])² ≤ E[|Z|] E[|Z|³]
    have h2 := avg_cauchy (fun y => Real.sqrt |Z y|) (fun y => |Z y| * Real.sqrt |Z y|)
    simp only [sq_sqrt (abs_nonneg _)] at h2
    have hpow : ∀ y, Real.sqrt |Z y| * (|Z y| * Real.sqrt |Z y|) = |Z y| ^ 2 := by
      intro y
      have hnn : 0 ≤ |Z y| := abs_nonneg _
      calc Real.sqrt |Z y| * (|Z y| * Real.sqrt |Z y|)
          = |Z y| * (Real.sqrt |Z y| * Real.sqrt |Z y|) := by ring
        _ = |Z y| * |Z y| := by rw [Real.mul_self_sqrt hnn]
        _ = |Z y| ^ 2 := by ring
    simp_rw [hpow] at h2
    have h3 : ∀ y, (|Z y| * Real.sqrt |Z y|) ^ 2 = |Z y| ^ 3 := by
      intro y
      have hnn : 0 ≤ |Z y| := abs_nonneg _
      calc (|Z y| * Real.sqrt |Z y|) ^ 2
          = |Z y| ^ 2 * (Real.sqrt |Z y| * Real.sqrt |Z y|) := by ring
        _ = |Z y| ^ 2 * |Z y| := by rw [Real.mul_self_sqrt hnn]
        _ = |Z y| ^ 3 := by ring
    simp_rw [h3] at h2
    simpa [sq_abs] using h2
  have h4 : (avg (fun y => |Z y| ^ 3)) ^ 2
      ≤ avg (fun y => Z y ^ 2) * avg (fun y => Z y ^ 4) := by
    have h := avg_cauchy (fun y => |Z y|) (fun y => |Z y| ^ 2)
    have hp : ∀ y, |Z y| * |Z y| ^ 2 = |Z y| ^ 3 := fun y => by ring
    have hq : ∀ y, (|Z y| ^ 2) ^ 2 = |Z y| ^ 4 := fun y => by ring
    simp_rw [hp, hq, sq_abs] at h
    have h44 : ∀ y, |Z y| ^ 4 = Z y ^ 4 := fun y => by
      rw [← sq_abs, ← sq_abs]; ring
    simp_rw [h44] at h
    exact h
  -- combine
  set s2 : ℝ := avg (fun y => Z y ^ 2) with hs2
  set s4 : ℝ := avg (fun y => Z y ^ 4) with hs4
  set a1 : ℝ := avg (fun y => |Z y|) with ha1
  set a3 : ℝ := avg (fun y => |Z y| ^ 3) with ha3
  have hs2nn : 0 ≤ s2 := by rw [hs2]; exact avg_nonneg fun y => sq_nonneg _
  have hs4nn : 0 ≤ s4 := by rw [hs4]; exact avg_nonneg fun y => by positivity
  have ha1nn : 0 ≤ a1 := by rw [ha1]; exact avg_nonneg fun y => abs_nonneg _
  have ha3nn : 0 ≤ a3 := by rw [ha3]; exact avg_nonneg fun y => by positivity
  have hden : 0 ≤ Real.sqrt (s2 * s4) := Real.sqrt_nonneg _
  by_cases hzero : s2 * s4 = 0
  · rw [hzero, Real.sqrt_zero, div_zero]
    exact ha1nn
  · have hpos : 0 < s2 * s4 := lt_of_le_of_ne (mul_nonneg hs2nn hs4nn) (Ne.symm hzero)
    have hsq' : s2 ^ 2 ≤ a1 * a3 := by simpa [hs2, ha1, ha3] using hsq
    have h4' : a3 ^ 2 ≤ s2 * s4 := by simpa [ha3, hs2, hs4] using h4
    have hroot : a3 ≤ Real.sqrt (s2 * s4) := by
      rw [← Real.sqrt_sq ha3nn]
      exact Real.sqrt_le_sqrt h4'
    have hmul : s2 ^ 2 ≤ a1 * Real.sqrt (s2 * s4) := by
      have := mul_le_mul_of_nonneg_left hroot ha1nn
      nlinarith
    rw [ge_iff_le]
    rw [le_div_iff₀ (Real.sqrt_pos.mpr hpos)]
    exact hmul

end Median
