import Median.BinaryAux

/-! # Moments of sums of independent coordinates

For `S = ∑ i, f i (ω i)` with independent uniform coordinates `ω i`, centered summands
(`𝔼 f i = 0`) bounded by `1`, the second moment is the sum of the variances `σ²`
(`avg_sum_sq`) and the fourth moment is at most `σ² + 3σ⁴` (`avg_sum_fourth_le`).
The two-sided Paley-Zygmund inequality (`avg_pz`) turns them into a constant lower bound
on `P(σ² ≤ 4 S²)`: this is the anti-concentration that breaks the symmetry of a balanced
configuration of the binary median dynamics.
-/

namespace Median
open Finset Real Dynamics

variable {n : ℕ} {γ : Type*} [Fintype γ]

/-- **Cauchy-Schwarz** for uniform averages. -/
lemma avg_cauchy (f g : γ → ℝ) :
    avg (fun y => f y * g y) ^ 2 ≤ avg (fun y => f y ^ 2) * avg (fun y => g y ^ 2) := by
  unfold avg
  have h := Finset.sum_mul_sq_le_sq_mul_sq univ f g
  calc ((∑ y, f y * g y) / (Fintype.card γ : ℝ)) ^ 2
      = (∑ y, f y * g y) ^ 2 / (Fintype.card γ : ℝ) ^ 2 := by rw [div_pow]
    _ ≤ ((∑ y, f y ^ 2) * ∑ y, g y ^ 2) / (Fintype.card γ : ℝ) ^ 2 := by gcongr
    _ = (∑ y, f y ^ 2) / (Fintype.card γ : ℝ) * ((∑ y, g y ^ 2) / (Fintype.card γ : ℝ)) := by
        rw [div_mul_div_comm, sq]

/-- **Independence of the head and the tail**: on `Fin (n + 1) → γ`, a product of a
function of `ω 0` and a function of `Fin.tail ω` averages to the product of averages. -/
lemma avg_head_tail (F : γ → ℝ) (G : (Fin n → γ) → ℝ) :
    avg (fun ω : Fin (n + 1) → γ => F (ω 0) * G (Fin.tail ω)) = avg F * avg G := by
  have h := avg_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => γ)).symm
    (fun p : γ × (Fin n → γ) => F p.1 * G p.2)
  rw [← avg_mul_prod, ← h]
  rfl

variable [Nonempty γ]

/-- A function of the tail alone has the same average over the longer product. -/
lemma avg_tail (G : (Fin n → γ) → ℝ) :
    avg (fun ω : Fin (n + 1) → γ => G (Fin.tail ω)) = avg G := by
  have h := avg_head_tail (n := n) (fun _ : γ => (1 : ℝ)) G
  rw [avg_const, one_mul] at h
  rw [← h]
  simp

omit [Fintype γ] [Nonempty γ] in
/-- The sum over `Fin (n + 1)` splits into the head and the tail sum. -/
lemma sum_head_tail (f : Fin (n + 1) → γ → ℝ) (ω : Fin (n + 1) → γ) :
    ∑ i, f i (ω i) = f 0 (ω 0) + ∑ i : Fin n, f i.succ (Fin.tail ω i) :=
  Fin.sum_univ_succ _

/-- The mean of a sum of independent coordinates. -/
lemma avg_sum_coords (f : Fin n → γ → ℝ) :
    avg (fun ω : Fin n → γ => ∑ i, f i (ω i)) = ∑ i, avg (f i) := by
  rw [avg_sum]
  exact Finset.sum_congr rfl fun i _ => avg_eval n i (f i)

/-- **Second moment** of a sum of independent centered coordinates. -/
lemma avg_sum_sq (f : Fin n → γ → ℝ) (hf0 : ∀ i, avg (f i) = 0) :
    avg (fun ω : Fin n → γ => (∑ i, f i (ω i)) ^ 2) = ∑ i, avg (fun y => f i y ^ 2) := by
  induction n with
  | zero => simp [avg]
  | succ n ih =>
    obtain ⟨Tl, hTl⟩ : ∃ Tl : (Fin n → γ) → ℝ, Tl = fun t => ∑ i : Fin n, f i.succ (t i) :=
      ⟨_, rfl⟩
    have hT0 : avg Tl = 0 := by
      rw [hTl, avg_sum_coords]
      simp [hf0]
    have hT2 : avg (fun t => Tl t ^ 2) = ∑ i : Fin n, avg (fun y => f i.succ y ^ 2) := by
      rw [hTl]
      exact ih (fun i => f i.succ) (fun i => hf0 i.succ)
    have hpt : ∀ ω : Fin (n + 1) → γ, (∑ i, f i (ω i)) ^ 2
        = (f 0 (ω 0) ^ 2 + 2 * f 0 (ω 0) * Tl (Fin.tail ω)) + Tl (Fin.tail ω) ^ 2 := by
      intro ω
      rw [sum_head_tail, hTl]
      ring
    have hA : avg (fun ω : Fin (n + 1) → γ => f 0 (ω 0) ^ 2) = avg (fun y => f 0 y ^ 2) :=
      avg_eval (n + 1) 0 (fun y => f 0 y ^ 2)
    have hB : avg (fun ω : Fin (n + 1) → γ => 2 * f 0 (ω 0) * Tl (Fin.tail ω)) = 0 := by
      rw [avg_head_tail (fun y => 2 * f 0 y) Tl, hT0, mul_zero]
    have hC : avg (fun ω : Fin (n + 1) → γ => Tl (Fin.tail ω) ^ 2)
        = ∑ i : Fin n, avg (fun y => f i.succ y ^ 2) := by
      rw [avg_tail (fun t => Tl t ^ 2), hT2]
    rw [show (fun ω : Fin (n + 1) → γ => (∑ i, f i (ω i)) ^ 2)
        = fun ω => (f 0 (ω 0) ^ 2 + 2 * f 0 (ω 0) * Tl (Fin.tail ω)) + Tl (Fin.tail ω) ^ 2
        from funext hpt]
    rw [avg_add, avg_add, hA, hB, hC, Fin.sum_univ_succ]
    ring

/-- **Fourth moment** of a sum of independent centered coordinates bounded by `1`:
`𝔼S⁴ ≤ σ² + 3σ⁴`. -/
lemma avg_sum_fourth_le (f : Fin n → γ → ℝ) (hf0 : ∀ i, avg (f i) = 0)
    (hfb : ∀ i y, |f i y| ≤ 1) :
    avg (fun ω : Fin n → γ => (∑ i, f i (ω i)) ^ 4)
      ≤ (∑ i, avg (fun y => f i y ^ 2)) + 3 * (∑ i, avg (fun y => f i y ^ 2)) ^ 2 := by
  induction n with
  | zero => simp [avg]
  | succ n ih =>
    obtain ⟨Tl, hTl⟩ : ∃ Tl : (Fin n → γ) → ℝ, Tl = fun t => ∑ i : Fin n, f i.succ (t i) :=
      ⟨_, rfl⟩
    obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = ∑ i : Fin n, avg (fun y => f i.succ y ^ 2) := ⟨_, rfl⟩
    obtain ⟨a, ha⟩ : ∃ a : ℝ, a = avg (fun y => f 0 y ^ 2) := ⟨_, rfl⟩
    have hT0 : avg Tl = 0 := by
      rw [hTl, avg_sum_coords]
      simp [hf0]
    have hT2 : avg (fun t => Tl t ^ 2) = σ := by
      rw [hTl, hσ]
      exact avg_sum_sq (fun i => f i.succ) (fun i => hf0 i.succ)
    have hT4 : avg (fun t => Tl t ^ 4) ≤ σ + 3 * σ ^ 2 := by
      rw [hTl, hσ]
      exact ih (fun i => f i.succ) (fun i => hf0 i.succ) (fun i y => hfb i.succ y)
    have hpt : ∀ ω : Fin (n + 1) → γ, (∑ i, f i (ω i)) ^ 4
        = f 0 (ω 0) ^ 4 + 4 * f 0 (ω 0) ^ 3 * Tl (Fin.tail ω)
          + 6 * f 0 (ω 0) ^ 2 * Tl (Fin.tail ω) ^ 2
          + 4 * f 0 (ω 0) * Tl (Fin.tail ω) ^ 3 + Tl (Fin.tail ω) ^ 4 := by
      intro ω
      rw [sum_head_tail, hTl]
      ring
    have hA : avg (fun ω : Fin (n + 1) → γ => f 0 (ω 0) ^ 4) = avg (fun y => f 0 y ^ 4) :=
      avg_eval (n + 1) 0 (fun y => f 0 y ^ 4)
    have hB : avg (fun ω : Fin (n + 1) → γ => 4 * f 0 (ω 0) ^ 3 * Tl (Fin.tail ω)) = 0 := by
      rw [avg_head_tail (fun y => 4 * f 0 y ^ 3) Tl, hT0, mul_zero]
    have hC : avg (fun ω : Fin (n + 1) → γ => 6 * f 0 (ω 0) ^ 2 * Tl (Fin.tail ω) ^ 2)
        = 6 * a * σ := by
      rw [avg_head_tail (fun y => 6 * f 0 y ^ 2) (fun t => Tl t ^ 2), hT2, avg_const_mul, ha]
    have hD : avg (fun ω : Fin (n + 1) → γ => 4 * f 0 (ω 0) * Tl (Fin.tail ω) ^ 3) = 0 := by
      rw [avg_head_tail (fun y => 4 * f 0 y) (fun t => Tl t ^ 3), avg_const_mul, hf0 0]
      ring
    have hE : avg (fun ω : Fin (n + 1) → γ => Tl (Fin.tail ω) ^ 4)
        = avg (fun t => Tl t ^ 4) := avg_tail (fun t => Tl t ^ 4)
    rw [show (fun ω : Fin (n + 1) → γ => (∑ i, f i (ω i)) ^ 4)
        = fun ω => f 0 (ω 0) ^ 4 + 4 * f 0 (ω 0) ^ 3 * Tl (Fin.tail ω)
          + 6 * f 0 (ω 0) ^ 2 * Tl (Fin.tail ω) ^ 2
          + 4 * f 0 (ω 0) * Tl (Fin.tail ω) ^ 3 + Tl (Fin.tail ω) ^ 4
        from funext hpt]
    rw [avg_add, avg_add, avg_add, avg_add, hA, hB, hC, hD, hE, Fin.sum_univ_succ, ← ha, ← hσ]
    -- `𝔼 f₀⁴ ≤ 𝔼 f₀² = a` since `|f₀| ≤ 1`
    have h4 : avg (fun y => f 0 y ^ 4) ≤ a := by
      rw [ha]
      refine avg_le_avg fun y => ?_
      have h1 : f 0 y ^ 2 ≤ 1 := by
        have := hfb 0 y
        rw [← sq_abs]
        nlinarith [abs_nonneg (f 0 y)]
      nlinarith [sq_nonneg (f 0 y)]
    have ha0 : 0 ≤ a := by
      rw [ha]
      exact avg_nonneg fun y => sq_nonneg _
    nlinarith [sq_nonneg a]

/-- **Paley-Zygmund, two-sided.** If `𝔼Z² = s > 0` and `𝔼Z⁴ ≤ 4 s²`, then `s ≤ 4 Z²`
with probability at least `9/64`. -/
lemma avg_pz (Z : γ → ℝ) {s : ℝ} (hs : 0 < s)
    (h2 : avg (fun y => Z y ^ 2) = s) (h4 : avg (fun y => Z y ^ 4) ≤ 4 * s ^ 2) :
    9 / 64 ≤ avg (fun y => if s ≤ 4 * Z y ^ 2 then (1 : ℝ) else 0) := by
  -- pointwise, `Z² ≤ s/4 + Z² 1[s ≤ 4Z²]`
  have hpt : ∀ y, Z y ^ 2
      ≤ s / 4 + Z y ^ 2 * (if s ≤ 4 * Z y ^ 2 then (1 : ℝ) else 0) := by
    intro y
    split_ifs with h
    · linarith
    · push Not at h
      linarith
  have h1 : s ≤ s / 4
      + avg (fun y => Z y ^ 2 * (if s ≤ 4 * Z y ^ 2 then (1 : ℝ) else 0)) := by
    have := avg_le_avg hpt
    rw [avg_add, avg_const, h2] at this
    exact this
  -- Cauchy-Schwarz: `(𝔼[Z² 1_A])² ≤ 𝔼Z⁴ P(A)`
  have hcs := avg_cauchy (fun y => Z y ^ 2) (fun y => if s ≤ 4 * Z y ^ 2 then (1 : ℝ) else 0)
  have hind : (fun y => (if s ≤ 4 * Z y ^ 2 then (1 : ℝ) else 0) ^ 2)
      = fun y => if s ≤ 4 * Z y ^ 2 then (1 : ℝ) else 0 := by
    funext y
    split_ifs <;> norm_num
  have hz4 : (fun y => (Z y ^ 2) ^ 2) = fun y => Z y ^ 4 := by
    funext y
    ring
  rw [hind, hz4] at hcs
  obtain ⟨B, hB⟩ : ∃ B, B = avg (fun y => Z y ^ 2 * (if s ≤ 4 * Z y ^ 2 then (1 : ℝ) else 0)) :=
    ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = avg (fun y => if s ≤ 4 * Z y ^ 2 then (1 : ℝ) else 0) := ⟨_, rfl⟩
  rw [← hB, ← hP] at hcs
  rw [← hB] at h1
  rw [← hP]
  have hP0 : 0 ≤ P := by
    rw [hP]
    exact avg_nonneg fun y => by split_ifs <;> norm_num
  have hB34 : 3 / 4 * s ≤ B := by linarith
  have hsq : (3 / 4 * s) ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (by positivity) hB34 2
  have h4P : avg (fun y => Z y ^ 4) * P ≤ 4 * s ^ 2 * P := mul_le_mul_of_nonneg_right h4 hP0
  have hs2 : 0 < s ^ 2 := by positivity
  nlinarith

end Median
