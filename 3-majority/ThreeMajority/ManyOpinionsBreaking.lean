import ThreeMajority.ManyOpinionsExpect
import ThreeMajority.ManyOpinionsMoments
import ThreeMajority.ManyOpinionsDrift
import Dynamics.Rounds

/-!
# The symmetry-breaking stage (BCNPT16, Lemma 3.3; roadmap MAJ-12 (a))

Becchetti, Clementi, Natale, Pasquale, Trevisan, *Stabilizing consensus with many opinions*,
SODA 2016, arXiv:1508.06782 (BCNPT16 below), Section 3. From a configuration with `j` colours,
the smallest support `c_𝕞` drifts down by `δ √n / j^{3/2}` per round (Equation (3)) as long as
every colour has more than `n/j − 16 √(j n log n)` agents, and one round overshoots below
`n/j − 64 √(j n log n)` with probability at most `1/n²` (Equation (6), Lemma B.1). The additive
drift lemma (`hitProb_additive_drift`, Lemma 3.2) then gives Lemma 3.3: within
`O(j² √(log n))` rounds, with probability at least `1/2`, some colour falls to
`n/j − 16 √(j n log n)` agents or dies.

* `BrokenSymmetry j x`: the exit condition of the stage for `j` colours.
* `min_count_drift`: **Equation (3)** (Hypothesis 1 of Lemma 3.2 for `Y = ⌊n/j⌋ − c_𝕞`).
* `min_count_overshoot`: **Equation (6)** (Hypothesis 2 of Lemma 3.2; Lemma B.1), in one-step
  form.
* `symmetry_breaking`: **Lemma 3.3**, as a hitting probability of the round-based kernel.

The paper assumes nothing on `j` in Lemma 3.3, but its proof uses `c_𝕞 ≥ n/(2j)` whenever
`c_𝕞 > n/j − √(j n log n)`, which needs `j³ log n = O(n)`; the statements here assume
`C j³ log n ≤ n` (implied by the standing assumption `j ≤ n^{1/3 − ε}` of Section 3 for large
`n`). The threshold is `16 √(j n log n)` instead of `√(j n log n)`, for the dropping stage
(Lemma 3.4, `dropping_stage1`).
-/

namespace ThreeMajority

open Finset Dynamics

section Defs

variable {n : ℕ} {σ : Type*} [DecidableEq σ]

/-- The exit condition of the symmetry-breaking stage for `j` colours (BCNPT16, Lemma 3.3, with
the threshold `16 √(j n log n)`): fewer than `j` colours remain, or at most `j` colours remain
and one of them has between `1` and `n/j − 16 √(j n log n)` agents. -/
def BrokenSymmetry (j : ℕ) (x : Fin n → σ) : Prop :=
  numColours x < j ∨ (numColours x ≤ j ∧ ∃ a, 0 < colourCount x a ∧
    (colourCount x a : ℝ) ≤ n / j - 16 * √(j * n * Real.log n))

/-- `BrokenSymmetry` unfolded. (Pinned, so that the definition is frozen together with the
statements that use it.) -/
theorem brokenSymmetry_iff (j : ℕ) (x : Fin n → σ) :
    BrokenSymmetry j x ↔ numColours x < j ∨ (numColours x ≤ j ∧ ∃ a, 0 < colourCount x a ∧
      (colourCount x a : ℝ) ≤ n / j - 16 * √(j * n * Real.log n)) := Iff.rfl

end Defs

section Potential

variable {n : ℕ} [NeZero n]

/-- A configuration of `n ≥ 1` agents has a colour. -/
lemma image_univ_nonempty (y : Fin n → Fin n) : (univ.image y).Nonempty :=
  (univ_nonempty_iff.mpr ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩).image y

/-- The smallest support among the colours of `x`, at most the average `n / numColours x`. -/
lemma card_mul_inf'_colourCount_le (x : Fin n → Fin n) :
    (numColours x : ℝ) *
      (univ.image x).inf' (image_univ_nonempty x) (fun a => (colourCount x a : ℝ))
      ≤ n := by
  have h := card_nsmul_le_sum (univ.image x) (fun a => (colourCount x a : ℝ))
    ((univ.image x).inf' (image_univ_nonempty x) (fun a => (colourCount x a : ℝ)))
    (fun a ha => inf'_le _ ha)
  rw [sum_image_colourCount, nsmul_eq_mul] at h
  exact h

/-- The potential of the symmetry-breaking stage for `j` colours. -/
noncomputable def breakPotential (j : ℕ) (y : Fin n → Fin n) : ℝ :=
  if numColours y < j then (n : ℝ) / j
  else (n : ℝ) / j - (univ.image y).inf' (image_univ_nonempty y) (fun a => (colourCount y a : ℝ))

/-- After rounds from `x` with `j` colours, the potential is `n/j` minus the smallest support
among the colours of `x` (dead colours count `0`). -/
lemma breakPotential_eq {j : ℕ} (x : Fin n → Fin n) (hx : numColours x = j) (y : Fin n → Fin n)
    (hy : univ.image y ⊆ univ.image x) :
    breakPotential j y = (n : ℝ) / j -
      (univ.image x).inf' (image_univ_nonempty x) (fun a => (colourCount y a : ℝ)) := by
  unfold breakPotential
  split_ifs with h
  · -- a colour of `x` is dead in `y`
    obtain ⟨a, hax, hay⟩ : ∃ a ∈ univ.image x, a ∉ univ.image y := by
      by_contra hc
      push Not at hc
      have := card_le_card (show univ.image x ⊆ univ.image y from hc)
      rw [← numColours, ← numColours] at this
      omega
    have h0 : colourCount y a = 0 := by
      rw [colourCount, card_eq_zero, filter_eq_empty_iff]
      intro v _ hv
      exact hay (mem_image.mpr ⟨v, mem_univ v, hv⟩)
    have hle :
        (univ.image x).inf' (image_univ_nonempty x) (fun a => (colourCount y a : ℝ)) ≤ 0 := by
      have := inf'_le (fun a => (colourCount y a : ℝ)) hax
      simpa [h0] using this
    have hge : 0 ≤ (univ.image x).inf' (image_univ_nonempty x) (fun a => (colourCount y a : ℝ)) :=
      (le_inf'_iff _ _).mpr fun _ _ => Nat.cast_nonneg _
    linarith
  · have heq : univ.image y = univ.image x := by
      refine eq_of_subset_of_card_le hy ?_
      rw [← numColours, ← numColours]
      omega
    congr 1
    exact inf'_congr (image_univ_nonempty y) heq fun _ _ => rfl
end Potential


/-- Outside `BrokenSymmetry j`, a configuration with at most `j` colours has exactly `j` colours,
all above the threshold. -/
lemma not_brokenSymmetry {n : ℕ} {j : ℕ} {x : Fin n → Fin n} (hI : numColours x ≤ j)
    (hB : ¬ BrokenSymmetry j x) : numColours x = j ∧ ∀ a ∈ univ.image x,
      (n : ℝ) / j - 16 * √(j * n * Real.log n) < colourCount x a := by
  unfold BrokenSymmetry at hB
  push Not at hB
  refine ⟨le_antisymm hI hB.1, fun a ha => hB.2 hI a ?_⟩
  obtain ⟨v, -, hv⟩ := mem_image.mp ha
  exact card_pos.mpr ⟨v, mem_filter.mpr ⟨mem_univ v, hv⟩⟩

/-- **Equation (3)** (BCNPT16, proof of Lemma 3.3, Hypothesis 1 of Lemma 3.2): there are
constants `δ > 0` and `C` such that, for every configuration `x` with `j ≥ 2` colours,
`C j³ log n ≤ n` and every colour above `n/j − 16 √(j n log n)` agents, the smallest support
among the colours of `x` decreases in expectation by at least `δ √n / j^{3/2}` in one round
(a colour that dies counts with support `0`). -/
theorem min_count_drift :
    ∃ δ C : ℝ, 0 < δ ∧ ∀ (n : ℕ) (x : Fin n → Fin n), 2 ≤ numColours x →
      C * (numColours x : ℝ) ^ 3 * Real.log n ≤ n →
      (∀ a ∈ univ.image x,
        (n : ℝ) / numColours x - 16 * √(numColours x * n * Real.log n) < colourCount x a) →
      ∀ h : (univ.image x).Nonempty,
        avg (fun r : Tgt3 n =>
            (univ.image x).inf' h fun a => (colourCount (stepCol x r) a : ℝ)) ≤
          (univ.image x).inf' h (fun a => (colourCount x a : ℝ)) -
            δ * √(n : ℝ) / (numColours x * √(numColours x : ℝ)) := by
  sorry

/-- **Equation (6)** (BCNPT16, proof of Lemma 3.3, Hypothesis 2 of Lemma 3.2; Lemma B.1), in
one-step form: there is `C` such that, for every configuration `x` with `j ≥ 2` colours,
`C j³ log n ≤ n` and every colour above `n/j − 16 √(j n log n)` agents, after one round some
colour of `x` is below `n/j − 64 √(j n log n)` agents with probability at most `1/n²`. -/
theorem min_count_overshoot :
    ∃ C : ℝ, ∀ (n : ℕ) (x : Fin n → Fin n), 2 ≤ numColours x →
      C * (numColours x : ℝ) ^ 3 * Real.log n ≤ n →
      (∀ a ∈ univ.image x,
        (n : ℝ) / numColours x - 16 * √(numColours x * n * Real.log n) < colourCount x a) →
      avg (fun r : Tgt3 n => if ∃ a ∈ univ.image x, (colourCount (stepCol x r) a : ℝ) <
          n / numColours x - 64 * √(numColours x * n * Real.log n) then (1 : ℝ) else 0) ≤
        1 / (n : ℝ) ^ 2 := by
  sorry

/-- **Lemma 3.3** (BCNPT16, symmetry-breaking stage): there is `C` such that, from every
configuration `c` with `j ≥ 2` colours and `C j³ log n ≤ n`, 3-Majority reaches
`BrokenSymmetry j` (some colour falls to `n/j − 16 √(j n log n)` agents, or dies) within any
`t ≥ C j² √(log n)` rounds with probability at least `1/2`. -/
theorem symmetry_breaking :
    ∃ C : ℝ, ∀ (n : ℕ) [NeZero n] (c : Fin n → Fin n), 2 ≤ numColours c →
      C * (numColours c : ℝ) ^ 3 * Real.log n ≤ n →
      ∀ t : ℕ, C * (numColours c : ℝ) ^ 2 * √(Real.log n) ≤ t →
        1 / 2 ≤ (Kernel.ofStep (stepCol : (Fin n → Fin n) → Tgt3 n → Fin n → Fin n)).hitProb
          (BrokenSymmetry (numColours c)) t c := by
  obtain ⟨δ, Cd, hδ, hD⟩ := min_count_drift
  obtain ⟨Co, hO⟩ := min_count_overshoot
  refine ⟨|Cd| + |Co| + 256 / δ + 1, fun n _ c hc2 hcond t ht => ?_⟩
  have hkn : numColours c ≤ n := by
    simpa [numColours] using card_image_le (s := (univ : Finset (Fin n))) (f := c)
  generalize hj : numColours c = j at hc2 hcond ht ⊢
  have hjn : j ≤ n := hj ▸ hkn
  -- arithmetic facts
  have aD := abs_nonneg Cd
  have aO := abs_nonneg Co
  have hδ' : 0 < 256 / δ := by positivity
  have hL : 0.6931471803 ≤ Real.log n :=
    Real.log_two_gt_d9.le.trans (Real.log_le_log (by norm_num) (by exact_mod_cast (by omega)))
  have hL0 : 0 ≤ Real.log n := by linarith
  have hj2 : (2 : ℝ) ≤ j := by exact_mod_cast hc2
  have hj0 : (0 : ℝ) < j := by linarith
  have hjn' : (j : ℝ) ≤ n := by exact_mod_cast hjn
  have hn0 : (0 : ℝ) < n := by linarith
  have hj8 : (8 : ℝ) ≤ (j : ℝ) ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hj2 3
    norm_num at this
    linarith
  have hX0 : 0 ≤ (j : ℝ) ^ 3 * Real.log n := by positivity
  have hX : 5 ≤ (j : ℝ) ^ 3 * Real.log n := by nlinarith
  have hcond' (D : ℝ) (hD : D ≤ |Cd| + |Co| + 256 / δ + 1) :
      D * (j : ℝ) ^ 3 * Real.log n ≤ n := by
    calc D * (j : ℝ) ^ 3 * Real.log n = D * ((j : ℝ) ^ 3 * Real.log n) := by ring
      _ ≤ (|Cd| + |Co| + 256 / δ + 1) * ((j : ℝ) ^ 3 * Real.log n) :=
          mul_le_mul_of_nonneg_right hD hX0
      _ = _ := by ring
      _ ≤ n := hcond
  -- the parameters of Lemma 3.2
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = δ * √(n : ℝ) / (j * √(j : ℝ)) := ⟨_, rfl⟩
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = 64 * √(j * n * Real.log n) := ⟨_, rfl⟩
  have hβ0 : 0 ≤ β := hβdef ▸ by positivity
  have hm : 16 * √(j * n * Real.log n) ≤ β := by
    rw [hβdef]; have := Real.sqrt_nonneg (j * n * Real.log n); linarith
  have hI : ∀ x : Fin n → Fin n, numColours x ≤ j →
      (Kernel.ofStep (stepCol (n := n) (σ := Fin n)) x).prob (fun y => numColours y ≤ j) = 1 := by
    intro x hx
    rw [Kernel.prob_ofStep]
    calc _ = Dynamics.avg (fun _ : Tgt3 n => (1 : ℝ)) := by
          congr 1
          funext r
          exact if_pos ((numColours_stepCol_le x r).trans hx)
      _ = 1 := Dynamics.avg_const 1
  have hfM : ∀ x : Fin n → Fin n, numColours x ≤ j → breakPotential j x ≤ (n : ℝ) / j := by
    intro x _
    unfold breakPotential
    split_ifs
    · exact le_rfl
    · have : 0 ≤ (univ.image x).inf' (image_univ_nonempty x) (fun a => (colourCount x a : ℝ)) :=
        (le_inf'_iff _ _).mpr fun _ _ => Nat.cast_nonneg _
      linarith
  have hfβ : ∀ x : Fin n → Fin n, numColours x ≤ j → ¬ BrokenSymmetry j x →
      breakPotential j x ≤ β := by
    intro x hx hB
    obtain ⟨hxj, hall⟩ := not_brokenSymmetry hx hB
    rw [breakPotential_eq x hxj x subset_rfl]
    have : (n : ℝ) / j - 16 * √(j * n * Real.log n) <
        (univ.image x).inf' (image_univ_nonempty x) (fun a => (colourCount x a : ℝ)) :=
      (lt_inf'_iff _).mpr hall
    linarith
  have hdrift : ∀ x : Fin n → Fin n, numColours x ≤ j → ¬ BrokenSymmetry j x →
      breakPotential j x + lam ≤
        (Kernel.ofStep (stepCol (n := n) (σ := Fin n))).apply (breakPotential j) x := by
    intro x hx hB
    obtain ⟨hxj, hall⟩ := not_brokenSymmetry hx hB
    rw [Kernel.apply_ofStep]
    have hpt : (fun r : Tgt3 n => breakPotential j (stepCol x r)) = fun r => (n : ℝ) / j -
        (univ.image x).inf' (image_univ_nonempty x) (fun a => (colourCount (stepCol x r) a : ℝ)) :=
      funext fun r => breakPotential_eq x hxj _ (image_stepCol_subset x r)
    rw [hpt, Dynamics.avg_sub, Dynamics.avg_const, breakPotential_eq x hxj x subset_rfl]
    have h := hD n x (hxj ▸ hc2) (hxj ▸ hcond' Cd (by linarith [le_abs_self Cd]))
      (hxj ▸ hall) (image_univ_nonempty x)
    rw [hxj] at h
    rw [hlam]
    have : avg (fun r : Tgt3 n => (univ.image x).inf' (image_univ_nonempty x)
        fun a => (colourCount (stepCol x r) a : ℝ)) = Dynamics.avg (fun r : Tgt3 n =>
        (univ.image x).inf' (image_univ_nonempty x)
          fun a => (colourCount (stepCol x r) a : ℝ)) := rfl
    rw [this] at h
    linarith
  have hjump : ∀ x : Fin n → Fin n, numColours x ≤ j → ¬ BrokenSymmetry j x →
      (Kernel.ofStep (stepCol (n := n) (σ := Fin n)) x).prob (fun y => β < breakPotential j y) ≤
        1 / (n : ℝ) ^ 2 := by
    intro x hx hB
    obtain ⟨hxj, hall⟩ := not_brokenSymmetry hx hB
    have h := hO n x (hxj ▸ hc2) (hxj ▸ hcond' Co (by linarith [le_abs_self Co])) (hxj ▸ hall)
    rw [hxj] at h
    rw [Kernel.prob_ofStep]
    refine le_trans (Dynamics.avg_le_avg fun r => ?_) h
    split_ifs with h1 h2
    · exact le_rfl
    · exfalso
      apply h2
      rw [breakPotential_eq x hxj _ (image_stepCol_subset x r)] at h1
      have : (univ.image x).inf' (image_univ_nonempty x)
          (fun a => (colourCount (stepCol x r) a : ℝ)) < (n : ℝ) / j - β := by linarith
      obtain ⟨a, ha, hlt⟩ := (inf'_lt_iff _).mp this
      exact ⟨a, ha, hβdef ▸ hlt⟩
    · norm_num
    · exact le_rfl
  have hfc : 0 ≤ breakPotential j c := by
    rw [breakPotential_eq c hj c subset_rfl, sub_nonneg, le_div_iff₀ hj0, mul_comm]
    have := card_mul_inf'_colourCount_le c
    rwa [hj] at this
  have key := hitProb_additive_drift (Kernel.ofStep (stepCol (n := n) (σ := Fin n)))
    (fun x => numColours x ≤ j) (BrokenSymmetry j) (breakPotential j) (lam := lam)
    (M := (n : ℝ) / j)
    (η := 1 / (n : ℝ) ^ 2) hβ0 (by positivity) hI hfM hfβ hdrift hjump t c hj.le hfc
  -- arithmetic: `λ t ≥ 4 β` and `(n/j) (1/n²) t ≤ λ t / 4`
  have hsj : 0 < √(j : ℝ) := Real.sqrt_pos.mpr hj0
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hn0
  have hsL : 0 ≤ √(Real.log n) := Real.sqrt_nonneg _
  have hjj : √(j : ℝ) * √(j : ℝ) = j := Real.mul_self_sqrt hj0.le
  have hnn : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hn0.le
  have hsplit : √(j * n * Real.log n) = √(j : ℝ) * √(n : ℝ) * √(Real.log n) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hj0.le]
  have hlam0 : 0 < lam := hlam ▸ by positivity
  have ht0 : (256 / δ) * (j : ℝ) ^ 2 * √(Real.log n) ≤ t := by
    refine le_trans ?_ ht
    have : 0 ≤ (j : ℝ) ^ 2 * √(Real.log n) := by positivity
    nlinarith
  have h4β : 4 * β ≤ lam * t := by
    have e : lam * ((256 / δ) * (j : ℝ) ^ 2 * √(Real.log n)) = 4 * β := by
      rw [hlam, hβdef, hsplit]
      field_simp
      nlinarith [hjj]
    rw [← e]
    exact mul_le_mul_of_nonneg_left ht0 hlam0.le
  have hsmall : (n : ℝ) / j * (1 / (n : ℝ) ^ 2) * t ≤ lam * t / 4 := by
    have hn4 : 4 ≤ δ * n := by
      have h1 := hcond' (256 / δ) (by linarith)
      have h3 : 256 / δ * 5 ≤ 256 / δ * ((j : ℝ) ^ 3 * Real.log n) :=
        mul_le_mul_of_nonneg_left hX hδ'.le
      have h4 : 256 / δ * (j : ℝ) ^ 3 * Real.log n = 256 / δ * ((j : ℝ) ^ 3 * Real.log n) := by
        ring
      have h5 : 256 / δ * 5 ≤ n := by linarith
      rw [div_mul_eq_mul_div, div_le_iff₀ hδ] at h5
      linarith
    have hsjn : √(j : ℝ) ≤ √(n : ℝ) := Real.sqrt_le_sqrt hjn'
    have ht00 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    have hkey : 4 * (√(j : ℝ) * j) ≤ δ * n * (√(n : ℝ) * j) :=
      mul_le_mul hn4 (mul_le_mul_of_nonneg_right hsjn hj0.le) (by positivity) (by positivity)
    have e1 : (n : ℝ) / j * (1 / (n : ℝ) ^ 2) = 1 / (j * n) := by
      field_simp
    have e2 : lam / 4 = δ * √(n : ℝ) / (4 * (j * √(j : ℝ))) := by
      rw [hlam, div_div, mul_comm (j * √(j : ℝ)) 4]
    have : (n : ℝ) / j * (1 / (n : ℝ) ^ 2) ≤ lam / 4 := by
      rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity)]
      linarith [show δ * √(n : ℝ) * (j * n) = δ * n * (√(n : ℝ) * j) by ring,
        show (1 : ℝ) * (4 * (j * √(j : ℝ))) = 4 * (√(j : ℝ) * j) by ring]
    calc (n : ℝ) / j * (1 / (n : ℝ) ^ 2) * t ≤ lam / 4 * t :=
          mul_le_mul_of_nonneg_right this ht00
      _ = lam * t / 4 := by ring
  have hsL' : 0 < √(Real.log n) := Real.sqrt_pos.mpr (by linarith)
  have ht0' : (0 : ℝ) < t := lt_of_lt_of_le (by positivity) ht0
  have hlt0 : 0 < lam * t := mul_pos hlam0 ht0'
  by_contra hcon
  push Not at hcon
  have : lam * t * (1 / 2) < lam * t * (1 - (Kernel.ofStep (stepCol (n := n) (σ := Fin n))).hitProb
      (BrokenSymmetry j) t c) := by
    apply mul_lt_mul_of_pos_left _ hlt0
    linarith
  linarith

end ThreeMajority
