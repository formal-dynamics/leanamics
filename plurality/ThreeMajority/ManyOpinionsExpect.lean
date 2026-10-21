import ThreeMajority.AnyStartVsVoter

/-!
# One round of 3-Majority with many colours (BCNPT16, Lemma 2.1; roadmap MAJ-12 (a))

Becchetti, Clementi, Natale, Pasquale, Trevisan, *Stabilizing consensus with many opinions*,
SODA 2016, arXiv:1508.06782 (BCNPT16 below), Section 2, for the model `stepCol` of
`ThreeMajority.AnyStartModel` (an agent adopts the colour of its second and third samples if they
agree, and the colour of its first sample otherwise: the rule of BCNPT16, Section 2).

* `adoptInd c a v s`: agent `v` adopts colour `a` with the sample triple `s`. In a uniformly
  random round the agents' triples are independent, so the new support of `a` is the sum
  `∑ v, adoptInd c a v (r v)` of independent `{0,1}` variables (`colourCount_stepCol_eq_sum`),
  each with mean `x_a (1 + x_a − ‖x‖₂²)`, `x = c/n` (`avg_adoptInd`). This is the form consumed
  by the Chernoff bounds `Dynamics.avg_chernoff_*` and by anti-concentration.
* `avg_colourCount_stepCol`, `avg_colourCount_stepCol_le`: **Lemma 2.1** (BCNPT16, Equation (1)),
  `𝔼[C_a'] = c_a (1 + c_a/n − ∑_b c_b²/n²) ≤ c_a (1 + c_a/n − 1/|W|)` with `W` the set of
  remaining colours.
-/

namespace ThreeMajority

open Finset Dynamics

variable {n : ℕ} {σ : Type*} [DecidableEq σ]

/-! ### The model, unfolded

These three equations are pinned with the statements of roadmap MAJ-12 (a), so that the meaning
of `numColours`, `colourCount` and `stepCol` is frozen together with the statements using them. -/

/-- The number of colours of a configuration. -/
theorem numColours_eq_card_image (c : Fin n → σ) : numColours c = (univ.image c).card := rfl

/-- The support of colour `a`. -/
theorem colourCount_eq_card_filter (c : Fin n → σ) (a : σ) :
    colourCount c a = (univ.filter fun v => c v = a).card := rfl

/-- One round of 3-Majority: agent `v` with samples `r v = (s₁, s₂, s₃)` adopts the colour of
`s₂` if `s₂` and `s₃` agree, and the colour of `s₁` otherwise (BCNPT16, Section 2). -/
theorem stepCol_apply (c : Fin n → σ) (r : Tgt3 n) (v : Fin n) :
    stepCol c r v = if c (r v).2.1 = c (r v).2.2 then c (r v).2.1 else c (r v).1 := rfl

/-- Agent `v`'s indicator of adopting colour `a` in a round where its sample triple is `s`
(the agent index is not used: all agents follow the same rule). -/
def adoptInd (c : Fin n → σ) (a : σ) (_ : Fin n) (s : Fin n × Fin n × Fin n) : ℝ :=
  if majColour c s = a then 1 else 0

lemma adoptInd_zero_one (c : Fin n → σ) (a : σ) (v : Fin n) (s : Fin n × Fin n × Fin n) :
    adoptInd c a v s = 0 ∨ adoptInd c a v s = 1 := by
  unfold adoptInd
  split_ifs <;> simp

/-- The support of colour `a` after one round is the sum of the agents' adoption indicators. -/
lemma colourCount_stepCol_eq_sum (c : Fin n → σ) (a : σ) (r : Tgt3 n) :
    (colourCount (stepCol c r) a : ℝ) = ∑ v, adoptInd c a v (r v) := by
  simp only [colourCount, adoptInd, stepCol]
  rw [natCast_card_filter]

/-- 3-Majority never creates a colour along a trajectory. -/
lemma image_runCol_subset (x : Fin n → σ) (l : List (Tgt3 n)) :
    univ.image (runCol x l) ⊆ univ.image x := by
  induction l generalizing x with
  | nil => exact subset_rfl
  | cons r l ih => exact (ih (stepCol x r)).trans (image_stepCol_subset x r)

/-- The number of colours never increases along a trajectory. -/
lemma numColours_runCol_le (x : Fin n → σ) (l : List (Tgt3 n)) :
    numColours (runCol x l) ≤ numColours x :=
  card_le_card (image_runCol_subset x l)

/-- If a colour of `x` has died, fewer colours remain. -/
lemma numColours_runCol_lt_of_dead (x : Fin n → σ) (l : List (Tgt3 n)) {a : σ}
    (ha : 0 < colourCount x a) (h0 : colourCount (runCol x l) a = 0) :
    numColours (runCol x l) < numColours x := by
  refine card_lt_card ⟨image_runCol_subset x l, fun hsub => ?_⟩
  obtain ⟨v, hv⟩ : ∃ v, x v = a := by
    obtain ⟨v, hv⟩ := card_pos.mp ha
    exact ⟨v, (mem_filter.mp hv).2⟩
  obtain ⟨w, -, hw⟩ := mem_image.mp (hsub (mem_image_of_mem x (mem_univ v)))
  have : w ∈ univ.filter fun u => runCol x l u = a := by simp [hw, hv]
  rw [colourCount, card_eq_zero] at h0
  rw [h0] at this
  exact absurd this (notMem_empty w)

variable [Fintype σ] [NeZero n]

/-- The probability that one agent adopts colour `a`: `x_a (1 + x_a − ‖x‖₂²)` with `x = c/n`
(BCNPT16, proof of Lemma 2.1 in Appendix A; Equation (2) of BCEKMN17, `alpha3M_weight`). -/
lemma avg_adoptInd (c : Fin n → σ) (a : σ) (v : Fin n) :
    avg (adoptInd c a v) = (colourCount c a : ℝ) / n *
      (1 + (colourCount c a : ℝ) / n - ∑ b, ((colourCount c b : ℝ) / n) ^ 2) := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have h := card_majColour_eq c a
  unfold adoptInd
  rw [show avg (fun s : Fin n × Fin n × Fin n => if majColour c s = a then (1 : ℝ) else 0) =
      Dynamics.avg (fun s : Fin n × Fin n × Fin n => if majColour c s = a then (1 : ℝ) else 0)
      from rfl, Dynamics.avg_indicator, h]
  simp only [Fintype.card_prod, Fintype.card_fin, div_pow, ← sum_div]
  push_cast
  field_simp
  ring

/-- **Lemma 2.1** (BCNPT16, Equation (1), equality): the expected support of colour `a` after
one round is `c_a (1 + c_a/n − ∑_b c_b²/n²)`. -/
theorem avg_colourCount_stepCol (c : Fin n → σ) (a : σ) :
    avg (fun r : Tgt3 n => (colourCount (stepCol c r) a : ℝ)) =
      colourCount c a * (1 + colourCount c a / n - ∑ b, ((colourCount c b : ℝ) / n) ^ 2) := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [show (fun r : Tgt3 n => (colourCount (stepCol c r) a : ℝ)) =
      fun r : Tgt3 n => ∑ v, adoptInd c a v (r v) from
      funext (colourCount_stepCol_eq_sum c a), avg_sum]
  rw [show (fun v : Fin n => avg (fun r : Tgt3 n => adoptInd c a v (r v))) =
      fun v : Fin n => avg (adoptInd c a v) from
      funext fun v => avg_eval n v (adoptInd c a v)]
  simp only [avg_adoptInd, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

omit [Fintype σ] [NeZero n] in
/-- The supports of the remaining colours add up to `n`. -/
lemma sum_image_colourCount (c : Fin n → σ) :
    ∑ b ∈ univ.image c, (colourCount c b : ℝ) = n := by
  have h := card_eq_sum_card_image c (univ : Finset (Fin n))
  simp only [card_univ, Fintype.card_fin] at h
  simp only [colourCount]
  exact_mod_cast h.symm

omit [NeZero n] in
/-- `∑_b c_b² ≥ n² / |W|` for the set `W` of remaining colours (Cauchy–Schwarz). -/
lemma sq_le_numColours_mul_sum_sq (c : Fin n → σ) :
    (n : ℝ) ^ 2 ≤ numColours c * ∑ b, ((colourCount c b : ℝ)) ^ 2 := by
  have hcs : (∑ b ∈ univ.image c, (colourCount c b : ℝ)) ^ 2 ≤
      #(univ.image c) * ∑ b ∈ univ.image c, ((colourCount c b : ℝ)) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [sum_image_colourCount] at hcs
  calc (n : ℝ) ^ 2 ≤ #(univ.image c) * ∑ b ∈ univ.image c, ((colourCount c b : ℝ)) ^ 2 := hcs
    _ ≤ numColours c * ∑ b, ((colourCount c b : ℝ)) ^ 2 := by
      rw [numColours]
      gcongr
      exact subset_univ _

omit [Fintype σ] in
/-- **Lemma 2.1** (BCNPT16, Equation (1), inequality): the expected support of colour `a` after
one round is at most `c_a (1 + c_a/n − 1/|W|)`, where `|W|` is the number of remaining colours.
Colours below the average `n/|W|` shrink in expectation. -/
theorem avg_colourCount_stepCol_le [Finite σ] (c : Fin n → σ) (a : σ) :
    avg (fun r : Tgt3 n => (colourCount (stepCol c r) a : ℝ)) ≤
      colourCount c a * (1 + colourCount c a / n - 1 / (numColours c : ℝ)) := by
  have := Fintype.ofFinite σ
  rw [avg_colourCount_stepCol]
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hW : (0 : ℝ) < numColours c := by
    have : 0 < numColours c := by
      rw [numColours, card_pos]
      exact univ_nonempty_iff.mpr ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩ |>.image c
    exact_mod_cast this
  have hsq := sq_le_numColours_mul_sum_sq c
  have hkey : 1 / (numColours c : ℝ) ≤ ∑ b, ((colourCount c b : ℝ) / n) ^ 2 := by
    simp only [div_pow, ← sum_div]
    rw [div_le_div_iff₀ hW (by positivity)]
    linarith
  have h0 : (0 : ℝ) ≤ colourCount c a := Nat.cast_nonneg _
  nlinarith


/-- An event of the round-based kernel of 3-Majority, as an `expList` over the rounds. -/
lemma event_ofStep_stepCol (P : (Fin n → σ) → Prop) [DecidablePred P] (T : ℕ)
    (x : Fin n → σ) :
    (Kernel.ofStep (stepCol (n := n) (σ := σ))).event P T x =
      expList (Tgt3 n) T (fun l => if P (runCol x l) then 1 else 0) := by
  rw [Kernel.event_eq_iterate, Kernel.iterate_ofStep]
  change Dynamics.expList _ _ _ = Dynamics.expList _ _ _
  congr 1
  funext l
  rw [runCol_eq_foldl]

/-- "Fewer than `j` colours" is absorbing for the round-based kernel of 3-Majority. -/
lemma prob_ofStep_numColours_lt (j : ℕ) (x : Fin n → σ) (hx : numColours x < j) :
    (Kernel.ofStep (stepCol (n := n) (σ := σ)) x).prob (fun y => numColours y < j) = 1 := by
  rw [Kernel.prob_ofStep]
  calc _ = Dynamics.avg (fun _ : Tgt3 n => (1 : ℝ)) := by
        congr 1
        funext r
        exact if_pos ((numColours_stepCol_le x r).trans_lt hx)
    _ = 1 := Dynamics.avg_const 1

end ThreeMajority
