import Median.AdversaryBinary

/-! # Adversary: reduction to two values

Helpers for `median_almost_stable` (`Median/Adversary.lean`):

* `runAdv_append_singleton`: the last round of a run against an adversary is the median rule
  followed by the adversary (hence `runAdv_isAdvRun`);
* `runAdv_mem`: if the start and the adversary only use values of `S`, so does the whole run (the
  median of three values is one of them);
* `isAdvRun_threshold`: the threshold `u ↦ [b ≤ P l u]` of a perturbed run is a perturbed run of
  2-Choices with the same budget, because thresholding commutes with the median rule
  (`threshold_step`) and does not increase the Hamming distance;
* `notAlmostStable_le_sum` (**threshold witness**): if, for every legal value `b` above the
  minimum `m`, the threshold run at `b` stays in almost consensus on some `c b` with at most `K`
  exceptions, then the run itself stays in almost consensus with at most `2K` exceptions on the
  largest legal value `v` with `v = m` or `c v = true`: nodes below `v` are exceptions of the
  threshold at `v`, nodes above `v` are exceptions of the threshold at the next legal value. So,
  pointwise in the rounds, failing almost stable consensus is at most the sum of the failures of
  the threshold runs.
-/

namespace Median
open Finset Dynamics

variable {n : ℕ} {α : Type*} [LinearOrder α]

/-- The last round of a run against an adversary: the median rule, then the adversary, who sees
all the rounds so far. -/
lemma runAdv_append_singleton (A : Adversary n α) (x : Config n α) (l : List (Round n))
    (r : Round n) : runAdv A x (l ++ [r]) = A (l ++ [r]) (step (runAdv A x l) r) := by
  induction l generalizing A x with
  | nil => rfl
  | cons r₀ l ih => exact ih (fun h => A (r₀ :: h)) (A [r₀] (step x r₀))

/-- If the start and the adversary only use values of `S`, so does the whole run. -/
lemma runAdv_mem {S : Set α} (A : Adversary n α) (hA : A.UsesValues S) (x : Config n α)
    (hx : ∀ v, x v ∈ S) (l : List (Round n)) (v : Fin n) : runAdv A x l v ∈ S := by
  induction l generalizing A x with
  | nil => exact hx v
  | cons r l ih =>
    refine ih (fun h => A (r :: h)) (fun h z u hu => hA _ z u hu) _ (fun u => ?_)
    by_cases hu : A [r] (step x r) u = step x r u
    · rw [hu]
      obtain ⟨w, hw⟩ := step_mem x r u
      rw [hw]
      exact hx w
    · exact hA _ _ u hu

/-- Thresholding does not increase the Hamming distance. -/
lemma hammingDist_threshold_le (b : α) (z z' : Config n α) :
    hammingDist (fun v => decide (b ≤ z v)) (fun v => decide (b ≤ z' v)) ≤ hammingDist z z' := by
  unfold hammingDist
  refine card_le_card fun v hv => ?_
  simp only [mem_filter, mem_univ, true_and] at hv ⊢
  exact fun h => hv (by rw [h])

/-- The threshold of a perturbed run is a perturbed run of 2-Choices. -/
lemma isAdvRun_threshold {F : ℕ} {x : Config n α} {P : List (Round n) → Config n α}
    (hP : IsAdvRun F x P) (b : α) :
    IsAdvRun F (fun v => decide (b ≤ x v)) (fun l v => decide (b ≤ P l v)) := by
  refine ⟨by funext v; simp [hP.1], fun l r => ?_⟩
  rw [← threshold_step]
  exact (hammingDist_threshold_le b _ _).trans (hP.2 l r)

/-- **Threshold witness.** Pointwise in the rounds, failing almost stable consensus with `2K`
exceptions is at most the sum, over the legal values `b` above the minimum `m`, of the failures
of the threshold runs with `K` exceptions. -/
lemma notAlmostStable_le_sum {S : Finset α} {m : α} (hm : m ∈ S) (hmin : ∀ b ∈ S, m ≤ b)
    {K : ℝ} (hK0 : 0 ≤ K) (T₀ H : ℕ) (P : List (Round n) → Config n α)
    (hPS : ∀ l v, P l v ∈ S) (l : List (Round n)) :
    notAlmostStable (2 * K) T₀ H P l
      ≤ ∑ b ∈ S.erase m, notAlmostStable K T₀ H (fun l v => decide (b ≤ P l v)) l := by
  have hnn : ∀ b ∈ S.erase m,
      0 ≤ notAlmostStable K T₀ H (fun l v => decide (b ≤ P l v)) l := fun b _ => by
    rw [notAlmostStable_eq]
    exact failInd_nonneg _
  by_cases hall : ∀ b ∈ S.erase m, ∃ c : Bool, ∀ t, T₀ ≤ t → t ≤ T₀ + H →
      AlmostConsensus K c (fun v => decide (b ≤ P (l.take t) v))
  · -- every threshold run stays in almost consensus: so does the run
    refine le_trans (le_of_eq ?_) (sum_nonneg hnn)
    rw [notAlmostStable_eq]
    refine failInd_of ?_
    choose! c hc using hall
    have hne : (S.filter fun b => b = m ∨ c b = true).Nonempty := ⟨m, by simp [hm]⟩
    obtain ⟨w, hw⟩ : ∃ w, w = (S.filter fun b => b = m ∨ c b = true).max' hne := ⟨_, rfl⟩
    have hwmem : w ∈ S.filter fun b => b = m ∨ c b = true := hw ▸ max'_mem _ _
    have hwS : w ∈ S := (mem_filter.mp hwmem).1
    have hwp : w = m ∨ c w = true := (mem_filter.mp hwmem).2
    have hwmax : ∀ b ∈ S, (b = m ∨ c b = true) → b ≤ w := fun b hb hp =>
      hw ▸ le_max' _ b (mem_filter.mpr ⟨hb, hp⟩)
    refine ⟨w, fun t h1 h2 => ?_⟩
    obtain ⟨y, hy⟩ : ∃ y, y = P (l.take t) := ⟨_, rfl⟩
    have hyS : ∀ v, y v ∈ S := fun v => hy ▸ hPS _ v
    -- the nodes below `w`
    have hA : ((univ.filter fun v => y v < w).card : ℝ) ≤ K := by
      by_cases hwm : w = m
      · have : (univ.filter fun v => y v < w) = ∅ := by
          refine filter_eq_empty_iff.mpr fun v _ => not_lt.mpr ?_
          rw [hwm]
          exact hmin _ (hyS v)
        rw [this, card_empty, Nat.cast_zero]
        exact hK0
      · have hcw : c w = true := hwp.resolve_left hwm
        have h := hc w (mem_erase.mpr ⟨hwm, hwS⟩) t h1 h2
        rw [hcw, ← hy] at h
        unfold AlmostConsensus at h
        convert h using 4 with v
        simp
    -- the nodes above `w`
    have hB : ((univ.filter fun v => w < y v).card : ℝ) ≤ K := by
      by_cases hex : ∃ v, w < y v
      · obtain ⟨v₀, hv₀⟩ := hex
        have hU : (S.filter fun b => w < b).Nonempty := ⟨y v₀, by simp [hyS v₀, hv₀]⟩
        obtain ⟨b', hb'⟩ : ∃ b', b' = (S.filter fun b => w < b).min' hU := ⟨_, rfl⟩
        have hb'mem : b' ∈ S.filter fun b => w < b := hb' ▸ min'_mem _ _
        have hb'S : b' ∈ S := (mem_filter.mp hb'mem).1
        have hwb' : w < b' := (mem_filter.mp hb'mem).2
        have hb'm : b' ≠ m := fun e => by
          have := hmin w hwS
          rw [e] at hwb'
          exact absurd hwb' (not_lt.mpr this)
        have hcb' : c b' = false := by
          by_contra hcon
          have := hwmax b' hb'S (Or.inr (by simpa using hcon))
          exact absurd hwb' (not_lt.mpr this)
        have h := hc b' (mem_erase.mpr ⟨hb'm, hb'S⟩) t h1 h2
        rw [hcb', ← hy] at h
        unfold AlmostConsensus at h
        refine le_trans ?_ h
        refine Nat.cast_le.mpr (card_le_card fun v hv => ?_)
        simp only [mem_filter, mem_univ, true_and] at hv ⊢
        have : b' ≤ y v := hb' ▸ min'_le _ _ (by simp [hyS v, hv])
        simpa using this
      · push Not at hex
        have : (univ.filter fun v => w < y v) = ∅ :=
          filter_eq_empty_iff.mpr fun v _ => not_lt.mpr (hex v)
        rw [this, card_empty, Nat.cast_zero]
        exact hK0
    unfold AlmostConsensus
    rw [← hy]
    have hsub : (univ.filter fun v => y v ≠ w)
        ⊆ (univ.filter fun v => y v < w) ∪ (univ.filter fun v => w < y v) := by
      intro v hv
      simp only [mem_filter, mem_univ, true_and, mem_union] at hv ⊢
      exact lt_or_gt_of_ne hv
    have hc := (card_le_card hsub).trans (card_union_le _ _)
    have hc' : ((univ.filter fun v => y v ≠ w).card : ℝ)
        ≤ (univ.filter fun v => y v < w).card + (univ.filter fun v => w < y v).card := by
      exact_mod_cast hc
    linarith
  · -- some threshold run fails: the sum is at least `1`
    push Not at hall
    obtain ⟨b, hb, hfail⟩ := hall
    have h1 : notAlmostStable K T₀ H (fun l v => decide (b ≤ P l v)) l = 1 := by
      rw [notAlmostStable_eq]
      exact failInd_of_not fun ⟨c, hcc⟩ => by
        obtain ⟨t, h1, h2, h3⟩ := hfail c
        exact h3 (hcc t h1 h2)
    calc notAlmostStable (2 * K) T₀ H P l ≤ 1 := notAlmostStable_le_one _ _ _ _ _
      _ = notAlmostStable K T₀ H (fun l v => decide (b ≤ P l v)) l := h1.symm
      _ ≤ ∑ b ∈ S.erase m, notAlmostStable K T₀ H (fun l v => decide (b ≤ P l v)) l :=
          single_le_sum hnn hb

end Median
