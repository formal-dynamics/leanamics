import ThreeMajority.AnyStartModel

/-!
# Majorization and Schur-convex observables (BCEKMN17, Section 2.1)

`Majorizes x y` (the paper's `x ⪰ y`): equal total sums, and for every `j` the sum of the `j`
largest entries of `x` is at least that of `y`. It is stated without sorting: every sum of `y`
over a set `S` is bounded by a sum of `x` over a set `S'` of the same size, which is the same as
comparing the sums of the `|S|` largest entries.

`SchurConvex φ`: an observable of configurations that is monotone for the majorization of the
configuration vectors (the paper's Schur-convex functions of `c`, for the preorder `⪯` on the
configuration space `𝒞`). Such an observable depends on the configuration only through its
sorted configuration vector. The indicator of "at most `κ` colours" is one of them
(`schurConvex_numColours_le`), which is how the comparison of Theorem 2 controls the number of
remaining colours.
-/

namespace ThreeMajority

open Finset

/-- Vector majorization `x ⪰ y` (BCEKMN17, Section 2.1): equal sums, and the sum of the `j`
largest entries of `y` is at most that of `x` for every `j`, in the sort-free form "every sum of
`y` over a set is bounded by a sum of `x` over a set of the same size". -/
def Majorizes {ι : Type*} [Fintype ι] (x y : ι → ℝ) : Prop :=
  ∑ i, x i = ∑ i, y i ∧
    ∀ S : Finset ι, ∃ S' : Finset ι, S'.card = S.card ∧ ∑ i ∈ S, y i ≤ ∑ i ∈ S', x i

section Majorizes

variable {ι : Type*} [Fintype ι]

lemma Majorizes.refl (x : ι → ℝ) : Majorizes x x :=
  ⟨rfl, fun S => ⟨S, rfl, le_rfl⟩⟩

lemma Majorizes.trans {x y z : ι → ℝ} (hxy : Majorizes x y) (hyz : Majorizes y z) :
    Majorizes x z := by
  refine ⟨hxy.1.trans hyz.1, fun S => ?_⟩
  obtain ⟨S₁, h₁, hs₁⟩ := hyz.2 S
  obtain ⟨S₂, h₂, hs₂⟩ := hxy.2 S₁
  exact ⟨S₂, h₂.trans h₁, hs₁.trans hs₂⟩

end Majorizes

variable {n : ℕ} {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The configuration vector `(c_a)_a` of a configuration, as a real vector. -/
noncomputable def countVec (c : Fin n → σ) : σ → ℝ :=
  fun a => (colourCount c a : ℝ)

/-- A Schur-convex observable of configurations (BCEKMN17, Section 2.1): monotone for the
majorization of the configuration vectors. -/
def SchurConvex (φ : (Fin n → σ) → ℝ) : Prop :=
  ∀ c c' : Fin n → σ, Majorizes (countVec c) (countVec c') → φ c' ≤ φ c

/-- A configuration whose vector majorizes another one has at most as many colours: the
`numColours c'` largest entries of `c'` already sum to `n`, so `c` has all its mass on as many
colours (BCEKMN17, Section 2.3, observation 1 after Lemma 1: consensus is maximal for `⪯`). -/
theorem numColours_le_of_majorizes {c c' : Fin n → σ}
    (h : Majorizes (countVec c) (countVec c')) : numColours c ≤ numColours c' := by
  obtain ⟨S', hcard, hsum⟩ := h.2 (univ.image c')
  -- the colours of `c'` carry all `n` agents
  have himg : ∑ a ∈ univ.image c', countVec c' a = n := by
    simp only [countVec, colourCount]
    rw [← Nat.cast_sum, ← card_eq_sum_card_image]
    simp
  have htot : ∑ a, countVec c a = n := by
    simp only [countVec, colourCount]
    rw [← Nat.cast_sum, ← card_eq_sum_card_fiberwise (fun v _ => mem_univ (c v))]
    simp
  -- hence so do the colours of `S'` for `c`, and every colour of `c` lies in `S'`
  have hsub : univ.image c ⊆ S' := by
    intro a ha
    by_contra haS
    obtain ⟨v, -, rfl⟩ := mem_image.mp ha
    have hpos : 0 < countVec c (c v) := by
      simp only [countVec, colourCount]
      exact_mod_cast card_pos.mpr ⟨v, by simp⟩
    have hle : ∑ a ∈ insert (c v) S', countVec c a ≤ ∑ a, countVec c a :=
      sum_le_univ_sum_of_nonneg fun _ => by simp only [countVec]; positivity
    rw [sum_insert haS] at hle
    linarith
  calc numColours c ≤ S'.card := card_le_card hsub
    _ = numColours c' := hcard

/-- The indicator of "at most `κ` colours" is Schur-convex. -/
theorem schurConvex_numColours_le (κ : ℕ) :
    SchurConvex (fun c : Fin n → σ => if numColours c ≤ κ then (1 : ℝ) else 0) := by
  intro c c' h
  have hle := numColours_le_of_majorizes h
  dsimp only
  by_cases h₁ : numColours c' ≤ κ
  · rw [if_pos h₁, if_pos (hle.trans h₁)]
  · rw [if_neg h₁]
    split_ifs <;> norm_num

end ThreeMajority
