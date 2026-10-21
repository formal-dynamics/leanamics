import Plurality.Model
import ThreeMajority.Main

/-!
# Two colors: the existing binary 3-majority development

For `k = 2` the 3-majority round `step` is *literally* the two-opinion process
of `ThreeMajority`: the set of nodes of color `1` evolves by `ThreeMajority.step`,
round by round and for every realization of the samples (`colorSet_step`,
`colorSet_run`). The one-round bridge is the bridge `ThreeMajority.stepCol_bool`
of the model with colours of any type, through `step_eq_stepCol` and the renaming
of the colors `Fin 2` as `Bool`. The binary consensus theorem
`ThreeMajority.majority3_consensus_whp` therefore holds for two colors as stated,
through `colorSet_run` and `mono_one_iff_colorSet`: from a `60%` majority,
3-majority with two colors reaches the majority color within `O(log n)` rounds
with probability `1 - O(1/n)`.

This is the `k = 2` instance of the paper's Corollary 3.12 (large plurality,
`λ = Θ(1)`), obtained by reusing the existing statement rather than by
re-proving it.
-/

namespace Plurality

open Finset
open ThreeMajority (Tgt3)

variable {n : ℕ}

/-- The set of nodes of a given color. -/
def colorSet {k : ℕ} (x : Config n k) (j : Fin k) : Finset (Fin n) := univ.filter fun v => x v = j

lemma card_colorSet {k : ℕ} (x : Config n k) (j : Fin k) : (colorSet x j).card = count x j := rfl

/-- **One round.** The color-`1` set evolves by the binary 3-majority step: the bridge
`ThreeMajority.stepCol_bool`, with the colors `Fin 2` renamed as `Bool`. -/
lemma colorSet_step (x : Config n 2) (r : Tgt3 n) :
    colorSet (step x r) 1 = ThreeMajority.step (colorSet x 1) r := by
  have he : Function.Injective fun j : Fin 2 => decide (j = 1) := by decide
  have h := ThreeMajority.stepCol_bool ((fun j : Fin 2 => decide (j = 1)) ∘ x) r
  rw [ThreeMajority.stepCol_comp he] at h
  simpa [colorSet, step_eq_stepCol] using h

/-- **Every trajectory.** The color-`1` set evolves by `ThreeMajority.run`. -/
lemma colorSet_run (x : Config n 2) (l : List (Tgt3 n)) :
    colorSet (run x l) 1 = ThreeMajority.run (colorSet x 1) l := by
  induction l generalizing x with
  | nil => rfl
  | cons r l ih => rw [run_cons, ih, colorSet_step, ThreeMajority.run_cons]

lemma mono_one_iff_colorSet (x : Config n 2) : Mono x 1 ↔ colorSet x 1 = univ := by
  simp [Mono, colorSet, Finset.eq_univ_iff_forall]

/-! ### Two colors from a vanishing bias -/

/-- The two-color configuration with color `1` exactly on `I`. -/
def ofSet (I : Finset (Fin n)) : Config n 2 := fun v => if v ∈ I then 1 else 0

lemma colorSet_ofSet (I : Finset (Fin n)) : colorSet (ofSet I) 1 = I := by
  ext v
  by_cases h : v ∈ I <;> simp [colorSet, ofSet, h]

lemma count_ofSet_one (I : Finset (Fin n)) : count (ofSet I) 1 = I.card := by
  rw [← card_colorSet, colorSet_ofSet]

lemma count_ofSet_zero (I : Finset (Fin n)) : count (ofSet I) 0 = n - I.card := by
  have h : (univ.filter fun v => ofSet I v = 0) = Iᶜ := by
    ext v
    by_cases hv : v ∈ I <;> simp [ofSet, hv]
  rw [count, h, card_compl, Fintype.card_fin]

end Plurality
