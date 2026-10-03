import Plurality.Model
import ThreeMajority.Main

/-!
# Two colors: the existing binary 3-majority development

For `k = 2` the 3-majority dynamics of this package is *literally* the process
formalized in `ThreeMajority`: the set of nodes of color `1` evolves by
`ThreeMajority.step`, round by round and for every realization of the samples
(`colorSet_step`, `colorSet_run`). The binary consensus theorem
`ThreeMajority.majority3_consensus_whp` therefore transfers verbatim
(`binary_consensus_whp`): from a `60%` majority, 3-majority with two colors
reaches the majority color within `O(log n)` rounds with probability
`1 - O(1/n)`.

This is the `k = 2` instance of the paper's Corollary 3.12 (large plurality,
`λ = Θ(1)`), obtained by reusing the existing statement rather than by
re-proving it.
-/

namespace Plurality

open Finset
open ThreeMajority (Tgt3 tgt3_nonempty T2a)

variable {n : ℕ}

/-- The set of nodes of a given color. -/
def colorSet {k : ℕ} (x : Config n k) (j : Fin k) : Finset (Fin n) := univ.filter fun v => x v = j

lemma card_colorSet {k : ℕ} (x : Config n k) (j : Fin k) : (colorSet x j).card = count x j := rfl

/-- With two colors, 3-majority returns color `1` iff at least two of the three
samples have color `1`. -/
lemma maj3_eq_one_iff (a b c : Fin 2) :
    maj3 a b c = 1 ↔
      2 ≤ (if a = 1 then 1 else 0) + (if b = 1 then 1 else 0) + (if c = 1 then 1 else 0) := by
  revert a b c
  decide

/-- **One round.** The color-`1` set evolves by the binary 3-majority step. -/
lemma colorSet_step (x : Config n 2) (r : Tgt3 n) :
    colorSet (step x r) 1 = ThreeMajority.step (colorSet x 1) r := by
  ext v
  simp only [colorSet, mem_filter, mem_univ, true_and, ThreeMajority.mem_step,
    ThreeMajority.sampleCount, ThreeMajority.sampleCountOf, step, stepWith]
  exact maj3_eq_one_iff _ _ _

/-- **Every trajectory.** The color-`1` set evolves by `ThreeMajority.run`. -/
lemma colorSet_run (x : Config n 2) (l : List (Tgt3 n)) :
    colorSet (run x l) 1 = ThreeMajority.run (colorSet x 1) l := by
  induction l generalizing x with
  | nil => rfl
  | cons r l ih => rw [run_cons, ih, colorSet_step, ThreeMajority.run_cons]

lemma mono_one_iff_colorSet (x : Config n 2) : Mono x 1 ↔ colorSet x 1 = univ := by
  simp [Mono, colorSet, Finset.eq_univ_iff_forall]

/-- **Binary plurality consensus** (reusing `ThreeMajority.majority3_consensus_whp`):
with two colors, if color `1` is supported by at least `60%` of the nodes and
`log n ≥ 30`, then after `10 + (⌈6 log n⌉ + 2) = O(log n)` rounds all nodes
support color `1` with probability at least `1 - 500/n`. -/
theorem binary_consensus_whp (hbig : (30 : ℝ) ≤ Real.log n) (x : Config n 2)
    (hx : (n : ℝ) * (3 / 5) ≤ count x 1) :
    1 - 500 / (n : ℝ)
      ≤ Dynamics.expList (Tgt3 n) (10 + (T2a n + 2))
          (fun l => if Mono (run x l) 1 then (1 : ℝ) else 0) := by
  have h := ThreeMajority.majority3_consensus_whp hbig (colorSet x 1) hx
  refine h.trans_eq ?_
  congr 1
  funext l
  rw [← colorSet_run]
  by_cases hm : Mono (run x l) 1
  · rw [if_pos hm, if_pos ((mono_one_iff_colorSet _).mp hm)]
  · rw [if_neg hm, if_neg (fun h' => hm ((mono_one_iff_colorSet _).mpr h'))]

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
