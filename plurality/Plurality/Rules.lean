import Plurality.Lower
import Plurality.Upper

/-!
# 3-input rules that solve plurality consensus (Section 4.2)

A **3-input rule** `f : Fin k → Fin k → Fin k → Fin k` is applied by every node
to the colors of its three samples (`stepWith f`). The paper characterizes the
rules that solve plurality consensus by two properties:

* **clear majority**: whenever two of the three colors agree, `f` returns that
  color;
* **uniform**: for three distinct colors `r, g, b`, each of them is returned
  on exactly two of the six orderings of `(r, g, b)`.

This file contains the definitions and the tools shared by the two parts of
Theorem 4.8: the counts `Δ` and `δ`, the solver predicate, and the fact that
consensus on a color is impossible once that color has disappeared
(`mono_le_alive`).
-/

namespace Plurality

open Finset Real Dynamics
open ThreeMajority (Tgt3 tgt3_nonempty)

variable {n k : ℕ}

/-- A 3-input rule. -/
abbrev Rule (k : ℕ) := Fin k → Fin k → Fin k → Fin k

/-- A rule is a *3-dynamics* in the sense of Definition 4.3: it returns one of
the colors it sees. -/
def Conservative (f : Rule k) : Prop := ∀ a b c, f a b c = a ∨ f a b c = b ∨ f a b c = c

/-- **Clear-majority property** (Definition 4.4). -/
def ClearMajority (f : Rule k) : Prop := ∀ a b, f a a b = a ∧ f a b a = a ∧ f b a a = a

/-- `Δ_r` for the pair `(r, b)`: on how many of the three orderings of
`(r, r, b)` the rule returns `r`. -/
def majCount (f : Rule k) (r b : Fin k) : ℕ :=
  (if f r r b = r then 1 else 0) + (if f r b r = r then 1 else 0) + (if f b r r = r then 1 else 0)

/-- `δ_c` for the triple `(r, g, b)`: on how many of the six orderings of
`(r, g, b)` the rule returns `c`. -/
def deltaCount (f : Rule k) (r g b c : Fin k) : ℕ :=
  (if f r g b = c then 1 else 0) + (if f r b g = c then 1 else 0) +
  (if f g r b = c then 1 else 0) + (if f g b r = c then 1 else 0) +
  (if f b r g = c then 1 else 0) + (if f b g r = c then 1 else 0)

/-- **Uniform property** (Definition 4.5). -/
def UniformRule (f : Rule k) : Prop :=
  ∀ r g b : Fin k, r ≠ g → g ≠ b → r ≠ b → deltaCount f r g b r = 2

/-- **`(s, ε)`-solver** (Definition 4.7): from every coloring in which `m` is
the unique plurality color with bias at least `s`, the probability that all
nodes eventually support `m` is at least `1 - ε`. Consensus is absorbing, so
"eventually" is the supremum over the horizon `T`. -/
def Solver (f : Rule k) (n : ℕ) (s ε : ℝ) : Prop :=
  ∀ (x : Config n k) (m : Fin k), argmaxSet (count x) = {m} → s ≤ bias (count x) →
    ∀ δ > 0, ∃ T : ℕ, 1 - ε - δ ≤
      expList (Tgt3 n) T (fun l => if Mono (runWith f x l) m then (1 : ℝ) else 0)

lemma ClearMajority.conservative_pair {f : Rule k} (hf : ClearMajority f) (r b : Fin k) :
    majCount f r b = 3 := by
  obtain ⟨h1, h2, h3⟩ := hf r b
  simp [majCount, h1, h2, h3]

/-- The counts of the three distinct colors sum to `6`. -/
lemma deltaCount_sum {f : Rule k} (hf : Conservative f) {r g b : Fin k}
    (hrg : r ≠ g) (hgb : g ≠ b) (hrb : r ≠ b) :
    deltaCount f r g b r + deltaCount f r g b g + deltaCount f r g b b = 6 := by
  unfold deltaCount
  have key (z : Fin k) (hz : z = r ∨ z = g ∨ z = b) :
      (if z = r then 1 else 0) + (if z = g then 1 else 0) + (if z = b then 1 else 0) = 1 := by
    rcases hz with rfl | rfl | rfl <;> simp [hrg, hgb, hrb, hrg.symm, hgb.symm, hrb.symm]
  have hmem (u v w : Fin k) (hu : u = r ∨ u = g ∨ u = b) (hv : v = r ∨ v = g ∨ v = b)
      (hw : w = r ∨ w = g ∨ w = b) : f u v w = r ∨ f u v w = g ∨ f u v w = b := by
    rcases hf u v w with h | h | h <;> rw [h] <;> assumption
  have hr : r = r ∨ r = g ∨ r = b := Or.inl rfl
  have hg : g = r ∨ g = g ∨ g = b := Or.inr (Or.inl rfl)
  have hb : b = r ∨ b = g ∨ b = b := Or.inr (Or.inr rfl)
  have := key _ (hmem r g b hr hg hb)
  have := key _ (hmem r b g hr hb hg)
  have := key _ (hmem g r b hg hr hb)
  have := key _ (hmem g b r hg hb hr)
  have := key _ (hmem b r g hb hr hg)
  have := key _ (hmem b g r hb hg hr)
  omega

/-- `δ` does not depend on the order in which the triple is listed. -/
lemma deltaCount_swap12 (f : Rule k) (r g b c : Fin k) :
    deltaCount f g r b c = deltaCount f r g b c := by
  unfold deltaCount; omega

lemma deltaCount_swap13 (f : Rule k) (r g b c : Fin k) :
    deltaCount f b g r c = deltaCount f r g b c := by
  unfold deltaCount; omega

/-! ### Absorption for conservative rules -/

lemma count_stepWith_eq_zero {f : Rule k} (hf : Conservative f) (x : Config n k) {j : Fin k}
    (hj : count x j = 0) (r : Tgt3 n) : count (stepWith f x r) j = 0 := by
  unfold count at *
  rw [card_eq_zero, filter_eq_empty_iff] at *
  intro v _ hv
  simp only [stepWith] at hv
  rcases hf (x (r v).1) (x (r v).2.1) (x (r v).2.2) with h | h | h <;>
    exact hj (mem_univ _) (h.symm.trans hv)

lemma count_runWith_eq_zero {f : Rule k} (hf : Conservative f) (x : Config n k) {j : Fin k}
    (hj : count x j = 0) (l : List (Tgt3 n)) : count (runWith f x l) j = 0 := by
  induction l generalizing x with
  | nil => exact hj
  | cons r l ih => exact ih _ (count_stepWith_eq_zero hf x hj r)

/-- **Consensus needs survival.** For every horizon `T`, the probability of
consensus on `m` at time `T` is at most the probability that `m` still has a
node at any fixed time `T₀`. -/
theorem mono_le_alive (hn : 1 ≤ n) {f : Rule k} (hf : Conservative f) (x : Config n k)
    (m : Fin k) (T T₀ : ℕ) :
    expList (Tgt3 n) T (fun l => if Mono (runWith f x l) m then (1 : ℝ) else 0)
      ≤ expList (Tgt3 n) T₀ (fun l => if 1 ≤ count (runWith f x l) m then (1 : ℝ) else 0) := by
  haveI := tgt3_nonempty hn
  -- consensus at `T` persists to `T + T₀`
  have h1 : expList (Tgt3 n) T (fun l => if Mono (runWith f x l) m then (1 : ℝ) else 0)
      ≤ expList (Tgt3 n) (T + T₀)
          (fun l => if Mono (runWith f x l) m then (1 : ℝ) else 0) := by
    rw [expList_append]
    refine expList_le_expList fun l₁ => ?_
    split_ifs with hm
    · have : ∀ l₂, (if Mono (runWith f x (l₁ ++ l₂)) m then (1 : ℝ) else 0) = 1 := fun l₂ => by
        rw [runWith_append, if_pos (runWith_mono hf hm l₂)]
      simp_rw [this]
      rw [expList_const]
    · exact expList_nonneg fun l₂ => by split <;> norm_num
  -- consensus at `T₀ + T` needs `m` alive at `T₀`
  have h2 : expList (Tgt3 n) (T₀ + T)
      (fun l => if Mono (runWith f x l) m then (1 : ℝ) else 0)
      ≤ expList (Tgt3 n) T₀
          (fun l => if 1 ≤ count (runWith f x l) m then (1 : ℝ) else 0) := by
    rw [expList_append]
    refine expList_le_expList fun l₁ => ?_
    split_ifs with ha
    · calc _ ≤ expList (Tgt3 n) T (fun _ => (1 : ℝ)) :=
            expList_le_expList fun l₂ => by split <;> norm_num
        _ = 1 := expList_const _ _
    · have h0 : count (runWith f x l₁) m = 0 := by omega
      have : ∀ l₂, (if Mono (runWith f x (l₁ ++ l₂)) m then (1 : ℝ) else 0) = 0 := fun l₂ => by
        rw [runWith_append, if_neg]
        rw [mono_iff_count, count_runWith_eq_zero hf _ h0]
        omega
      simp_rw [this]
      rw [expList_const]
  rw [add_comm] at h1
  exact h1.trans h2

/-! ### Sums over the sampled colors -/

/-- A triple sum of weights against a product of functions factorizes. -/
lemma sum_triple_factor (w P Q R : Fin k → ℝ) :
    ∑ a, ∑ b, ∑ c, w a * w b * w c * (P a * Q b * R c)
      = (∑ a, w a * P a) * (∑ b, w b * Q b) * (∑ c, w c * R c) := by
  have e : (∑ a, w a * P a) * (∑ b, w b * Q b) * (∑ c, w c * R c)
      = ∑ a, ∑ b, ∑ c, (w a * P a) * (w b * Q b) * (w c * R c) := by
    rw [sum_mul_sum, sum_mul]
    refine sum_congr rfl fun a _ => ?_
    rw [sum_mul]
    exact sum_congr rfl fun b _ => by rw [mul_sum]
  rw [e]
  exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun c _ => by ring

lemma sum_weight_ind (w : Fin k → ℝ) (c : Fin k) :
    ∑ a, w a * (if a = c then (1 : ℝ) else 0) = w c := by
  simp

end Plurality
