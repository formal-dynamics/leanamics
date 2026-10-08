import Undecided.MajorityAssembly

/-! # Symmetry of the two opinions, and the probability forms (UND-1)

Exchanging the opinions `a` and `b` commutes with the update rule (`update_swap`), hence with
rounds (`step_swap`, `foldl_swap`), and exchanges the counts (`count_swap`). So the explicit
result for an `a`-majority (`majority_explicit`) gives the one for a `b`-majority
(`prob_b_ge`).
-/

namespace Undecided
open Finset Dynamics Real

/-- Exchange the opinions `a` and `b`. -/
def swapOp : Op → Op
  | .a => .b
  | .b => .a
  | .u => .u

lemma swapOp_swapOp (o : Op) : swapOp (swapOp o) = o := by
  cases o <;> rfl

lemma update_swap (s t : Op) : update (swapOp s) (swapOp t) = swapOp (update s t) := by
  cases s <;> cases t <;> rfl

variable {n : ℕ}

lemma step_swap (x : Config n) (r : Fin n → Fin n) :
    step (swapOp ∘ x) r = swapOp ∘ step x r := by
  funext v
  exact update_swap (x v) (x (r v))

lemma foldl_swap (l : List (Fin n → Fin n)) (x : Config n) :
    l.foldl step (swapOp ∘ x) = swapOp ∘ l.foldl step x := by
  induction l generalizing x with
  | nil => rfl
  | cons r l ih => simp only [List.foldl_cons, step_swap, ih]

lemma count_swap (x : Config n) (o : Op) : count (swapOp ∘ x) o = count x (swapOp o) := by
  unfold count
  congr 1
  refine Finset.filter_congr fun v _ => ?_
  constructor
  · intro h
    rw [← h, Function.comp_apply, swapOp_swapOp]
  · intro h
    rw [Function.comp_apply, h, swapOp_swapOp]

lemma swap_eq_const (y : Config n) (o : Op) :
    swapOp ∘ y = (fun _ => o) ↔ y = fun _ => swapOp o := by
  constructor
  · intro h
    funext v
    rw [← congrFun h v, Function.comp_apply, swapOp_swapOp]
  · intro h
    funext v
    rw [Function.comp_apply, h, swapOp_swapOp]

/-- `exp x ≥ x³/6` at `x = log n`. -/
lemma log_cube_le {n : ℕ} (hn : 1 ≤ n) : log (n : ℝ) ^ 3 / 6 ≤ n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hL0 : (0 : ℝ) ≤ log n := log_nonneg (by exact_mod_cast hn)
  have h1 := pow_div_factorial_le_exp (log (n : ℝ)) hL0 3
  rw [exp_log hn0] at h1
  norm_num [Nat.factorial] at h1
  linarith

/-- **`a`-majority, probability form**: `1 - 2/n ≤ P(all nodes hold a after ⌈10⁴ log n⌉
rounds)`. -/
lemma prob_a_ge (hL : (10000 : ℝ) ≤ log n) (x : Config n)
    (hx : 10000 * √(n * log n) ≤ (count x .a : ℝ) - count x .b) :
    1 - 2 / n ≤ expList (Fin n → Fin n) ⌈10000 * log n⌉₊
      (fun l => if l.foldl step x = (fun _ => Op.a) then (1 : ℝ) else 0) := by
  haveI : NeZero n := ⟨by have := one_le_of_log hL; omega⟩
  rw [prob_allA_eq]
  linarith [majority_explicit hL x hx]

/-- **`b`-majority, probability form** (by the symmetry `a ↔ b`). -/
lemma prob_b_ge (hL : (10000 : ℝ) ≤ log n) (x : Config n)
    (hx : 10000 * √(n * log n) ≤ (count x .b : ℝ) - count x .a) :
    1 - 2 / n ≤ expList (Fin n → Fin n) ⌈10000 * log n⌉₊
      (fun l => if l.foldl step x = (fun _ => Op.b) then (1 : ℝ) else 0) := by
  have hx' : 10000 * √(n * log n) ≤ (count (swapOp ∘ x) .a : ℝ) - count (swapOp ∘ x) .b := by
    rw [count_swap, count_swap]
    exact hx
  have h := prob_a_ge hL (swapOp ∘ x) hx'
  simp only [foldl_swap, swap_eq_const] at h
  exact h

end Undecided
