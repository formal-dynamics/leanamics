import Undecided.PluralityBasic
import Undecided.PluralityConc

/-! # One round of the `k`-colour undecided-state dynamics: the good event (UND-3)

After one round from `x`, the number of nodes in state `o` is a sum over the nodes `v` of
indicators that depend only on the node `r v` sampled by `v` (`ind`), hence a sum of
independent indicators, and the two-sided Bernstein bound of `PluralityConc` applies.

With `cᵢ = cnt x i`, `q = und x`, the expected next counts are `µᵢ = mu x i = cᵢ(cᵢ + 2q)/n`
(the paper's (3)) and `µ_q = muU x` (the paper's (4)); for a colour `m`, the number of nodes
holding another colour is `oth x m = n - q - c_m`, with expected next value
`muS x m = n - µ_q - µ_m`.

A round from `x` to `y` is **good** (`Good ℓ m x y`) when every colour count is at most its
mean plus `dev ℓ`, the count of `m` at least its mean minus `dev ℓ`, the number of nodes of
other colours at most its mean plus `dev ℓ`, and the undecided count within `dev ℓ` of its mean.
A round is bad with probability at most `(k + 4) e^{-ℓ}` (`bad_le`).
-/

namespace Undecided.Plurality
open Finset Dynamics Real

variable {n k : ℕ}

/-- The size `cᵢ` of colour community `i`, as a real number. -/
noncomputable def cnt (x : Config n k) (i : Fin k) : ℝ := count x (some i)

/-- The number `q` of undecided nodes, as a real number. -/
noncomputable def und (x : Config n k) : ℝ := count x none

/-- Expected size after one round of colour community `i`: `cᵢ(cᵢ + 2q)/n` (the paper's (3)).
-/
noncomputable def mu (x : Config n k) (i : Fin k) : ℝ := cnt x i * (cnt x i + 2 * und x) / n

/-- Expected number of undecided nodes after one round (the paper's (4)). -/
noncomputable def muU (x : Config n k) : ℝ :=
  (und x ^ 2 + (n - und x) ^ 2 - ∑ i, cnt x i ^ 2) / n

/-- Number of nodes holding a colour other than `m`. -/
noncomputable def oth (x : Config n k) (m : Fin k) : ℝ := n - und x - cnt x m

/-- Expected number of nodes holding a colour other than `m` after one round. -/
noncomputable def muS (x : Config n k) (m : Fin k) : ℝ := n - muU x - mu x m

/-- A round from `x` to `y` is good: the counts are within `dev ℓ` of their means in the
directions used by the analysis. -/
def Good (ℓ : ℝ) (m : Fin k) (x y : Config n k) : Prop :=
  (∀ i, cnt y i ≤ mu x i + dev ℓ (mu x i)) ∧ mu x m - dev ℓ (mu x m) ≤ cnt y m ∧
    oth y m ≤ muS x m + dev ℓ (muS x m) ∧ muU x - dev ℓ (muU x) ≤ und y ∧
    und y ≤ muU x + dev ℓ (muU x)

/-! ### Elementary facts -/

lemma cnt_nonneg (x : Config n k) (i : Fin k) : 0 ≤ cnt x i := Nat.cast_nonneg _

lemma und_nonneg (x : Config n k) : 0 ≤ und x := Nat.cast_nonneg _

/-- `q + ∑ᵢ cᵢ = n`. -/
lemma und_add_sum (x : Config n k) : und x + ∑ i, cnt x i = n := by
  unfold und cnt
  exact_mod_cast count_none_add_sum x

/-- The nodes of colours other than `m` are `∑_{j ≠ m} cⱼ`. -/
lemma oth_eq_sum (x : Config n k) (m : Fin k) :
    oth x m = ∑ j ∈ univ.erase m, cnt x j := by
  have h := und_add_sum x
  rw [← add_sum_erase _ _ (mem_univ m)] at h
  unfold oth
  linarith

lemma oth_nonneg (x : Config n k) (m : Fin k) : 0 ≤ oth x m := by
  rw [oth_eq_sum]
  exact sum_nonneg fun j _ => cnt_nonneg x j

/-- The expected number of nodes of other colours is `∑_{j ≠ m} µⱼ`. -/
lemma muS_eq_sum (x : Config n k) (m : Fin k) :
    muS x m = ∑ j ∈ univ.erase m, mu x j := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [muS, muU, mu]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsum := und_add_sum x
  have hall : ∑ j, mu x j = ∑ j, cnt x j ^ 2 / n + 2 * und x * (∑ j, cnt x j) / n := by
    unfold mu
    rw [mul_sum, sum_div, ← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    ring
  have hall' : ∑ j, mu x j = n - muU x := by
    rw [hall]
    have e : ∑ j, cnt x j = n - und x := by linarith
    rw [e, muU, ← sum_div]
    field_simp
    ring
  rw [← add_sum_erase _ _ (mem_univ m)] at hall'
  unfold muS
  linarith

/-! ### Counts after one round as sums of independent indicators -/

/-- The indicator that node `v`, sampling node `w`, is in state `o` after the round. -/
noncomputable def ind (x : Config n k) (o : Option (Fin k)) (v w : Fin n) : ℝ :=
  if update (x v) (x w) = o then 1 else 0

lemma ind_01 (x : Config n k) (o : Option (Fin k)) (v w : Fin n) :
    ind x o v w = 0 ∨ ind x o v w = 1 := by
  unfold ind
  split <;> simp

lemma count_step_ind (x : Config n k) (r : Fin n → Fin n) (o : Option (Fin k)) :
    (count (step x r) o : ℝ) = ∑ v, ind x o v (r v) :=
  count_step_eq_sum x r o

/-- The indicator that node `v`, sampling `w`, holds a colour other than `m` after the round.
-/
noncomputable def indS (x : Config n k) (m : Fin k) (v w : Fin n) : ℝ :=
  1 - ind x none v w - ind x (some m) v w

lemma indS_01 (x : Config n k) (m : Fin k) (v w : Fin n) :
    indS x m v w = 0 ∨ indS x m v w = 1 := by
  unfold indS ind
  by_cases h1 : update (x v) (x w) = none
  · have h2 : update (x v) (x w) ≠ some m := by rw [h1]; simp
    simp [h1]
  · by_cases h2 : update (x v) (x w) = some m <;> simp [h1, h2]

lemma oth_step_ind (x : Config n k) (m : Fin k) (r : Fin n → Fin n) :
    oth (step x r) m = ∑ v, indS x m v (r v) := by
  unfold oth und cnt indS
  rw [count_step_ind, count_step_ind, sum_sub_distrib, sum_sub_distrib]
  simp

variable [NeZero n]

/-- The expected count after one round is the sum of the per-node probabilities. -/
lemma sum_avg_ind (x : Config n k) (o : Option (Fin k)) :
    ∑ v, avg (ind x o v) = avg (fun r : Fin n → Fin n => (count (step x r) o : ℝ)) := by
  simp_rw [count_step_ind]
  rw [avg_sum]
  exact (sum_congr rfl fun v _ => avg_eval n v (ind x o v)).symm

lemma sum_avg_ind_some (x : Config n k) (i : Fin k) :
    ∑ v, avg (ind x (some i) v) = mu x i := by
  rw [sum_avg_ind, expected_count_some]
  rfl

lemma sum_avg_ind_none (x : Config n k) : ∑ v, avg (ind x none v) = muU x := by
  rw [sum_avg_ind, expected_count_none]
  rfl

lemma sum_avg_indS (x : Config n k) (m : Fin k) : ∑ v, avg (indS x m v) = muS x m := by
  have h (v : Fin n) : avg (indS x m v) = 1 - avg (ind x none v) - avg (ind x (some m) v) := by
    unfold indS
    rw [avg_sub, avg_sub, avg_const]
  simp_rw [h]
  rw [sum_sub_distrib, sum_sub_distrib, sum_avg_ind_none, sum_avg_ind_some]
  simp [muS]

/-- **A bad round is rare**: the probability that a round from `x` is not good is at most
`(k + 4) e^{-ℓ}`. -/
theorem bad_le (x : Config n k) (m : Fin k) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    avg (fun r : Fin n → Fin n => by classical exact if Good ℓ m x (step x r) then 0 else 1)
      ≤ (k + 4) * exp (-ℓ) := by
  classical
  -- the five families of tail events
  set U : Fin k → (Fin n → Fin n) → ℝ := fun i r =>
    if mu x i + dev ℓ (mu x i) ≤ cnt (step x r) i then 1 else 0 with hU
  set Dm : (Fin n → Fin n) → ℝ := fun r =>
    if cnt (step x r) m ≤ mu x m - dev ℓ (mu x m) then 1 else 0 with hDm
  set Us : (Fin n → Fin n) → ℝ := fun r =>
    if muS x m + dev ℓ (muS x m) ≤ oth (step x r) m then 1 else 0 with hUs
  set Dq : (Fin n → Fin n) → ℝ := fun r =>
    if und (step x r) ≤ muU x - dev ℓ (muU x) then 1 else 0 with hDq
  set Uq : (Fin n → Fin n) → ℝ := fun r =>
    if muU x + dev ℓ (muU x) ≤ und (step x r) then 1 else 0 with hUq
  have hpt (r : Fin n → Fin n) : (if Good ℓ m x (step x r) then (0 : ℝ) else 1) ≤
      ∑ i, U i r + Dm r + Us r + Dq r + Uq r := by
    have h0 : ∀ i, 0 ≤ U i r := fun i => by simp only [hU]; split <;> norm_num
    have h1 : 0 ≤ Dm r := by simp only [hDm]; split <;> norm_num
    have h2 : 0 ≤ Us r := by simp only [hUs]; split <;> norm_num
    have h3 : 0 ≤ Dq r := by simp only [hDq]; split <;> norm_num
    have h4 : 0 ≤ Uq r := by simp only [hUq]; split <;> norm_num
    have hS : 0 ≤ ∑ i, U i r := sum_nonneg fun i _ => h0 i
    split_ifs with hG
    · linarith
    · unfold Good at hG
      simp only [not_and_or, not_forall, not_le] at hG
      rcases hG with ⟨i, hi⟩ | hG | hG | hG | hG
      · have : U i r = 1 := by simp only [hU]; rw [if_pos hi.le]
        have := single_le_sum (fun j _ => h0 j) (mem_univ i)
        linarith
      · have : Dm r = 1 := by simp only [hDm]; rw [if_pos hG.le]
        linarith
      · have : Us r = 1 := by simp only [hUs]; rw [if_pos hG.le]
        linarith
      · have : Dq r = 1 := by simp only [hDq]; rw [if_pos hG.le]
        linarith
      · have : Uq r = 1 := by simp only [hUq]; rw [if_pos hG.le]
        linarith
  -- each tail event has probability at most `e^{-ℓ}`
  have hUi (i : Fin k) : avg (U i) ≤ exp (-ℓ) := by
    have := tail_up (ind x (some i)) (ind_01 x (some i)) hℓ
    rw [sum_avg_ind_some] at this
    convert this using 2 with r
    simp only [hU, cnt, count_step_ind]
  have hD : avg Dm ≤ exp (-ℓ) := by
    have := tail_down (ind x (some m)) (ind_01 x (some m)) hℓ
    rw [sum_avg_ind_some] at this
    convert this using 2 with r
    simp only [hDm, cnt, count_step_ind]
  have hS : avg Us ≤ exp (-ℓ) := by
    have := tail_up (indS x m) (indS_01 x m) hℓ
    rw [sum_avg_indS] at this
    convert this using 2 with r
    simp only [hUs, oth_step_ind]
  have hDq' : avg Dq ≤ exp (-ℓ) := by
    have := tail_down (ind x none) (ind_01 x none) hℓ
    rw [sum_avg_ind_none] at this
    convert this using 2 with r
    simp only [hDq, und, count_step_ind]
  have hUq' : avg Uq ≤ exp (-ℓ) := by
    have := tail_up (ind x none) (ind_01 x none) hℓ
    rw [sum_avg_ind_none] at this
    convert this using 2 with r
    simp only [hUq, und, count_step_ind]
  calc avg (fun r : Fin n → Fin n => if Good ℓ m x (step x r) then (0 : ℝ) else 1)
      ≤ avg (fun r => ∑ i, U i r + Dm r + Us r + Dq r + Uq r) := avg_le_avg hpt
    _ = ∑ i, avg (U i) + avg Dm + avg Us + avg Dq + avg Uq := by
        rw [avg_add, avg_add, avg_add, avg_add, avg_sum]
    _ ≤ ∑ _i : Fin k, exp (-ℓ) + exp (-ℓ) + exp (-ℓ) + exp (-ℓ) + exp (-ℓ) := by
        have := sum_le_sum fun i (_ : i ∈ univ) => hUi i
        linarith
    _ = (k + 4) * exp (-ℓ) := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end Undecided.Plurality
