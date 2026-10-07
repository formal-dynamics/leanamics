import Undecided.Basic

/-! # The undecided-state dynamics with `k` colours (UND-3: the model)

Becchetti, Clementi, Natale, Pasquale and Silvestri, *Plurality consensus in the gossip model*
(SODA 2015, arXiv:1407.2565), Section 2. Each of `n` nodes of the complete graph holds one of
`k` colours or is undecided. In every round each node samples one node uniformly at random
(with replacement, possibly itself) and updates by Table 1 of the paper:

| node `u` \ sampled `v` | undecided | colour `i` | colour `j` |
| --- | --- | --- | --- |
| undecided | undecided | `i` | `j` |
| colour `i` | `i` | `i` | undecided |

A state is an `Option (Fin k)`: `none` is the undecided state, `some i` is colour `i`. With
`cᵢ = count x (some i)` and `q = count x none`, one round gives in expectation
`cᵢ (cᵢ + 2q) / n` nodes of colour `i` and `(q² + (n - q)² - ∑ᵢ cᵢ²) / n` undecided nodes: the
paper's equations (3) and (4) (`expected_count_some`, `expected_count_none`).

The **monochromatic distance** (Section 2.1) of a configuration is
`md(c) = ∑ᵢ (cᵢ / c₁)²`, where `c₁ = maxᵢ cᵢ` is the size of the plurality colour
(`md`, `maxCount`); `1 ≤ md(c) ≤ k` (the paper's (1): `one_le_md`, `md_le_card`).

These definitions generalize `Undecided.Basic` (the binary model) without changing it; the
binary model is the case `k = 2` (`Undecided/PluralityBinary.lean`).
-/

namespace Undecided.Plurality
open Finset Dynamics

/-- Configurations of `n` nodes with `k` colours (Section 2): node `v` supports colour `i`
(`x v = some i`) or is undecided (`x v = none`). -/
abbrev Config (n k : ℕ) := Fin n → Option (Fin k)

variable {n k : ℕ}

/-- The update rule of the undecided-state dynamics (Table 1 of the paper): new state of a node
in state `s` that samples a node in state `t`. An undecided node adopts the sampled state; a
node with colour `i` keeps it if it samples colour `i` or an undecided node, and becomes
undecided if it samples another colour. -/
def update : Option (Fin k) → Option (Fin k) → Option (Fin k)
  | none, t => t
  | some i, none => some i
  | some i, some j => if i = j then some i else none

/-- One synchronous round of the undecided-state dynamics on the complete graph (Section 2):
node `v` samples node `r v` and applies `update` (Table 1). -/
def step (x : Config n k) (r : Fin n → Fin n) : Config n k := fun v => update (x v) (x (r v))

/-- Number of nodes in state `o`: `count x (some i)` is the paper's `cᵢ`, `count x none` its
`q`. -/
def count (x : Config n k) (o : Option (Fin k)) : ℕ := (univ.filter fun v => x v = o).card

/-- Size `c₁ = maxᵢ cᵢ` of the plurality colour community (`0` if `k = 0`). -/
def maxCount (x : Config n k) : ℕ := univ.sup fun i => count x (some i)

/-- The **monochromatic distance** of Section 2.1, `md(c) = ∑ᵢ (cᵢ / c₁)²`, where `c₁` is the
size of the plurality colour (`maxCount`). -/
noncomputable def md (x : Config n k) : ℝ := ∑ i, ((count x (some i) : ℝ) / maxCount x) ^ 2

/-! ### Defining equations

Stated as theorems so that their (frozen) statements pin down the definitions above. -/

/-- Defining equation of `step` (Section 2): node `v` samples node `r v` and applies Table 1. -/
theorem step_apply (x : Config n k) (r : Fin n → Fin n) (v : Fin n) :
    step x r v = update (x v) (x (r v)) := rfl

/-- Defining equation of `count`: the number of nodes in state `o`. -/
theorem count_def (x : Config n k) (o : Option (Fin k)) :
    count x o = (univ.filter fun v => x v = o).card := rfl

/-- Defining equation of `maxCount`: `c₁ = maxᵢ cᵢ`. -/
theorem maxCount_def (x : Config n k) : maxCount x = univ.sup fun i => count x (some i) := rfl

/-- Defining equation of the monochromatic distance (Section 2.1): `md(c) = ∑ᵢ (cᵢ / c₁)²`. -/
theorem md_def (x : Config n k) : md x = ∑ i, ((count x (some i) : ℝ) / maxCount x) ^ 2 := rfl

/-! ### Basic facts -/

lemma count_le_maxCount (x : Config n k) (i : Fin k) : count x (some i) ≤ maxCount x :=
  le_sup (f := fun i => count x (some i)) (mem_univ i)

/-- If colour `m` is a plurality colour, `md(c) = ∑ᵢ (cᵢ / c_m)²` (the formula of the paper,
whose colours are numbered so that colour `1` is the plurality). -/
theorem md_eq_of_plurality (x : Config n k) {m : Fin k}
    (hm : ∀ i, count x (some i) ≤ count x (some m)) :
    md x = ∑ i, ((count x (some i) : ℝ) / count x (some m)) ^ 2 := by
  have h : maxCount x = count x (some m) :=
    le_antisymm (Finset.sup_le fun i _ => hm i) (count_le_maxCount x m)
  rw [md, h]

/-- The paper's (1), upper half: `md(c) ≤ k`. -/
theorem md_le_card (x : Config n k) : md x ≤ k := by
  have hterm (i : Fin k) : ((count x (some i) : ℝ) / maxCount x) ^ 2 ≤ 1 := by
    have h0 : (0 : ℝ) ≤ (count x (some i) : ℝ) / maxCount x := by positivity
    have h1 : (count x (some i) : ℝ) / maxCount x ≤ 1 := by
      rcases Nat.eq_zero_or_pos (maxCount x) with h | h
      · simp [h]
      · rw [div_le_one (by exact_mod_cast h)]
        exact_mod_cast count_le_maxCount x i
    nlinarith
  calc md x ≤ ∑ _i : Fin k, (1 : ℝ) := sum_le_sum fun i _ => hterm i
    _ = k := by simp

/-- The paper's (1), lower half: `1 ≤ md(c)` as soon as some colour is present. -/
theorem one_le_md (x : Config n k) (hx : ∃ i, 0 < count x (some i)) : 1 ≤ md x := by
  obtain ⟨i, hi⟩ := hx
  have hne : (univ : Finset (Fin k)).Nonempty := ⟨i, mem_univ i⟩
  obtain ⟨m, -, hm⟩ := exists_mem_eq_sup univ hne fun i => count x (some i)
  have hmax : maxCount x = count x (some m) := hm
  have hpos : (0 : ℝ) < count x (some m) := by
    have := count_le_maxCount x i
    rw [hmax] at this
    exact_mod_cast lt_of_lt_of_le hi this
  have hterm : ((count x (some m) : ℝ) / maxCount x) ^ 2 = 1 := by
    rw [hmax, div_self hpos.ne', one_pow]
  calc (1 : ℝ) = ((count x (some m) : ℝ) / maxCount x) ^ 2 := hterm.symm
    _ ≤ md x := single_le_sum (f := fun i => ((count x (some i) : ℝ) / maxCount x) ^ 2)
          (fun _ _ => sq_nonneg _) (mem_univ m)

/-- A colour that is supported by every node stays so: the monochromatic configurations are
fixed points of the dynamics. -/
lemma step_const (o : Option (Fin k)) (r : Fin n → Fin n) :
    step (fun _ => o) r = fun _ => o := by
  funext v
  cases o with
  | none => rfl
  | some i => simp [step, update]

/-- The colour counts and the undecided count add up to `n`. -/
lemma count_none_add_sum (x : Config n k) :
    count x none + ∑ i, count x (some i) = n := by
  have h := card_eq_sum_card_fiberwise (s := (univ : Finset (Fin n))) (t := univ)
    (f := x) (fun _ _ => mem_univ _)
  rw [card_univ, Fintype.card_fin, Fintype.sum_option] at h
  exact h.symm

lemma count_eq_sum (x : Config n k) (o : Option (Fin k)) :
    (count x o : ℝ) = ∑ v : Fin n, if x v = o then (1 : ℝ) else 0 := by
  unfold count
  rw [card_filter]
  push_cast
  rfl

lemma count_step_eq_sum (x : Config n k) (r : Fin n → Fin n) (o : Option (Fin k)) :
    (count (step x r) o : ℝ) =
      ∑ v, if update (x v) (x (r v)) = o then (1 : ℝ) else 0 := by
  rw [count_eq_sum]
  rfl

lemma avg_indicator_eq (x : Config n k) (o : Option (Fin k)) :
    avg (fun v : Fin n => if x v = o then (1 : ℝ) else 0) = (count x o : ℝ) / n := by
  rw [avg_indicator]
  simp [count, Fintype.card_fin]

/-- A node in state `s` that samples `t` has colour `i` afterwards exactly when it had colour
`i` and sampled colour `i` or an undecided node, or it was undecided and sampled colour `i`. -/
lemma indicator_update_some (s t : Option (Fin k)) (i : Fin k) :
    (if update s t = some i then (1 : ℝ) else 0) =
      (if s = some i then (1 : ℝ) else 0) *
          ((if t = some i then (1 : ℝ) else 0) + (if t = none then (1 : ℝ) else 0)) +
        (if s = none then (1 : ℝ) else 0) * (if t = some i then (1 : ℝ) else 0) := by
  rcases s with _ | j <;> rcases t with _ | l <;> simp only [update] <;> split_ifs <;> simp_all

/-- A node in state `s` that samples `t` is undecided afterwards exactly when both are
undecided, or it had a colour and sampled a different colour. -/
lemma indicator_update_none (s t : Option (Fin k)) :
    (if update s t = none then (1 : ℝ) else 0) =
      (if s = none then (1 : ℝ) else 0) * (if t = none then (1 : ℝ) else 0) +
        ∑ i, (if s = some i then (1 : ℝ) else 0) *
          (1 - (if t = none then (1 : ℝ) else 0) - (if t = some i then (1 : ℝ) else 0)) := by
  rcases s with _ | j
  · simp [update]
  · rw [sum_eq_single j (fun i _ hi => by simp [Ne.symm hi]) (by simp)]
    rcases t with _ | l
    · simp [update]
    · by_cases hjl : j = l
      · subst hjl
        simp [update]
      · simp [update, hjl, Ne.symm hjl]

lemma node_prob_some (x : Config n k) (v : Fin n) (i : Fin k) :
    avg (fun w : Fin n => if update (x v) (x w) = some i then (1 : ℝ) else 0) =
      (if x v = some i then (1 : ℝ) else 0) *
          ((count x (some i) : ℝ) / n + (count x none : ℝ) / n) +
        (if x v = none then (1 : ℝ) else 0) * ((count x (some i) : ℝ) / n) := by
  simp_rw [indicator_update_some]
  rw [avg_add, avg_const_mul, avg_const_mul, avg_add, avg_indicator_eq, avg_indicator_eq]

variable [NeZero n]

lemma node_prob_none (x : Config n k) (v : Fin n) :
    avg (fun w : Fin n => if update (x v) (x w) = none then (1 : ℝ) else 0) =
      (if x v = none then (1 : ℝ) else 0) * ((count x none : ℝ) / n) +
        ∑ i, (if x v = some i then (1 : ℝ) else 0) *
          (1 - (count x none : ℝ) / n - (count x (some i) : ℝ) / n) := by
  simp_rw [indicator_update_none]
  rw [avg_add, avg_const_mul, avg_indicator_eq, avg_sum]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  rw [avg_const_mul, avg_sub, avg_sub, avg_const, avg_indicator_eq, avg_indicator_eq]

/-- The paper's equation (3): `µᵢ = E[Cᵢ' | c] = cᵢ (cᵢ + 2q) / n`. -/
theorem expected_count_some (x : Config n k) (i : Fin k) :
    avg (fun r : Fin n → Fin n => (count (step x r) (some i) : ℝ)) =
      count x (some i) * (count x (some i) + 2 * count x none) / n := by
  simp_rw [count_step_eq_sum]
  rw [avg_sum]
  have hmarg (v : Fin n) :
      avg (fun r : Fin n → Fin n => if update (x v) (x (r v)) = some i then (1 : ℝ) else 0) =
        avg (fun w : Fin n => if update (x v) (x w) = some i then (1 : ℝ) else 0) :=
    avg_eval (γ := Fin n) n v (fun w => if update (x v) (x w) = some i then (1 : ℝ) else 0)
  simp_rw [hmarg, node_prob_some]
  rw [sum_add_distrib, ← sum_mul, ← sum_mul, ← count_eq_sum, ← count_eq_sum]
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  field_simp
  ring

/-- The paper's equation (4): `µ_q = E[Q' | c] = (q² + ∑_{i ≠ j} cᵢ cⱼ) / n
= (q² + (n - q)² - ∑ᵢ cᵢ²) / n`. -/
theorem expected_count_none (x : Config n k) :
    avg (fun r : Fin n → Fin n => (count (step x r) none : ℝ)) =
      ((count x none : ℝ) ^ 2 + (n - count x none) ^ 2 - ∑ i, (count x (some i) : ℝ) ^ 2) /
        n := by
  simp_rw [count_step_eq_sum]
  rw [avg_sum]
  have hmarg (v : Fin n) :
      avg (fun r : Fin n → Fin n => if update (x v) (x (r v)) = none then (1 : ℝ) else 0) =
        avg (fun w : Fin n => if update (x v) (x w) = none then (1 : ℝ) else 0) :=
    avg_eval (γ := Fin n) n v (fun w => if update (x v) (x w) = none then (1 : ℝ) else 0)
  simp_rw [hmarg, node_prob_none]
  rw [sum_add_distrib, ← sum_mul, ← count_eq_sum, sum_comm]
  simp_rw [← sum_mul, ← count_eq_sum]
  have hsum : (count x none : ℝ) + ∑ i, (count x (some i) : ℝ) = n := by
    exact_mod_cast count_none_add_sum x
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  have e : ∑ i, (count x (some i) : ℝ) * (1 - (count x none : ℝ) / n -
      (count x (some i) : ℝ) / n) =
      ((n - count x none) * ∑ i, (count x (some i) : ℝ) - ∑ i, (count x (some i) : ℝ) ^ 2) /
        n := by
    rw [mul_sum, ← sum_sub_distrib, sum_div]
    refine sum_congr rfl fun i _ => ?_
    field_simp
  rw [e, ← hsum]
  field_simp
  ring

end Undecided.Plurality
