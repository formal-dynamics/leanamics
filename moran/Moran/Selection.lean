import Moran.Counts

/-! # Moran's chain with selection on mutant counts

Population genetics follows the number `k` of mutants, of fitness `r > 0`, in a population of
constant size `n` whose residents have fitness `1`. With selection by fecundity (Moran 1959), the
individual that reproduces is drawn with probability proportional to its fitness and the one that
dies is drawn uniformly from the whole population, possibly the same one: from `k` mutants the
count goes up by one with probability `rk/(rk + n - k) · (n - k)/n`, down by one with probability
`(n - k)/(rk + n - k) · k/n`, and stays otherwise (`moranSelectionCountKernel`). If the offspring
replaces one of the other individuals, the second factors are `(n - k)/(n - 1)` and `k/(n - 1)`
(`birthDeathCountKernel`). Both are birth–death chains on `{0, …, n}` (`birthDeathChain`, which
extends the symmetric chains of `Moran.Counts`, `birthDeath_eq_birthDeathChain`).

The Birth–death kernel on the complete graph, `moranKernel ⊤ r` (the parent is drawn
proportionally to fitness and its offspring replaces a uniformly random neighbour, that is another
vertex: a `SimpleGraph` has no self-loops), lumps to `birthDeathCountKernel` under the number of
mutants (`moranKernel_top_lumps`). Moran's chain has the same jump chain
(`moranSelectionCountKernel_sameJumpChain`): until absorption at `0` or `n`, the count moves up
with probability `r/(1 + r)` and down with probability `1/(1 + r)` (`birthDeathCountKernel_jump`,
`moranSelectionCountKernel_jump`).
Hence, for `r ≠ 1` and `n ≥ 1`, both chains fix the mutants from `k` copies with Moran's
probability `(1 - r^{-k})/(1 - r^{-n})` (`birthDeathCountKernel_fixation`, from `moran_formula`
through the lumping, and `moranSelectionCountKernel_fixation`, through the jump chain).

For `r = 1` the two chains are the neutral chains `pullCountKernel` and `moranCountKernel`
(`birthDeathCountKernel_one`, `moranSelectionCountKernel_one`), so neutral push on `K_n` lumps to
the count chain of death–Birth (`moranKernel_top_one_lumps`). On every regular graph, neutral push
and pull are even the same kernel on configurations (`moranKernel_one_eq_pullKernel`).
-/

namespace Moran
open Dynamics Finset

/-! ### Birth–death chains on `{0, …, n}` -/

/-- One move of a birth–death chain: down by one (`0`), stay (`1`) or up by one (`2`), with
probabilities `d`, `1 - d - u` and `u`. -/
noncomputable def moveDistOf (d u : ℝ) (hd : 0 ≤ d) (hu : 0 ≤ u) (h1 : d + u ≤ 1) :
    Distribution (Fin 3) where
  weight := ![d, 1 - d - u, u]
  nonneg i := by
    fin_cases i
    · exact hd
    · show 0 ≤ 1 - d - u
      linarith
    · exact hu
  sum_one := by
    simp only [Fin.sum_univ_three, Matrix.cons_val]
    ring

/-- A **birth–death chain** on `{0, …, n}`: from `k`, the count goes down by one with probability
`d k`, up by one with probability `u k`, and stays otherwise. (The moves are clamped to
`{0, …, n}`; the chains below have `d = u = 0` at `0` and at `n`.) -/
noncomputable def birthDeathChain {n : ℕ} (d u : Fin (n + 1) → ℝ) (hd : ∀ k, 0 ≤ d k)
    (hu : ∀ k, 0 ≤ u k) (h1 : ∀ k, d k + u k ≤ 1) : Kernel (Fin (n + 1)) := fun k =>
  (moveDistOf (d k) (u k) (hd k) (hu k) (h1 k)).map ![countDown k, k, countUp k]

section BirthDeathChain
variable {n : ℕ} {d u : Fin (n + 1) → ℝ} {hd : ∀ k, 0 ≤ d k} {hu : ∀ k, 0 ≤ u k}
  {h1 : ∀ k, d k + u k ≤ 1}

/-- One step of a birth–death chain, on observables. -/
theorem birthDeathChain_expect (k : Fin (n + 1)) (g : Fin (n + 1) → ℝ) :
    (birthDeathChain d u hd hu h1 k).expect g =
      d k * g (countDown k) + (1 - d k - u k) * g k + u k * g (countUp k) := by
  rw [birthDeathChain, Distribution.map_expect]
  simp only [Distribution.expect, moveDistOf, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

/-- The transition probabilities of a birth–death chain to the other states. -/
theorem birthDeathChain_weight_of_ne {k y : Fin (n + 1)} (hy : y ≠ k) :
    (birthDeathChain d u hd hu h1 k).weight y =
      d k * (if countDown k = y then 1 else 0) + u k * (if countUp k = y then 1 else 0) := by
  rw [Distribution.weight_eq_expect_ite, birthDeathChain_expect, if_neg (Ne.symm hy)]
  ring

/-- A birth–death chain stays at a state from which it cannot move. -/
theorem birthDeathChain_prob_self {k : Fin (n + 1)} (hdk : d k = 0) (huk : u k = 0) :
    (birthDeathChain d u hd hu h1 k).prob (· = k) = 1 := by
  rw [Distribution.prob_eq_expect, birthDeathChain_expect, hdk, huk, if_pos rfl]
  ring

/-- Birth–death chains whose move probabilities are proportional, with a positive factor that
may depend on the state, have the same jump chain. -/
theorem birthDeathChain_sameJumpChain {d' u' : Fin (n + 1) → ℝ} {hd' : ∀ k, 0 ≤ d' k}
    {hu' : ∀ k, 0 ≤ u' k} {h1' : ∀ k, d' k + u' k ≤ 1} (c : Fin (n + 1) → ℝ)
    (hc : ∀ k, 0 < c k) (hdc : ∀ k, d k = c k * d' k) (huc : ∀ k, u k = c k * u' k) :
    (birthDeathChain d u hd hu h1).SameJumpChain (birthDeathChain d' u' hd' hu' h1') :=
  Kernel.sameJumpChain_of_weight fun k => ⟨c k, hc k, fun y hy => by
    rw [birthDeathChain_weight_of_ne hy, birthDeathChain_weight_of_ne hy, hdc, huc]
    ring⟩

end BirthDeathChain

/-- The symmetric birth–death chains of `Moran.Counts` are the birth–death chains with equal
probabilities of moving down and up. -/
theorem birthDeath_eq_birthDeathChain {n : ℕ} (q : Fin (n + 1) → ℝ) (h0 : ∀ k, 0 ≤ q k)
    (h1 : ∀ k, 2 * q k ≤ 1) :
    birthDeath q h0 h1 = birthDeathChain q q h0 h0 fun k => by linarith [h1 k] := by
  funext k
  refine Distribution.ext_expect fun g => ?_
  rw [birthDeath_expect, birthDeathChain_expect]
  ring

/-! ### Moran's chain with selection on counts, with and without self-loops -/

lemma fitnessSum_nonneg (n : ℕ) {r : ℝ} (hr : 0 < r) (k : Fin (n + 1)) :
    0 ≤ r * k + (n - k) :=
  add_nonneg (mul_nonneg hr.le (Nat.cast_nonneg _)) (sub_nonneg.2 (count_le n k))

/-- The total fitness `rk + n - k` of a population of `n ≥ 1` is positive. -/
lemma fitnessSum_pos {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r) (k : Fin (n + 1)) :
    0 < r * k + (n - k) := by
  have hrk : 0 ≤ r * k := mul_nonneg hr.le (Nat.cast_nonneg _)
  rcases (Fin.is_le k).lt_or_eq with hk | hk
  · have : (k : ℝ) < n := by exact_mod_cast hk
    linarith
  · have hk' : (k : ℝ) = n := by exact_mod_cast hk
    have : (0 : ℝ) < n := by exact_mod_cast hn
    rw [hk', sub_self, add_zero]
    exact mul_pos hr this

lemma cast_mul_pred_nonneg (m : ℕ) : (0 : ℝ) ≤ m * (m - 1) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith

lemma count_mul_nonneg (n : ℕ) (k : Fin (n + 1)) : (0 : ℝ) ≤ k * (n - k) :=
  mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.2 (count_le n k))

/-- A population of at most one individual has no pair of a mutant and a resident:
`k (n - k) = 0`. -/
lemma count_mul_eq_zero_of_lt_two {n : ℕ} (hn : n < 2) (k : Fin (n + 1)) :
    (k : ℝ) * (n - k) = 0 := by
  have hk := Fin.is_le k
  interval_cases n <;> interval_cases (k : ℕ) <;> norm_num

lemma bd_den_nonneg (n : ℕ) {r : ℝ} (hr : 0 < r) (k : Fin (n + 1)) :
    0 ≤ (r * k + (n - k)) * ((n : ℝ) - 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact mul_nonneg (fitnessSum_nonneg n hr k) (sub_nonneg.2 (by exact_mod_cast hn))

lemma bd_down_nonneg (n : ℕ) {r : ℝ} (hr : 0 < r) (k : Fin (n + 1)) :
    0 ≤ (k : ℝ) * (n - k) / ((r * k + (n - k)) * (n - 1)) :=
  div_nonneg (count_mul_nonneg n k) (bd_den_nonneg n hr k)

lemma bd_up_nonneg (n : ℕ) {r : ℝ} (hr : 0 < r) (k : Fin (n + 1)) :
    0 ≤ r * k * (n - k) / ((r * k + (n - k)) * (n - 1)) := by
  rw [mul_assoc]
  exact div_nonneg (mul_nonneg hr.le (count_mul_nonneg n k)) (bd_den_nonneg n hr k)

lemma bd_move_le (n : ℕ) {r : ℝ} (hr : 0 < r) (k : Fin (n + 1)) :
    (k : ℝ) * (n - k) / ((r * k + (n - k)) * (n - 1)) +
      r * k * (n - k) / ((r * k + (n - k)) * (n - 1)) ≤ 1 := by
  rcases lt_or_ge n 2 with hn | hn
  · rw [mul_assoc r, count_mul_eq_zero_of_lt_two hn k]
    norm_num
  · have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hD : 0 < (r * k + (n - k)) * (n - 1) :=
      mul_pos (fitnessSum_pos (by omega) hr k) (by linarith)
    rw [← add_div, div_le_one hD]
    have h1 := cast_mul_pred_nonneg k
    have h2 := cast_mul_pred_nonneg (n - k)
    rw [Nat.cast_sub (Fin.is_le k)] at h2
    nlinarith [mul_nonneg hr.le h1]

lemma ms_den_nonneg (n : ℕ) {r : ℝ} (hr : 0 < r) (k : Fin (n + 1)) :
    0 ≤ (r * k + (n - k)) * (n : ℝ) :=
  mul_nonneg (fitnessSum_nonneg n hr k) (Nat.cast_nonneg _)

lemma ms_down_nonneg (n : ℕ) {r : ℝ} (hr : 0 < r) (k : Fin (n + 1)) :
    0 ≤ (k : ℝ) * (n - k) / ((r * k + (n - k)) * n) :=
  div_nonneg (count_mul_nonneg n k) (ms_den_nonneg n hr k)

lemma ms_up_nonneg (n : ℕ) {r : ℝ} (hr : 0 < r) (k : Fin (n + 1)) :
    0 ≤ r * k * (n - k) / ((r * k + (n - k)) * n) := by
  rw [mul_assoc]
  exact div_nonneg (mul_nonneg hr.le (count_mul_nonneg n k)) (ms_den_nonneg n hr k)

lemma ms_move_le (n : ℕ) {r : ℝ} (hr : 0 < r) (k : Fin (n + 1)) :
    (k : ℝ) * (n - k) / ((r * k + (n - k)) * n) +
      r * k * (n - k) / ((r * k + (n - k)) * n) ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hD : 0 < (r * k + (n - k)) * (n : ℝ) :=
      mul_pos (fitnessSum_pos hn hr k) (by exact_mod_cast hn)
    rw [← add_div, div_le_one hD]
    nlinarith [mul_nonneg hr.le (sq_nonneg (k : ℝ)), sq_nonneg ((n : ℝ) - k)]

/-- **Birth–death with fitness `r` on mutant counts, without self-loops.** In a population of `n`,
the reproducing individual is drawn with probability proportional to its fitness (`r` for each of
the `k` mutants, `1` for each of the `n - k` residents) and its offspring replaces one of the
other `n - 1` individuals, drawn uniformly: the count goes up by one with probability
`rk(n-k)/((rk + n - k)(n - 1))`, down by one with probability `k(n-k)/((rk + n - k)(n - 1))`, and
stays otherwise. -/
noncomputable def birthDeathCountKernel (n : ℕ) (r : ℝ) (hr : 0 < r) : Kernel (Fin (n + 1)) :=
  birthDeathChain (fun k => (k : ℝ) * (n - k) / ((r * k + (n - k)) * (n - 1)))
    (fun k => r * k * (n - k) / ((r * k + (n - k)) * (n - 1)))
    (bd_down_nonneg n hr) (bd_up_nonneg n hr) (bd_move_le n hr)

/-- **Moran's chain with selection on mutant counts** (Moran 1959, selection by fecundity). In a
population of `n`, the reproducing individual is drawn with probability proportional to its
fitness and the dying individual uniformly from the whole population, independently (possibly
the same one): from `k` mutants the count goes up by one with probability
`rk(n-k)/((rk + n - k) n)`, down by one with probability `k(n-k)/((rk + n - k) n)`, and stays
otherwise. -/
noncomputable def moranSelectionCountKernel (n : ℕ) (r : ℝ) (hr : 0 < r) :
    Kernel (Fin (n + 1)) :=
  birthDeathChain (fun k => (k : ℝ) * (n - k) / ((r * k + (n - k)) * n))
    (fun k => r * k * (n - k) / ((r * k + (n - k)) * n))
    (ms_down_nonneg n hr) (ms_up_nonneg n hr) (ms_move_le n hr)

/-- The walk on `{0, …, n}` that moves up by one with probability `r/(1 + r)` and down by one with
probability `1/(1 + r)`, absorbed at `0` and at `n`. -/
noncomputable def biasedWalk (n : ℕ) (r : ℝ) (hr : 0 < r) : Kernel (Fin (n + 1)) :=
  birthDeathChain (fun k => if (k : ℕ) = 0 ∨ (k : ℕ) = n then 0 else 1 / (1 + r))
    (fun k => if (k : ℕ) = 0 ∨ (k : ℕ) = n then 0 else r / (1 + r))
    (fun k => by
      split
      · exact le_rfl
      · exact div_nonneg zero_le_one (by linarith))
    (fun k => by
      split
      · exact le_rfl
      · exact div_nonneg hr.le (by linarith))
    (fun k => by
      split
      · norm_num
      · rw [← add_div, div_le_one (by linarith)])

/-- **Moran's chain and the chain without self-loops have the same jump chain.** Off the
diagonal, the rows of Moran's chain are `(n - 1)/n` times those of the chain without self-loops:
the offspring replaces its own parent with probability `1/n`, and otherwise a uniformly random
other individual. -/
theorem moranSelectionCountKernel_sameJumpChain (n : ℕ) {r : ℝ} (hr : 0 < r) :
    (moranSelectionCountKernel n r hr).SameJumpChain (birthDeathCountKernel n r hr) := by
  rcases lt_or_ge n 2 with hn | hn
  · refine birthDeathChain_sameJumpChain (fun _ => 1) (fun _ => one_pos) (fun k => ?_)
      (fun k => ?_)
    · simp only [count_mul_eq_zero_of_lt_two hn k, zero_div, mul_zero]
    · simp only [mul_assoc r, count_mul_eq_zero_of_lt_two hn k, mul_zero, zero_div]
  · have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    refine birthDeathChain_sameJumpChain (fun _ => (n - 1) / n)
      (fun _ => div_pos (by linarith) (by linarith)) (fun k => ?_) (fun k => ?_)
    all_goals
      have hF := (fitnessSum_pos (by omega) hr k).ne'
      have h1 : (n : ℝ) - 1 ≠ 0 := by linarith
      have h2 : (n : ℝ) ≠ 0 := by linarith
      field_simp

/-- The biased walk is its own jump chain. -/
theorem biasedWalk_jump (n : ℕ) {r : ℝ} (hr : 0 < r) :
    (biasedWalk n r hr).jump = biasedWalk n r hr := by
  refine Kernel.jump_eq_self _ fun k => ?_
  rw [Distribution.weight_eq_expect_ite, biasedWalk, birthDeathChain_expect, if_pos rfl]
  by_cases hk : (k : ℕ) = 0 ∨ (k : ℕ) = n
  · right
    rw [if_pos hk, if_pos hk]
    ring
  · left
    rw [if_neg hk, if_neg hk]
    have hd : countDown k ≠ k := by
      simp only [countDown, ne_eq, Fin.ext_iff]
      omega
    have hu : countUp k ≠ k := by
      have := Fin.is_le k
      simp only [countUp, ne_eq, Fin.ext_iff]
      omega
    have h1r : 1 + r ≠ 0 := (by linarith : (0 : ℝ) < 1 + r).ne'
    rw [if_neg hd, if_neg hu]
    field_simp
    ring

/-- **The jump chain of Birth–death with selection on counts** (without self-loops, hence also
with self-loops by `moranSelectionCountKernel_sameJumpChain`): until absorption at `0` or `n`,
the count moves up by one with probability `r/(1 + r)` and down by one with probability
`1/(1 + r)`. -/
theorem birthDeathCountKernel_jump (n : ℕ) {r : ℝ} (hr : 0 < r) :
    (birthDeathCountKernel n r hr).jump = biasedWalk n r hr := by
  have h1r : (0 : ℝ) < 1 + r := by linarith
  have h : (birthDeathCountKernel n r hr).SameJumpChain (biasedWalk n r hr) := by
    refine birthDeathChain_sameJumpChain
      (fun k => if (k : ℕ) = 0 ∨ (k : ℕ) = n then 1
        else (1 + r) * ((k : ℝ) * (n - k) / ((r * k + (n - k)) * (n - 1))))
      (fun k => ?_) (fun k => ?_) (fun k => ?_)
    all_goals by_cases hk : (k : ℕ) = 0 ∨ (k : ℕ) = n
    · simp only [if_pos hk]
      exact one_pos
    · have hle := Fin.is_le k
      have hk1 : 1 ≤ (k : ℕ) := Nat.pos_of_ne_zero fun h => hk (Or.inl h)
      have hkn' : (k : ℕ) < n := lt_of_le_of_ne hle fun h => hk (Or.inr h)
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
      have hkn : (k : ℝ) < n := by exact_mod_cast hkn'
      have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
      have hF := fitnessSum_pos (by omega) hr k
      simp only [if_neg hk]
      have : 0 < (k : ℝ) * (n - k) := mul_pos hk0 (by linarith)
      have : 0 < (r * k + (n - k)) * ((n : ℝ) - 1) := mul_pos hF (by linarith)
      positivity
    · have h0 : (k : ℝ) * (n - k) = 0 := by
        rcases hk with hk | hk <;> simp [hk]
      simp only [if_pos hk, h0, zero_div, mul_zero]
    · simp only [if_neg hk]
      field_simp
    · have h0 : (k : ℝ) * (n - k) = 0 := by
        rcases hk with hk | hk <;> simp [hk]
      simp only [if_pos hk, mul_assoc r, h0, zero_div, mul_zero]
    · simp only [if_neg hk]
      field_simp
  rw [h, biasedWalk_jump]

/-- **The jump chain of Moran's chain with selection on counts**: until absorption at `0` or `n`,
the count moves up by one with probability `r/(1 + r)` and down by one with probability
`1/(1 + r)`. -/
theorem moranSelectionCountKernel_jump (n : ℕ) {r : ℝ} (hr : 0 < r) :
    (moranSelectionCountKernel n r hr).jump = biasedWalk n r hr :=
  (moranSelectionCountKernel_sameJumpChain n hr).trans (birthDeathCountKernel_jump n hr)

/-- **The neutral case without self-loops**: with `r = 1`, the chain is the neutral chain on counts
without self-loops of `Moran.Counts`. -/
theorem birthDeathCountKernel_one (n : ℕ) :
    birthDeathCountKernel n 1 one_pos = pullCountKernel n := by
  funext k
  refine Distribution.ext_expect fun g => ?_
  rw [birthDeathCountKernel, birthDeathChain_expect, pullCountKernel, birthDeath_expect]
  ring

/-- **The neutral case of Moran's chain**: with `r = 1`, Moran's chain with selection is Moran's
neutral chain on counts. -/
theorem moranSelectionCountKernel_one (n : ℕ) :
    moranSelectionCountKernel n 1 one_pos = moranCountKernel n := by
  funext k
  refine Distribution.ext_expect fun g => ?_
  rw [moranSelectionCountKernel, birthDeathChain_expect, moranCountKernel, birthDeath_expect]
  ring

/-! ### Birth–death on the complete graph lumps to the chain without self-loops -/

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- The total fitness is `r` times the number of mutants plus the number of residents. -/
lemma totalFitness_eq (r : ℝ) (s : Config V) :
    totalFitness r s = r * mutants s + (Fintype.card V - mutants s) := by
  unfold totalFitness fitness
  rw [sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one, mul_comm]
  simp only [Bool.not_eq_true]
  rw [card_filter_false, Nat.cast_sub (mutants_le_card s)]
  rfl

/-- In one Birth–death step on the complete graph, the parent has type `b` and its offspring
replaces a vertex of type `c ≠ b` with probability `f · #b · #c / (F (n - 1))`, where `f` is the
fitness of type `b` and `F` the total fitness. -/
lemma pairDist_top_prob [Nonempty V] {r : ℝ} (hr : 0 < r) (s : Config V) {b c : Bool}
    (hbc : b ≠ c) :
    (pairDist (⊤ : SimpleGraph V) r hr s).prob (fun p => s p.1 = b ∧ s p.2 = c) =
      (if b then r else 1) * ((univ.filter fun u => s u = b).card *
        (univ.filter fun w => s w = c).card : ℝ) /
          (totalFitness r s * (Fintype.card V - 1)) := by
  classical
  have hp (p : V × V) : (pairDist (⊤ : SimpleGraph V) r hr s).weight p *
      (if s p.1 = b ∧ s p.2 = c then 1 else 0) =
        if s p.1 = b ∧ s p.2 = c then
          (if b then r else 1) / totalFitness r s * ((Fintype.card V : ℝ) - 1)⁻¹ else 0 := by
    by_cases hs : s p.1 = b ∧ s p.2 = c
    · have hne : p.1 ≠ p.2 := fun he => hbc (by rw [← hs.1, ← hs.2, he])
      rw [if_pos hs, if_pos hs, pairDist_weight, target_top_of_ne hne, mul_one, fitness, hs.1]
    · rw [if_neg hs, if_neg hs, mul_zero]
  rw [Distribution.prob_eq_expect]
  simp only [Distribution.expect]
  rw [sum_congr rfl fun p _ => hp p, ← sum_filter, sum_const, nsmul_eq_mul, ← univ_product_univ,
    filter_product (p := fun u => s u = b) (q := fun w => s w = c), card_product, Nat.cast_mul]
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- **Birth–death with selection on the complete graph is the chain on counts without
self-loops.** Under the Birth–death kernel on `K_n` (the parent is drawn with probability
proportional to its fitness, and its offspring replaces a uniformly random other vertex), the
number of mutants goes up by one with probability `rk(n-k)/((rk + n - k)(n - 1))` from `k` mutants,
down by one with probability `k(n-k)/((rk + n - k)(n - 1))`, and stays otherwise: it is
`birthDeathCountKernel n r`. -/
theorem moranKernel_top_lumps [Nonempty V] {r : ℝ} (hr : 0 < r) :
    Kernel.Lumps mutantCount (moranKernel (⊤ : SimpleGraph V) r hr)
      (birthDeathCountKernel (Fintype.card V) r hr) := by
  classical
  refine Kernel.lumps_iff_apply.2 fun g s => ?_
  have hdecomp (p : V × V) : g (mutantCount (Function.update s p.2 (s p.1))) =
      g (mutantCount s) +
        (g (countUp (mutantCount s)) - g (mutantCount s)) *
          (if s p.1 = true ∧ s p.2 = false then 1 else 0) +
        (g (countDown (mutantCount s)) - g (mutantCount s)) *
          (if s p.1 = false ∧ s p.2 = true then 1 else 0) := by
    rw [mutantCount_update]
    by_cases h1 : s p.1 = true ∧ s p.2 = false
    · have h2 : ¬ (s p.1 = false ∧ s p.2 = true) := by simp [h1.1]
      rw [if_pos ⟨h1.2, h1.1⟩, if_pos h1, if_neg h2]
      ring
    · have h1' : ¬ (s p.2 = false ∧ s p.1 = true) := fun h => h1 ⟨h.2, h.1⟩
      by_cases h2 : s p.1 = false ∧ s p.2 = true
      · rw [if_neg h1', if_pos ⟨h2.2, h2.1⟩, if_neg h1, if_pos h2]
        ring
      · have h2' : ¬ (s p.2 = true ∧ s p.1 = false) := fun h => h2 ⟨h.2, h.1⟩
        rw [if_neg h1', if_neg h2', if_neg h1, if_neg h2]
        ring
  have hup := pairDist_top_prob hr s (b := true) (c := false) (by decide)
  have hdown := pairDist_top_prob hr s (b := false) (c := true) Bool.false_ne_true
  rw [card_filter_false] at hup hdown
  simp only [Kernel.apply, moranKernel, Distribution.map_expect]
  rw [birthDeathCountKernel, birthDeathChain_expect]
  simp only [hdecomp]
  rw [Distribution.expect_add, Distribution.expect_add, Distribution.expect_const,
    Distribution.expect_mul, Distribution.expect_mul, ← Distribution.prob_eq_expect,
    ← Distribution.prob_eq_expect, hup, hdown, totalFitness_eq, mutantCount_val,
    Nat.cast_sub (mutants_le_card s)]
  have hfilter : (univ.filter fun u => s u = true).card = mutants s := rfl
  rw [hfilter]
  simp only [if_true, Bool.false_eq_true, if_false]
  ring

/-- **Neutral push on the complete graph is the chain on counts of death–Birth.** With `r = 1`,
the Birth–death kernel on `K_n` (the sequential push voter) lumps to the neutral chain on counts
without self-loops, as death–Birth does (`pullKernel_top_lumps`). -/
theorem moranKernel_top_one_lumps [Nonempty V] :
    Kernel.Lumps mutantCount (moranKernel (⊤ : SimpleGraph V) 1 one_pos)
      (pullCountKernel (Fintype.card V)) := by
  rw [← birthDeathCountKernel_one]
  exact moranKernel_top_lumps one_pos

/-! ### Fixation on counts -/

/-- Fixation of the chain without self-loops, from the count of a configuration. -/
lemma birthDeathCountKernel_fixation_count [Nonempty V] {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1)
    (s : Config V) :
    ⨆ t, (birthDeathCountKernel (Fintype.card V) r hr).event (· = Fin.last (Fintype.card V)) t
        (mutantCount s) =
      (1 - (1 / r) ^ (mutantCount s : ℕ)) / (1 - (1 / r) ^ Fintype.card V) := by
  have h := moran_formula (V := V) hr hr1 s
  unfold fixation at h
  simp only [funext allMutant_eq_ite] at h
  calc ⨆ t, (birthDeathCountKernel (Fintype.card V) r hr).event (· = Fin.last (Fintype.card V)) t
        (mutantCount s)
      = ⨆ t, (moranKernel (⊤ : SimpleGraph V) r hr).iterate t
          (fun x => if mutantCount x = Fin.last (Fintype.card V) then 1 else 0) s :=
        iSup_congr fun t => by
          rw [← (moranKernel_top_lumps (V := V) hr).event, Kernel.event_eq_iterate]
    _ = _ := by rw [h, mutantCount_val]

/-- **Moran's formula on counts, without self-loops.** For `r ≠ 1`, the chain without self-loops
in a population of `n ≥ 1` fixes the mutants from `k` copies with probability
`(1 - r^{-k})/(1 - r^{-n})`. Derived from Moran's formula on the complete graph (`moran_formula`)
through the lumping `moranKernel_top_lumps`. -/
theorem birthDeathCountKernel_fixation {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1)
    (k : Fin (n + 1)) :
    ⨆ t, (birthDeathCountKernel n r hr).event (· = Fin.last n) t k =
      (1 - (1 / r) ^ (k : ℕ)) / (1 - (1 / r) ^ n) := by
  have key (m : ℕ) (hm : Fintype.card (Fin n) = m) (y : Fin (m + 1)) (s : Config (Fin n))
      (hs : (mutantCount s : ℕ) = y) :
      ⨆ t, (birthDeathCountKernel m r hr).event (· = Fin.last m) t y =
        (1 - (1 / r) ^ (y : ℕ)) / (1 - (1 / r) ^ m) := by
    subst hm
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    obtain rfl : mutantCount s = y := Fin.ext hs
    exact birthDeathCountKernel_fixation_count hr hr1 s
  refine key n (Fintype.card_fin n) k (fun i => decide ((i : ℕ) < k)) ?_
  simp only [mutantCount, countFin_val, decide_eq_true_eq]
  rw [Fin.card_filter_val_lt]
  exact min_eq_right (Fin.is_le k)

/-- **Moran's formula for Moran's chain with selection on counts** (Moran 1959). For `r ≠ 1`, in
a population of `n ≥ 1`, Moran's chain fixes the mutants from `k` copies with probability
`(1 - r^{-k})/(1 - r^{-n})`. It has the same jump chain as the chain without self-loops
(`moranSelectionCountKernel_sameJumpChain`), hence the same absorption probabilities
(`Dynamics.Kernel.SameJumpChain.iSup_event_eq`). -/
theorem moranSelectionCountKernel_fixation {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r)
    (hr1 : r ≠ 1) (k : Fin (n + 1)) :
    ⨆ t, (moranSelectionCountKernel n r hr).event (· = Fin.last n) t k =
      (1 - (1 / r) ^ (k : ℕ)) / (1 - (1 / r) ^ n) := by
  have habs (K : Kernel (Fin (n + 1))) (hK : ∀ a, a = Fin.last n → (K a).prob (· = a) = 1) :
      ∀ a, a = Fin.last n → (K a).prob (· = Fin.last n) = 1 := fun a ha => by
    subst ha
    exact hK _ rfl
  have hlast : (n : ℝ) - ((Fin.last n : Fin (n + 1)) : ℕ) = 0 := by simp
  rw [(moranSelectionCountKernel_sameJumpChain n hr).iSup_event_eq
      (habs _ fun a ha => birthDeathChain_prob_self (by rw [ha, hlast]; simp)
        (by rw [ha, hlast]; simp))
      (habs _ fun a ha => birthDeathChain_prob_self (by rw [ha, hlast]; simp)
        (by rw [ha, hlast]; simp)),
    birthDeathCountKernel_fixation hn hr hr1 k]

/-! ### Neutral push and pull on regular graphs -/

/-- On a regular graph, a vertex places its offspring on a neighbour with the same probability as
that neighbour places its offspring on it. -/
lemma target_comm_of_regular (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : ∀ v, G.degree v = d) (u w : V) : target G u w = target G w u := by
  unfold target
  rw [hreg u, hreg w]
  by_cases hd : d = 0
  · simp only [if_pos hd]
    by_cases h : w = u
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  · simp only [if_neg hd]
    by_cases h : G.Adj u w
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg fun h' => h h'.symm]

/-- **Neutral push and pull are the same chain on every regular graph.** On a regular graph, the
neutral Birth–death kernel (a uniformly random vertex places a copy of its type on a uniformly
random neighbour: the sequential push voter) and the death–Birth kernel (a uniformly random vertex
adopts the type of a uniformly random neighbour: the sequential pull voter) are the same kernel on
configurations. -/
theorem moranKernel_one_eq_pullKernel [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hreg : ∀ v, G.degree v = d) : moranKernel G 1 one_pos = pullKernel G := by
  funext s
  refine Distribution.ext_expect fun g => ?_
  rw [moranKernel, pullKernel, Distribution.map_expect, Distribution.map_expect]
  simp only [Distribution.expect]
  rw [← Equiv.sum_comp (Equiv.prodComm V V)]
  refine sum_congr rfl fun p _ => ?_
  rw [pair_weight_neutral]
  simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
  rw [target_comm_of_regular G hreg]
  rfl

end Moran
