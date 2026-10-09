import Median.TwoChoicesExpect
import Median.Binary
import Median.AnyStartScalar

/-! # The k-party 2-Choices dynamics: plurality consensus from a gap of order `√(n log n)`

Elsässer, Friedetzky, Kaaser, Mallmann-Trenn and Trinker, *Efficient k-party voting with two
choices* (arXiv:1602.04667; v5, *Rapid asynchronous plurality consensus*), Theorem 1 (upper
bound, without the adversary): on `K_n`, if the largest colour `A` (count `a = c₁`) leads every
other colour by at least `z √(n log n)`, 2-Choices reaches consensus on `A` within
`O((n/c₁) log n) ⊆ O(k log n)` rounds w.h.p.

The proof of the paper, as split here:
* **Lemma 1** (`distance_increases`): for `a ≤ n/2`, the gap to the second largest colour grows
  by a factor `1 + a/(4n)` in one round w.h.p.; the expectation part is `expected_gap_ge`
  (with the aggregation `sum_sq_le_aggregate`).
* **Lemma 2** (`count_stochDom`): a colour that is not larger than another one is stochastically
  dominated by it after one round (the paper states it as a coupling).
* **Growth phase** (proof of Theorem 1): one round (`growth_round`) and the whole phase
  (`growth_phase`): within `O((n/a) log n)` rounds the plurality colour holds three quarters of
  the nodes w.h.p.
* **Finishing phase** (proof of Theorem 1, where the paper cites Cooper et al. for two colours):
  from three quarters, the indicator of the colour dominates the binary median process
  (`run_dominates`), which reaches consensus by `Median.binary_consensus` (`finish_phase`).

With two colours the dynamics is the median dynamics, so `Median.consensus_whp` transfers
(`two_colours_consensus_whp`).
-/

namespace Median.TwoChoices
open Finset Dynamics Filter Topology

variable {n : ℕ} {α : Type*} [DecidableEq α]

/-! ### Consensus is absorbing -/

/-- More rounds never hurt: the probability of being in consensus on `i` is monotone in the
number of rounds. -/
theorem expList_consensus_mono [NeZero n] (x : Config n α) (i : α) {T₁ T₂ : ℕ} (h : T₁ ≤ T₂) :
    expList (Round n) T₁ (fun l => if run x l = (fun _ => i) then (1 : ℝ) else 0)
      ≤ expList (Round n) T₂ (fun l => if run x l = (fun _ => i) then (1 : ℝ) else 0) := by
  have hne : Nonempty (Round n) := ⟨fun _ => ((0 : Fin n), (0 : Fin n))⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [expList_append]
  refine expList_le_expList fun l₁ => ?_
  by_cases h1 : run x l₁ = fun _ => i
  · rw [if_pos h1]
    have h2 : ∀ l₂ : List (Round n),
        (if run x (l₁ ++ l₂) = (fun _ => i) then (1 : ℝ) else 0) = 1 := by
      intro l₂
      rw [run_append, h1, run_of_consensus _ ⟨i, fun _ => rfl⟩, if_pos rfl]
    simp_rw [h2]
    rw [expList_const]
  · rw [if_neg h1]
    exact expList_nonneg fun l₂ => by split_ifs <;> norm_num

/-- **Almost agreement** (proof of Theorem 1, last paragraph): from every configuration, the
probability of not being in consensus after `t` rounds tends to zero. -/
theorem absorbed [NeZero n] [Fintype α] [Nonempty α] (x : Config n α) :
    Tendsto (fun t => (kernel n α).iterate t notConsensus x) atTop (𝓝 0) := by
  have hstep : ∀ y : Config n α, (kernel n α).apply notConsensus y ≤ notConsensus y := by
    intro y
    unfold kernel
    rw [Dynamics.Kernel.apply_ofStep]
    by_cases h : Consensus y
    · have hfun : (fun r : Round n => notConsensus (step y r))
          = fun _ : Round n => notConsensus y := by
        funext r
        rw [step_of_consensus y h r]
      rw [hfun, avg_const]
    · rw [notConsensus_noncons h]
      have hle : avg (fun r : Round n => notConsensus (step y r))
          ≤ avg (fun _ : Round n => (1 : ℝ)) :=
        avg_le_avg fun r => by
          rcases notConsensus_cases (step y r) with h' | h' <;> simp [h']
      rw [avg_const] at hle
      exact hle
  have hacc : ∀ y : Config n α, ∃ t, (kernel n α).iterate t notConsensus y < 1 := by
    intro y
    refine ⟨1, ?_⟩
    show (kernel n α).apply notConsensus y < 1
    unfold kernel
    rw [Dynamics.Kernel.apply_ofStep]
    have hzero : notConsensus (step y (fun _ : Fin n => ((0 : Fin n), (0 : Fin n)))) = 0 := by
      have hfix : step y (fun _ : Fin n => ((0 : Fin n), (0 : Fin n))) = fun _ => y 0 := by
        funext v
        exact step_of_eq y _ v rfl
      rw [hfix]
      exact notConsensus_cons ⟨y 0, fun _ => rfl⟩
    refine Dynamics.avg_lt_one (b := fun _ : Fin n => ((0 : Fin n), (0 : Fin n)))
      (fun r => ?_) (by simp only [hzero, zero_lt_one])
    rcases notConsensus_cases (step y r) with h | h <;> simp [h]
  exact Dynamics.Kernel.finite_absorption (kernel n α) notConsensus
    (fun y => notConsensus_cases y) hstep hacc x

/-! ### Two colours -/

/-- **Two colours** (Elsässer et al., Section 2.1, citing Cooper et al. for `k = 2`): the binary
result `Median.consensus_whp` transferred through `run_bool`: from a gap of `C √(n log n)`
between `true` and `false`, all nodes hold `true` after `⌈C log n⌉` rounds w.p. `≥ 1 − C/n`. -/
theorem two_colours_consensus_whp : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) [NeZero n], C ≤ Real.log n →
    ∀ x : Config n Bool, C * √(n * Real.log n) ≤ (count x true : ℝ) - count x false →
      1 - C / n ≤ expList (Round n) ⌈C * Real.log n⌉₊
        (fun l => if run x l = (fun _ => true) then (1 : ℝ) else 0) := by
  obtain ⟨C, hC, h⟩ := consensus_whp
  refine ⟨C, hC, fun n _ hL x hx => ?_⟩
  have hsum : (count x true : ℝ) + count x false = n := by
    exact_mod_cast count_true_add_count_false x
  have hx' : C * √(n * Real.log n) ≤ (ones x : ℝ) - (n - ones x) := by
    rw [← count_true]
    linarith
  simp_rw [run_bool]
  exact h n hL x hx'

/-! ### The finishing phase -/

/-- `65536 log n ≤ n` once `log n ≥ 128`. -/
lemma log_le_div_of_log_ge {n : ℕ} (hL : (128 : ℝ) ≤ Real.log n) :
    65536 * Real.log n ≤ (n : ℝ) := by
  have hn : (0 : ℝ) < n := by
    by_contra h
    have h0 : (n : ℝ) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg n)
    rw [h0, Real.log_zero] at hL
    norm_num at hL
  have h4 := log_pow_four_div_le hn (by linarith)
  have hc : (65536 : ℝ) * Real.log n ≤ Real.log n ^ 4 / 24 := by
    have h3 : (128 : ℝ) ^ 3 ≤ Real.log n ^ 3 := pow_le_pow_left₀ (by norm_num) hL 3
    nlinarith
  linarith

/-- **Finishing phase**: if colour `i` holds at least three quarters of the nodes and
`log n ≥ 128`, all nodes hold `i` after `⌈128 log n⌉` rounds w.p. `≥ 1 − 128/n`. The indicator of
`i` dominates the binary median process (`run_dominates`), whose gap is `≥ n/2 ≥ 128 √(n log n)`,
and `Median.binary_consensus` applies. -/
theorem finish_phase [NeZero n] (hL : (128 : ℝ) ≤ Real.log n) (x : Config n α) (i : α)
    (hx : 3 * (n : ℝ) / 4 ≤ count x i) :
    1 - 128 / (n : ℝ) ≤ expList (Round n) ⌈128 * Real.log n⌉₊
      (fun l => if run x l = (fun _ => i) then (1 : ℝ) else 0) := by
  set y : Config n Bool := fun u => decide (x u = i) with hy
  have hones : (ones y : ℝ) = count x i := by
    unfold ones count
    simp [hy]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlog := log_le_div_of_log_ge hL
  have hgap : 128 * √((n : ℝ) * Real.log n) ≤ gapR y := by
    unfold gapR falsesR
    rw [hones]
    have hs : √((n : ℝ) * Real.log n) ≤ n / 256 := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith
    linarith
  refine (binary_consensus hL y hgap).trans (expList_le_expList fun l => ?_)
  by_cases h1 : Median.run y l = fun _ => true
  · have h2 : run x l = fun _ => i := by
      funext v
      exact run_dominates x i l v (by rw [h1])
    rw [if_pos h1, if_pos h2]
  · rw [if_neg h1]
    split_ifs <;> norm_num

/-! ### Lemmas 1 and 2 -/

/-- **Lemma 1** (the distance increases): let `i` be the largest colour (`a = c_i ≤ n/2`) and `j`
the second largest (`b = c_j`). There are constants `z` and `C` such that, if `log n ≥ C` and
`a − b ≥ z √(n log n)`, then after one round `a' − b' > (a − b)(1 + a/(4n))` with probability
at least `1 − C/n²`. -/
theorem distance_increases : ∃ z C : ℝ, 0 < z ∧ 0 < C ∧ ∀ (n : ℕ) [NeZero n],
    C ≤ Real.log n → ∀ (k : ℕ) (x : Config n (Fin k)) (i j : Fin k), j ≠ i →
      (∀ l ≠ i, count x l ≤ count x j) → (count x i : ℝ) ≤ n / 2 →
      z * √(n * Real.log n) ≤ (count x i : ℝ) - count x j →
      1 - C / (n : ℝ) ^ 2 ≤ avg (fun r : Round n =>
        if ((count x i : ℝ) - count x j) * (1 + count x i / (4 * n))
            < (count (step x r) i : ℝ) - count (step x r) j then (1 : ℝ) else 0) := by
  sorry

/-- **Lemma 2** (the coupling), as the stochastic domination it provides: if colour `c` has at
most as many nodes as colour `b`, then after one round `c'` is stochastically dominated by
`b'`: `P(c' ≥ t) ≤ P(b' ≥ t)` for every `t`. -/
theorem count_stochDom (x : Config n α) {b c : α} (h : count x c ≤ count x b) (t : ℕ) :
    avg (fun r : Round n => if t ≤ count (step x r) c then (1 : ℝ) else 0)
      ≤ avg (fun r : Round n => if t ≤ count (step x r) b then (1 : ℝ) else 0) := by
  sorry

/-! ### The growth phase -/

/-- **One round of the growth phase** (proof of Theorem 1: Lemma 1 for every other colour, by
Lemma 2 and a union bound, here up to `a ≤ 3n/4` with the factor `1 + a/(8n)`): if colour `i`
(count `a ≤ 3n/4`) leads every other colour by at least `g ≥ z √(n log n)`, then with
probability at least `1 − C/n²` after one round `a' ≥ a` and `i` leads every other colour by at
least `g (1 + a/(8n))`. -/
theorem growth_round : ∃ z C : ℝ, 0 < z ∧ 0 < C ∧ ∀ (n : ℕ) [NeZero n], C ≤ Real.log n →
    ∀ (k : ℕ) (x : Config n (Fin k)) (i : Fin k) (g : ℝ), z * √(n * Real.log n) ≤ g →
      (∀ j ≠ i, (count x j : ℝ) + g ≤ count x i) → (count x i : ℝ) ≤ 3 * n / 4 →
      1 - C / (n : ℝ) ^ 2 ≤ avg (fun r : Round n =>
        if (count x i : ℝ) ≤ count (step x r) i ∧
            ∀ j ≠ i, (count (step x r) j : ℝ) + g * (1 + count x i / (8 * n))
              ≤ count (step x r) i
        then (1 : ℝ) else 0) := by
  sorry

/-- **The growth phase** (proof of Theorem 1): if colour `i` leads every other colour by at
least `z √(n log n)`, then after `⌈C (n/c_i) log n⌉` rounds it holds at least three quarters of
the nodes, with probability at least `1 − C/n`. -/
theorem growth_phase : ∃ z C : ℝ, 0 < z ∧ 0 < C ∧ ∀ (n : ℕ) [NeZero n], C ≤ Real.log n →
    ∀ (k : ℕ) (x : Config n (Fin k)) (i : Fin k),
      (∀ j ≠ i, (count x j : ℝ) + z * √(n * Real.log n) ≤ count x i) →
      1 - C / n ≤ expList (Round n) ⌈C * (n / count x i) * Real.log n⌉₊
        (fun l => if 3 * (n : ℝ) / 4 ≤ count (run x l) i then (1 : ℝ) else 0) := by
  sorry

/-! ### Theorem 1 -/

/-- The plurality colour holds at least `n/k` nodes. -/
lemma div_le_count_of_max {k : ℕ} (x : Config n (Fin k)) (i : Fin k)
    (h : ∀ j, count x j ≤ count x i) : (n : ℝ) ≤ k * count x i := by
  have hs : ∑ j : Fin k, (count x j : ℝ) = n := by exact_mod_cast sum_count x
  rw [← hs]
  calc ∑ j : Fin k, (count x j : ℝ) ≤ ∑ _j : Fin k, (count x i : ℝ) :=
        sum_le_sum fun j _ => by exact_mod_cast h j
    _ = k * count x i := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Theorem 1** (upper bound, without the adversary): there are constants `z` and `C` such
that, if `log n ≥ C` and colour `i` leads every other colour by at least `z √(n log n)`
(`c₁ − c₂ ≥ z √(n log n)`), then all nodes hold `i` after `⌈C (n/c₁) log n⌉` rounds with
probability at least `1 − C/n`. No bound on the number `k` of colours is needed (the paper
assumes `k = O(n^ε)`). -/
theorem plurality_whp : ∃ z C : ℝ, 0 < z ∧ 0 < C ∧ ∀ (n : ℕ) [NeZero n], C ≤ Real.log n →
    ∀ (k : ℕ) (x : Config n (Fin k)) (i : Fin k),
      (∀ j ≠ i, (count x j : ℝ) + z * √(n * Real.log n) ≤ count x i) →
      1 - C / n ≤ expList (Round n) ⌈C * (n / count x i) * Real.log n⌉₊
        (fun l => if run x l = (fun _ => i) then (1 : ℝ) else 0) := by
  -- growth phase (`growth_phase`), then the finishing phase (`finish_phase`) from the
  -- configuration reached, and padding by monotonicity (`expList_consensus_mono`)
  obtain ⟨z, C₁, hz, hC₁, hg⟩ := growth_phase
  refine ⟨z, C₁ + 256, hz, by positivity, fun n _ hL k x i hx => ?_⟩
  have hL1 : C₁ ≤ Real.log n := by linarith
  have hL2 : (128 : ℝ) ≤ Real.log n := by linarith
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hn128 : (128 : ℝ) ≤ n := hL2.trans ((Real.log_le_sub_one_of_pos hn).trans (by linarith))
  have hmax : ∀ j, count x j ≤ count x i := by
    intro j
    by_cases hj : j = i
    · rw [hj]
    · have h1 := hx j hj
      have h2 : 0 ≤ z * √(n * Real.log n) := by positivity
      have : (count x j : ℝ) ≤ count x i := by linarith
      exact_mod_cast this
  have hk := div_le_count_of_max x i hmax
  have hci : (0 : ℝ) < count x i := by
    by_contra h0
    have : (count x i : ℝ) = 0 := le_antisymm (not_lt.mp h0) (Nat.cast_nonneg _)
    rw [this, mul_zero] at hk
    linarith
  have han : (count x i : ℝ) ≤ n := by exact_mod_cast count_le x i
  have hX1 : (1 : ℝ) ≤ n / count x i := by rw [le_div_iff₀ hci]; linarith
  have hX : Real.log n ≤ n / count x i * Real.log n := by nlinarith
  have hT : ⌈C₁ * (n / count x i) * Real.log n⌉₊ + ⌈128 * Real.log n⌉₊
      ≤ ⌈(C₁ + 256) * (n / count x i) * Real.log n⌉₊ := by
    refine ceil_add_ceil_le (by positivity) (by positivity) ?_
    have e : (C₁ + 256) * (n / count x i) * Real.log n
        = C₁ * (n / count x i) * Real.log n + 256 * (n / count x i * Real.log n) := by ring
    rw [e]
    linarith
  set T₁ := ⌈C₁ * (n / count x i) * Real.log n⌉₊ with hT₁
  set T₂ := ⌈128 * Real.log n⌉₊ with hT₂
  have h128 : 0 ≤ 1 - 128 / (n : ℝ) := by rw [sub_nonneg, div_le_one hn]; exact hn128
  have hgx := hg n hL1 k x i hx
  refine le_trans ?_ (expList_consensus_mono x i hT)
  rw [expList_append]
  calc 1 - (C₁ + 256) / (n : ℝ)
      ≤ (1 - 128 / (n : ℝ)) * (1 - C₁ / n) := by
        have : 0 ≤ 128 * C₁ / (n : ℝ) ^ 2 := by positivity
        have e : (1 - 128 / (n : ℝ)) * (1 - C₁ / n) = 1 - (C₁ + 128) / n + 128 * C₁ / n ^ 2 := by
          field_simp
          ring
        rw [e]
        have : (C₁ + 128) / (n : ℝ) ≤ (C₁ + 256) / n :=
          div_le_div_of_nonneg_right (by linarith) hn.le
        linarith
    _ ≤ (1 - 128 / (n : ℝ)) * expList (Round n) T₁
          (fun l => if 3 * (n : ℝ) / 4 ≤ count (run x l) i then (1 : ℝ) else 0) :=
        mul_le_mul_of_nonneg_left hgx h128
    _ = expList (Round n) T₁ (fun l => (1 - 128 / (n : ℝ)) *
          (if 3 * (n : ℝ) / 4 ≤ count (run x l) i then (1 : ℝ) else 0)) :=
        (expList_const_mul _ _ _).symm
    _ ≤ expList (Round n) T₁ (fun l₁ => expList (Round n) T₂ (fun l₂ =>
          if run x (l₁ ++ l₂) = (fun _ => i) then (1 : ℝ) else 0)) := by
        refine expList_le_expList fun l₁ => ?_
        by_cases hgood : 3 * (n : ℝ) / 4 ≤ count (run x l₁) i
        · rw [if_pos hgood, mul_one]
          simp_rw [run_append]
          exact finish_phase hL2 (run x l₁) i hgood
        · rw [if_neg hgood, mul_zero]
          exact expList_nonneg fun l₂ => by split_ifs <;> norm_num

/-- **Theorem 1 in the form `O(k log n)`** (roadmap MAJ-4): the same conclusion after
`⌈C k log n⌉` rounds, since `c₁ ≥ n/k`. -/
theorem plurality_whp_k : ∃ z C : ℝ, 0 < z ∧ 0 < C ∧ ∀ (n : ℕ) [NeZero n], C ≤ Real.log n →
    ∀ (k : ℕ) (x : Config n (Fin k)) (i : Fin k),
      (∀ j ≠ i, (count x j : ℝ) + z * √(n * Real.log n) ≤ count x i) →
      1 - C / n ≤ expList (Round n) ⌈C * k * Real.log n⌉₊
        (fun l => if run x l = (fun _ => i) then (1 : ℝ) else 0) := by
  obtain ⟨z, C, hz, hC, h⟩ := plurality_whp
  refine ⟨z, C, hz, hC, fun n _ hL k x i hx => ?_⟩
  refine (h n hL k x i hx).trans (expList_consensus_mono x i (Nat.ceil_mono ?_))
  have hL0 : 0 ≤ Real.log n := hC.le.trans hL
  have hmax : ∀ j, count x j ≤ count x i := by
    intro j
    by_cases hj : j = i
    · rw [hj]
    · have := hx j hj
      have : (count x j : ℝ) ≤ count x i := by
        have : 0 ≤ z * √(n * Real.log n) := by positivity
        linarith
      exact_mod_cast this
  have hk := div_le_count_of_max x i hmax
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hci : (0 : ℝ) < count x i := by
    by_contra h0
    have : (count x i : ℝ) = 0 := le_antisymm (not_lt.mp h0) (Nat.cast_nonneg _)
    rw [this, mul_zero] at hk
    linarith
  have hdiv : (n : ℝ) / count x i ≤ k := by
    rw [div_le_iff₀ hci]
    linarith
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdiv hC.le) hL0
  linarith

end Median.TwoChoices
