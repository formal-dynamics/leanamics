import Median.TwoChoicesExpect
import Median.TwoChoicesConc
import Median.Binary
import Median.AnyStartScalar
import Dynamics.Tail
import Median.AnyStartDrift

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
  refine ⟨128, 2, by norm_num, by norm_num, ?_⟩
  intro n _ hC k x i j hij hsecond ha_le hgap
  have hL : (0 : ℝ) < Real.log n := by linarith
  have hn1 : 1 ≤ n := one_le_of_log_pos hL
  have hn : (0 : ℝ) < n := by exact_mod_cast hn1
  haveI : Nonempty (Round n) := ⟨fun _ => ((0 : Fin n), (0 : Fin n))⟩
  let a : ℝ := (count x i : ℝ)
  let b : ℝ := (count x j : ℝ)
  let g : ℝ := a - b
  have hsqrt : 0 < √((n : ℝ) * Real.log n) :=
    Real.sqrt_pos.mpr (mul_pos hn hL)
  have hg0 : 0 < g := by
    have hpos : (0 : ℝ) < 128 * √((n : ℝ) * Real.log n) := mul_pos (by norm_num) hsqrt
    exact lt_of_lt_of_le hpos hgap
  have ha0 : 0 < a := by
    have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg _
    linarith
  have hga : g ≤ a := by
    have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg _
    linarith
  have hji : count x j ≤ count x i := by
    rw [← Nat.cast_le (α := ℝ)]
    exact le_of_lt (by linarith : b < a)
  have hbound : ∀ l, count x l ≤ count x i := by
    intro l
    by_cases hl : l = i
    · rw [hl]
    · exact (hsecond l hl).trans hji
  have ha_pos : 0 < count x i := by
    rw [← Nat.cast_pos (α := ℝ)]
    exact ha0
  have hsq : (128 : ℝ) ^ 2 * (n : ℝ) * Real.log n ≤ g ^ 2 := by
    have hbase : 0 ≤ 128 * √((n : ℝ) * Real.log n) := by positivity
    have hpow := pow_le_pow_left₀ hbase hgap 2
    have hmul : 0 ≤ (n : ℝ) * Real.log n := mul_nonneg hn.le hL.le
    rw [mul_pow, Real.sq_sqrt hmul] at hpow
    have heq : (128 : ℝ) ^ 2 * n * Real.log n = 128 ^ 2 * ((n : ℝ) * Real.log n) := by ring
    linarith [heq]
  let lam : ℝ := g * a / (8 * n)
  let E : ℝ := avg (fun ρ : Round n => (count (step x ρ) i : ℝ) - count (step x ρ) j)
  have hE : g * (1 + (a / n) * (1 - a / n)) ≤ E := expected_gap_ge x hji hsecond
  have hmargin := distance_margin hn ha0 hg0 ha_le
  have hthr : g * (1 + a / (4 * n)) < E - lam := by
    have hlow : g * (1 + (a / n) * (1 - a / n)) - lam ≤ E - lam := by linarith [hE]
    exact lt_of_lt_of_le hmargin hlow
  have htail := gap_tail_twelve x i j hij hbound ha_pos hg0.le hga hL.le hn1 hsq
  let bad : Round n → ℝ := fun r =>
    if (count (step x r) i : ℝ) - count (step x r) j ≤ E - lam then 1 else 0
  let good : Round n → ℝ := fun r =>
    if g * (1 + a / (4 * n)) < (count (step x r) i : ℝ) - count (step x r) j then 1 else 0
  have hpt (r : Round n) : (1 : ℝ) - bad r ≤ good r := by
    by_cases hbad : (count (step x r) i : ℝ) - count (step x r) j ≤ E - lam
    · simp only [bad, good, if_pos hbad, sub_self]
      split_ifs <;> norm_num
    · have hgt : E - lam < (count (step x r) i : ℝ) - count (step x r) j := lt_of_not_ge hbad
      have hgood : g * (1 + a / (4 * n)) < (count (step x r) i : ℝ) - count (step x r) j :=
        hthr.trans hgt
      simp only [bad, good, if_neg hbad, if_pos hgood, sub_zero]
      exact le_rfl
  have havg : avg (fun r => (1 : ℝ) - bad r) = 1 - avg bad := by rw [avg_sub, avg_const]
  have hbad_le : avg bad ≤ 1 / (n : ℝ) ^ 2 := by
    have h12 : avg bad ≤ 1 / (n : ℝ) ^ 12 := htail
    exact h12.trans (one_div_pow_twelve_le hn1)
  have hgood : 1 - 2 / (n : ℝ) ^ 2 ≤ avg good := by
    have hone : 1 - avg bad ≤ avg good := by
      rw [← havg]
      exact avg_le_avg hpt
    have htwo : 1 / (n : ℝ) ^ 2 ≤ 2 / (n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) (by positivity)
    linarith [hone, hbad_le, htwo]
  exact hgood

/-! ### Lemma 2: one round of stochastic domination

The sample pairs that make a node adopt a colour, and a measure-preserving reindexing of rounds.
Cardinalities are computed from pairs of nodes, so the argument does not need `[Fintype α]`. -/

/-- Sample pairs on which the two nodes agree. -/
def pairAgree (x : Config n α) : Finset (Fin n × Fin n) :=
  univ.filter fun p => x p.1 = x p.2

/-- Sample pairs on which both nodes hold colour `col`. -/
def pairBoth (x : Config n α) (col : α) : Finset (Fin n × Fin n) :=
  univ.filter fun p => x p.1 = col ∧ x p.2 = col

/-- Sample pairs that agree on a colour other than `col`. -/
def pairAgreeOff (x : Config n α) (col : α) : Finset (Fin n × Fin n) :=
  univ.filter fun p => x p.1 = x p.2 ∧ x p.1 ≠ col

/-- Sample pairs that make a node of colour `own` adopt `col`. -/
def adoptPairs (x : Config n α) (own col : α) : Finset (Fin n × Fin n) :=
  univ.filter fun p => rule own (x p.1) (x p.2) = col

lemma pairBoth_card (x : Config n α) (col : α) :
    (pairBoth x col).card = count x col * count x col := by
  let s : Finset (Fin n) := univ.filter fun v => x v = col
  have hs : pairBoth x col = s ×ˢ s := by
    ext p
    constructor
    · intro hp
      simp only [pairBoth, mem_filter, mem_univ, true_and] at hp
      refine mem_product.mpr ⟨?_, ?_⟩
      · simp only [s, mem_filter, mem_univ, true_and]
        exact hp.1
      · simp only [s, mem_filter, mem_univ, true_and]
        exact hp.2
    · intro hp
      obtain ⟨hp1, hp2⟩ := mem_product.mp hp
      simp only [s, mem_filter, mem_univ, true_and] at hp1 hp2
      simp only [pairBoth, mem_filter, mem_univ, true_and]
      exact ⟨hp1, hp2⟩
  rw [hs, card_product]
  rfl

lemma pairBoth_subset_pairAgree (x : Config n α) (col : α) :
    pairBoth x col ⊆ pairAgree x := by
  intro p hp
  simp only [pairBoth, pairAgree, mem_filter, mem_univ, true_and] at hp ⊢
  exact hp.1.trans hp.2.symm

lemma pairAgreeOff_eq (x : Config n α) (col : α) :
    pairAgreeOff x col = pairAgree x \ pairBoth x col := by
  ext p
  constructor
  · intro hp
    simp only [pairAgreeOff, mem_filter, mem_univ, true_and] at hp
    refine mem_sdiff.mpr ⟨?_, ?_⟩
    · simp only [pairAgree, mem_filter, mem_univ, true_and]
      exact hp.1
    · intro hboth
      simp only [pairBoth, mem_filter, mem_univ, true_and] at hboth
      exact hp.2 hboth.1
  · intro hp
    obtain ⟨hagree, hnot⟩ := mem_sdiff.mp hp
    simp only [pairAgree, mem_filter, mem_univ, true_and] at hagree
    simp only [pairAgreeOff, mem_filter, mem_univ, true_and]
    refine ⟨hagree, ?_⟩
    intro hc
    apply hnot
    simp only [pairBoth, mem_filter, mem_univ, true_and]
    exact ⟨hc, hagree ▸ hc⟩

lemma pairAgreeOff_card (x : Config n α) (col : α) :
    (pairAgreeOff x col).card = (pairAgree x).card - (pairBoth x col).card := by
  rw [pairAgreeOff_eq, card_sdiff_of_subset (pairBoth_subset_pairAgree x col)]

lemma pairUniv_card : (univ : Finset (Fin n × Fin n)).card = n * n := by
  simp [card_univ, Fintype.card_prod, Fintype.card_fin]

/-- A node of colour `col` adopts `col` unless its two samples agree on a different colour. -/
lemma adoptPairs_self_eq (x : Config n α) (col : α) :
    adoptPairs x col col = univ \ pairAgreeOff x col := by
  ext p
  constructor
  · intro hp
    simp only [adoptPairs, mem_filter, mem_univ, true_and] at hp
    refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
    intro hoff
    simp only [pairAgreeOff, mem_filter, mem_univ, true_and] at hoff
    unfold rule at hp
    rw [if_pos hoff.1] at hp
    exact hoff.2 hp
  · intro hp
    obtain ⟨_, hnot⟩ := mem_sdiff.mp hp
    simp only [adoptPairs, mem_filter, mem_univ, true_and]
    unfold rule
    by_cases hab : x p.1 = x p.2
    · rw [if_pos hab]
      by_contra hne
      apply hnot
      simp only [pairAgreeOff, mem_filter, mem_univ, true_and]
      exact ⟨hab, hne⟩
    · rw [if_neg hab]

lemma adoptPairs_self_card (x : Config n α) (col : α) :
    (adoptPairs x col col).card = n * n - (pairAgreeOff x col).card := by
  rw [adoptPairs_self_eq, card_sdiff_of_subset (subset_univ _), pairUniv_card]

/-- A node of a different colour adopts `col` only when both samples hold `col`. -/
lemma adoptPairs_ne (x : Config n α) {own col : α} (h : own ≠ col) :
    adoptPairs x own col = pairBoth x col := by
  ext p
  simp only [adoptPairs, pairBoth, mem_filter, mem_univ, true_and]
  unfold rule
  by_cases hab : x p.1 = x p.2
  · rw [if_pos hab]
    constructor
    · intro hc
      exact ⟨hc, hab ▸ hc⟩
    · intro hboth
      exact hboth.1
  · rw [if_neg hab]
    constructor
    · intro hc
      exact (h hc).elim
    · intro ⟨h1, h2⟩
      exact (hab (h1.trans h2.symm)).elim

/-- If `c` is at most as large as `b` and a node of colour `c` is sent to a node of colour `b`,
the node has at most as many adopting sample pairs for `c` as its image has for `b`. -/
lemma adoptPairs_card_le (x : Config n α) {b c own₁ own₂ : α}
    (hbc : count x c ≤ count x b) (hown : own₁ = c → own₂ = b) :
    (adoptPairs x own₁ c).card ≤ (adoptPairs x own₂ b).card := by
  have hsq : count x c * count x c ≤ count x b * count x b := Nat.mul_le_mul hbc hbc
  have hDle : (pairAgree x).card ≤ n * n := by
    rw [← pairUniv_card]
    exact card_le_card (subset_univ _)
  by_cases h1 : own₁ = c
  · have h2 : own₂ = b := hown h1
    rw [h1, h2, adoptPairs_self_card, adoptPairs_self_card, pairAgreeOff_card, pairAgreeOff_card,
      pairBoth_card, pairBoth_card]
    exact Nat.sub_le_sub_left (Nat.sub_le_sub_left hsq _) _
  · rw [adoptPairs_ne x h1, pairBoth_card]
    by_cases h2 : own₂ = b
    · rw [h2, adoptPairs_self_card, pairAgreeOff_card, pairBoth_card]
      have hDb : count x b * count x b ≤ (pairAgree x).card := by
        rw [← pairBoth_card]
        exact card_le_card (pairBoth_subset_pairAgree x b)
      have hsum : count x b * count x b + ((pairAgree x).card - count x b * count x b)
          = (pairAgree x).card := by
        rw [add_comm]
        exact Nat.sub_add_cancel hDb
      have hleN : count x b * count x b + ((pairAgree x).card - count x b * count x b)
          ≤ n * n := by
        rw [hsum]
        exact hDle
      exact hsq.trans (Nat.le_sub_of_add_le hleN)
    · rw [adoptPairs_ne x h2, pairBoth_card]
      exact hsq

lemma count_step_adopt (x : Config n α) (r : Round n) (col : α) :
    count (step x r) col =
      (univ.filter fun v => r v ∈ adoptPairs x (x v) col).card := by
  simp only [count, step, adoptPairs]
  congr 1
  ext v
  simp only [mem_filter, mem_univ, true_and]

/-- **Lemma 2** (the coupling), as the stochastic domination it provides: if colour `c` has at
most as many nodes as colour `b`, then after one round `c'` is stochastically dominated by
`b'`: `P(c' ≥ t) ≤ P(b' ≥ t)` for every `t`. -/
theorem count_stochDom (x : Config n α) {b c : α} (h : count x c ≤ count x b) (t : ℕ) :
    avg (fun r : Round n => if t ≤ count (step x r) c then (1 : ℝ) else 0)
      ≤ avg (fun r : Round n => if t ≤ count (step x r) b then (1 : ℝ) else 0) := by
  classical
  -- A permutation of nodes sending every node of colour `c` to a node of colour `b`.
  let Vc : Finset (Fin n) := univ.filter fun v => x v = c
  let Vb : Finset (Fin n) := univ.filter fun v => x v = b
  have hVc : Vc.card = count x c := rfl
  have hVb : Vb.card = count x b := rfl
  have hcards : Vc.card ≤ Vb.card := by
    rw [hVc, hVb]
    exact h
  obtain ⟨tB, htB, htc⟩ := Finset.exists_subset_card_eq hcards
  obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_map_finset_eq Vc tB htc.symm
  have hτcol : ∀ v, x v = c → x (τ v) = b := by
    intro v hv
    have hvmem : v ∈ Vc := by
      simp only [Vc, mem_filter, mem_univ, true_and]
      exact hv
    have hmap : τ.toEmbedding v ∈ Vc.map τ.toEmbedding := mem_map_of_mem _ hvmem
    rw [hτ] at hmap
    have hVbmem : τ v ∈ Vb := htB hmap
    simp only [Vb, mem_filter, mem_univ, true_and] at hVbmem
    exact hVbmem
  -- For each node, a permutation of sample pairs embedding its adopting set into the image's.
  have hπex : ∀ v, ∃ π : Equiv.Perm (Fin n × Fin n),
      ∀ p, p ∈ adoptPairs x (x v) c → π p ∈ adoptPairs x (x (τ v)) b := by
    intro v
    have hle := adoptPairs_card_le x h (hτcol v)
    obtain ⟨s, hs, hsc⟩ := Finset.exists_subset_card_eq hle
    obtain ⟨π, hπ⟩ := Equiv.Perm.exists_map_finset_eq (adoptPairs x (x v) c) s hsc.symm
    refine ⟨π, fun p hp => ?_⟩
    have hmap : π.toEmbedding p ∈ (adoptPairs x (x v) c).map π.toEmbedding :=
      mem_map_of_mem _ hp
    rw [hπ] at hmap
    exact hs hmap
  choose π hπmem using hπex
  -- Reindex a round by `τ` on the nodes and by `π` on each node's samples.
  let Φ : Round n ≃ Round n :=
    { toFun := fun r w => π (τ.symm w) (r (τ.symm w))
      invFun := fun r v => (π v).symm (r (τ v))
      left_inv := fun r => by
        funext v
        change (π v).symm (π (τ.symm (τ v)) (r (τ.symm (τ v)))) = r v
        rw [Equiv.symm_apply_apply]
        exact (π v).symm_apply_apply _
      right_inv := fun r => by
        funext w
        change π (τ.symm w) ((π (τ.symm w)).symm (r (τ (τ.symm w)))) = r w
        have hτw : τ (τ.symm w) = w := Equiv.apply_symm_apply τ w
        rw [hτw]
        exact (π (τ.symm w)).apply_symm_apply (r w) }
  have hdom : ∀ r, count (step x r) c ≤ count (step x (Φ r)) b := by
    intro r
    let src : Finset (Fin n) := univ.filter fun v => r v ∈ adoptPairs x (x v) c
    let tgt : Finset (Fin n) := univ.filter fun w => Φ r w ∈ adoptPairs x (x w) b
    have hsrc : count (step x r) c = src.card := by rw [count_step_adopt]
    have htgt : count (step x (Φ r)) b = tgt.card := by rw [count_step_adopt]
    have hle : src.card ≤ tgt.card := by
      refine card_le_card_of_injOn (τ : Fin n → Fin n) ?_ ?_
      · intro v hv
        simp only [src, mem_coe, mem_filter, mem_univ, true_and] at hv
        simp only [tgt, mem_coe, mem_filter, mem_univ, true_and]
        have hΦ : Φ r (τ v) = π v (r v) := by
          change π (τ.symm (τ v)) (r (τ.symm (τ v))) = π v (r v)
          rw [Equiv.symm_apply_apply]
        rw [hΦ]
        exact hπmem v (r v) hv
      · intro v _ w _ heq
        exact τ.injective heq
    rw [hsrc, htgt]
    exact hle
  have hpt : ∀ r, (if t ≤ count (step x r) c then (1 : ℝ) else 0)
      ≤ (if t ≤ count (step x (Φ r)) b then (1 : ℝ) else 0) := by
    intro r
    have hle := hdom r
    split_ifs with hc hb
    · norm_num
    · exact absurd (hc.trans hle) hb
    · norm_num
    · norm_num
  have havg := avg_le_avg hpt
  have heq := avg_equiv Φ (fun r => if t ≤ count (step x r) b then (1 : ℝ) else 0)
  exact havg.trans (le_of_eq heq)

/-! ### The growth phase -/

omit [DecidableEq α] in
/-- One round with the concrete constants `z = 128` and failure `2/n²`. -/
lemma growth_round_aux [NeZero n] {k : ℕ} (hC : (2 : ℝ) ≤ Real.log n)
    (x : Config n (Fin k)) (i : Fin k) (g : ℝ)
    (hgap : 128 * √(n * Real.log n) ≤ g)
    (hlead : ∀ j ≠ i, (count x j : ℝ) + g ≤ count x i)
    (ha_le : (count x i : ℝ) ≤ 3 * n / 4) :
    1 - 2 / (n : ℝ) ^ 2 ≤ avg (fun r : Round n =>
      if (count x i : ℝ) ≤ count (step x r) i ∧
          ∀ j ≠ i, (count (step x r) j : ℝ) + g * (1 + count x i / (8 * n))
            ≤ count (step x r) i
      then (1 : ℝ) else 0) := by
  have hL : (0 : ℝ) < Real.log n := by linarith
  have hn1 : 1 ≤ n := one_le_of_log_pos hL
  have hn : (0 : ℝ) < n := by exact_mod_cast hn1
  haveI : Nonempty (Round n) := ⟨fun _ => ((0 : Fin n), (0 : Fin n))⟩
  have hg0 : 0 < g := by
    have hpos : (0 : ℝ) < 128 * √((n : ℝ) * Real.log n) :=
      mul_pos (by norm_num) (Real.sqrt_pos.mpr (mul_pos hn hL))
    exact lt_of_lt_of_le hpos hgap
  have ha_lt_nat : count x i < n := by
    have h34 : (3 : ℝ) * n / 4 < n := by
      rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 4)]
      linarith [hn]
    exact_mod_cast ha_le.trans_lt h34
  have hpos : ∃ j : Fin k, j ≠ i ∧ 0 < count x j := by
    by_contra hnone
    have hzero : ∑ j ∈ univ.erase i, count x j = 0 := by
      refine sum_eq_zero fun j hj => ?_
      have hnot := (not_exists.mp hnone) j
      have hne := ne_of_mem_erase hj
      have : ¬ 0 < count x j := fun hp => hnot ⟨hne, hp⟩
      omega
    have hsum := sum_count x
    rw [← add_sum_erase univ (count x) (mem_univ i), hzero, add_zero] at hsum
    exact ha_lt_nat.ne hsum
  obtain ⟨j0, hj0_ne, hj0_pos⟩ := hpos
  have hga : g ≤ (count x i : ℝ) := by
    have hlead0 := hlead j0 hj0_ne
    have h0 : (0 : ℝ) ≤ count x j0 := Nat.cast_nonneg _
    linarith
  have ha_pos : 0 < count x i := by
    have : (0 : ℝ) < count x i := by linarith [hga, hg0]
    exact_mod_cast this
  have hsq : (128 : ℝ) ^ 2 * (n : ℝ) * Real.log n ≤ g ^ 2 := by
    have hbase : 0 ≤ 128 * √((n : ℝ) * Real.log n) := by positivity
    have hpow := pow_le_pow_left₀ hbase hgap 2
    have hmul : 0 ≤ (n : ℝ) * Real.log n := mul_nonneg hn.le hL.le
    rw [mul_pow, Real.sq_sqrt hmul] at hpow
    have heq : (128 : ℝ) ^ 2 * n * Real.log n = 128 ^ 2 * ((n : ℝ) * Real.log n) := by ring
    linarith [heq]
  have hne : ((univ : Finset (Fin k)).erase i).Nonempty :=
    ⟨j0, mem_erase.mpr ⟨hj0_ne, mem_univ _⟩⟩
  obtain ⟨s, hs, hmax⟩ := Finset.exists_max_image (univ.erase i) (count x) hne
  have hsecond : ∀ l ≠ i, count x l ≤ count x s := by
    intro l hl
    exact hmax l (mem_erase.mpr ⟨hl, mem_univ _⟩)
  have hji : count x s ≤ count x i := by
    have : (count x s : ℝ) ≤ count x i := by
      linarith [hlead s (ne_of_mem_erase hs), hg0.le]
    exact_mod_cast this
  have hbound : ∀ l, count x l ≤ count x i := by
    intro l
    by_cases hl : l = i
    · rw [hl]
    · exact (hsecond l hl).trans hji
  let thr : ℝ := g * (1 + count x i / (8 * n))
  let factor : ℝ := 1 + ((count x i : ℝ) / n) * (1 - (count x i : ℝ) / n)
  have hfac0 : 0 ≤ factor := by
    unfold factor
    have han : (count x i : ℝ) / n ≤ 3 / 4 := by
      rw [div_le_div_iff₀ hn (by norm_num : (0 : ℝ) < 4)]
      linarith [ha_le]
    have hsub : 0 ≤ 1 - (count x i : ℝ) / n := by linarith
    have hcoef : 0 ≤ (count x i : ℝ) / n := div_nonneg (Nat.cast_nonneg _) hn.le
    have : 0 ≤ (count x i : ℝ) / n * (1 - (count x i : ℝ) / n) := mul_nonneg hcoef hsub
    linarith
  have hmargin := three_quarter_margin (n := (n : ℝ)) (a := (count x i : ℝ)) (g := g)
    hn (Nat.cast_nonneg (count x i)) hg0.le ha_le
  have hEs_low : g * factor
      ≤ avg (fun r : Round n => (count (step x r) i : ℝ) - count (step x r) s) := by
    refine (mul_le_mul_of_nonneg_right ?_ hfac0).trans (expected_gap_ge x hji hsecond)
    linarith [hlead s (ne_of_mem_erase hs)]
  have hthr_s : thr
      ≤ avg (fun r : Round n => (count (step x r) i : ℝ) - count (step x r) s)
        - g * (count x i : ℝ) / (8 * n) := by
    unfold thr factor at *
    linarith [hmargin, hEs_low]
  have hmono (j : Fin k) (hj : j ≠ i) :
      avg (fun r : Round n => (count (step x r) i : ℝ) - count (step x r) s)
        ≤ avg (fun r : Round n => (count (step x r) i : ℝ) - count (step x r) j) := by
    have hm := expected_count_mono x (hsecond j hj)
    rw [avg_sub, avg_sub]
    linarith
  have hthr_j (j : Fin k) (hj : j ≠ i) :
      thr ≤ avg (fun ρ : Round n => (count (step x ρ) i : ℝ) - count (step x ρ) j)
        - g * (count x i : ℝ) / (8 * n) := by
    linarith [hthr_s, hmono j hj]
  have hlow : (n : ℝ) / 4 * g
      ≤ (count x i : ℝ) * n - ∑ j : Fin k, (count x j : ℝ) ^ 2 := by
    have hS := sum_sq_le_aggregate x i (b := (count x s : ℝ))
      (fun j hj => by exact_mod_cast hsecond j hj)
    have hring : (count x i : ℝ) * n
        - ((count x i : ℝ) ^ 2 + (n - count x i) * count x s)
        = (n - count x i) * ((count x i : ℝ) - count x s) := by ring
    have hge : (n - (count x i : ℝ)) * ((count x i : ℝ) - count x s)
        ≤ (count x i : ℝ) * n - ∑ j : Fin k, (count x j : ℝ) ^ 2 := by
      linarith [hS, hring]
    have hna : (n : ℝ) / 4 ≤ n - count x i := by
      rw [le_sub_iff_add_le]
      have : (n : ℝ) / 4 + 3 * n / 4 = n := by field_simp; ring
      linarith [ha_le, this]
    have hδ : g ≤ (count x i : ℝ) - count x s := by
      linarith [hlead s (ne_of_mem_erase hs)]
    have hnn : (0 : ℝ) ≤ n - (count x i : ℝ) := by
      have : (count x i : ℝ) ≤ n := by exact_mod_cast count_le x i
      linarith
    exact (mul_le_mul hna hδ hg0.le hnn).trans hge
  have hdrift : (count x i : ℝ) * g / (4 * n)
      ≤ avg (fun ρ : Round n => (count (step x ρ) i : ℝ)) - (count x i : ℝ) := by
    have hform : avg (fun ρ : Round n => (count (step x ρ) i : ℝ)) - (count x i : ℝ)
        = (count x i : ℝ) * ((count x i : ℝ) * n
          - ∑ j : Fin k, (count x j : ℝ) ^ 2) / n ^ 2 := by
      rw [expected_count_mul]
      field_simp
      ring
    have hmul : (count x i : ℝ) * ((n : ℝ) / 4 * g) / n ^ 2
        ≤ (count x i : ℝ) * ((count x i : ℝ) * n
          - ∑ j : Fin k, (count x j : ℝ) ^ 2) / n ^ 2 := by
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left hlow (Nat.cast_nonneg _)
    have heq : (count x i : ℝ) * g / (4 * n)
        = (count x i : ℝ) * ((n : ℝ) / 4 * g) / n ^ 2 := by
      field_simp
    linarith [hform, hmul, heq]
  have hcount_thr : (count x i : ℝ)
      ≤ avg (fun ρ : Round n => (count (step x ρ) i : ℝ))
        - (count x i : ℝ) * g / (4 * n) := by
    linarith [hdrift]
  have htail_j (j : Fin k) (hj : j ≠ i) :=
    gap_tail_twelve x i j hj hbound ha_pos hg0.le hga hL.le hn1 hsq
  have hcount := count_tail_twelve x i hbound ha_pos hg0.le hga hL.le hn1 hsq
  let P : Finset (Fin k) := (univ.erase i).filter (fun j => 0 < count x j)
  have hPcard : P.card ≤ n := by
    have hsub : P ⊆ (univ : Finset (Fin n)).image x := by
      intro j hj
      have hjpos : 0 < count x j := (mem_filter.mp hj).2
      unfold count at hjpos
      rw [Finset.card_pos] at hjpos
      obtain ⟨v, hv⟩ := hjpos
      exact mem_image.mpr ⟨v, mem_univ v, (mem_filter.mp hv).2⟩
    calc P.card ≤ ((univ : Finset (Fin n)).image x).card := card_le_card hsub
      _ ≤ (univ : Finset (Fin n)).card := card_image_le
      _ = n := by rw [card_univ, Fintype.card_fin]
  let drop : Round n → ℝ := fun r =>
    if (count (step x r) i : ℝ) < (count x i : ℝ) then 1 else 0
  let gapf : Fin k → Round n → ℝ := fun j r =>
    if (count (step x r) i : ℝ) - count (step x r) j < thr then 1 else 0
  let bad : Round n → ℝ := fun r => drop r + ∑ j ∈ P, gapf j r
  let good : Round n → ℝ := fun r =>
    if (count x i : ℝ) ≤ count (step x r) i ∧
        ∀ j ≠ i, (count (step x r) j : ℝ) + thr ≤ count (step x r) i
      then 1 else 0
  have hdrop_le (r : Round n) : drop r
      ≤ (if (count (step x r) i : ℝ)
            ≤ avg (fun ρ : Round n => (count (step x ρ) i : ℝ))
              - (count x i : ℝ) * g / (4 * n) then (1 : ℝ) else 0) := by
    by_cases hlt : (count (step x r) i : ℝ) < (count x i : ℝ)
    · have hle : (count (step x r) i : ℝ)
          ≤ avg (fun ρ : Round n => (count (step x ρ) i : ℝ))
            - (count x i : ℝ) * g / (4 * n) := by
        linarith [hlt, hcount_thr]
      unfold drop
      rw [if_pos hlt, if_pos hle]
    · unfold drop
      rw [if_neg hlt]
      split_ifs <;> norm_num
  have hgap_le (j : Fin k) (hj : j ≠ i) (r : Round n) : gapf j r
      ≤ (if (count (step x r) i : ℝ) - count (step x r) j
            ≤ avg (fun ρ : Round n => (count (step x ρ) i : ℝ) - count (step x ρ) j)
              - g * (count x i : ℝ) / (8 * n) then (1 : ℝ) else 0) := by
    by_cases hlt : (count (step x r) i : ℝ) - count (step x r) j < thr
    · have hle : (count (step x r) i : ℝ) - count (step x r) j
          ≤ avg (fun ρ : Round n => (count (step x ρ) i : ℝ) - count (step x ρ) j)
            - g * (count x i : ℝ) / (8 * n) := by
        linarith [hlt, hthr_j j hj]
      unfold gapf
      rw [if_pos hlt, if_pos hle]
    · unfold gapf
      rw [if_neg hlt]
      split_ifs <;> norm_num
  have hpt (r : Round n) : (1 : ℝ) - bad r ≤ good r := by
    by_cases hgood : (count x i : ℝ) ≤ count (step x r) i ∧
        ∀ j ≠ i, (count (step x r) j : ℝ) + thr ≤ count (step x r) i
    · have hnn : 0 ≤ bad r := by
        refine add_nonneg ?_ ?_
        · unfold drop; split_ifs <;> norm_num
        · exact sum_nonneg fun _ _ => by unfold gapf; split_ifs <;> norm_num
      unfold good
      rw [if_pos hgood]
      linarith
    · unfold good
      rw [if_neg hgood]
      suffices (1 : ℝ) ≤ bad r by linarith
      have hdisj : (count (step x r) i : ℝ) < count x i ∨
          ∃ j, j ≠ i ∧ (count (step x r) i : ℝ) < count (step x r) j + thr := by
        by_cases hA : (count x i : ℝ) ≤ count (step x r) i
        · have hexists : ∃ j, j ≠ i ∧
              ¬ ((count (step x r) j : ℝ) + thr ≤ count (step x r) i) := by
            by_contra hall
            have hall' : ∀ j ≠ i, (count (step x r) j : ℝ) + thr ≤ count (step x r) i := by
              intro j hj
              by_contra hfail
              exact hall ⟨j, hj, hfail⟩
            exact hgood ⟨hA, hall'⟩
          obtain ⟨j, hj, hfail⟩ := hexists
          exact Or.inr ⟨j, hj, lt_of_not_ge hfail⟩
        · exact Or.inl (lt_of_not_ge hA)
      rcases hdisj with hlt | ⟨j, hj, hfail⟩
      · have hdrop1 : drop r = 1 := by unfold drop; rw [if_pos hlt]
        have hsum0 : 0 ≤ ∑ j ∈ P, gapf j r :=
          sum_nonneg fun _ _ => by unfold gapf; split_ifs <;> norm_num
        unfold bad
        rw [hdrop1]
        linarith
      · have hltj : (count (step x r) i : ℝ) - count (step x r) j < thr := by linarith
        have hmem : ∃ j ∈ P, (count (step x r) i : ℝ) - count (step x r) j < thr := by
          by_cases hjp : 0 < count x j
          · exact ⟨j, mem_filter.mpr ⟨mem_erase.mpr ⟨hj, mem_univ _⟩, hjp⟩, hltj⟩
          · have hz : count x j = 0 := by omega
            have hz' : count (step x r) j = 0 := count_step_eq_zero x r j hz
            have ha' : (count (step x r) i : ℝ) < thr := by
              have : (count (step x r) j : ℝ) = 0 := by exact_mod_cast hz'
              linarith
            have hlt0 : (count (step x r) i : ℝ) - count (step x r) j0 < thr := by
              have h0 : (0 : ℝ) ≤ count (step x r) j0 := Nat.cast_nonneg _
              linarith [ha', h0]
            exact ⟨j0, mem_filter.mpr ⟨mem_erase.mpr ⟨hj0_ne, mem_univ _⟩, hj0_pos⟩, hlt0⟩
        obtain ⟨j1, hj1, hlt1⟩ := hmem
        have hgap1 : gapf j1 r = 1 := by unfold gapf; rw [if_pos hlt1]
        have hsum : gapf j1 r ≤ ∑ j ∈ P, gapf j r :=
          Finset.single_le_sum (f := fun j => gapf j r)
            (fun _ _ => by unfold gapf; split_ifs <;> norm_num) hj1
        have hdrop0 : 0 ≤ drop r := by unfold drop; split_ifs <;> norm_num
        unfold bad
        linarith
  have havg : avg (fun r => (1 : ℝ) - bad r) = 1 - avg bad := by rw [avg_sub, avg_const]
  have hone : 1 - avg bad ≤ avg good := by
    rw [← havg]
    exact avg_le_avg hpt
  have hsplit : avg bad = avg drop + ∑ j ∈ P, avg (gapf j) := by
    unfold bad
    rw [avg_add, avg_sum]
  have hdrop_avg : avg drop ≤ 1 / (n : ℝ) ^ 12 := (avg_le_avg hdrop_le).trans hcount
  have hgap_avgs : ∑ j ∈ P, avg (gapf j) ≤ (P.card : ℝ) * (1 / (n : ℝ) ^ 12) := by
    calc ∑ j ∈ P, avg (gapf j)
        ≤ ∑ j ∈ P, (1 / (n : ℝ) ^ 12) := by
          refine sum_le_sum fun j hj => ?_
          exact (avg_le_avg (hgap_le j (ne_of_mem_erase (mem_filter.mp hj).1))).trans
            (htail_j j (ne_of_mem_erase (mem_filter.mp hj).1))
      _ = (P.card : ℝ) * (1 / (n : ℝ) ^ 12) := by rw [sum_const, nsmul_eq_mul]
  have hbad_le : avg bad ≤ 2 / (n : ℝ) ^ 2 := by
    rw [hsplit]
    have hpack : avg drop + ∑ j ∈ P, avg (gapf j)
        ≤ ((P.card : ℝ) + 1) * (1 / (n : ℝ) ^ 12) := by
      have heq : 1 / (n : ℝ) ^ 12 + (P.card : ℝ) * (1 / (n : ℝ) ^ 12)
          = ((P.card : ℝ) + 1) * (1 / (n : ℝ) ^ 12) := by ring
      linarith [hdrop_avg, hgap_avgs, heq]
    have hcardR : (P.card : ℝ) ≤ n := by exact_mod_cast hPcard
    have hsmall : ((n : ℝ) + 1) / (n : ℝ) ^ 12 ≤ 2 / (n : ℝ) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hn1r : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      have h3 : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 12 :=
        pow_le_pow_right₀ hn1r (by norm_num : (3 : ℕ) ≤ 12)
      have h2n : (n : ℝ) + 1 ≤ 2 * n := by linarith [hn1r]
      have hstep : ((n : ℝ) + 1) * (n : ℝ) ^ 2 ≤ (2 * n) * (n : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right h2n (by positivity)
      have heq : (2 * (n : ℝ)) * (n : ℝ) ^ 2 = 2 * (n : ℝ) ^ 3 := by ring
      have hlast : 2 * (n : ℝ) ^ 3 ≤ 2 * (n : ℝ) ^ 12 :=
        mul_le_mul_of_nonneg_left h3 (by norm_num)
      linarith [hstep, heq, hlast]
    have hmulcard : ((P.card : ℝ) + 1) * (1 / (n : ℝ) ^ 12)
        ≤ ((n : ℝ) + 1) * (1 / (n : ℝ) ^ 12) :=
      mul_le_mul_of_nonneg_right (by linarith [hcardR]) (by positivity)
    have heqdiv : ((n : ℝ) + 1) * (1 / (n : ℝ) ^ 12) = ((n : ℝ) + 1) / (n : ℝ) ^ 12 := by
      ring
    linarith [hpack, hmulcard, heqdiv, hsmall]
  have hgood_avg : 1 - 2 / (n : ℝ) ^ 2 ≤ avg good := by linarith [hone, hbad_le]
  exact hgood_avg

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
  refine ⟨128, 2, by norm_num, by norm_num, ?_⟩
  intro n _ hC k x i g hgap hlead ha_le
  exact growth_round_aux hC x i g hgap hlead ha_le

/-- Once colour `i` holds at least `3n/4` and `log n ≥ 128`, one round keeps it there except
with probability `1/n²`. -/
lemma stay_three_quarters [NeZero n] [Fintype α] (hL : (128 : ℝ) ≤ Real.log n)
    (x : Config n α) (i : α) (ha : 3 * (n : ℝ) / 4 ≤ count x i) :
    1 - 1 / (n : ℝ) ^ 2 ≤ avg (fun r : Round n =>
      if 3 * (n : ℝ) / 4 ≤ count (step x r) i then (1 : ℝ) else 0) := by
  have hL0 : (0 : ℝ) < Real.log n := by linarith
  have hn1 : 1 ≤ n := one_le_of_log_pos hL0
  have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  haveI : Nonempty (Round n) := ⟨fun _ => ((0 : Fin n), (0 : Fin n))⟩
  have ha_pos : 0 < count x i := by
    have : (0 : ℝ) < count x i := by
      have h34 : (0 : ℝ) < 3 * n / 4 := by positivity
      linarith
    exact_mod_cast this
  have ha_le_n : (count x i : ℝ) ≤ n := by exact_mod_cast count_le x i
  have hother (j : α) (hj : j ≠ i) : (count x j : ℝ) ≤ n - count x i := by
    have hsum : ∑ l : α, (count x l : ℝ) = n := by exact_mod_cast sum_count x
    have hrest : ∑ l ∈ univ.erase i, (count x l : ℝ) = n - count x i := by
      rw [← add_sum_erase univ (fun l => (count x l : ℝ)) (mem_univ i)] at hsum
      linarith
    have hineq := Finset.single_le_sum (f := fun l => (count x l : ℝ))
      (fun _ _ => Nat.cast_nonneg _) (mem_erase.mpr ⟨hj, mem_univ _⟩)
    linarith
  have hcomp : n - (count x i : ℝ) ≤ count x i := by linarith [ha]
  have hbound : ∀ l, count x l ≤ count x i := by
    intro l
    by_cases hl : l = i
    · rw [hl]
    · exact_mod_cast (hother l hl).trans hcomp
  have hS := sum_sq_le_aggregate x i hother
  have hring : (count x i : ℝ) * n
      - ((count x i : ℝ) ^ 2 + (n - count x i) ^ 2)
      = (n - count x i) * (2 * (count x i : ℝ) - n) := by ring
  have hge : (n - (count x i : ℝ)) * (2 * (count x i : ℝ) - n)
      ≤ (count x i : ℝ) * n - ∑ j : α, (count x j : ℝ) ^ 2 := by
    linarith [hS, hring]
  have hdrift : (count x i : ℝ) * ((n - count x i) * (2 * (count x i : ℝ) - n)) / n ^ 2
      ≤ avg (fun ρ : Round n => (count (step x ρ) i : ℝ)) - (count x i : ℝ) := by
    have hform : avg (fun ρ : Round n => (count (step x ρ) i : ℝ)) - (count x i : ℝ)
        = (count x i : ℝ) * ((count x i : ℝ) * n
          - ∑ j : α, (count x j : ℝ) ^ 2) / n ^ 2 := by
      rw [expected_count_mul]
      field_simp; ring
    have hmul : (count x i : ℝ) * ((n - count x i) * (2 * (count x i : ℝ) - n)) / n ^ 2
        ≤ (count x i : ℝ) * ((count x i : ℝ) * n
          - ∑ j : α, (count x j : ℝ) ^ 2) / n ^ 2 := by
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left hge (Nat.cast_nonneg _)
    linarith [hform, hmul]
  have hlog : 2 * Real.log n ≤ (n : ℝ) / 32768 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 32768)]
    have heq : 2 * Real.log n * 32768 = 65536 * Real.log n := by ring
    linarith [log_le_div_of_log_ge hL, heq]
  have h4 : 4 * (count x i : ℝ) ^ 2 / n ≤ 4 * n := by
    have hsq : (count x i : ℝ) ^ 2 ≤ n ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) ha_le_n 2
    rw [div_le_iff₀ hn]
    nlinarith [hsq]
  have hfinish {lam : ℝ}
      (hcut : 3 * (n : ℝ) / 4
        ≤ avg (fun ρ : Round n => (count (step x ρ) i : ℝ)) - lam)
      (htail : avg (fun r : Round n =>
          if (count (step x r) i : ℝ)
              ≤ avg (fun ρ : Round n => (count (step x ρ) i : ℝ)) - lam
            then (1 : ℝ) else 0) ≤ 1 / (n : ℝ) ^ 2) :
      1 - 1 / (n : ℝ) ^ 2 ≤ avg (fun r : Round n =>
        if 3 * (n : ℝ) / 4 ≤ count (step x r) i then (1 : ℝ) else 0) := by
    let bad : Round n → ℝ := fun r =>
      if (count (step x r) i : ℝ)
          ≤ avg (fun ρ : Round n => (count (step x ρ) i : ℝ)) - lam then 1 else 0
    let good : Round n → ℝ := fun r =>
      if 3 * (n : ℝ) / 4 ≤ count (step x r) i then 1 else 0
    have hpt (r : Round n) : (1 : ℝ) - bad r ≤ good r := by
      by_cases hbad : (count (step x r) i : ℝ)
          ≤ avg (fun ρ : Round n => (count (step x ρ) i : ℝ)) - lam
      · unfold bad good
        rw [if_pos hbad]
        split_ifs <;> norm_num
      · have hgt : avg (fun ρ : Round n => (count (step x ρ) i : ℝ)) - lam
            < (count (step x r) i : ℝ) := lt_of_not_ge hbad
        have hgood : 3 * (n : ℝ) / 4 ≤ count (step x r) i := by linarith [hcut, hgt]
        unfold bad good
        rw [if_neg hbad, if_pos hgood, sub_zero]
        try exact le_rfl
    have havg : avg (fun r => (1 : ℝ) - bad r) = 1 - avg bad := by rw [avg_sub, avg_const]
    have hone : 1 - avg bad ≤ avg good := by
      rw [← havg]
      exact avg_le_avg hpt
    have hbad : avg bad ≤ 1 / (n : ℝ) ^ 2 := htail
    linarith
  by_cases h7 : (count x i : ℝ) ≤ 7 * n / 8
  · let lam : ℝ := 3 * (n : ℝ) / 64
    have hlam0 : 0 ≤ lam := by unfold lam; positivity
    have hfloor : lam
        ≤ (count x i : ℝ) * ((n - count x i) * (2 * (count x i : ℝ) - n)) / n ^ 2 := by
      have ha1 : 3 * (n : ℝ) / 4 ≤ count x i := ha
      have ha2 : (n : ℝ) / 8 ≤ n - count x i := by
        have heq : (n : ℝ) - 7 * n / 8 = n / 8 := by field_simp; ring
        linarith [h7, heq]
      have ha3 : (n : ℝ) / 2 ≤ 2 * (count x i : ℝ) - n := by
        have heq : 2 * (3 * (n : ℝ) / 4) - n = n / 2 := by field_simp; ring
        linarith [ha, heq]
      have hna0 : (0 : ℝ) ≤ n - count x i := by linarith [ha_le_n]
      have hhalf0 : (0 : ℝ) ≤ n / 2 := by positivity
      have heighth0 : (0 : ℝ) ≤ n / 8 := by positivity
      have hstep1 : (n : ℝ) / 8 * (n / 2) ≤ (n - count x i) * (2 * (count x i : ℝ) - n) :=
        mul_le_mul ha2 ha3 hhalf0 hna0
      have ha0 : (0 : ℝ) ≤ count x i := Nat.cast_nonneg _
      have hstep2 : (3 * (n : ℝ) / 4) * (n / 8 * (n / 2))
          ≤ (count x i : ℝ) * ((n - count x i) * (2 * (count x i : ℝ) - n)) :=
        mul_le_mul ha1 hstep1 (mul_nonneg heighth0 hhalf0) ha0
      have heq : (3 * (n : ℝ) / 4) * (n / 8 * (n / 2)) = 3 * n ^ 3 / 64 := by
        field_simp; ring
      have hdiv : (3 * n ^ 3 / 64) / n ^ 2 ≤
          (count x i : ℝ) * ((n - count x i) * (2 * (count x i : ℝ) - n)) / n ^ 2 :=
        div_le_div_of_nonneg_right (by linarith [hstep2, heq]) (by positivity)
      have heqlam : lam = (3 * n ^ 3 / 64) / n ^ 2 := by
        unfold lam
        field_simp
      linarith [hdiv, heqlam]
    have hcut : 3 * (n : ℝ) / 4
        ≤ avg (fun ρ : Round n => (count (step x ρ) i : ℝ)) - lam := by
      linarith [hdrift, hfloor, ha]
    have hdenle : 4 * (count x i : ℝ) ^ 2 / n + 2 * lam / 3 ≤ 5 * n := by
      have hlam_small : 2 * lam / 3 ≤ n := by
        unfold lam
        have heq : 2 * (3 * (n : ℝ) / 64) / 3 = n / 32 := by field_simp; ring
        linarith [heq, hn]
      linarith [h4, hlam_small]
    have hlow_exp : 2 * Real.log n
        ≤ lam ^ 2 / (4 * (count x i : ℝ) ^ 2 / n + 2 * lam / 3) := by
      have hdenpos : 0 < 4 * (count x i : ℝ) ^ 2 / n + 2 * lam / 3 := by
        have : 0 < 4 * (count x i : ℝ) ^ 2 / n := by positivity
        have : 0 ≤ 2 * lam / 3 := by unfold lam; positivity
        linarith
      have hbig : lam ^ 2 / (5 * n) ≤ lam ^ 2 / (4 * (count x i : ℝ) ^ 2 / n + 2 * lam / 3) :=
        div_le_div_of_nonneg_left (sq_nonneg _) hdenpos hdenle
      have heq : lam ^ 2 / (5 * n) = 9 * n / 20480 := by
        unfold lam
        field_simp; ring
      have hnum : (n : ℝ) / 32768 ≤ 9 * n / 20480 := by
        rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
        nlinarith [hn]
      linarith [hbig, heq, hnum, hlog]
    have htail := count_dev_le x i hbound ha_pos hlam0
    have hexp : Real.exp (-(lam ^ 2 / (4 * (count x i : ℝ) ^ 2 / n + 2 * lam / 3)))
        ≤ 1 / (n : ℝ) ^ 2 := by
      refine le_trans (Real.exp_le_exp.mpr (neg_le_neg hlow_exp)) ?_
      exact le_of_eq (exp_neg_two_log hn1)
    exact hfinish hcut (htail.trans hexp)
  · have hgt7 : 7 * (n : ℝ) / 8 < count x i := lt_of_not_ge h7
    let lam : ℝ := n / 8
    have hlam0 : 0 ≤ lam := by unfold lam; positivity
    have hnn : 0 ≤ (n - (count x i : ℝ)) * (2 * (count x i : ℝ) - n) := by
      have h1 : 0 ≤ n - (count x i : ℝ) := by linarith [ha_le_n]
      have h2 : 0 ≤ 2 * (count x i : ℝ) - n := by linarith [ha]
      exact mul_nonneg h1 h2
    have hcut : 3 * (n : ℝ) / 4
        ≤ avg (fun ρ : Round n => (count (step x ρ) i : ℝ)) - lam := by
      have h78 : 7 * (n : ℝ) / 8 - n / 8 = 3 * n / 4 := by field_simp; ring
      have hdrift0 : 0 ≤ avg (fun ρ : Round n => (count (step x ρ) i : ℝ)) - count x i := by
        have hmul : 0 ≤ (count x i : ℝ) * ((n - count x i) * (2 * (count x i : ℝ) - n)) / n ^ 2 :=
          div_nonneg (mul_nonneg (Nat.cast_nonneg _) hnn) (by positivity)
        linarith [hdrift, hmul]
      unfold lam
      linarith [hdrift0, hgt7, h78]
    have hdenle : 4 * (count x i : ℝ) ^ 2 / n + 2 * lam / 3 ≤ 5 * n := by
      have hlam_small : 2 * lam / 3 ≤ n := by
        unfold lam
        have heq : 2 * ((n : ℝ) / 8) / 3 = n / 12 := by field_simp; ring
        linarith [heq, hn]
      linarith [h4, hlam_small]
    have hlow_exp : 2 * Real.log n
        ≤ lam ^ 2 / (4 * (count x i : ℝ) ^ 2 / n + 2 * lam / 3) := by
      have hdenpos : 0 < 4 * (count x i : ℝ) ^ 2 / n + 2 * lam / 3 := by
        have : 0 < 4 * (count x i : ℝ) ^ 2 / n := by positivity
        have : 0 ≤ 2 * lam / 3 := by unfold lam; positivity
        linarith
      have hbig : lam ^ 2 / (5 * n) ≤ lam ^ 2 / (4 * (count x i : ℝ) ^ 2 / n + 2 * lam / 3) :=
        div_le_div_of_nonneg_left (sq_nonneg _) hdenpos hdenle
      have heq : lam ^ 2 / (5 * n) = n / 320 := by
        unfold lam
        field_simp; ring
      have hnum : (n : ℝ) / 32768 ≤ n / 320 := by
        rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
        nlinarith [hn]
      linarith [hbig, heq, hnum, hlog]
    have htail := count_dev_le x i hbound ha_pos hlam0
    have hexp : Real.exp (-(lam ^ 2 / (4 * (count x i : ℝ) ^ 2 / n + 2 * lam / 3)))
        ≤ 1 / (n : ℝ) ^ 2 := by
      refine le_trans (Real.exp_le_exp.mpr (neg_le_neg hlow_exp)) ?_
      exact le_of_eq (exp_neg_two_log hn1)
    exact hfinish hcut (htail.trans hexp)

/-- States from which colour `i` already holds `3n/4`, or still leads every other colour by the
grown gap `g₀ q^t` and has not fallen below its initial count. -/
def growthSet (n : ℕ) {k : ℕ} (i : Fin k) (a0 g0 q : ℝ) (t : ℕ) : Set (Config n (Fin k)) :=
  {y | 3 * (n : ℝ) / 4 ≤ (count y i : ℝ)} ∪
  {y | a0 ≤ (count y i : ℝ) ∧ ∀ j ≠ i, (count y j : ℝ) + g0 * q ^ t ≤ (count y i : ℝ)}

/-- `(1 + a/(8n))` to the power `⌈128 (n/a) log n⌉` exceeds `n`, once `log n ≥ 128` and
`128 √(n log n) ≤ a ≤ n`. Bernoulli gives `(1 + a/(8n))^{⌈16 n/a⌉} ≥ 3`, and `⌈log n⌉ + 1`
further powers exceed `n` because `log 3 > 1`. -/
lemma growth_ratio_pow_gt {n : ℕ} (hL : (128 : ℝ) ≤ Real.log n) {a : ℝ}
    (ha0 : 128 * √(n * Real.log n) ≤ a) (han : a ≤ n) :
    (n : ℝ) < (1 + a / (8 * n)) ^ ⌈128 * (n / a) * Real.log n⌉₊ := by
  have hL0 : (0 : ℝ) < Real.log n := by linarith
  have hn1 : 1 ≤ n := one_le_of_log_pos hL0
  have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have ha_pos : 0 < a := by
    have hsqrt : (0 : ℝ) < 128 * √(n * Real.log n) :=
      mul_pos (by norm_num) (Real.sqrt_pos.mpr (mul_pos hn hL0))
    exact lt_of_lt_of_le hsqrt ha0
  let u : ℝ := a / (8 * n)
  have hu : 0 < u := by
    unfold u
    exact div_pos ha_pos (mul_pos (by norm_num) hn)
  let B : ℕ := ⌈2 / u⌉₊
  have hBu : (2 : ℝ) ≤ (B : ℝ) * u := by
    have hceil : 2 / u ≤ (B : ℝ) := Nat.le_ceil _
    have hmul := mul_le_mul_of_nonneg_right hceil hu.le
    have hcanc : 2 / u * u = 2 := by unfold u; field_simp
    linarith
  have hbern : 1 + B * u ≤ (1 + u) ^ B :=
    one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ u) B
  have hbase : (3 : ℝ) ≤ (1 + u) ^ B := by
    linarith [hBu, hbern]
  let m : ℕ := ⌈Real.log n⌉₊ + 1
  have hm_lt : (m : ℝ) < Real.log n + 2 := by
    have hceil : (⌈Real.log n⌉₊ : ℝ) < Real.log n + 1 :=
      Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ Real.log n)
    have hmcast : (m : ℝ) = (⌈Real.log n⌉₊ : ℝ) + 1 := by
      simp only [m, Nat.cast_add, Nat.cast_one]
    linarith
  have hm_ge : Real.log n + 1 ≤ (m : ℝ) := by
    have hceil : Real.log n ≤ (⌈Real.log n⌉₊ : ℝ) := Nat.le_ceil _
    have hmcast : (m : ℝ) = (⌈Real.log n⌉₊ : ℝ) + 1 := by
      simp only [m, Nat.cast_add, Nat.cast_one]
    linarith
  have hlog3 : (1 : ℝ) < Real.log 3 := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
  have h3exp : (3 : ℝ) ^ m = Real.exp ((m : ℝ) * Real.log 3) := by
    have hlog : Real.log ((3 : ℝ) ^ m) = (m : ℝ) * Real.log 3 := Real.log_pow 3 m
    rw [← hlog]
    exact (Real.exp_log (pow_pos (by norm_num : (0 : ℝ) < 3) m)).symm
  have h3gt : (n : ℝ) < (3 : ℝ) ^ m := by
    rw [h3exp]
    have hmul : (m : ℝ) ≤ (m : ℝ) * Real.log 3 := by
      calc (m : ℝ) = (m : ℝ) * 1 := by ring
        _ ≤ (m : ℝ) * Real.log 3 :=
          mul_le_mul_of_nonneg_left hlog3.le (Nat.cast_nonneg _)
    have hexp : Real.exp (Real.log n + 1) ≤ Real.exp ((m : ℝ) * Real.log 3) :=
      Real.exp_le_exp.mpr (by linarith [hm_ge, hmul])
    have hexp_add : Real.exp (Real.log n + 1) = n * Real.exp 1 := by
      rw [Real.exp_add, Real.exp_log hn]
    have hone : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
    have hnt : (n : ℝ) < n * Real.exp 1 :=
      calc (n : ℝ) = n * 1 := by ring
        _ < n * Real.exp 1 := mul_lt_mul_of_pos_left hone hn
    linarith [hexp, hexp_add, hnt]
  have hu_eq : 2 / u = 16 * (n / a) := by unfold u; field_simp; ring
  have hBlt : (B : ℝ) < 16 * (n / a) + 1 := by
    have hceil : (B : ℝ) < 2 / u + 1 := Nat.ceil_lt_add_one (le_of_lt (div_pos (by norm_num) hu))
    linarith
  have hr1 : (1 : ℝ) ≤ n / a := (one_le_div ha_pos).mpr han
  have hprod : (B : ℝ) * (m : ℝ) < (16 * (n / a) + 1) * (Real.log n + 2) :=
    mul_lt_mul_of_lt_of_le_of_nonneg_of_pos hBlt hm_lt.le (Nat.cast_nonneg _)
      (by linarith : (0 : ℝ) < Real.log n + 2)
  have hpack : (16 * (n / a) + 1) * (Real.log n + 2) ≤ 64 * (n / a) * Real.log n := by
    have h32 : 32 * (n / a) ≤ 32 * (n / a) * Real.log n := by
      calc 32 * (n / a) = 32 * (n / a) * 1 := by ring
        _ ≤ 32 * (n / a) * Real.log n :=
          mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ Real.log n)
            (mul_nonneg (by norm_num) (div_nonneg hn.le ha_pos.le))
    have hL16 : Real.log n + 2 ≤ 16 * Real.log n := by linarith
    have h16 : 16 * Real.log n ≤ 16 * (n / a) * Real.log n := by
      calc 16 * Real.log n = 16 * Real.log n * 1 := by ring
        _ ≤ 16 * Real.log n * (n / a) :=
          mul_le_mul_of_nonneg_left hr1 (mul_nonneg (by norm_num) (by linarith))
        _ = 16 * (n / a) * Real.log n := by ring
    have hsum : 32 * (n / a) + (Real.log n + 2) ≤ 48 * (n / a) * Real.log n := by
      linarith [h32, hL16, h16]
    have hring : (16 * (n / a) + 1) * (Real.log n + 2)
        = 16 * (n / a) * Real.log n + 32 * (n / a) + Real.log n + 2 := by ring
    linarith [hsum, hring]
  let Tfin : ℕ := ⌈128 * (n / a) * Real.log n⌉₊
  have h64 : 64 * (n / a) * Real.log n ≤ 128 * (n / a) * Real.log n := by
    have hnn : (0 : ℝ) ≤ (n / a) * Real.log n :=
      mul_nonneg (div_nonneg hn.le ha_pos.le) (by linarith)
    linarith
  have hceilT : 128 * (n / a) * Real.log n ≤ (Tfin : ℝ) := Nat.le_ceil _
  have hlt : (B : ℝ) * (m : ℝ) < (Tfin : ℝ) :=
    lt_of_lt_of_le hprod (hpack.trans (h64.trans hceilT))
  have hBm : B * m < Tfin := by
    rw [← Nat.cast_mul] at hlt
    exact_mod_cast hlt
  have hpow3 : (3 : ℝ) ^ m ≤ (1 + u) ^ (B * m) := by
    calc (3 : ℝ) ^ m ≤ ((1 + u) ^ B) ^ m := pow_le_pow_left₀ (by norm_num) hbase m
      _ = (1 + u) ^ (B * m) := by rw [← pow_mul]
  have hpowT : (1 + u) ^ (B * m) ≤ (1 + u) ^ Tfin :=
    pow_le_pow_right₀ (by linarith) hBm.le
  exact lt_of_lt_of_le h3gt (hpow3.trans hpowT)

/-- **The growth phase** (proof of Theorem 1): if colour `i` leads every other colour by at
least `z √(n log n)`, then after `⌈C (n/c_i) log n⌉` rounds it holds at least three quarters of
the nodes, with probability at least `1 − C/n`. -/
theorem growth_phase : ∃ z C : ℝ, 0 < z ∧ 0 < C ∧ ∀ (n : ℕ) [NeZero n], C ≤ Real.log n →
    ∀ (k : ℕ) (x : Config n (Fin k)) (i : Fin k),
      (∀ j ≠ i, (count x j : ℝ) + z * √(n * Real.log n) ≤ count x i) →
      1 - C / n ≤ expList (Round n) ⌈C * (n / count x i) * Real.log n⌉₊
        (fun l => if 3 * (n : ℝ) / 4 ≤ count (run x l) i then (1 : ℝ) else 0) := by
  refine ⟨128, 128, by norm_num, by norm_num, ?_⟩
  intro n _ hL k x i hx
  have hL0 : (0 : ℝ) < Real.log n := by linarith
  have hn1 : 1 ≤ n := one_le_of_log_pos hL0
  have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  haveI : Nonempty (Round n) := ⟨fun _ => ((0 : Fin n), (0 : Fin n))⟩
  let g0 : ℝ := 128 * √(n * Real.log n)
  let q : ℝ := 1 + (count x i : ℝ) / (8 * n)
  have hg0_pos : 0 < g0 := by
    unfold g0
    exact mul_pos (by norm_num) (Real.sqrt_pos.mpr (mul_pos hn hL0))
  have hg0_le_n : g0 ≤ (n : ℝ) := by
    have hlogn := log_le_div_of_log_ge hL
    have h16384 : (16384 : ℝ) * Real.log n ≤ n := by linarith
    have hsq : g0 ^ 2 ≤ (n : ℝ) ^ 2 := by
      unfold g0
      rw [mul_pow, Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg n) (by linarith : 0 ≤ Real.log n))]
      have h128 : (128 : ℝ) ^ 2 = 16384 := by norm_num
      rw [h128]
      have hmul : 16384 * Real.log n * n ≤ n * n :=
        mul_le_mul_of_nonneg_right h16384 (Nat.cast_nonneg n)
      have hcomm : (16384 : ℝ) * (n * Real.log n) = 16384 * Real.log n * n := by ring
      have hsqn : (n : ℝ) ^ 2 = n * n := by ring
      linarith
    exact le_of_sq_le_sq hsq (Nat.cast_nonneg n)
  have hcount_ge : g0 ≤ (count x i : ℝ) := by
    by_cases honly : ∀ j : Fin k, j = i
    · have hsingle : ∑ j : Fin k, count x j = count x i :=
        Fintype.sum_eq_single i fun j hj => (hj (honly j)).elim
      have hncount : count x i = n := by
        rw [← hsingle]
        exact sum_count x
      have : (count x i : ℝ) = n := by exact_mod_cast hncount
      linarith [hg0_le_n]
    · obtain ⟨j, hj⟩ := not_forall.mp honly
      have h0 : (0 : ℝ) ≤ count x j := Nat.cast_nonneg _
      unfold g0
      linarith [hx j hj, h0]
  have hcount_pos : (0 : ℝ) < count x i := lt_of_lt_of_le hg0_pos hcount_ge
  have hcount_le : (count x i : ℝ) ≤ n := by exact_mod_cast count_le x i
  have hq_one : (1 : ℝ) ≤ q := by
    unfold q
    have : (0 : ℝ) ≤ (count x i : ℝ) / (8 * n) :=
      div_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) hn.le)
    linarith
  have hg0_one : (1 : ℝ) ≤ g0 := by
    have hsqrt1 : (1 : ℝ) ≤ √(n * Real.log n) := by
      rw [Real.le_sqrt (by norm_num) (mul_nonneg (Nat.cast_nonneg n) hL0.le)]
      have hn1r : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      have hlog1 : (1 : ℝ) ≤ Real.log n := by linarith
      calc (1 : ℝ) ^ 2 = 1 := by norm_num
        _ = 1 * 1 := by ring
        _ ≤ (n : ℝ) * 1 := mul_le_mul_of_nonneg_right hn1r (by norm_num)
        _ ≤ (n : ℝ) * Real.log n := mul_le_mul_of_nonneg_left hlog1 hn.le
    unfold g0
    have hs : (0 : ℝ) ≤ √(n * Real.log n) := Real.sqrt_nonneg _
    calc (1 : ℝ) ≤ √(n * Real.log n) := hsqrt1
      _ = 1 * √(n * Real.log n) := by ring
      _ ≤ 128 * √(n * Real.log n) :=
        mul_le_mul_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 128) hs
  let T : ℕ := ⌈128 * (n / count x i) * Real.log n⌉₊
  have hlog_le_sqrt : Real.log n ≤ √(n * Real.log n) := by
    have hLn : Real.log n ≤ n := (Real.log_le_sub_one_of_pos hn).trans (by linarith)
    rw [Real.le_sqrt (by linarith) (mul_nonneg (Nat.cast_nonneg n) (by linarith))]
    nlinarith [hLn]
  have h128log : 128 * Real.log n ≤ (count x i : ℝ) := by
    have : 128 * Real.log n ≤ g0 := by
      unfold g0
      exact mul_le_mul_of_nonneg_left hlog_le_sqrt (by norm_num)
    exact this.trans hcount_ge
  have harg : 128 * (n / count x i) * Real.log n ≤ (n : ℝ) := by
    have hre : 128 * (n / count x i) * Real.log n
        = 128 * Real.log n * (n / count x i) := by ring
    have hmul : 128 * Real.log n * (n / count x i)
        ≤ (count x i : ℝ) * (n / count x i) :=
      mul_le_mul_of_nonneg_right h128log (div_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg _))
    have hcanc : (count x i : ℝ) * (n / count x i) = n := by field_simp
    linarith
  have hT_le : T ≤ n := by
    change ⌈128 * (n / count x i) * Real.log n⌉₊ ≤ n
    exact Nat.ceil_le.mpr harg
  have hTmul : (T : ℝ) * (2 / (n : ℝ) ^ 2) ≤ 128 / n := by
    have hTcast : (T : ℝ) ≤ n := by exact_mod_cast hT_le
    have hmul : (T : ℝ) * (2 / (n : ℝ) ^ 2) ≤ n * (2 / (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hTcast (by positivity)
    have heq : (n : ℝ) * (2 / (n : ℝ) ^ 2) = 2 / n := by field_simp
    have h2 : (2 : ℝ) / n ≤ 128 / n :=
      div_le_div_of_nonneg_right (by norm_num) hn.le
    linarith
  have hqpow : (n : ℝ) < q ^ T :=
    growth_ratio_pow_gt hL hcount_ge hcount_le
  have hgapT : (n : ℝ) < g0 * q ^ T := by
    have hqt : (0 : ℝ) ≤ q ^ T := pow_nonneg (by linarith) _
    have : q ^ T ≤ g0 * q ^ T := le_mul_of_one_le_left hqt hg0_one
    linarith [hqpow]
  have hx0 : x ∈ growthSet n i (count x i) g0 q 0 := by
    simp only [growthSet, Set.mem_union, Set.mem_setOf_eq, pow_zero, mul_one]
    exact Or.inr ⟨le_rfl, hx⟩
  have hGT (y : Config n (Fin k)) (hy : y ∈ growthSet n i (count x i) g0 q T) :
      3 * (n : ℝ) / 4 ≤ (count y i : ℝ) := by
    simp only [growthSet, Set.mem_union, Set.mem_setOf_eq] at hy
    rcases hy with hy | hy
    · exact hy
    · by_cases honly : ∀ j : Fin k, j = i
      · have hsingle : ∑ j : Fin k, count y j = count y i :=
          Fintype.sum_eq_single i fun j hj => (hj (honly j)).elim
        have hncount : count y i = n := by
          rw [← hsingle]
          exact sum_count y
        have hcast : (count y i : ℝ) = n := by exact_mod_cast hncount
        have h34 : 3 * (n : ℝ) / 4 ≤ n := by
          rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
          linarith [hn]
        linarith
      · exfalso
        obtain ⟨j, hj⟩ := not_forall.mp honly
        have hcj : (0 : ℝ) ≤ count y j := Nat.cast_nonneg _
        have hci : (count y i : ℝ) ≤ n := by exact_mod_cast count_le y i
        linarith [hy.2 j hj, hcj, hci, hgapT]
  have hstep : ∀ t < T, ∀ y ∈ growthSet n i (count x i) g0 q t,
      avg (fun r => by classical exact if step y r ∈ growthSet n i (count x i) g0 q (t + 1) then (0 : ℝ) else 1)
        ≤ 2 / (n : ℝ) ^ 2 := by
    intro t _ht y hy
    by_cases hbig : 3 * (n : ℝ) / 4 ≤ (count y i : ℝ)
    · have hstay := stay_three_quarters hL y i hbig
      have hfail : avg (fun r : Round n =>
          if 3 * (n : ℝ) / 4 ≤ count (step y r) i then (0 : ℝ) else 1) ≤ 1 / (n : ℝ) ^ 2 := by
        have hite : ∀ r : Round n,
            (1 : ℝ) - (if 3 * (n : ℝ) / 4 ≤ count (step y r) i then 1 else 0)
              = (if 3 * (n : ℝ) / 4 ≤ count (step y r) i then 0 else 1) := by
          intro r; split_ifs <;> norm_num
        have havg : avg (fun r => (1 : ℝ) -
            (if 3 * (n : ℝ) / 4 ≤ count (step y r) i then 1 else 0))
            = 1 - avg (fun r => if 3 * (n : ℝ) / 4 ≤ count (step y r) i then (1 : ℝ) else 0) := by
          rw [avg_sub, avg_const]
        have hfun : (fun r : Round n => (1 : ℝ) -
            (if 3 * (n : ℝ) / 4 ≤ count (step y r) i then 1 else 0))
            = fun r => if 3 * (n : ℝ) / 4 ≤ count (step y r) i then 0 else 1 := by
          funext r; exact hite r
        rw [hfun] at havg
        linarith
      refine le_trans (avg_le_avg fun r => ?_) (hfail.trans ?_)
      · by_cases hG : step y r ∈ growthSet n i (count x i) g0 q (t + 1)
        · rw [if_pos hG]
          split_ifs <;> norm_num
        · have hnot : ¬ 3 * (n : ℝ) / 4 ≤ (count (step y r) i : ℝ) := by
            intro hc
            apply hG
            simp only [growthSet, Set.mem_union, Set.mem_setOf_eq]
            exact Or.inl hc
          rw [if_neg hG, if_neg hnot]
      · exact div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) (by positivity)
    · simp only [growthSet, Set.mem_union, Set.mem_setOf_eq] at hy
      rcases hy with hy | hy
      · exact absurd hy hbig
      · have hfactor : g0 * q ^ (t + 1)
            ≤ (g0 * q ^ t) * (1 + (count y i : ℝ) / (8 * n)) := by
          have hq_le : q ≤ 1 + (count y i : ℝ) / (8 * n) := by
            unfold q
            have : (count x i : ℝ) / (8 * n) ≤ (count y i : ℝ) / (8 * n) :=
              div_le_div_of_nonneg_right hy.1 (by positivity)
            linarith
          have hpow : g0 * q ^ (t + 1) = g0 * q ^ t * q := by rw [pow_succ]; ring
          have hmul : g0 * q ^ t * q
              ≤ g0 * q ^ t * (1 + (count y i : ℝ) / (8 * n)) :=
            mul_le_mul_of_nonneg_left hq_le
              (mul_nonneg hg0_pos.le (pow_nonneg (by linarith : (0 : ℝ) ≤ q) _))
          linarith
        have hgap_g : 128 * √(n * Real.log n) ≤ g0 * q ^ t := by
          have hqt : (1 : ℝ) ≤ q ^ t := one_le_pow₀ hq_one
          have hg : g0 ≤ g0 * q ^ t := le_mul_of_one_le_right hg0_pos.le hqt
          unfold g0 at hg
          exact hg
        have hround := growth_round_aux (le_trans (by norm_num : (2 : ℝ) ≤ 128) hL)
          y i (g0 * q ^ t) hgap_g hy.2 (lt_of_not_ge hbig).le
        have hfail : avg (fun r : Round n =>
            if (count y i : ℝ) ≤ count (step y r) i ∧
                ∀ j ≠ i, (count (step y r) j : ℝ)
                    + (g0 * q ^ t) * (1 + (count y i : ℝ) / (8 * n))
                  ≤ count (step y r) i
              then (0 : ℝ) else 1) ≤ 2 / (n : ℝ) ^ 2 := by
          have hite : ∀ r : Round n, (1 : ℝ) -
              (if (count y i : ℝ) ≤ count (step y r) i ∧
                  ∀ j ≠ i, (count (step y r) j : ℝ)
                      + (g0 * q ^ t) * (1 + (count y i : ℝ) / (8 * n))
                    ≤ count (step y r) i
                then (1 : ℝ) else 0)
              = (if (count y i : ℝ) ≤ count (step y r) i ∧
                  ∀ j ≠ i, (count (step y r) j : ℝ)
                      + (g0 * q ^ t) * (1 + (count y i : ℝ) / (8 * n))
                    ≤ count (step y r) i
                then (0 : ℝ) else 1) := by
            intro r; split_ifs <;> norm_num
          have havg : avg (fun r => (1 : ℝ) -
              (if (count y i : ℝ) ≤ count (step y r) i ∧
                  ∀ j ≠ i, (count (step y r) j : ℝ)
                      + (g0 * q ^ t) * (1 + (count y i : ℝ) / (8 * n))
                    ≤ count (step y r) i
                then (1 : ℝ) else 0))
              = 1 - avg (fun r =>
                if (count y i : ℝ) ≤ count (step y r) i ∧
                    ∀ j ≠ i, (count (step y r) j : ℝ)
                        + (g0 * q ^ t) * (1 + (count y i : ℝ) / (8 * n))
                      ≤ count (step y r) i
                  then (1 : ℝ) else 0) := by
            rw [avg_sub, avg_const]
          have hfun : (fun r : Round n => (1 : ℝ) -
              (if (count y i : ℝ) ≤ count (step y r) i ∧
                  ∀ j ≠ i, (count (step y r) j : ℝ)
                      + (g0 * q ^ t) * (1 + (count y i : ℝ) / (8 * n))
                    ≤ count (step y r) i
                then (1 : ℝ) else 0))
              = fun r => if (count y i : ℝ) ≤ count (step y r) i ∧
                  ∀ j ≠ i, (count (step y r) j : ℝ)
                      + (g0 * q ^ t) * (1 + (count y i : ℝ) / (8 * n))
                    ≤ count (step y r) i
                then 0 else 1 := by
            funext r; exact hite r
          rw [hfun] at havg
          linarith
        refine le_trans (avg_le_avg fun r => ?_) hfail
        by_cases hG : step y r ∈ growthSet n i (count x i) g0 q (t + 1)
        · rw [if_pos hG]
          split_ifs <;> norm_num
        · have hnot : ¬ ((count y i : ℝ) ≤ count (step y r) i ∧
              ∀ j ≠ i, (count (step y r) j : ℝ)
                  + (g0 * q ^ t) * (1 + (count y i : ℝ) / (8 * n))
                ≤ count (step y r) i) := by
            intro hev
            apply hG
            simp only [growthSet, Set.mem_union, Set.mem_setOf_eq]
            refine Or.inr ⟨hy.1.trans hev.1, fun j hj => ?_⟩
            linarith [hev.2 j hj, hfactor]
          rw [if_neg hG, if_neg hnot]
  have hesc := expList_escape step (by positivity : (0 : ℝ) ≤ 2 / (n : ℝ) ^ 2) T
    (growthSet n i (count x i) g0 q) x hx0 hstep
  have hcount_fail : expList (Round n) T (fun l =>
      if 3 * (n : ℝ) / 4 ≤ count (run x l) i then (0 : ℝ) else 1)
      ≤ (T : ℝ) * (2 / (n : ℝ) ^ 2) := by
    refine le_trans (expList_le_expList fun l => ?_) hesc
    by_cases hmem : run x l ∈ growthSet n i (count x i) g0 q T
    · have hc := hGT _ hmem
      have hfold : l.foldl step x ∈ growthSet n i (count x i) g0 q T := hmem
      classical
      rw [if_pos hc, if_pos hfold]
    · have hnot : ¬ 3 * (n : ℝ) / 4 ≤ count (run x l) i := by
        intro hc
        apply hmem
        simp only [growthSet, Set.mem_union, Set.mem_setOf_eq]
        exact Or.inl hc
      have hfold : ¬ l.foldl step x ∈ growthSet n i (count x i) g0 q T := hmem
      classical
      rw [if_neg hnot, if_neg hfold]
  have hflip : expList (Round n) T (fun l =>
      if 3 * (n : ℝ) / 4 ≤ count (run x l) i then (1 : ℝ) else 0)
      = 1 - expList (Round n) T (fun l =>
        if 3 * (n : ℝ) / 4 ≤ count (run x l) i then (0 : ℝ) else 1) := by
    have h := expList_one_sub (R := Round n) T (fun l =>
      if 3 * (n : ℝ) / 4 ≤ count (run x l) i then (0 : ℝ) else 1)
    have hfun : (fun l => (1 : ℝ) -
        (if 3 * (n : ℝ) / 4 ≤ count (run x l) i then 0 else 1))
        = fun l => if 3 * (n : ℝ) / 4 ≤ count (run x l) i then 1 else 0 := by
      funext l; split_ifs <;> norm_num
    rw [hfun] at h
    exact h
  rw [hflip]
  linarith [hcount_fail, hTmul]

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
