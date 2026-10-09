import Median.TwoChoicesExpect
import Dynamics.Concentration
import Dynamics.Tail

/-! # The k-party 2-Choices dynamics: an almost linear lower bound

Berenbrink, Clementi, Elsässer, Kling, Mallmann-Trenn and Natale, *Ignore or comply? On breaking
symmetry in consensus* (PODC 2017, arXiv:1702.04921), Section 6, Theorem 3 (`lem:lowerTCstrong`;
proof in Appendix C): let `γ` be a large enough constant, `ℓ` the largest support and
`ℓ' = max {2ℓ, γ log n}`. With probability at least `1 − 1/n` no colour has a support larger than
`ℓ'` during the first `n/(γ ℓ')` rounds. In particular, from a configuration in which every colour
has `O(log n)` nodes (hence `k = Ω(n/log n)` colours), 2-Choices needs `Ω(n/log n)` rounds to reach
consensus (Theorem 1, simplified; roadmap MAJ-6 (a)).

The intermediate facts: most nodes see two different colours and keep their own (`step_of_ne`,
`expected_see_distinct`, `expected_changed_le`); a colour gains at most the nodes that see it
twice (`count_step_le`), whose number is a sum of `n` independent Bernoulli variables of
parameter `(c_i/n)²` (`avg_exp_twice`); hence, for one colour, an exponential supermartingale
gives the tail bound `colour_escape_le`, and a union bound over the colours gives the theorem.
-/

namespace Median.TwoChoices
open Finset Dynamics Real

variable {n : ℕ} {α : Type*} [DecidableEq α]

/-! ### Most nodes keep their own colour -/

/-- The number of nodes seeing colour `i` twice, as a sum of independent coordinates. -/
lemma twice_eq_sum (x : Config n α) (r : Round n) (i : α) :
    (twice x r i : ℝ) = ∑ v : Fin n, (fun p : Fin n × Fin n =>
      if x p.1 = i ∧ x p.2 = i then (1 : ℝ) else 0) (r v) := by
  rw [sum_boole]
  rfl

/-- **The number of nodes seeing colour `i` twice** is a sum of `n` independent Bernoulli
variables of parameter `(c_i/n)²`: its exponential moment is `(1 + (c_i/n)² (e^θ − 1))^n`. -/
theorem avg_exp_twice (x : Config n α) (i : α) (θ : ℝ) :
    avg (fun r : Round n => exp (θ * twice x r i))
      = (1 + ((count x i : ℝ) / n) ^ 2 * (exp θ - 1)) ^ n := by
  rw [show (fun r : Round n => exp (θ * twice x r i)) = fun r : Round n =>
      exp (θ * ∑ v : Fin n, (fun (_ : Fin n) (p : Fin n × Fin n) =>
        if x p.1 = i ∧ x p.2 = i then (1 : ℝ) else 0) v (r v)) from
      funext fun r => by rw [twice_eq_sum]]
  rw [avg_exp_sum (fun (_ : Fin n) (p : Fin n × Fin n) =>
    if x p.1 = i ∧ x p.2 = i then (1 : ℝ) else 0) θ]
  have h : ∀ v : Fin n, avg (fun p : Fin n × Fin n =>
      exp (θ * if x p.1 = i ∧ x p.2 = i then (1 : ℝ) else 0))
        = 1 + ((count x i : ℝ) / n) ^ 2 * (exp θ - 1) := by
    intro v
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      exact v.elim0
    · haveI : NeZero n := ⟨hn.ne'⟩
      have hpt : (fun p : Fin n × Fin n => exp (θ * if x p.1 = i ∧ x p.2 = i then (1 : ℝ) else 0))
          = fun p => 1 + (exp θ - 1) * (if x p.1 = i ∧ x p.2 = i then (1 : ℝ) else 0) := by
        funext p
        split_ifs <;> simp
      rw [hpt, avg_add, avg_const, avg_const_mul, avg_pair]
      ring
  rw [prod_congr rfl fun v _ => h v, prod_const, card_univ, Fintype.card_fin]

variable [Fintype α]

/-- **Most nodes see two different colours** (proof of Theorem 3): the expected number of nodes
whose two samples hold different colours, which therefore keep their own colour (`step_of_ne`),
is `n − ∑_j c_j²/n`. -/
theorem expected_see_distinct [NeZero n] (x : Config n α) :
    avg (fun r : Round n => ((univ.filter fun v => x (r v).1 ≠ x (r v).2).card : ℝ))
      = n - (∑ j : α, (count x j : ℝ) ^ 2) / n := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hind : ∀ a b : α, (if a ≠ b then (1 : ℝ) else 0)
      = 1 - ∑ j : α, if a = j ∧ b = j then (1 : ℝ) else 0 := by
    intro a b
    by_cases hab : a = b
    · subst hab
      simp
    · rw [if_pos hab, sum_eq_zero, sub_zero]
      intro j _
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hab (h1.trans h2.symm)
  have hcard : ∀ r : Round n, ((univ.filter fun v => x (r v).1 ≠ x (r v).2).card : ℝ)
      = ∑ v : Fin n, (fun p : Fin n × Fin n => if x p.1 ≠ x p.2 then (1 : ℝ) else 0) (r v) := by
    intro r
    rw [sum_boole]
  simp_rw [hcard]
  rw [avg_sum]
  have hv : ∀ v : Fin n, avg (fun r : Round n =>
      (fun p : Fin n × Fin n => if x p.1 ≠ x p.2 then (1 : ℝ) else 0) (r v))
        = 1 - ∑ j : α, ((count x j : ℝ) / n) ^ 2 := by
    intro v
    rw [Dynamics.avg_eval n v (fun p : Fin n × Fin n => if x p.1 ≠ x p.2 then (1 : ℝ) else 0)]
    simp_rw [hind]
    rw [avg_sub, avg_const, avg_sum]
    simp_rw [avg_pair]
  simp_rw [hv]
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, sum_div]
  simp_rw [div_pow]
  rw [mul_sub, mul_one, mul_sum]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  field_simp

/-- **Few nodes change colour**: if every colour has at most `ℓ` nodes, the expected number of
nodes that change colour in one round is at most `∑_j c_j²/n ≤ ℓ`. -/
theorem expected_changed_le [NeZero n] (x : Config n α) {ℓ : ℝ}
    (hℓ : ∀ j, (count x j : ℝ) ≤ ℓ) :
    avg (fun r : Round n => ((univ.filter fun v => step x r v ≠ x v).card : ℝ)) ≤ ℓ := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hsub : ∀ r : Round n, ((univ.filter fun v => step x r v ≠ x v).card : ℝ)
      ≤ n - ((univ.filter fun v => x (r v).1 ≠ x (r v).2).card : ℝ) := by
    intro r
    have hdisj : ((univ.filter fun v => step x r v ≠ x v).card
        + (univ.filter fun v => x (r v).1 ≠ x (r v).2).card) ≤ n := by
      rw [← card_union_of_disjoint]
      · exact (card_le_univ _).trans (by rw [Fintype.card_fin])
      · rw [disjoint_filter]
        intro v _ h1 h2
        exact h1 (step_of_ne x r v h2)
    have : ((univ.filter fun v => step x r v ≠ x v).card : ℝ)
        + (univ.filter fun v => x (r v).1 ≠ x (r v).2).card ≤ n := by exact_mod_cast hdisj
    linarith
  calc avg (fun r : Round n => ((univ.filter fun v => step x r v ≠ x v).card : ℝ))
      ≤ avg (fun r : Round n =>
          (n : ℝ) - ((univ.filter fun v => x (r v).1 ≠ x (r v).2).card : ℝ)) :=
        avg_le_avg hsub
    _ = (∑ j : α, (count x j : ℝ) ^ 2) / n := by
        rw [avg_sub, avg_const, expected_see_distinct]
        ring
    _ ≤ ℓ := by
        rw [div_le_iff₀ hn]
        exact sum_sq_le_max x hℓ

/-! ### One colour stays small -/

omit [Fintype α] in
/-- An extinct colour stays extinct for the whole run. -/
lemma count_run_eq_zero (x : Config n α) (i : α) (h : count x i = 0) (l : List (Round n)) :
    count (run x l) i = 0 := by
  induction l generalizing x with
  | nil => simpa [run] using h
  | cons r l ih =>
    rw [run_cons]
    exact ih (step x r) (count_step_eq_zero x r i h)

omit [Fintype α] in
/-- The escape event on `r :: l` is the escape event of length `T` started from `step x r`
(`t = 0` is impossible while `count x i ≤ L`). -/
lemma escape_cons_iff (x : Config n α) (i : α) (r : Round n) (l : List (Round n)) {L : ℝ}
    (hx : (count x i : ℝ) ≤ L) (T : ℕ) :
    (∃ t ≤ T + 1, L < count (run x ((r :: l).take t)) i)
      ↔ ∃ t ≤ T, L < count (run (step x r) (l.take t)) i := by
  constructor
  · rintro ⟨t, ht, hlt⟩
    cases t with
    | zero =>
      simp [run] at hlt
      linarith
    | succ t =>
      refine ⟨t, Nat.le_of_succ_le_succ ht, ?_⟩
      rwa [List.take_succ_cons, run_cons] at hlt
  · rintro ⟨t, ht, hlt⟩
    refine ⟨t + 1, Nat.succ_le_succ ht, ?_⟩
    rwa [List.take_succ_cons, run_cons]

omit [Fintype α] in
/-- **Tail bound for one colour** (proof of Theorem 3, with the binomial domination replaced by
an exponential supermartingale at `θ = 1`): if colour `i` has at most `L` nodes, the
probability that it exceeds `L` at some time `t ≤ T` is at most
`exp (−(L − c_i) + (e − 1) T L² / n)`. -/
theorem colour_escape_le [NeZero n] (x : Config n α) (i : α) {L : ℝ}
    (hL : (count x i : ℝ) ≤ L) (T : ℕ) :
    expList (Round n) T (fun l => if ∃ t ≤ T, L < count (run x (l.take t)) i then (1 : ℝ) else 0)
      ≤ exp (-(L - count x i) + (exp 1 - 1) * T * L ^ 2 / n) := by
  classical
  haveI : Nonempty (Round n) := ⟨fun _ => ((0 : Fin n), (0 : Fin n))⟩
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have he : (1 : ℝ) ≤ exp 1 := by linarith [Real.exp_one_gt_two]
  revert x
  induction T with
  | zero =>
    intro x hL
    rw [expList_zero]
    have hnot : ¬ ∃ t ≤ 0, L < count (run x (([] : List (Round n)).take t)) i := by
      rintro ⟨t, ht, hlt⟩
      obtain rfl : t = 0 := Nat.le_zero.mp ht
      simp [run] at hlt
      linarith
    rw [if_neg hnot]
    exact (exp_pos _).le
  | succ T ih =>
    intro x hL
    rw [expList_succ]
    have hL0 : (0 : ℝ) ≤ L := le_trans (Nat.cast_nonneg _) hL
    have hsq : (count x i : ℝ) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hL 2
    -- one round: the inner expectation is at most `Φ_T(c) · exp (twice)`
    have hstep : ∀ r : Round n,
        expList (Round n) T (fun l =>
            if ∃ t ≤ T + 1, L < count (run x ((r :: l).take t)) i then (1 : ℝ) else 0)
          ≤ exp (-(L - count x i) + (exp 1 - 1) * T * L ^ 2 / n) * exp (twice x r i) := by
      intro r
      have hfun : expList (Round n) T (fun l =>
            if ∃ t ≤ T + 1, L < count (run x ((r :: l).take t)) i then (1 : ℝ) else 0)
          = expList (Round n) T (fun l =>
            if ∃ t ≤ T, L < count (run (step x r) (l.take t)) i then (1 : ℝ) else 0) := by
        congr 1
        funext l
        exact if_congr (escape_cons_iff x i r l hL T) rfl rfl
      rw [hfun]
      have hct : (count (step x r) i : ℝ) ≤ count x i + twice x r i := by
        exact_mod_cast count_step_le x r i
      have hΦ : exp (-(L - count (step x r) i) + (exp 1 - 1) * T * L ^ 2 / n)
          ≤ exp (-(L - count x i) + (twice x r i : ℝ) + (exp 1 - 1) * T * L ^ 2 / n) := by
        apply exp_le_exp.mpr
        linarith
      have hsplit : exp (-(L - count x i) + (twice x r i : ℝ) + (exp 1 - 1) * T * L ^ 2 / n)
          = exp (-(L - count x i) + (exp 1 - 1) * T * L ^ 2 / n) * exp (twice x r i) := by
        rw [← Real.exp_add]
        ring_nf
      by_cases hy : (count (step x r) i : ℝ) ≤ L
      · exact (ih (step x r) hy).trans (hΦ.trans_eq hsplit)
      · have htrue : (fun l : List (Round n) =>
            if ∃ t ≤ T, L < count (run (step x r) (l.take t)) i then (1 : ℝ) else 0)
            = fun _ => 1 := by
          funext l
          rw [if_pos]
          refine ⟨0, Nat.zero_le _, ?_⟩
          simp only [run]
          exact not_le.mp hy
        rw [htrue, expList_const]
        have hone : (1 : ℝ) ≤ exp (-(L - count (step x r) i) + (exp 1 - 1) * T * L ^ 2 / n) := by
          refine le_trans (le_of_eq Real.exp_zero.symm) (exp_le_exp.mpr ?_)
          have hpos : 0 < -(L - (count (step x r) i : ℝ)) := by linarith [not_le.mp hy]
          have hrest : 0 ≤ (exp 1 - 1) * (T : ℝ) * L ^ 2 / n := by
            apply div_nonneg
            · exact mul_nonneg (mul_nonneg (sub_nonneg.mpr he) (Nat.cast_nonneg T)) (sq_nonneg L)
            · exact hn.le
          linarith
        exact hone.trans (hΦ.trans_eq hsplit)
    -- average the exponential moment of `twice`
    have havg : avg (fun r : Round n =>
          exp (-(L - count x i) + (exp 1 - 1) * T * L ^ 2 / n) * exp (twice x r i))
        = exp (-(L - count x i) + (exp 1 - 1) * T * L ^ 2 / n)
          * (1 + ((count x i : ℝ) / n) ^ 2 * (exp 1 - 1)) ^ n := by
      rw [avg_const_mul]
      have hmom := avg_exp_twice x i 1
      simp only [one_mul] at hmom
      rw [hmom]
    have hnn : 0 ≤ 1 + ((count x i : ℝ) / n) ^ 2 * (exp 1 - 1) := by
      have : 0 ≤ ((count x i : ℝ) / n) ^ 2 * (exp 1 - 1) :=
        mul_nonneg (sq_nonneg _) (sub_nonneg.mpr he)
      linarith
    have hbase : 1 + ((count x i : ℝ) / n) ^ 2 * (exp 1 - 1)
        ≤ exp (((count x i : ℝ) / n) ^ 2 * (exp 1 - 1)) := by
      rw [add_comm]
      exact add_one_le_exp _
    have hpow : (1 + ((count x i : ℝ) / n) ^ 2 * (exp 1 - 1)) ^ n
        ≤ exp (((count x i : ℝ) / n) ^ 2 * (exp 1 - 1)) ^ n :=
      pow_le_pow_left₀ hnn hbase n
    have hpow' : exp (((count x i : ℝ) / n) ^ 2 * (exp 1 - 1)) ^ n
        = exp ((n : ℝ) * (((count x i : ℝ) / n) ^ 2 * (exp 1 - 1))) := by
      rw [← exp_nsmul]
      simp
    have hid : (n : ℝ) * (((count x i : ℝ) / n) ^ 2 * (exp 1 - 1))
        = (count x i : ℝ) ^ 2 / n * (exp 1 - 1) := by
      field_simp
    have hcmp : (count x i : ℝ) ^ 2 / n * (exp 1 - 1) ≤ L ^ 2 / n * (exp 1 - 1) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hsq hn.le) (sub_nonneg.mpr he)
    calc avg (fun r => expList (Round n) T (fun l =>
            if ∃ t ≤ T + 1, L < count (run x ((r :: l).take t)) i then (1 : ℝ) else 0))
        ≤ avg (fun r => exp (-(L - count x i) + (exp 1 - 1) * T * L ^ 2 / n)
            * exp (twice x r i)) := avg_le_avg hstep
      _ = exp (-(L - count x i) + (exp 1 - 1) * T * L ^ 2 / n)
            * (1 + ((count x i : ℝ) / n) ^ 2 * (exp 1 - 1)) ^ n := havg
      _ ≤ exp (-(L - count x i) + (exp 1 - 1) * T * L ^ 2 / n)
            * exp ((n : ℝ) * (((count x i : ℝ) / n) ^ 2 * (exp 1 - 1))) := by
          apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
          exact hpow.trans (le_of_eq hpow')
      _ ≤ exp (-(L - count x i) + (exp 1 - 1) * ((T + 1 : ℕ) : ℝ) * L ^ 2 / n) := by
          rw [hid, ← exp_add]
          apply exp_le_exp.mpr
          have hsum : (exp 1 - 1) * (T : ℝ) * L ^ 2 / n + L ^ 2 / n * (exp 1 - 1)
              = (exp 1 - 1) * ((T + 1 : ℕ) : ℝ) * L ^ 2 / n := by
            push_cast
            field_simp
          linarith

/-! ### Theorem 3 -/

/-- **Theorem 3** (`lem:lowerTCstrong`): there is a constant `γ₀` such that for every
`γ ≥ γ₀`, every configuration whose colours have at most `ℓ` nodes each, with
`ℓ' = max {2ℓ, γ log n}`, and every `T < n/(γ ℓ')`, the probability that some colour has more
than `ℓ'` nodes at some time `t ≤ T` is at most `1/n`. -/
theorem lower_bound_strong : ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ γ : ℝ, γ₀ ≤ γ →
    ∀ (n : ℕ) [NeZero n] (k : ℕ) (x : Config n (Fin k)) (ℓ : ℝ), (∀ i, (count x i : ℝ) ≤ ℓ) →
      ∀ T : ℕ, (T : ℝ) < n / (γ * max (2 * ℓ) (γ * Real.log n)) →
        expList (Round n) T (fun l =>
          if ∃ t ≤ T, ∃ i, max (2 * ℓ) (γ * Real.log n) < count (run x (l.take t)) i
          then (1 : ℝ) else 0) ≤ 1 / n := by
  classical
  refine ⟨8, by norm_num, fun γ hγ n _ k x ℓ hx T hT => ?_⟩
  have hn0 : n ≠ 0 := NeZero.ne n
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hL0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  have hγpos : (0 : ℝ) < γ := by linarith
  -- the node `0` has some colour, so `ℓ ≥ 1` and `ℓ' ≥ 2`
  set ℓ' : ℝ := max (2 * ℓ) (γ * Real.log n) with hℓ'def
  have hℓ1 : (1 : ℝ) ≤ ℓ := by
    let v : Fin n := ⟨0, Nat.pos_of_ne_zero hn0⟩
    have hc : 0 < count x (x v) := by
      unfold count
      exact card_pos.mpr ⟨v, by simp⟩
    have : (1 : ℝ) ≤ count x (x v) := by exact_mod_cast Nat.succ_le_of_lt hc
    exact this.trans (hx (x v))
  have hℓ'2 : (2 : ℝ) ≤ ℓ' := by
    have : (2 : ℝ) * ℓ ≤ ℓ' := by rw [hℓ'def]; exact le_max_left _ _
    linarith
  have hℓ'pos : (0 : ℝ) < ℓ' := by linarith
  have hden : 0 < γ * ℓ' := by positivity
  -- only colours that are already present can ever exceed `ℓ'`
  let P := (univ : Finset (Fin k)).filter fun i => 0 < count x i
  have hPsub : P ⊆ univ.image x := by
    intro i hi
    have hpos : 0 < count x i := (mem_filter.mp hi).2
    rw [count, card_pos] at hpos
    obtain ⟨v, hv⟩ := hpos
    exact mem_image.mpr ⟨v, mem_univ v, (mem_filter.mp hv).2⟩
  have hPcard : P.card ≤ n := by
    calc P.card ≤ (univ.image x).card := card_le_card hPsub
      _ ≤ (univ : Finset (Fin n)).card := card_image_le
      _ = n := by simp
  have hpt : ∀ l : List (Round n),
      (if ∃ t ≤ T, ∃ i, ℓ' < count (run x (l.take t)) i then (1 : ℝ) else 0)
        ≤ ∑ i ∈ P, if ∃ t ≤ T, ℓ' < count (run x (l.take t)) i then (1 : ℝ) else 0 := by
    intro l
    by_cases hE : ∃ t ≤ T, ∃ i, ℓ' < count (run x (l.take t)) i
    · rw [if_pos hE]
      obtain ⟨t, ht, i, hi⟩ := hE
      have hpos : 0 < count x i := by
        by_contra h0
        have h00 : count x i = 0 := Nat.eq_zero_of_not_pos h0
        have hrun := count_run_eq_zero x i h00 (l.take t)
        rw [hrun] at hi
        have : ℓ' < 0 := by exact_mod_cast hi
        linarith
      have hiP : i ∈ P := mem_filter.mpr ⟨mem_univ i, hpos⟩
      have hone : (if ∃ t ≤ T, ℓ' < count (run x (l.take t)) i then (1 : ℝ) else 0) = 1 :=
        if_pos ⟨t, ht, hi⟩
      calc (1 : ℝ)
          = (if ∃ t ≤ T, ℓ' < count (run x (l.take t)) i then (1 : ℝ) else 0) := hone.symm
        _ ≤ ∑ j ∈ P, if ∃ t ≤ T, ℓ' < count (run x (l.take t)) j then (1 : ℝ) else 0 := by
            refine single_le_sum
              (f := fun j => if ∃ t ≤ T, ℓ' < count (run x (l.take t)) j then (1 : ℝ) else 0)
              (fun j _ => by split_ifs <;> norm_num) hiP
    · rw [if_neg hE]
      exact sum_nonneg fun j _ => by split_ifs <;> norm_num
  -- each present colour escapes with probability at most `1/n²`
  have hcolour : ∀ i ∈ P, expList (Round n) T (fun l =>
      if ∃ t ≤ T, ℓ' < count (run x (l.take t)) i then (1 : ℝ) else 0) ≤ 1 / (n : ℝ) ^ 2 := by
    intro i hi
    have hc : (count x i : ℝ) ≤ ℓ := hx i
    have hc2 : (count x i : ℝ) ≤ ℓ' / 2 := by
      have hℓle : ℓ ≤ ℓ' / 2 := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2), mul_comm, hℓ'def]
        exact le_max_left _ _
      exact hc.trans hℓle
    have hesc := colour_escape_le x i (L := ℓ') (hc2.trans (by linarith : ℓ' / 2 ≤ ℓ')) T
    -- the exponent is at most `-2 log n`
    have hTγ : (T : ℝ) * (γ * ℓ') < n := by rwa [lt_div_iff₀ hden] at hT
    have hTℓ : (T : ℝ) * ℓ' < n / γ := by
      rw [lt_div_iff₀ hγpos]
      linarith [show (T : ℝ) * ℓ' * γ = T * (γ * ℓ') by ring]
    have hfrac : (T : ℝ) * ℓ' ^ 2 / n < ℓ' / γ := by
      calc (T : ℝ) * ℓ' ^ 2 / n = T * ℓ' * ℓ' / n := by ring
        _ < (n / γ) * ℓ' / n :=
            div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hTℓ hℓ'pos) hn
        _ = ℓ' / γ := by field_simp
    have hδ : (exp 1 - 1) * ((T : ℝ) * ℓ' ^ 2 / n) < ℓ' / 4 := by
      have he1 : exp 1 - 1 < 2 := by linarith [Real.exp_one_lt_three]
      have he0 : 0 < exp 1 - 1 := by linarith [Real.exp_one_gt_two]
      have h1 : (exp 1 - 1) * ((T : ℝ) * ℓ' ^ 2 / n) < (exp 1 - 1) * (ℓ' / γ) :=
        mul_lt_mul_of_pos_left hfrac he0
      have h2 : (exp 1 - 1) * (ℓ' / γ) ≤ 2 * (ℓ' / γ) :=
        mul_le_mul_of_nonneg_right he1.le (by positivity)
      have h3 : 2 * (ℓ' / γ) ≤ ℓ' / 4 := by
        have h24 : (2 : ℝ) / γ ≤ 1 / 4 := by
          rw [div_le_div_iff₀ hγpos (by norm_num)]
          nlinarith
        calc 2 * (ℓ' / γ) = (2 / γ) * ℓ' := by ring
          _ ≤ (1 / 4) * ℓ' := mul_le_mul_of_nonneg_right h24 hℓ'pos.le
          _ = ℓ' / 4 := by ring
      linarith
    have hexple : -(ℓ' - (count x i : ℝ)) + (exp 1 - 1) * T * ℓ' ^ 2 / n
        ≤ -(2 * Real.log n) := by
      have hlt : -(ℓ' - (count x i : ℝ)) + (exp 1 - 1) * T * ℓ' ^ 2 / n < -ℓ' / 4 := by
        have hhalf : -(ℓ' - (count x i : ℝ)) ≤ -ℓ' / 2 := by linarith
        have hassoc : (exp 1 - 1) * (T : ℝ) * ℓ' ^ 2 / n
            = (exp 1 - 1) * ((T : ℝ) * ℓ' ^ 2 / n) := by ring
        linarith
      have hquarter : -ℓ' / 4 ≤ -(2 * Real.log n) := by
        have h1 : -ℓ' / 4 ≤ -(γ * Real.log n) / 4 := by
          have : γ * Real.log n ≤ ℓ' := by rw [hℓ'def]; exact le_max_right _ _
          have := div_le_div_of_nonneg_right this (by norm_num : (0 : ℝ) ≤ 4)
          linarith
        have h2 : -(γ * Real.log n) / 4 ≤ -(2 * Real.log n) := by
          have hγ4 : (2 : ℝ) ≤ γ / 4 := by linarith
          have : 2 * Real.log n ≤ γ * Real.log n / 4 := by
            calc 2 * Real.log n ≤ (γ / 4) * Real.log n := mul_le_mul_of_nonneg_right hγ4 hL0
              _ = γ * Real.log n / 4 := by ring
          linarith
        linarith
      exact le_trans hlt.le hquarter
    calc expList (Round n) T (fun l =>
          if ∃ t ≤ T, ℓ' < count (run x (l.take t)) i then (1 : ℝ) else 0)
        ≤ exp (-(ℓ' - count x i) + (exp 1 - 1) * T * ℓ' ^ 2 / n) := hesc
      _ ≤ exp (-(2 * Real.log n)) := exp_le_exp.mpr hexple
      _ = 1 / (n : ℝ) ^ 2 := exp_neg_two_log hn1
  calc expList (Round n) T (fun l =>
        if ∃ t ≤ T, ∃ i, ℓ' < count (run x (l.take t)) i then (1 : ℝ) else 0)
      ≤ expList (Round n) T (fun l =>
        ∑ i ∈ P, if ∃ t ≤ T, ℓ' < count (run x (l.take t)) i then (1 : ℝ) else 0) :=
        expList_le_expList hpt
    _ = ∑ i ∈ P, expList (Round n) T (fun l =>
        if ∃ t ≤ T, ℓ' < count (run x (l.take t)) i then (1 : ℝ) else 0) :=
        expList_finset_sum T P _
    _ ≤ ∑ _i ∈ P, (1 / (n : ℝ) ^ 2) := sum_le_sum hcolour
    _ = P.card * (1 / (n : ℝ) ^ 2) := by
        rw [sum_const]
        simp [nsmul_eq_mul]
    _ ≤ n * (1 / (n : ℝ) ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast hPcard
    _ = 1 / n := by field_simp

/-- **The `Ω(n/log n)` lower bound** (Theorem 1, simplified; roadmap MAJ-6 (a)): for every
`β > 0` there is a constant `C` such that, from any configuration in which every colour has at
most `β log n` nodes, 2-Choices has not reached consensus (all nodes on one colour `c`) during
the first `T` rounds with probability at least `1 − 1/n`, for every `T` with
`(T + 1) C log n < n`. -/
theorem consensus_time_lower (β : ℝ) (hβ : 0 < β) : ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) [NeZero n] (k : ℕ) (x : Config n (Fin k)), (∀ i, (count x i : ℝ) ≤ β * Real.log n) →
      ∀ T : ℕ, ((T : ℝ) + 1) * C * Real.log n < n →
        expList (Round n) T (fun l =>
          if ∃ t ≤ T, ∃ c, run x (l.take t) = fun _ => c then (1 : ℝ) else 0) ≤ 1 / n := by
  obtain ⟨γ₀, hγ₀, h⟩ := lower_bound_strong
  set γ := max γ₀ (max (2 * β) 1) with hγ
  have hγ1 : 1 ≤ γ := (le_max_right _ _).trans (le_max_right _ _)
  have hγβ : 2 * β ≤ γ := (le_max_left _ _).trans (le_max_right _ _)
  refine ⟨γ ^ 2, by positivity, fun n _ k x hx T hT => ?_⟩
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have hL0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  -- `log n > 0`: otherwise no colour could hold the node `0`
  have hLpos : 0 < Real.log n := by
    rcases hL0.lt_or_eq with h0 | h0
    · exact h0
    · exfalso
      have h1 := hx (x ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩)
      rw [← h0, mul_zero] at h1
      have : 0 < count x (x ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩) := by
        unfold count
        exact card_pos.mpr ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩, by simp⟩
      have : (0 : ℝ) < count x (x ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩) := by exact_mod_cast this
      linarith
  have hmax : max (2 * (β * Real.log n)) (γ * Real.log n) = γ * Real.log n := by
    rw [max_eq_right]
    nlinarith
  have hT' : (T : ℝ) < n / (γ * max (2 * (β * Real.log n)) (γ * Real.log n)) := by
    rw [hmax, lt_div_iff₀ (by positivity)]
    nlinarith
  have hbound := h γ (le_max_left _ _) n k x (β * Real.log n) hx T hT'
  refine le_trans (expList_le_expList fun l => ?_) hbound
  by_cases hc : ∃ t ≤ T, ∃ c, run x (l.take t) = fun _ => c
  · obtain ⟨t, ht, c, hcv⟩ := hc
    have hcount : count (run x (l.take t)) c = n := by
      unfold count
      rw [filter_true_of_mem fun v _ => congrFun hcv v, card_univ, Fintype.card_fin]
    have hlt : max (2 * (β * Real.log n)) (γ * Real.log n) < count (run x (l.take t)) c := by
      rw [hmax, hcount]
      have h1 : γ * Real.log n ≤ γ ^ 2 * Real.log n := by
        have := mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ γ) (by linarith : (0 : ℝ) ≤ γ - 1))
          hL0
        nlinarith
      have hT1 : (1 : ℝ) ≤ T + 1 := by have := Nat.cast_nonneg (α := ℝ) T; linarith
      have h2 : γ ^ 2 * Real.log n ≤ ((T : ℝ) + 1) * γ ^ 2 * Real.log n := by
        have : 0 ≤ γ ^ 2 * Real.log n := by positivity
        nlinarith
      linarith
    rw [if_pos ⟨t, ht, c, hcv⟩, if_pos ⟨t, ht, c, hlt⟩]
  · rw [if_neg hc]
    split_ifs <;> norm_num

end Median.TwoChoices
