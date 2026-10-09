import Median.TwoChoicesExpect
import Dynamics.Concentration

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

/-- **Tail bound for one colour** (proof of Theorem 3, with the binomial domination replaced by
an exponential supermartingale at `θ = 1`): if colour `i` has at most `L` nodes, the
probability that it exceeds `L` at some time `t ≤ T` is at most
`exp (−(L − c_i) + (e − 1) T L² / n)`. -/
theorem colour_escape_le [NeZero n] (x : Config n α) (i : α) {L : ℝ}
    (hL : (count x i : ℝ) ≤ L) (T : ℕ) :
    expList (Round n) T (fun l => if ∃ t ≤ T, L < count (run x (l.take t)) i then (1 : ℝ) else 0)
      ≤ exp (-(L - count x i) + (exp 1 - 1) * T * L ^ 2 / n) := by
  sorry

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
  sorry

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
