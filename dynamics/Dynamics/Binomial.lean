import Mathlib.Probability.Distributions.Binomial
import Dynamics.Relations

/-!
# The binomial law

`Distribution.binomial n p` is the law of the number of successes in `n` independent trials of
success probability `p`: a distribution on `{0, …, n}` (`Fin (n + 1)`) with weight
`C(n, k) p^k (1 - p)^(n - k)` at `k`. Its weights are those of Mathlib's binomial distribution
`ProbabilityTheory.binomial` (`Distribution.binomial_weight_eq`), and it is the law of the number
of heads of independent Bernoulli(`p`) coins indexed by any finite type with `n` elements
(`Distribution.independent_bernoulli_map_countFin`, `Distribution.independent_bernoulli_map_card`),
so its mean is `n p` (`Distribution.binomial_expect_val`). The number of elements with a property
is `countFin`, an element of `{0, …, n}`.

Two facts used on the way are stated in general: the indicator of an event is a Bernoulli coin
with the probability of the event (`Distribution.map_decide_eq_bernoulli`), and an independent
product transported coordinatewise is the independent product of the transported coordinates
(`Distribution.independent_map_pi`).
-/

namespace Dynamics
open Finset

/-- The number of elements of a finite type `ι` with the property `P`, as an element of
`{0, …, |ι|}`. -/
def countFin {ι : Type*} [Fintype ι] (P : ι → Prop) [DecidablePred P] :
    Fin (Fintype.card ι + 1) :=
  ⟨(univ.filter P).card, Nat.lt_succ_of_le ((card_filter_le _ _).trans card_univ.le)⟩

@[simp] lemma countFin_val {ι : Type*} [Fintype ι] (P : ι → Prop) [DecidablePred P] :
    (countFin P : ℕ) = (univ.filter P).card := rfl

namespace Distribution
variable {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]

/-- The **binomial law** `Bin(n, p)` on `{0, …, n}`: weight `C(n, k) p^k (1 - p)^(n - k)` at
`k`, the law of the number of successes in `n` independent trials of success probability
`p`. -/
noncomputable def binomial (n : ℕ) (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    Distribution (Fin (n + 1)) where
  weight k := n.choose k * p ^ (k : ℕ) * (1 - p) ^ (n - k)
  nonneg k := by
    have : 0 ≤ 1 - p := sub_nonneg.2 h1
    positivity
  sum_one := by
    rw [Fin.sum_univ_eq_sum_range (fun k => (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k))]
    have h := add_pow p (1 - p) n
    rw [show p + (1 - p) = 1 by ring, one_pow] at h
    exact (sum_congr rfl fun k _ => by ring).trans h.symm

/-- The weights of `binomial n p` are those of Mathlib's binomial distribution `Bin(n, p)` on
`ℕ` (`ProbabilityTheory.binomial`, with `p` in the unit interval). -/
theorem binomial_weight_eq (n : ℕ) (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (k : Fin (n + 1)) :
    (binomial n p h0 h1).weight k =
      (ProbabilityTheory.binomial n ⟨p, h0, h1⟩).real {(k : ℕ)} := by
  rw [ProbabilityTheory.binomial_real_singleton]
  rfl

/-- The indicator of an event `P` is a Bernoulli coin with the probability of `P`. -/
theorem map_decide_eq_bernoulli (p : Distribution α) (P : α → Prop) [DecidablePred P] :
    p.map (fun a => decide (P a)) = bernoulli (p.prob P) (p.prob_nonneg P) (p.prob_le_one P) := by
  refine ext_expect fun g => ?_
  have hg : (fun a => g (decide (P a))) =
      fun a => g false + (g true - g false) * (if P a then 1 else 0) := by
    funext a
    by_cases h : P a <;> simp [h]
  rw [map_expect, hg, expect_add, expect_const, expect_mul, ← prob_eq_expect]
  simp only [expect, bernoulli, Fintype.sum_bool, if_true, Bool.false_eq_true, if_false]
  ring

variable [DecidableEq ι]

/-- An independent product transported coordinatewise, by `f i` on coordinate `i`, is the
independent product of the transported coordinates. -/
theorem independent_map_pi (q : ι → Distribution α) (f : ι → α → β) :
    (independent q).map (fun x i => f i (x i)) = independent fun i => (q i).map (f i) := by
  classical
  refine ext fun y => ?_
  simp only [map, independent]
  rw [Fintype.prod_sum]
  refine sum_congr rfl fun x _ => ?_
  by_cases hx : (fun i => f i (x i)) = y
  · rw [if_pos hx]
    exact (prod_congr rfl fun i _ => if_pos (congrFun hx i)).symm
  · rw [if_neg hx]
    obtain ⟨i, hi⟩ : ∃ i, f i (x i) ≠ y i := by
      by_contra! h
      exact hx (funext h)
    exact (prod_eq_zero (mem_univ i) (if_neg hi)).symm

/-- Exactly `C(|ι|, k)` maps `ι → Bool` take the value `true` `k` times. -/
theorem card_countFin_eq (k : Fin (Fintype.card ι + 1)) :
    (univ.filter fun ω : ι → Bool => (countFin fun i => ω i = true) = k).card =
      (Fintype.card ι).choose k := by
  have hc := card_powersetCard (k : ℕ) (univ : Finset ι)
  rw [card_univ] at hc
  rw [← hc]
  refine card_nbij' (fun ω => univ.filter fun i => ω i = true) (fun S i => decide (i ∈ S))
    (fun ω hω => ?_) (fun S hS => ?_) (fun ω _ => ?_) (fun S _ => ?_)
  · rw [mem_coe, mem_filter, Fin.ext_iff, countFin_val] at hω
    rw [mem_coe, mem_powersetCard]
    exact ⟨subset_univ _, hω.2⟩
  · rw [mem_coe, mem_powersetCard] at hS
    rw [mem_coe, mem_filter, Fin.ext_iff, countFin_val]
    refine ⟨mem_univ _, ?_⟩
    simp only [decide_eq_true_eq, filter_mem_eq_inter, univ_inter, hS.2]
  · funext i
    by_cases h : ω i = true <;> simp [h]
  · ext i
    simp

/-- **The number of heads is binomial.** The number of heads of independent Bernoulli(`p`) coins
indexed by a finite type `ι` has the binomial law `Bin(|ι|, p)`. -/
theorem independent_bernoulli_map_countFin (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    (independent fun _ : ι => bernoulli p h0 h1).map (fun ω => countFin fun i => ω i = true) =
      binomial (Fintype.card ι) p h0 h1 := by
  classical
  refine ext fun k => ?_
  have hprod (ω : ι → Bool) : ∏ i, (bernoulli p h0 h1).weight (ω i) =
      p ^ (countFin fun i => ω i = true : ℕ) *
        (1 - p) ^ (Fintype.card ι - (countFin fun i => ω i = true : ℕ)) := by
    have hcard := card_filter_add_card_filter_not (s := univ) (fun i => ω i = true)
    rw [card_univ] at hcard
    simp only [bernoulli, prod_ite, prod_const, countFin_val]
    congr 2
    omega
  simp only [map, independent]
  rw [← sum_filter]
  rw [sum_congr rfl fun ω hω => by rw [hprod, (mem_filter.1 hω).2], sum_const,
    card_countFin_eq, nsmul_eq_mul]
  simp only [binomial]
  ring

/-- `independent_bernoulli_map_countFin` for a finite type with `m` elements, the number of heads
counted in `{0, …, m}`. -/
theorem independent_bernoulli_map_card {m : ℕ} (hm : Fintype.card ι = m) (p : ℝ) (h0 : 0 ≤ p)
    (h1 : p ≤ 1) :
    (independent fun _ : ι => bernoulli p h0 h1).map
        (fun ω => Fin.cast (congrArg (· + 1) hm) (countFin fun i => ω i = true)) =
      binomial m p h0 h1 := by
  subst hm
  exact independent_bernoulli_map_countFin p h0 h1

end Distribution

namespace Distribution

/-- **The mean of the binomial law**: `𝔼[Bin(n, p)] = n p`, the expected number of heads of `n`
independent coins. -/
theorem binomial_expect_val (n : ℕ) (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    (binomial n p h0 h1).expect (fun k => (k : ℝ)) = n * p := by
  classical
  have hcoin : (bernoulli p h0 h1).expect (fun b => if b = true then 1 else 0) = p := by
    simp [expect, bernoulli]
  rw [← independent_bernoulli_map_card (Fintype.card_fin n) p h0 h1, map_expect]
  have hcount (ω : Fin n → Bool) :
      (((Fin.cast (congrArg (· + 1) (Fintype.card_fin n))
        (countFin fun i => ω i = true) : Fin (n + 1)) : ℕ) : ℝ) =
        ∑ i, if ω i = true then 1 else 0 := by
    rw [Fin.val_cast, countFin_val, sum_boole]
  simp only [hcount, expect_sum]
  rw [sum_congr rfl fun i _ => independent_expect_eval (fun _ : Fin n => bernoulli p h0 h1) i
    fun b => if b = true then (1 : ℝ) else 0]
  simp [hcoin]

end Distribution
end Dynamics
