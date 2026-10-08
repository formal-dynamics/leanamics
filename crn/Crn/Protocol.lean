import Crn.Basic
import Crn.PairCount

/-!
# CRNs are population protocols (CRN-1)

The population protocol of a network `N` runs on `n` agents, each holding a species. In one
interaction it draws a uniformly random ordered pair `(u, v)` of distinct agents and,
independently, a uniformly random reaction `r` of `N`. The pair *reacts* if the species of
`u` and `v` are the reactants of `r`, and then `r` fires; otherwise nothing changes. Drawing
the reaction uniformly is what a common rate constant means when several reactions share
their reactants (as `X + Y → X + B` and `X + Y → Y + B` in approximate majority). We observe
the protocol on count vectors, which do not depend on which agent receives which product.

Key identity (`pair_prob_of_ne`, `pair_prob_of_eq`): the pair has species `{A, B}` with
probability `#A·#B / C(n, 2)`, or `C(#A, 2) / C(n, 2)` if `A = B`. This is the mass-action
propensity divided by the common factor `k·C(n, 2)` (`pair_prob_eq_propensity`). Hence the
protocol reacts with probability `a₀(x) / (k·|N|·C(n, 2))` (`reactProb_eq`), each interaction is
a jump of the mass-action chain with that probability and a no-op otherwise (`ppStep_expect`),
and conditioned on the pair reacting the protocol is exactly the jump chain
(`condStep_eq_jumpKernel`, and `jumpKernel_eq_ppKernel` as kernels on count vectors).
-/

namespace Crn
open Dynamics Finset

variable {S : Type*} [Fintype S] [DecidableEq S] {n : ℕ}

/-- An ordered pair `(u, v)` of distinct agents among `n` (initiator and responder). -/
abbrev AgentPair (n : ℕ) := {p : Fin n × Fin n // p.1 ≠ p.2}

/-- With at least two agents there is a pair of distinct agents. -/
lemma agentPair_nonempty (hn : 2 ≤ n) : Nonempty (AgentPair n) :=
  ⟨⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [Fin.ext_iff]⟩⟩

/-- The scheduler of the population protocol: a uniformly random ordered pair of distinct
agents. -/
noncomputable def pairDist (hn : 2 ≤ n) : Distribution (AgentPair n) :=
  haveI := agentPair_nonempty hn
  Distribution.uniform _

/-- The count vector of a configuration `c` (agent `v` holds species `c v`). -/
def counts (c : Fin n → S) : Counts S n :=
  ⟨fun a => (univ.filter fun v => c v = a).card, by
    rw [← card_eq_sum_card_fiberwise (fun _ _ => mem_univ _), card_univ, Fintype.card_fin]⟩

/-- One draw of the population protocol of `N`: a uniformly random ordered pair of distinct
agents and, independently, a uniformly random reaction of `N`. -/
noncomputable def sampleDist (N : Network S) (hn : 2 ≤ n) :
    Distribution (AgentPair n × N.reactions) :=
  haveI := agentPair_nonempty hn
  haveI := N.nonempty.coe_sort
  Distribution.uniform _

/-- In configuration `c`, the drawn pair reacts by the drawn reaction: the species of the two
agents are the reactants of the reaction. -/
def Reacts (N : Network S) (c : Fin n → S) (ω : AgentPair n × N.reactions) : Prop :=
  s(c ω.1.1.1, c ω.1.1.2) = (ω.2 : Reaction S).reactants

instance instDecidablePredReacts (N : Network S) (c : Fin n → S) :
    DecidablePred (Reacts N c) := fun _ => by
  unfold Reacts
  infer_instance

/-- The count vector after the interaction `ω` from configuration `c`: the drawn reaction
fires if the drawn pair reacts by it. -/
def outcome (N : Network S) (c : Fin n → S) (ω : AgentPair n × N.reactions) : Counts S n :=
  if Reacts N c ω then (counts c).react ω.2 else counts c

/-- One interaction of the population protocol of `N` from configuration `c`, observed on
count vectors. -/
noncomputable def ppStep (N : Network S) (hn : 2 ≤ n) (c : Fin n → S) :
    Distribution (Counts S n) :=
  (sampleDist N hn).map (outcome N c)

/-- One interaction of the population protocol of `N` from configuration `c`, conditioned on
the drawn pair reacting, observed on count vectors. If no pair can react, nothing changes. -/
noncomputable def condStep (N : Network S) (hn : 2 ≤ n) (c : Fin n → S) :
    Distribution (Counts S n) :=
  if h : (sampleDist N hn).prob (Reacts N c) = 0 then Distribution.point (counts c)
  else (condition (sampleDist N hn) (Reacts N c) h).map (outcome N c)

/-- The population protocol of `N` conditioned on reacting pairs, as a kernel on count
vectors: from `x`, one conditioned interaction from some configuration with counts `x` (one
exists; `condStep_eq_jumpKernel` shows that the choice does not matter). -/
noncomputable def ppKernel (N : Network S) (hn : 2 ≤ n) : Kernel (Counts S n) := fun x => by
  classical
  exact if h : ∃ c : Fin n → S, counts c = x then condStep N hn h.choose
    else Distribution.point x

/-! ### Helper lemmas -/

/-- The count of species `a` in a configuration. -/
lemma counts_val (c : Fin n → S) (a : S) :
    (counts c).1 a = (univ.filter fun v => c v = a).card := rfl

/-- Every count vector is the count vector of some configuration. -/
lemma exists_counts_eq (x : Counts S n) : ∃ c : Fin n → S, counts c = x := by
  have hT : Fintype.card (Σ a : S, Fin (x.1 a)) = n := by
    simp [Fintype.card_sigma, x.2]
  let e : (Σ a : S, Fin (x.1 a)) ≃ Fin n := Fintype.equivFinOfCardEq hT
  refine ⟨fun i => (e.symm i).1, Subtype.ext (funext fun a => ?_)⟩
  rw [counts_val, card_filter,
    Equiv.sum_comp e.symm (fun t : Σ a : S, Fin (x.1 a) => if t.1 = a then 1 else 0),
    Fintype.sum_sigma]
  simp [apply_ite Finset.card]

/-- The probability of an event under the scheduler: a counting ratio over the `n·(n - 1)`
ordered pairs of distinct agents. -/
lemma pairDist_prob (hn : 2 ≤ n) (E : AgentPair n → Prop) [DecidablePred E] :
    (pairDist hn).prob E = (univ.filter E).card / (n * (n - 1) : ℕ) := by
  haveI := agentPair_nonempty hn
  rw [pairDist, uniform_prob, card_pairs]

/-- `m·(m - 1) = 2·C(m, 2)`, cast to `ℝ`. -/
lemma cast_mul_pred (m : ℕ) : ((m * (m - 1) : ℕ) : ℝ) = 2 * (m.choose 2 : ℝ) := by
  rw [Nat.cast_choose_two]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · rw [Nat.cast_mul, Nat.cast_sub hm, Nat.cast_one]
    ring

/-- `C(n, 2) > 0` for `n ≥ 2`. -/
lemma choose_two_pos (hn : 2 ≤ n) : (0 : ℝ) < n.choose 2 := by
  exact_mod_cast Nat.choose_pos hn

omit [Fintype S] [DecidableEq S] in
/-- Expectation under one draw of the protocol: the pair is averaged first, then the
reaction. -/
lemma sampleDist_expect (N : Network S) (hn : 2 ≤ n) (F : AgentPair n × N.reactions → ℝ) :
    (sampleDist N hn).expect F =
      (∑ r : N.reactions, (pairDist hn).expect fun p => F (p, r)) / N.reactions.card := by
  haveI := agentPair_nonempty hn
  haveI := N.nonempty.coe_sort
  rw [sampleDist, uniform_prod_expect, Fintype.card_coe]
  rfl

/-- **Key identity** (roadmap CRN-1), `A ≠ B`: a uniformly random ordered pair of distinct
agents has species `{A, B}` with probability `#A·#B / C(n, 2)`. -/
theorem pair_prob_of_ne (hn : 2 ≤ n) (c : Fin n → S) {A B : S} (hAB : A ≠ B) :
    (pairDist hn).prob (fun p => s(c p.1.1, c p.1.2) = s(A, B)) =
      ((counts c).1 A * (counts c).1 B : ℝ) / n.choose 2 := by
  rw [pairDist_prob, card_filter_pairs, card_pairs_of_ne c hAB, cast_mul_pred, counts_val,
    counts_val]
  have := choose_two_pos hn
  push_cast
  field_simp

/-- **Key identity** (roadmap CRN-1), `A = B`: a uniformly random ordered pair of distinct
agents has species `{A, A}` with probability `C(#A, 2) / C(n, 2)`. -/
theorem pair_prob_of_eq (hn : 2 ≤ n) (c : Fin n → S) (A : S) :
    (pairDist hn).prob (fun p => s(c p.1.1, c p.1.2) = s(A, A)) =
      (((counts c).1 A).choose 2 : ℝ) / n.choose 2 := by
  rw [pairDist_prob, card_filter_pairs, card_pairs_of_eq c A, cast_mul_pred, cast_mul_pred,
    counts_val]
  have := choose_two_pos hn
  field_simp

/-- **Key identity** (roadmap CRN-1): the probability that a uniformly random ordered pair of
distinct agents has the reactant species of `r` is the mass-action propensity of `r` divided
by the common factor `k·C(n, 2)`. -/
theorem pair_prob_eq_propensity {k : ℝ} (hk : 0 < k) (hn : 2 ≤ n) (c : Fin n → S)
    (r : Reaction S) :
    (pairDist hn).prob (fun p => s(c p.1.1, c p.1.2) = r.reactants) =
      r.propensity k (counts c) / (k * n.choose 2) := by
  obtain ⟨z, P⟩ := r
  have := choose_two_pos hn
  induction z using Sym2.ind with
  | h A B =>
    dsimp only
    by_cases hAB : A = B
    · subst hAB
      rw [pair_prob_of_eq hn c A, Reaction.propensity_of_eq k _ _ rfl]
      field_simp
    · rw [pair_prob_of_ne hn c hAB, Reaction.propensity_of_ne k _ _ rfl hAB]
      field_simp

/-- The core computation: the expectation of `g(r)` on the event that the drawn pair reacts by
the drawn reaction `r` is `∑ᵣ aᵣ(x)·g(r) / (k·|N|·C(n, 2))`. -/
lemma sampleDist_expect_reacts (N : Network S) {k : ℝ} (hk : 0 < k) (hn : 2 ≤ n)
    (c : Fin n → S) (g : N.reactions → ℝ) :
    (sampleDist N hn).expect (fun ω => if Reacts N c ω then g ω.2 else 0) =
      (∑ r : N.reactions, (r : Reaction S).propensity k (counts c) * g r) /
        (k * N.reactions.card * n.choose 2) := by
  rw [sampleDist_expect]
  have h1 (r : N.reactions) :
      ((pairDist hn).expect fun p => if Reacts N c (p, r) then g (p, r).2 else 0) =
        g r * ((r : Reaction S).propensity k (counts c) / (k * n.choose 2)) := by
    rw [← pair_prob_eq_propensity hk hn c r, prob_eq_expect, ← Distribution.expect_mul]
    congr 1
    funext p
    simp only [Reacts]
    split_ifs <;> simp
  simp only [h1, sum_div]
  exact sum_congr rfl fun r _ => by ring

/-- The drawn pair reacts with probability `a₀(x) / (k·|N|·C(n, 2))`, `x` the counts. -/
theorem reactProb_eq (N : Network S) {k : ℝ} (hk : 0 < k) (hn : 2 ≤ n) (c : Fin n → S) :
    (sampleDist N hn).prob (Reacts N c) =
      N.totalPropensity k (counts c) / (k * N.reactions.card * n.choose 2) := by
  have h := sampleDist_expect_reacts N hk hn c fun _ => 1
  simp only [mul_one] at h
  rw [prob_eq_expect, h, Network.totalPropensity,
    sum_coe_sort N.reactions fun r => r.propensity k (counts c)]

/-- One interaction of the population protocol is a step of the mass-action jump chain with
the probability that the drawn pair reacts, and a no-op otherwise. -/
theorem ppStep_expect (N : Network S) {k : ℝ} (hk : 0 < k) (hn : 2 ≤ n) (c : Fin n → S)
    (f : Counts S n → ℝ) :
    (ppStep N hn c).expect f =
      (1 - (sampleDist N hn).prob (Reacts N c)) * f (counts c) +
        (sampleDist N hn).prob (Reacts N c) * (N.jumpKernel k hk n (counts c)).expect f := by
  have hsplit : (fun ω => f (outcome N c ω)) = fun ω => f (counts c) +
      (if Reacts N c ω then f ((counts c).react ω.2) - f (counts c) else 0) := by
    funext ω
    unfold outcome
    split_ifs <;> ring
  have hC := choose_two_pos hn
  have hR : (0 : ℝ) < N.reactions.card := by exact_mod_cast N.nonempty.card_pos
  have hcore := sampleDist_expect_reacts N hk hn c fun r => f ((counts c).react r) - f (counts c)
  beta_reduce at hcore
  rw [ppStep, Distribution.map_expect, hsplit, Distribution.expect_add, Distribution.expect_const,
    hcore, reactProb_eq N hk hn c, div_mul_eq_mul_div,
    Network.totalPropensity_mul_expect,
    sum_coe_sort N.reactions fun r => r.propensity k (counts c) * (f ((counts c).react r) -
      f (counts c)), Network.totalPropensity]
  simp only [mul_sub, sum_sub_distrib, ← sum_mul]
  field_simp
  ring

/-- **CRN-1, pointwise.** From every configuration, one interaction of the population protocol
conditioned on the pair reacting moves the count vector as one step of the jump chain of
stochastic mass-action kinetics with a common rate constant. -/
theorem condStep_eq_jumpKernel (N : Network S) {k : ℝ} (hk : 0 < k) (hn : 2 ≤ n)
    (c : Fin n → S) :
    condStep N hn c = N.jumpKernel k hk n (counts c) := by
  have hρ := reactProb_eq N hk hn c
  have hC := choose_two_pos hn
  have hR : (0 : ℝ) < N.reactions.card := by exact_mod_cast N.nonempty.card_pos
  have hden : k * N.reactions.card * n.choose 2 ≠ 0 := by positivity
  by_cases h0 : (sampleDist N hn).prob (Reacts N c) = 0
  · have ha : N.totalPropensity k (counts c) = 0 := by
      rw [hρ] at h0
      exact (div_eq_zero_iff.1 h0).resolve_right hden
    simp only [condStep, Network.jumpKernel, dif_pos h0, dif_pos ha]
  · have ha : N.totalPropensity k (counts c) ≠ 0 := fun ha => h0 (by rw [hρ, ha, zero_div])
    refine dist_ext_expect fun f => ?_
    have hout : (fun ω => if Reacts N c ω then f (outcome N c ω) else 0) =
        fun ω => if Reacts N c ω then f ((counts c).react ω.2) else 0 := by
      funext ω
      unfold outcome
      split_ifs <;> rfl
    have hmul := N.totalPropensity_mul_expect hk (counts c) f
    have hcore := sampleDist_expect_reacts N hk hn c fun r => f ((counts c).react r)
    beta_reduce at hcore
    rw [condStep, dif_neg h0, Distribution.map_expect, condition_expect, hout, hcore, hρ,
      sum_coe_sort N.reactions fun r => r.propensity k (counts c) * f ((counts c).react r),
      ← hmul]
    field_simp

/-- **CRN-1** (roadmap; Anderson–Kurtz 2011 for the jump chain). For a count-conserving
bimolecular CRN with a common rate constant `k`, the jump chain of stochastic mass-action
kinetics equals the population protocol picking a uniformly random ordered pair of distinct
agents, conditioned on the pair reacting, as kernels on count vectors. -/
theorem jumpKernel_eq_ppKernel (N : Network S) {k : ℝ} (hk : 0 < k) (hn : 2 ≤ n) :
    N.jumpKernel k hk n = ppKernel N hn := by
  funext x
  have hex : ∃ c : Fin n → S, counts c = x := exists_counts_eq x
  simp only [ppKernel, dif_pos hex]
  rw [condStep_eq_jumpKernel N hk hn, hex.choose_spec]

end Crn
