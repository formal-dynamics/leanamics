import Dynamics.Kernel
import Crn.DistLemmas

/-!
# Count-conserving bimolecular CRNs and their mass-action jump chain (CRN-1)

A chemical reaction network (CRN) on a finite set `S` of species is a finite set of reactions.
We consider the count-conserving bimolecular ones, `A + B → C + D`: two reactant molecules are
replaced by two product molecules. The total number `n` of molecules is then conserved, and the
state space is the finite set `Counts S n` of count vectors.

Under stochastic mass-action kinetics with a common rate constant `k`, reaction `r` fires at
rate `aᵣ(x) = k · ∏ₐ C(xₐ, νₐ)`, where `ν` counts the reactants of each species: `k·#A·#B` for
`A + B` with `A ≠ B` and `k·C(#A, 2)` for `A + A`, that is `k` times the number of unordered
pairs of molecules that can react (Gillespie's combinatorial form, as in Doty, SODA 2014, §2).
The continuous-time Markov chain on counts (Anderson–Kurtz 2011) leaves `x` at rate
`a₀(x) = ∑ᵣ aᵣ(x)`; its jump chain fires `r` with probability `aᵣ(x) / a₀(x)`. A terminal
state (`a₀(x) = 0`) is made absorbing.
-/

namespace Crn
open Dynamics Finset

/-- A count-conserving bimolecular reaction `A + B → C + D` (roadmap CRN-1): the unordered pair
of reactant species `s(A, B)` is replaced by the unordered pair of product species `s(C, D)`.
Equal species (`A = B` or `C = D`) are allowed. -/
structure Reaction (S : Type*) where
  /-- The two reactant species. -/
  reactants : Sym2 S
  /-- The two product species. -/
  products : Sym2 S
  deriving DecidableEq

/-- A count-conserving bimolecular CRN (roadmap CRN-1): a nonempty finite set of reactions, none
of which leaves the counts unchanged. All reactions share one rate constant, which is a
parameter of the kinetics (`Network.jumpKernel`). -/
structure Network (S : Type*) where
  /-- The reactions. -/
  reactions : Finset (Reaction S)
  /-- There is at least one reaction. -/
  nonempty : reactions.Nonempty
  /-- No reaction is a no-op. -/
  nontrivial : ∀ r ∈ reactions, r.reactants ≠ r.products

variable {S : Type*} [Fintype S] [DecidableEq S] {n : ℕ}

/-- Count vectors of `n` molecules: the number of molecules of each species, summing to `n`. -/
abbrev Counts (S : Type*) [Fintype S] (n : ℕ) := {x : S → ℕ // ∑ a, x a = n}

/-- Count vectors of `n` molecules form a finite type, enumerated by `Finset.piAntidiag`. -/
instance Counts.instFintype : Fintype (Counts S n) :=
  Fintype.subtype (piAntidiag univ n) (by simp)

namespace Reaction

/-- Number of reactant molecules of species `a` (`0`, `1` or `2`). -/
def consumed (r : Reaction S) (a : S) : ℕ := r.reactants.toMultiset.count a

/-- Number of product molecules of species `a` (`0`, `1` or `2`). -/
def produced (r : Reaction S) (a : S) : ℕ := r.products.toMultiset.count a

omit [Fintype S] in
/-- A reaction consumes two molecules. -/
lemma sum_consumed [Fintype S] (r : Reaction S) : ∑ a, r.consumed a = 2 := by
  simp only [consumed]
  rw [Multiset.sum_count_eq_card (fun _ _ => mem_univ _), Sym2.card_toMultiset]

omit [Fintype S] in
/-- A reaction produces two molecules. -/
lemma sum_produced [Fintype S] (r : Reaction S) : ∑ a, r.produced a = 2 := by
  simp only [produced]
  rw [Multiset.sum_count_eq_card (fun _ _ => mem_univ _), Sym2.card_toMultiset]

/-- Stochastic mass-action propensity of `r` at counts `x` with rate constant `k`, in
Gillespie's combinatorial form `k · ∏ₐ C(xₐ, νₐ)`, `ν` the reactant multiplicities
(`propensity_of_ne`, `propensity_of_eq`). It vanishes iff `r` lacks reactant molecules. -/
noncomputable def propensity (k : ℝ) (r : Reaction S) (x : Counts S n) : ℝ :=
  k * ∏ a, ((x.1 a).choose (r.consumed a) : ℝ)

omit [Fintype S] in
/-- Multiplicity of the species `a` in the unordered pair `s(A, B)`. -/
lemma count_toMultiset_mk (A B a : S) :
    (s(A, B) : Sym2 S).toMultiset.count a =
      (if a = A then 1 else 0) + (if a = B then 1 else 0) := by
  simp only [Sym2.toMultiset, Sym2.lift_mk, Multiset.coe_count, List.count_cons, List.count_nil,
    beq_iff_eq]
  rcases eq_or_ne a A with rfl | ha <;> rcases eq_or_ne a B with rfl | hb <;> simp_all [eq_comm]

/-- A reaction with nonzero propensity has all its reactant molecules. -/
lemma consumed_le_of_propensity_ne_zero {k : ℝ} {r : Reaction S} {x : Counts S n}
    (h : r.propensity k x ≠ 0) (a : S) : r.consumed a ≤ x.1 a := by
  by_contra hlt
  apply h
  rw [propensity, prod_eq_zero (mem_univ a) (by simp [Nat.choose_eq_zero_of_lt (not_le.1 hlt)]),
    mul_zero]

/-- Propensities are nonnegative for a nonnegative rate constant. -/
lemma propensity_nonneg {k : ℝ} (hk : 0 ≤ k) (r : Reaction S) (x : Counts S n) :
    0 ≤ r.propensity k x :=
  mul_nonneg hk (prod_nonneg fun _ _ => Nat.cast_nonneg _)

/-- For `A + B → ⋯` with `A ≠ B` the propensity is `k·#A·#B`. -/
theorem propensity_of_ne (k : ℝ) (r : Reaction S) (x : Counts S n) {A B : S}
    (hr : r.reactants = s(A, B)) (hAB : A ≠ B) :
    r.propensity k x = k * x.1 A * x.1 B := by
  have hc (a : S) : ((x.1 a).choose (r.consumed a) : ℝ) =
      (if a = A then (x.1 A : ℝ) else 1) * (if a = B then (x.1 B : ℝ) else 1) := by
    rw [consumed, hr, count_toMultiset_mk]
    by_cases ha : a = A
    · subst ha
      simp [hAB]
    · by_cases hb : a = B
      · subst hb
        simp [ha]
      · simp [ha, hb]
  simp only [propensity, hc, prod_mul_distrib, Fintype.prod_ite_eq']
  ring

/-- For `A + A → ⋯` the propensity is `k·C(#A, 2)`. -/
theorem propensity_of_eq (k : ℝ) (r : Reaction S) (x : Counts S n) {A : S}
    (hr : r.reactants = s(A, A)) :
    r.propensity k x = k * (x.1 A).choose 2 := by
  have hc (a : S) : ((x.1 a).choose (r.consumed a) : ℝ) =
      if a = A then ((x.1 A).choose 2 : ℝ) else 1 := by
    rw [consumed, hr, count_toMultiset_mk]
    by_cases ha : a = A
    · subst ha
      simp
    · simp [ha]
  simp only [propensity, hc, Fintype.prod_ite_eq']

end Reaction

namespace Counts

/-- The counts after one firing of `r`: `xₐ - νₐ + ν'ₐ` with `ν`, `ν'` the reactant and product
multiplicities. If `r` lacks reactant molecules, `x` is returned unchanged (such a firing has
probability zero in every chain below). -/
def react (x : Counts S n) (r : Reaction S) : Counts S n :=
  if h : ∀ a, r.consumed a ≤ x.1 a then
    ⟨fun a => x.1 a - r.consumed a + r.produced a, by
      have h2 : 2 ≤ n := by
        rw [← x.2, ← r.sum_consumed]
        exact sum_le_sum fun a _ => h a
      rw [sum_add_distrib, sum_tsub_distrib _ fun a _ => h a, x.2, r.sum_consumed,
        r.sum_produced]
      omega⟩
  else x

/-- The counts after firing an applicable reaction. -/
lemma react_val {x : Counts S n} {r : Reaction S} (h : ∀ a, r.consumed a ≤ x.1 a) (a : S) :
    (x.react r).1 a = x.1 a - r.consumed a + r.produced a := by
  simp [react, dif_pos h]

/-- Firing an applicable reaction whose products differ from its reactants changes the counts. -/
lemma react_ne_self {x : Counts S n} {r : Reaction S} (hr : r.reactants ≠ r.products)
    (h : ∀ a, r.consumed a ≤ x.1 a) : x.react r ≠ x := by
  intro he
  apply hr
  have hcount (a : S) : r.consumed a = r.produced a := by
    have h1 := congrArg (fun y : Counts S n => y.1 a) he
    have h2 := h a
    simp only [react_val h] at h1
    omega
  refine Sym2.ext fun a => ?_
  rw [← Sym2.mem_toMultiset, ← Sym2.mem_toMultiset, ← Multiset.count_pos, ← Multiset.count_pos]
  exact iff_of_eq (congrArg (0 < ·) (hcount a))

end Counts

namespace Network

/-- Total propensity `a₀(x) = ∑ᵣ aᵣ(x)`, the rate at which the counts leave `x`. -/
noncomputable def totalPropensity (N : Network S) (k : ℝ) (x : Counts S n) : ℝ :=
  ∑ r ∈ N.reactions, r.propensity k x

/-- The reaction fired by the jump chain from `x`: `r` with probability `aᵣ(x) / a₀(x)`. -/
noncomputable def nextReaction (N : Network S) {k : ℝ} (hk : 0 < k) (x : Counts S n)
    (h : N.totalPropensity k x ≠ 0) : Distribution N.reactions :=
  normalize (fun r => (r : Reaction S).propensity k x)
    (fun _ => mul_nonneg hk.le (prod_nonneg fun _ _ => Nat.cast_nonneg _))
    (by rwa [sum_coe_sort N.reactions fun r => r.propensity k x])

/-- The jump chain of stochastic mass-action kinetics with common rate constant `k > 0`
(roadmap CRN-1): from `x`, fire reaction `r` with probability `aᵣ(x) / a₀(x)`; a terminal state
(`a₀(x) = 0`) is absorbing. -/
noncomputable def jumpKernel (N : Network S) (k : ℝ) (hk : 0 < k) (n : ℕ) :
    Kernel (Counts S n) := fun x =>
  if h : N.totalPropensity k x = 0 then Distribution.point x
  else (N.nextReaction hk x h).map fun r => x.react r

/-- The jump chain's expectation times the total propensity, valid also at terminal states:
`a₀(x)·E[f] = ∑ᵣ aᵣ(x)·f(x.react r)`. -/
lemma totalPropensity_mul_expect (N : Network S) {k : ℝ} (hk : 0 < k) (x : Counts S n)
    (f : Counts S n → ℝ) :
    N.totalPropensity k x * (N.jumpKernel k hk n x).expect f =
      ∑ r ∈ N.reactions, r.propensity k x * f (x.react r) := by
  by_cases h : N.totalPropensity k x = 0
  · have hz : ∀ r ∈ N.reactions, r.propensity k x = 0 :=
      (sum_eq_zero_iff_of_nonneg fun r _ => Reaction.propensity_nonneg hk.le r x).1 h
    rw [h, zero_mul]
    exact (sum_eq_zero fun r hr => by rw [hz r hr, zero_mul]).symm
  · simp only [jumpKernel, dif_neg h]
    rw [Distribution.map_expect, nextReaction, normalize_expect,
      sum_coe_sort N.reactions fun r => r.propensity k x,
      sum_coe_sort N.reactions fun r => r.propensity k x * f (x.react r)]
    exact mul_div_cancel₀ _ h

/-- The jump chain really jumps: from a non-terminal state it never stays put (every reaction
of the network changes the counts). -/
theorem jumpKernel_weight_self (N : Network S) {k : ℝ} (hk : 0 < k) (x : Counts S n)
    (h : N.totalPropensity k x ≠ 0) :
    (N.jumpKernel k hk n x).weight x = 0 := by
  classical
  rw [weight_eq_expect]
  simp only [jumpKernel, dif_neg h]
  rw [Distribution.map_expect]
  unfold Distribution.expect
  refine sum_eq_zero fun r _ => ?_
  by_cases hrx : x.react r = x
  · have hz : (r : Reaction S).propensity k x = 0 := by
      by_contra hne
      exact Counts.react_ne_self (N.nontrivial r r.2)
        (Reaction.consumed_le_of_propensity_ne_zero hne) hrx
    simp [nextReaction, normalize, hz]
  · simp [hrx]

end Network

end Crn
