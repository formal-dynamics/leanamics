import Crn.StableThreshold
import Crn.StableRemainder
import Crn.StableSemilinearSet
import Mathlib.ModelTheory.Arithmetic.Presburger.Semilinear.Basic

/-!
# Semilinear predicates are stably computable (CRN-3, easy direction)

[AADFP06, Theorem 5]: every Presburger-definable predicate on input counts is stably computable.
Its proof applies Presburger's quantifier elimination [AADFP06, Theorem 4] to write the predicate
as a Boolean combination of threshold and remainder predicates (equalities are conjunctions of
two thresholds), which are stably computable [AADFP06, Lemma 5], and concludes by Boolean
closure [AADFP06, Corollary 2].

We take the Boolean combinations of threshold and remainder predicates as the definition of the
class (`IsSemilinearPred`) and prove that all of them are stably computable. That this class is
exactly the class of semilinear (equivalently, by Ginsburg–Spanier, Presburger-definable) sets of
count vectors is not formalized; only the inclusion into Mathlib's semilinear sets is stated
(`IsSemilinearPred.isSemilinearSet`; Mathlib's `presburger.definable_iff_isSemilinearSet` then
gives Presburger definability). The converse inclusion is Presburger's quantifier elimination.
-/

namespace Crn

variable {X : Type*} [Fintype X]

/-- The semilinear predicates on input counts, defined as the Boolean combinations of threshold
predicates `∑ᵢ aᵢ xᵢ < c` and remainder predicates `∑ᵢ aᵢ xᵢ ≡ c (mod m)` [AADFP06, proof of
Theorem 5]. By Presburger's quantifier elimination [AADFP06, Theorem 4] and Ginsburg–Spanier
[AADFP06, Theorem 3] these are exactly the predicates whose truth sets are semilinear, that is,
Presburger-definable; only the inclusion `IsSemilinearPred.isSemilinearSet` is formalized. -/
inductive IsSemilinearPred : ((X → ℕ) → Bool) → Prop
  /-- Threshold predicates `∑ᵢ aᵢ xᵢ < c` [AADFP06, Lemma 5(1)]. -/
  | threshold (a : X → ℤ) (c : ℤ) : IsSemilinearPred (threshold a c)
  /-- Remainder predicates `∑ᵢ aᵢ xᵢ ≡ c (mod m)`, `m > 0` [AADFP06, Lemma 5(2)]. -/
  | remainder (a : X → ℤ) (c : ℤ) {m : ℕ} (hm : 0 < m) : IsSemilinearPred (remainder a c m)
  /-- Negation. -/
  | not {φ : (X → ℕ) → Bool} : IsSemilinearPred φ → IsSemilinearPred fun x => !φ x
  /-- Conjunction. -/
  | and {φ ψ : (X → ℕ) → Bool} : IsSemilinearPred φ → IsSemilinearPred ψ →
      IsSemilinearPred fun x => φ x && ψ x
  /-- Disjunction. -/
  | or {φ ψ : (X → ℕ) → Bool} : IsSemilinearPred φ → IsSemilinearPred ψ →
      IsSemilinearPred fun x => φ x || ψ x

/-- The truth set of a semilinear predicate is a semilinear set of count vectors in Mathlib's
sense, hence Presburger-definable (`presburger.definable_iff_isSemilinearSet`). This checks that
`IsSemilinearPred` is not larger than the semilinear predicates. -/
theorem IsSemilinearPred.isSemilinearSet {φ : (X → ℕ) → Bool} (h : IsSemilinearPred φ) :
    IsSemilinearSet {x : X → ℕ | φ x = true} := by
  induction h with
  | threshold a c => exact isSemilinearSet_threshold a c
  | remainder a c _ => exact isSemilinearSet_remainder a c _
  | @not φ _ ih =>
    have e : {x : X → ℕ | (!φ x) = true} = {x | φ x = true}ᶜ := by ext; simp
    rw [e]
    exact ih.compl
  | @and φ ψ _ _ ih₁ ih₂ =>
    have e : {x : X → ℕ | (φ x && ψ x) = true} = {x | φ x = true} ∩ {x | ψ x = true} := by
      ext; simp
    rw [e]
    exact ih₁.inter ih₂
  | @or φ ψ _ _ ih₁ ih₂ =>
    have e : {x : X → ℕ | (φ x || ψ x) = true} = {x | φ x = true} ∪ {x | ψ x = true} := by
      ext; simp
    rw [e]
    exact ih₁.union ih₂

variable [DecidableEq X]

/-- **CRN-3, easy direction** [AADFP06, Theorem 5, with Lemma 5 and Corollary 2]: every Boolean
combination of threshold and remainder predicates is stably computable by a population
protocol. -/
theorem IsSemilinearPred.stablyComputable {φ : (X → ℕ) → Bool} (h : IsSemilinearPred φ) :
    StablyComputable φ := by
  induction h with
  | threshold a c => exact stablyComputable_threshold a c
  | remainder a c hm => exact stablyComputable_remainder a c hm
  | not _ ih => exact ih.not
  | and _ _ ih₁ ih₂ => exact ih₁.and ih₂
  | or _ _ ih₁ ih₂ => exact ih₁.or ih₂

end Crn
