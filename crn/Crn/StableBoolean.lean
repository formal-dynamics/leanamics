import Crn.StableProduct

/-!
# Boolean closure of stably computable predicates (CRN-3)

[AADFP06, §4.1, Lemma 3 and Corollary 2]: the stably computable predicates are closed under every
2-place Boolean function, by the parallel composition of two protocols. Its states are pairs
`(p₁, p₂)`, its input function is `s ↦ (I₁ s, I₂ s)`, both components make their own transition
in every encounter, and the output of `(p₁, p₂)` is `ξ(O₁ p₁, O₂ p₂)`.
-/

namespace Crn

variable {X : Type*} [Fintype X] [DecidableEq X] {φ ψ : (X → ℕ) → Bool}

/-- **[AADFP06, Lemma 3]** For every 2-place Boolean function `ξ`, if `φ` and `ψ` are stably
computable then so is `ξ(φ, ψ)` (parallel composition). -/
theorem StablyComputable.map₂ (ξ : Bool → Bool → Bool) (hφ : StablyComputable φ)
    (hψ : StablyComputable ψ) : StablyComputable fun x => ξ (φ x) (ψ x) := by
  obtain ⟨Q₁, _, P₁, h₁⟩ := hφ
  obtain ⟨Q₂, _, P₂, h₂⟩ := hψ
  exact ⟨Q₁ × Q₂, inferInstance, P₁.prod P₂ ξ, Protocol.prod_stablyComputes h₁ h₂⟩

/-- Stably computable predicates are closed under negation [AADFP06, Corollary 2]. -/
theorem StablyComputable.not (hφ : StablyComputable φ) : StablyComputable fun x => !φ x :=
  hφ.map₂ (fun a _ => !a) hφ

/-- Stably computable predicates are closed under conjunction [AADFP06, Corollary 2]. -/
theorem StablyComputable.and (hφ : StablyComputable φ) (hψ : StablyComputable ψ) :
    StablyComputable fun x => φ x && ψ x :=
  hφ.map₂ (· && ·) hψ

/-- Stably computable predicates are closed under disjunction [AADFP06, Corollary 2]. -/
theorem StablyComputable.or (hφ : StablyComputable φ) (hψ : StablyComputable ψ) :
    StablyComputable fun x => φ x || ψ x :=
  hφ.map₂ (· || ·) hψ

end Crn
