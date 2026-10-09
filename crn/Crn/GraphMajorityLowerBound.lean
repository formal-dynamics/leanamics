import Crn.GraphMajorityAmbassador

/-!
# At least 4 states are needed for majority (CRN-4)

**[MNRS14, Theorem 1]**: no population protocol with at most 3 states stably computes the
majority of a 2-type population on every interaction graph, so the 4-state ambassador protocol
(`ambassador_graphStablyComputes`) has the minimal number of states.

The paper's proof only uses complete interaction graphs (a population `V` and the population
`V ∪ {u, v}` with two extra agents, interacting in a supergraph), so we pin the stronger form
`not_stablyComputesOnGraph_top_majority`: no protocol with at most 3 states stably computes
majority on the complete graphs of all nonempty populations (the standard populations of
`Protocol.StablyComputes`), even with ties excluded from the domain. The statement on all
connected graphs follows (`not_graphStablyComputes_majority`).

Proof route [MNRS14, Theorem 1]: both outputs occur, so with at most 3 states one output value
`b` has a single state `q₁`. Say `b` is the output of a red majority (otherwise exchange the
colors). On `V = Fin 3`, the inputs `C₁ = (r, r, g)` and `C₂ = (r, r, r)` both reach the
configuration "all `q₁`". Adding two green agents gives `C₁' = (r, r, g, g, g)` (green
majority) and `C₂' = (r, r, r, g, g)` (red majority); running the same encounters inside `V`
(`Protocol.GraphReaches.extend`) both reach the configuration "`q₁` on `V`, green input state on
the two extra agents", from which output-stable configurations with both outputs would be
reachable: a contradiction. The paper takes `|V| = 2k + 1` with `k ≥ 2`; `k = 1` already works.

## References

* [MNRS14] G. B. Mertzios, S. E. Nikoletseas, C. L. Raptopoulos, P. G. Spirakis, *Determining
  majority in networks with local interactions and very small local memory*, ICALP 2014;
  arXiv:1404.7671.
-/

namespace Crn

/-- **[MNRS14, Theorem 1], strong form.** No population protocol with at most 3 states stably
computes the majority of two input types on the complete graphs of all nonempty populations,
with the tie inputs excluded from the domain. -/
theorem not_stablyComputesOnGraph_top_majority {Q : Type*} [Fintype Q]
    (hQ : Fintype.card Q ≤ 3) (P : Protocol Bool Q) :
    ¬ ∀ n, 0 < n → P.StablyComputesOnGraph (⊤ : SimpleGraph (Fin n)) HasMajority majority := by
  sorry

/-- **[MNRS14, Theorem 1].** No population protocol with at most 3 states stably computes the
majority of two input types on every connected interaction graph: `R(𝒫_majority) > 3`. -/
theorem not_graphStablyComputes_majority {Q : Type*} [Fintype Q] (hQ : Fintype.card Q ≤ 3)
    (P : Protocol Bool Q) : ¬ P.GraphStablyComputes HasMajority majority :=
  fun h => not_stablyComputesOnGraph_top_majority hQ P h.top

/-- **The rank of majority is 4** [MNRS14, Theorems 1 and 2]: the 4-state ambassador protocol
stably computes majority on every connected graph, and no protocol with fewer states does. -/
theorem rank_majority_eq_four :
    (∃ (Q : Type) (_ : Fintype Q) (P : Protocol Bool Q),
      Fintype.card Q = 4 ∧ P.GraphStablyComputes HasMajority majority) ∧
    ∀ (Q : Type) [Fintype Q] (P : Protocol Bool Q),
      P.GraphStablyComputes HasMajority majority → 4 ≤ Fintype.card Q :=
  ⟨⟨AmbState, inferInstance, ambassador, card_ambState, ambassador_graphStablyComputes⟩,
    fun _ _ P h => by
      by_contra hlt
      exact not_graphStablyComputes_majority (by omega) P h⟩

end Crn
