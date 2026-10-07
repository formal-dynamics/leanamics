import Crn.Basic
import Crn.StableSemilinear
import Crn.StableTransfer

/-!
# Stable computation by count-conserving CRNs (CRN-3, transfer)

A population protocol is a count-conserving bimolecular CRN on the species `Q` [CDS14, §2.2]:
the transition `δ(p, q) = (p', q')` is the reaction `p + q → p' + q'` (CRN-1's `Reaction`), and
the count vectors reachable in the CRN are those of the configurations reachable in the protocol
(`Protocol.exists_network`). Transitions that do not change the multiset `{p, q}` do not change
the counts and give no reaction (CRN-1's networks have no such reactions).

A CRN with species `S` stably decides a predicate [CDS14, §2.2] through an injective input map
`I : X ↪ S` (the input species) and an output map `O : S → Bool` (every species votes, as in the
definitions of [AAE06]): from the initial count vector with `xᵢ` molecules of `I i` and nothing
else, every reachable count vector can reach an output-stable one, in which every present species
votes for the predicate's value, as in every count vector reachable from it. With the transfer,
every stably computable predicate, hence every semilinear one, is stably decided by a
count-conserving bimolecular CRN (`IsSemilinearPred.exists_network`).

## References

* [CDS14] H.-L. Chen, D. Doty, D. Soloveichik, *Deterministic function computation with
  chemical reaction networks*, Natural Computing 13 (2014).
* [AAE06] D. Angluin, J. Aspnes, D. Eisenstat, *Stably computable predicates are semilinear*,
  PODC 2006.
-/

namespace Crn

open Finset

variable {n : ℕ}

/-- The count vector `x` pushed forward along `f : X → S`: `(x.map f) a = ∑_{i : f i = a} xᵢ`.
For the input map `I` of a CRN, `x.map I` is the initial count vector of the input counts `x`:
`xᵢ` molecules of the input species `I i` and no other molecules [CDS14, §2.2]. -/
def Counts.map {X S : Type*} [Fintype X] [Fintype S] [DecidableEq S] (f : X → S)
    (x : Counts X n) : Counts S n :=
  ⟨fun a => ∑ i with f i = a, x.1 i, by rw [Finset.sum_fiberwise, x.2]⟩

/-- Pushing input counts forward: `counts (f ∘ ι) = (counts ι).map f`. -/
lemma counts_comp {X S : Type*} [Fintype X] [DecidableEq X] [Fintype S] [DecidableEq S]
    (f : X → S) (ι : Fin n → X) : counts (f ∘ ι) = (counts ι).map f := by
  refine Subtype.ext (funext fun a => ?_)
  have h := sum_comp_eq_sum_counts ι fun i => if f i = a then 1 else 0
  simp only [smul_eq_mul, mul_ite, mul_one, mul_zero] at h
  rw [counts_val, card_filter]
  simp only [Counts.map, sum_filter]
  exact h

section Reach

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- One reaction event `x → y` of the CRN `N` on count vectors [CDS14, §2.1]: some reaction of
`N` whose reactant molecules are all present fires (`Counts.react`). -/
def Network.Step (N : Network S) (x y : Counts S n) : Prop :=
  ∃ r ∈ N.reactions, (∀ a, r.consumed a ≤ x.1 a) ∧ y = x.react r

/-- Reachability `x →* y` in the CRN `N` [CDS14, §2.1]: the reflexive-transitive closure of
reaction events. -/
def Network.Reaches (N : Network S) : Counts S n → Counts S n → Prop :=
  Relation.ReflTransGen N.Step

/-- A count vector `y` is output-stable with output `b` for the CRN `N` with output map `O`
[CDS14, §2.2, every species voting]: in every count vector reachable from `y`, every species
that is present votes `b`. -/
def Network.OutputStable (N : Network S) (O : S → Bool) (b : Bool) (y : Counts S n) : Prop :=
  ∀ z, N.Reaches y z → ∀ a, z.1 a ≠ 0 → O a = b

/-- The CRN `N` with input species `I : X ↪ S` and output map `O : S → Bool` stably decides the
predicate `φ` [CDS14, §2.2, leaderless and with every species voting]: for every nonzero input
count vector `x`, every count vector reachable from the initial count vector `x.map I` can reach
an output-stable count vector with output `φ x`. -/
def Network.StablyComputes {X : Type*} [Fintype X] (N : Network S) (I : X ↪ S) (O : S → Bool)
    (φ : (X → ℕ) → Bool) : Prop :=
  ∀ n, 0 < n → ∀ x : Counts X n, ∀ y, N.Reaches (x.map I) y →
    ∃ z, N.Reaches y z ∧ N.OutputStable O (φ x.1) z

end Reach

/-- **CRN-3, transfer to CRNs** ([CDS14, §2.2]; reachability version of CRN-1). A population
protocol with finitely many states and at least one transition that changes the multiset of
states of the two agents yields a count-conserving bimolecular CRN on the species `Q`, whose
reactions are the transitions `p + q → δ₁(p, q) + δ₂(p, q)` that change `{p, q}`: in every
population, the count vectors reachable in the CRN from the counts of a configuration `c` are
exactly the counts of the configurations reachable from `c` in the protocol. -/
theorem Protocol.exists_network {X Q : Type*} [Fintype Q] [DecidableEq Q] (P : Protocol X Q)
    (hP : ∃ p q : Q, s(p, q) ≠ s((P.δ (p, q)).1, (P.δ (p, q)).2)) :
    ∃ N : Network Q,
      (∀ r : Reaction Q, r ∈ N.reactions ↔ r.reactants ≠ r.products ∧
        ∃ p q : Q, r.reactants = s(p, q) ∧ r.products = s((P.δ (p, q)).1, (P.δ (p, q)).2)) ∧
      ∀ (n : ℕ) (c : Fin n → Q) (y : Counts Q n),
        N.Reaches (counts c) y ↔ ∃ c', P.Reaches c c' ∧ counts c' = y := by
  let R : Finset (Reaction Q) := (univ.image fun pq : Q × Q => P.reactionOf pq.1 pq.2).filter
    fun r => r.reactants ≠ r.products
  have hmem : ∀ r : Reaction Q, r ∈ R ↔ r.reactants ≠ r.products ∧
      ∃ p q : Q, r.reactants = s(p, q) ∧ r.products = s((P.δ (p, q)).1, (P.δ (p, q)).2) := by
    intro r
    simp only [R, mem_filter, mem_image, mem_univ, true_and, Prod.exists]
    constructor
    · rintro ⟨⟨p, q, rfl⟩, h⟩
      exact ⟨h, p, q, rfl, rfl⟩
    · rintro ⟨h, p, q, h1, h2⟩
      refine ⟨⟨p, q, ?_⟩, h⟩
      cases r
      simp only [Protocol.reactionOf] at h1 h2 ⊢
      rw [h1, h2]
  obtain ⟨p₀, q₀, h₀⟩ := hP
  have hne : R.Nonempty := ⟨P.reactionOf p₀ q₀, (hmem _).2 ⟨h₀, p₀, q₀, rfl, rfl⟩⟩
  refine ⟨⟨R, hne, fun r hr => ((hmem r).1 hr).1⟩, hmem, fun n c y => ⟨fun h => ?_, ?_⟩⟩
  · induction h with
    | refl => exact ⟨c, Protocol.Reaches.refl c, rfl⟩
    | tail _ hst ih =>
      obtain ⟨c', hc', rfl⟩ := ih
      obtain ⟨r, hr, happ, rfl⟩ := hst
      obtain ⟨-, p, q, h1, h2⟩ := (hmem r).1 hr
      obtain ⟨e, he1, he2⟩ := exists_agentPair c' (p := p) (q := q) fun a => by
        have := happ a
        rwa [Reaction.consumed, h1] at this
      refine ⟨P.interact c' e, hc'.trans (Protocol.reaches_interact c' e), ?_⟩
      rw [counts_interact, he1, he2]
      congr 1
      cases r
      simp only [Protocol.reactionOf] at h1 h2 ⊢
      rw [h1, h2]
  · rintro ⟨c', hc', rfl⟩
    induction hc' with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hst ih =>
      obtain ⟨e, rfl⟩ := hst
      rename_i b _
      by_cases htriv : (P.reactionOf (b e.1.1) (b e.1.2)).reactants =
          (P.reactionOf (b e.1.1) (b e.1.2)).products
      · rw [counts_interact_of_trivial P b e htriv]
        exact ih
      · exact ih.tail ⟨_, (hmem _).2 ⟨htriv, _, _, rfl, rfl⟩, consumed_le_counts P b e,
          counts_interact P b e⟩

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **CRN-3, transfer of stable computation**: every predicate stably computable by a population
protocol is stably decided by a count-conserving bimolecular CRN with finitely many species,
injective input map and no initial context [CDS14, §2.2]. -/
theorem StablyComputable.exists_network {φ : (X → ℕ) → Bool} (h : StablyComputable φ) :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (N : Network S) (I : X ↪ S)
      (O : S → Bool), N.StablyComputes I O φ := by
  obtain ⟨Q, hQ, P, hP⟩ := h
  classical
  haveI : Fintype Q := Fintype.ofFinite Q
  by_cases hX : IsEmpty X
  · -- no input symbol: there is no nonempty population, any network works
    refine ⟨Bool, inferInstance, inferInstance,
      ⟨{⟨s(false, false), s(true, true)⟩}, by simp, by simp⟩,
      ⟨fun a => hX.elim a, fun a => hX.elim a⟩, fun _ => false, ?_⟩
    intro n hn x
    have hx := x.2
    simp only [univ_eq_empty, sum_empty] at hx
    omega
  rw [not_isEmpty_iff] at hX
  obtain ⟨i₀⟩ := hX
  let eX := Fintype.equivFin X
  have hP' := tagInputs_stablyComputes (eX := eX) hP
  obtain ⟨N, -, hN⟩ := (P.tagInputs eX).exists_network (tagInputs_nontrivial i₀)
  refine ⟨Fin (Fintype.card X) ⊕ Q, inferInstance, inferInstance, N,
    ⟨Sum.inl ∘ eX, Sum.inl_injective.comp eX.injective⟩, (P.tagInputs eX).output, ?_⟩
  intro n hn x y hy
  obtain ⟨ι, rfl⟩ := exists_counts_eq x
  rw [← counts_comp] at hy
  obtain ⟨c, hc, rfl⟩ := (hN n _ y).1 hy
  obtain ⟨d, hd, hds⟩ := hP' n hn ι c hc
  refine ⟨counts d, (hN n c (counts d)).2 ⟨d, hd, rfl⟩, fun z hz a ha => ?_⟩
  obtain ⟨d', hd', rfl⟩ := (hN n d z).1 hz
  rw [counts_val] at ha
  obtain ⟨w, hw⟩ := card_pos.1 (Nat.pos_of_ne_zero ha)
  rw [← (mem_filter.1 hw).2]
  exact hds d' hd' w

/-- **CRN-3** (roadmap, easy direction, for CRNs): every Boolean combination of threshold and
remainder predicates is stably decided by a count-conserving bimolecular CRN [AADFP06,
Theorem 5; CDS14, Theorem 2.1, "if" direction]. -/
theorem IsSemilinearPred.exists_network {φ : (X → ℕ) → Bool} (h : IsSemilinearPred φ) :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (N : Network S) (I : X ↪ S)
      (O : S → Bool), N.StablyComputes I O φ :=
  h.stablyComputable.exists_network

end Crn
