import Crn.Protocol

/-!
# Population protocols and stable computation (CRN-3)

A population protocol [AADFP06, §3.1] has an input alphabet `X`, a finite set `Q` of states, an
input function `I : X → Q`, an output function `O : Q → Y` and a transition function
`δ : Q × Q → Q × Q` on the states of (initiator, responder). We compute predicates under the
all-agents predicate output convention [AADFP06, §3.4], so `Y = Bool`. Protocols run in the
standard population `Pₙ` [AADFP06, §3.3]: the agents `Fin n` with the complete interaction graph,
whose encounters are the ordered pairs of distinct agents (CRN-1's `AgentPair n`). A
configuration assigns a state to each agent (`Fin n → Q`, as the configurations of CRN-1); the
encounter `(u, v)` replaces the states `p = c u`, `q = c v` by `δ(p, q)`.

An input assignment `ι : Fin n → X` starts the protocol in the configuration `I ∘ ι` and
represents the count vector `counts ι` of input symbols (the symbol-count input convention
[AADFP06, §3.4]). A protocol *stably computes* a predicate `φ` on count vectors if, from every
initial configuration of a nonempty population, every reachable configuration can reach an
output-stable configuration in which all agents output `φ` of the input counts. AADFP06 phrase
this with fair executions; for finite populations both forms are equivalent, and this
combinatorial form is the one of [AAER07] (see `FORMALIZATION_DIFFERENCES.md`).

## References

* [AADFP06] D. Angluin, J. Aspnes, Z. Diamadi, M. J. Fischer, R. Peralta, *Computation in
  networks of passively mobile finite-state sensors*, Distributed Computing 18 (2006).
* [AAER07] D. Angluin, J. Aspnes, D. Eisenstat, E. Ruppert, *The computational power of
  population protocols*, Distributed Computing 20 (2007).
-/

namespace Crn

/-- A population protocol [AADFP06, §3.1] with input alphabet `X` and states `Q`, computing
predicates (output alphabet `Bool`, the all-agents predicate output convention of §3.4). The
state set is required to be finite where it matters (`StablyComputable`). -/
structure Protocol (X Q : Type*) where
  /-- The input function `I : X → Q`. -/
  input : X → Q
  /-- The output function `O : Q → Bool`. -/
  output : Q → Bool
  /-- The transition function `δ : Q × Q → Q × Q` on the states of (initiator, responder). -/
  δ : Q × Q → Q × Q

variable {X Q : Type*} {n : ℕ}

/-- The configuration after the encounter `e = (u, v)` from `c` [AADFP06, §3.1]: the initiator
`u` gets `δ₁(c u, c v)`, the responder `v` gets `δ₂(c u, c v)` and every other agent keeps its
state. -/
def Protocol.interact (P : Protocol X Q) (c : Fin n → Q) (e : AgentPair n) : Fin n → Q :=
  Function.update (Function.update c e.1.1 (P.δ (c e.1.1, c e.1.2)).1) e.1.2
    (P.δ (c e.1.1, c e.1.2)).2

/-- One step `c → c'` [AADFP06, §3.1]: `c'` results from `c` by an encounter of two distinct
agents (the complete interaction graph). -/
def Protocol.Step (P : Protocol X Q) (c c' : Fin n → Q) : Prop :=
  ∃ e : AgentPair n, c' = P.interact c e

/-- Reachability `c →* c'` [AADFP06, §3.1]: the reflexive-transitive closure of one-step
transitions. -/
def Protocol.Reaches (P : Protocol X Q) : (Fin n → Q) → (Fin n → Q) → Prop :=
  Relation.ReflTransGen P.Step

/-- `c` is output-stable with output `b` [AADFP06, §3.2, with the all-agents predicate output
convention of §3.4]: in every configuration reachable from `c`, every agent outputs `b`. -/
def Protocol.OutputStable (P : Protocol X Q) (b : Bool) (c : Fin n → Q) : Prop :=
  ∀ c', P.Reaches c c' → ∀ v, P.output (c' v) = b

variable [Fintype X] [DecidableEq X]

/-- `P` stably computes the predicate `φ` on input count vectors [AADFP06, §§3.2–3.4: standard
populations, symbol-count input convention, all-agents predicate output convention], in the
combinatorial form of [AAER07]: for every nonempty standard population `Fin n` and every input
assignment `ι`, every configuration reachable from the initial configuration `I ∘ ι` can reach
an output-stable configuration whose common output is `φ` of the input counts `counts ι`. -/
def Protocol.StablyComputes (P : Protocol X Q) (φ : (X → ℕ) → Bool) : Prop :=
  ∀ n, 0 < n → ∀ ι : Fin n → X, ∀ c, P.Reaches (P.input ∘ ι) c →
    ∃ d, P.Reaches c d ∧ P.OutputStable (φ (counts ι).1) d

/-- A predicate on input count vectors is stably computable [AADFP06, §3] if some population
protocol with finitely many states stably computes it. -/
def StablyComputable (φ : (X → ℕ) → Bool) : Prop :=
  ∃ (Q : Type) (_ : Finite Q) (P : Protocol X Q), P.StablyComputes φ

/-- Sanity check of `Protocol.StablyComputes`: a protocol stably computes at most one predicate
on nonzero count vectors (a computation converges to at most one output [AADFP06, §3.2], on
which all agents agree [AADFP06, §3.4]). -/
theorem Protocol.StablyComputes.unique {P : Protocol X Q} {φ ψ : (X → ℕ) → Bool}
    (hφ : P.StablyComputes φ) (hψ : P.StablyComputes ψ) {x : X → ℕ} (hx : x ≠ 0) :
    φ x = ψ x := by
  obtain ⟨ι, hι⟩ := exists_counts_eq (⟨x, rfl⟩ : Counts X (∑ i, x i))
  have hx' : (counts ι).1 = x := congrArg Subtype.val hι
  have hn : 0 < ∑ i, x i := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
    exact lt_of_lt_of_le (Nat.pos_of_ne_zero hi)
      (Finset.single_le_sum (fun j _ => Nat.zero_le (x j)) (Finset.mem_univ i))
  obtain ⟨d, hd, hdφ⟩ := hφ _ hn ι _ Relation.ReflTransGen.refl
  obtain ⟨e, he, heψ⟩ := hψ _ hn ι d hd
  have h1 := hdφ e he ⟨0, hn⟩
  have h2 := heψ e Relation.ReflTransGen.refl ⟨0, hn⟩
  rw [hx'] at h1 h2
  rw [← h1, h2]

end Crn
