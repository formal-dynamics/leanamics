import Crn.StableInteract

/-!
# Population protocols on an interaction graph (CRN-4)

Mertzios, Nikoletseas, Raptopoulos and Spirakis [MNRS14, §2] run population protocols on an
arbitrary connected interaction graph `G`: two agents may interact only if they share an edge.
On an undirected graph an interaction is an *oriented edge* (a `SimpleGraph.Dart`): the tail is
the initiator, the head the responder. This file generalizes the reachability form of stable
computation of `Crn.Protocol.StablyComputes` (`StableBasic`, complete interaction graph) to
interactions along the edges of `G : SimpleGraph (Fin n)`, without changing the existing
definitions:

* `Protocol.GraphStep`, `Protocol.GraphReaches`, `Protocol.GraphOutputStable`: one encounter
  along an edge of `G`, reachability, and output stability on `G`;
* `Protocol.StablyComputesOnGraph P G D φ`: on the graph `G`, from every input whose count
  vector lies in the domain `D`, every reachable configuration can reach an output-stable
  configuration with output `φ`. The domain is needed because majority is a partial function
  [MNRS14, §2: "a (possibly partial) function"]: the paper only asks for the correct output "if
  there exists initially a majority" (Theorem 2);
* `Protocol.GraphStablyComputes P D φ`: stable computation on every connected graph.

On the complete graph `⊤` these notions are the existing ones (`graphStep_top`,
`graphReaches_top`, `graphOutputStable_top`, `stablyComputesOnGraph_top_iff`), so
`GraphStablyComputes P (fun _ => True) φ` implies `P.StablyComputes φ`
(`GraphStablyComputes.stablyComputes`).

The majority problem has the input alphabet `Bool` (`true` is the paper's red `r`, `false` its
green `g`), `majority x = decide (x false < x true)` (output `true` for a red majority) and the
domain `HasMajority x : x true ≠ x false` (no tie).

## References

* [MNRS14] G. B. Mertzios, S. E. Nikoletseas, C. L. Raptopoulos, P. G. Spirakis, *Determining
  majority in networks with local interactions and very small local memory*, ICALP 2014;
  arXiv:1404.7671 (numbering of the arXiv version); Distributed Computing 30 (2017).
-/

namespace Crn

open Finset

variable {X Q : Type*} {n : ℕ}

/-- The ordered pair (initiator, responder) of distinct agents of an oriented edge `d` of `G`
[MNRS14, §2: the tail of `d` is the initiator, the head the responder]. -/
def dartPair {G : SimpleGraph (Fin n)} (d : G.Dart) : AgentPair n :=
  ⟨d.toProd, d.adj.ne⟩

namespace Protocol

/-- One step `c → c'` on the interaction graph `G` [MNRS14, §2.2, "directly reachable"]: `c'`
results from `c` by the encounter of the two endpoints of an oriented edge of `G`. -/
def GraphStep (P : Protocol X Q) (G : SimpleGraph (Fin n)) (c c' : Fin n → Q) : Prop :=
  ∃ d : G.Dart, c' = P.interact c (dartPair d)

/-- Reachability on the interaction graph `G`: the reflexive-transitive closure of
`GraphStep`. -/
def GraphReaches (P : Protocol X Q) (G : SimpleGraph (Fin n)) :
    (Fin n → Q) → (Fin n → Q) → Prop :=
  Relation.ReflTransGen (P.GraphStep G)

/-- `c` is output-stable with output `b` on `G` [MNRS14, §2, property (b)]: in every
configuration reachable from `c` on `G`, every agent outputs `b`. -/
def GraphOutputStable (P : Protocol X Q) (G : SimpleGraph (Fin n)) (b : Bool)
    (c : Fin n → Q) : Prop :=
  ∀ c', P.GraphReaches G c c' → ∀ v, P.output (c' v) = b

variable [Fintype X] [DecidableEq X]

/-- `P` stably computes the partial predicate `φ` with domain `D` on the interaction graph `G`
[MNRS14, §2], in the reachability form of `Protocol.StablyComputes`: for every input
assignment `ι` whose count vector lies in `D`, every configuration reachable on `G` from the
initial configuration `I ∘ ι` can reach on `G` an output-stable configuration whose common
output is `φ` of the input counts. -/
def StablyComputesOnGraph (P : Protocol X Q) (G : SimpleGraph (Fin n))
    (D : (X → ℕ) → Prop) (φ : (X → ℕ) → Bool) : Prop :=
  ∀ ι : Fin n → X, D (counts ι).1 → ∀ c, P.GraphReaches G (P.input ∘ ι) c →
    ∃ d, P.GraphReaches G c d ∧ P.GraphOutputStable G (φ (counts ι).1) d

/-- `P` stably computes the partial predicate `φ` with domain `D` on every connected
interaction graph [MNRS14, §2: "an arbitrary connected network"]. -/
def GraphStablyComputes (P : Protocol X Q) (D : (X → ℕ) → Prop) (φ : (X → ℕ) → Bool) :
    Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.Connected → P.StablyComputesOnGraph G D φ

end Protocol

/-- The majority predicate on two input types [MNRS14, §3]: `true` (red) is the majority. -/
def majority (x : Bool → ℕ) : Bool :=
  decide (x false < x true)

/-- The domain of the majority function [MNRS14, Theorem 2: "if there exists initially a
majority"]: the two input counts differ. -/
def HasMajority (x : Bool → ℕ) : Prop :=
  x true ≠ x false

namespace Protocol

variable (P : Protocol X Q)

/-! ### The complete graph: agreement with `Protocol.StablyComputes` -/

/-- On the complete graph, a graph step is a step of the standard population. -/
theorem graphStep_top : P.GraphStep (⊤ : SimpleGraph (Fin n)) = P.Step := by
  funext c c'
  apply propext
  constructor
  · rintro ⟨d, rfl⟩
    exact ⟨dartPair d, rfl⟩
  · rintro ⟨e, rfl⟩
    exact ⟨⟨e.1, by simpa using e.2⟩, rfl⟩

/-- On the complete graph, reachability is reachability in the standard population. -/
theorem graphReaches_top : P.GraphReaches (⊤ : SimpleGraph (Fin n)) = P.Reaches := by
  unfold GraphReaches Reaches
  rw [graphStep_top]

/-- On the complete graph, output stability is output stability in the standard population. -/
theorem graphOutputStable_top (b : Bool) (c : Fin n → Q) :
    P.GraphOutputStable (⊤ : SimpleGraph (Fin n)) b c ↔ P.OutputStable b c := by
  unfold GraphOutputStable OutputStable
  rw [graphReaches_top]

variable [Fintype X] [DecidableEq X]

/-- **Agreement with `Protocol.StablyComputes`.** Stable computation on the complete graphs of
all nonempty populations, with the trivial domain, is the existing notion
`Protocol.StablyComputes` of CRN-3. -/
theorem stablyComputesOnGraph_top_iff (φ : (X → ℕ) → Bool) :
    (∀ n, 0 < n → P.StablyComputesOnGraph (⊤ : SimpleGraph (Fin n)) (fun _ => True) φ) ↔
      P.StablyComputes φ := by
  unfold StablyComputesOnGraph StablyComputes
  simp only [graphReaches_top, graphOutputStable_top, true_implies]

variable {P} in
/-- Stable computation on every connected graph implies stable computation in the standard
population (complete interaction graph). -/
theorem GraphStablyComputes.stablyComputes {φ : (X → ℕ) → Bool}
    (h : P.GraphStablyComputes (fun _ => True) φ) : P.StablyComputes φ := by
  rw [← P.stablyComputesOnGraph_top_iff]
  intro n hn
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact h n ⊤ SimpleGraph.connected_top

variable {P} in
/-- Stable computation on every connected graph gives stable computation on the complete graph
of every nonempty population, for any domain. -/
theorem GraphStablyComputes.top {D : (X → ℕ) → Prop} {φ : (X → ℕ) → Bool}
    (h : P.GraphStablyComputes D φ) (n : ℕ) (hn : 0 < n) :
    P.StablyComputesOnGraph (⊤ : SimpleGraph (Fin n)) D φ := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact h n ⊤ SimpleGraph.connected_top

/-! ### Embedding a population into a larger one -/

omit [Fintype X] [DecidableEq X] in
/-- **Embedding lemma** (used in the proof of [MNRS14, Theorem 1]: "ignoring agents `v` and `u`
during these steps"). If `c` reaches `d` on `G` and `f` embeds the agents of `G` into those of
`G'`, mapping edges to edges, then any configuration of `G'` that agrees with `c` on the image of
`f` reaches, on `G'`, the configuration that agrees with `d` on the image of `f` and is unchanged
elsewhere. -/
theorem GraphReaches.extend {m : ℕ} {G : SimpleGraph (Fin m)} {G' : SimpleGraph (Fin n)}
    {f : Fin m → Fin n} (hf : Function.Injective f) (hG : ∀ u v, G.Adj u v → G'.Adj (f u) (f v))
    {c d : Fin m → Q} (h : P.GraphReaches G c d) (e : Fin n → Q) :
    P.GraphReaches G' (Function.extend f c e) (Function.extend f d e) := by
  sorry

end Protocol

end Crn
