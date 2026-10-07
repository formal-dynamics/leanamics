import Voter.Lazy
import Voter.Coalescence
import Mathlib.Combinatorics.SimpleGraph.Density

/-! # Volume, conductance and the minority potential (VOT-5)

Definitions of Section 2 of Berenbrink, Giakkoupis, Kermarrec, Mallmann-Trenn, *Bounds on the
voter model in dynamic networks*, ICALP 2016, arXiv:1603.01895 (BGKM16 below), for a finite simple
graph `G` with `m` edges:

* `vol G S`: the volume `vol(S) = ∑_{u ∈ S} d(u)` of a vertex set;
* `conductance G`: `φ(G) = min {∑_{u ∈ U} λ_u / vol(U) : U ⊆ V, 0 < vol(U) ≤ m}`, where `λ_u`
  counts the neighbours of `u` outside `U`, so that `∑_{u ∈ U} λ_u` is the number of edges between
  `U` and `V ∖ U` (Mathlib's `SimpleGraph.interedges`, ordered adjacent pairs in `U × Uᶜ`);
* `discordant G s u`: `λ_u`, the number of neighbours of `u` holding another opinion than `u`;
* `minority G s`: for two opinions, the side `s_t` of smaller volume;
* `potential G s`: the potential `Ψ(s_t) = √vol(s_t)` of the analysis of the voter model;
* `dynamicLazy G hd t`: one round of the lazy voter on a dynamic graph.

The voter process of BGKM16 ("Standard Voter Model", Section 1.1: in every synchronous step every
node chooses a neighbour uniformly at random and adopts its opinion with probability `1/2`) is the
lazy voter `lazyNeighbor G hd` of VOT-2, with configuration kernel `transition (lazyNeighbor G hd)`.
-/

namespace Voter
open Dynamics Finset

variable {V C : Type*} [Fintype V] [DecidableEq V]

section Static
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Volume** (BGKM16, Section 2): `vol(S) = ∑_{u ∈ S} d(u)`. -/
def vol (S : Finset V) : ℕ := ∑ u ∈ S, G.degree u

/-- **Conductance** (BGKM16, Section 2):
`φ(G) = min {∑_{u ∈ U} λ_u / vol(U) : U ⊆ V, 0 < vol(U) ≤ m}`, where `m` is the number of edges
and `λ_u` is the number of neighbours of `u` outside `U`. The sum `∑_{u ∈ U} λ_u` is the number of
ordered adjacent pairs `(u, w)` with `u ∈ U` and `w ∉ U` (`SimpleGraph.interedges`), i.e. the
number of edges between `U` and `V ∖ U`. When no set `U` qualifies (no edges) the infimum is over
an empty family and `φ(G) = 0`. -/
noncomputable def conductance : ℝ :=
  ⨅ U : {U : Finset V // 0 < vol G U ∧ vol G U ≤ G.edgeFinset.card},
    ((G.interedges U.1 U.1ᶜ).card : ℝ) / vol G U.1

/-- `λ_u` (BGKM16, Section 2): the number of neighbours of `u` whose opinion differs from the
opinion of `u`. For two opinions these are the neighbours of `u` on the other side. -/
def discordant [DecidableEq C] (s : Config V C) (u : V) : ℕ :=
  ((G.neighborFinset u).filter (fun w => s w ≠ s u)).card

/-- The **minority side** `s_t` (BGKM16, Section 2) of a two-opinion configuration: the vertices
with opinion `false` (the paper's opinion `0`) if their volume is at most the volume of the
vertices with opinion `true`, and the vertices with opinion `true` otherwise. -/
def minority (s : Config V Bool) : Finset V :=
  if vol G (univ.filter fun u => s u = false) ≤ vol G (univ.filter fun u => s u = true) then
    univ.filter fun u => s u = false
  else univ.filter fun u => s u = true

/-- The **potential** `Ψ(s_t) = √vol(s_t)` (BGKM16, Section 2) of a two-opinion configuration:
the square root of the volume of its minority side. -/
noncomputable def potential (s : Config V Bool) : ℝ := Real.sqrt (vol G (minority G s))

end Static

section Dynamic

/-- The lazy voter on a **dynamic graph** (BGKM16, Section 1.1): the round from time `t` to time
`t + 1`, started in the configuration `x`, is a round of the lazy voter on the graph `G t x`.
Letting the graph depend on the current configuration models an adversary that knows the current
opinions when it redistributes the edges. -/
noncomputable def dynamicLazy [Fintype C] (G : ℕ → Config V C → SimpleGraph V)
    [∀ t x, DecidableRel (G t x).Adj] (hd : ∀ t x v, 0 < (G t x).degree v) (t : ℕ) :
    Kernel (Config V C) :=
  fun x => transition (lazyNeighbor (G t x) (hd t x)) x

end Dynamic

end Voter
