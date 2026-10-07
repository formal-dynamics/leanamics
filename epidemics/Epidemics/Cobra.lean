import Dynamics.Uniform
import Mathlib

/-! # The COBRA walk and the BIPS epidemic (EPI-4, model)

Cooper, Radzik, Rivera, *The coalescing-branching random walk on expanders and the dual epidemic
process*, PODC 2016 (arXiv:1602.05768), Section 1.

Both processes run on a finite simple graph `G` with a branching factor `k`, and are driven by the
same rounds of randomness: in every round each vertex `x` samples `k` neighbours, independently and
uniformly at random with replacement. A round is an element of the finite type `Choices G k`, and
`t` i.i.d. uniform rounds are averaged with `Dynamics.expList (Choices G k) t`.

* **COBRA** (coalescing-branching random walk): every vertex of the current set `C_t` pushes to its
  `k` sampled neighbours, and `C_{t+1}` is the set of all vertices pushed to. A vertex is active
  only when it has just been chosen ("not necessarily for the first time").
* **BIPS** (biased infection with persistent source `v`): the source `v` is always infected, and
  every other vertex is infected at time `t + 1` iff at least one of its `k` sampled neighbours
  was infected at time `t` (an SIS-type epidemic).
-/

namespace Epidemics
open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- One round of neighbour choices: every vertex `x` samples `k` neighbours `r x 0, …, r x (k-1)`.
A uniformly random element of this finite product type is exactly the paper's sampling: for
every vertex, `k` neighbours chosen uniformly at random with replacement, independently across
vertices (and, through `Dynamics.expList`, across rounds). -/
def Choices (G : SimpleGraph V) (k : ℕ) : Type _ := (x : V) → Fin k → G.neighborSet x

/-- Rounds of neighbour choices form a finite type, so `Dynamics.expList` can average over them. -/
instance instFintypeChoices (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    Fintype (Choices G k) :=
  inferInstanceAs (Fintype ((x : V) → Fin k → G.neighborSet x))

omit [Fintype V] [DecidableEq V] in
/-- On a connected graph with at least two vertices every vertex has a neighbour, so rounds of
neighbour choices exist: the processes are well defined on the graphs of the paper, and
`Dynamics.expList (Choices G k) t` is a genuine probability average (its total mass is `1`). -/
theorem choices_nonempty (G : SimpleGraph V) [Nontrivial V] (hG : G.Connected) (k : ℕ) :
    Nonempty (Choices G k) := by
  have h (x : V) : Nonempty (G.neighborSet x) :=
    let ⟨u, hu⟩ := hG.preconnected.exists_adj_of_nontrivial x
    ⟨⟨u, hu⟩⟩
  exact ⟨fun x _ => (h x).some⟩

variable {G : SimpleGraph V} {k : ℕ}

/-- One COBRA round (Section 1, "Coalescing Branching Random Walk"): each vertex of `D` pushes to
its `k` sampled neighbours; the next set consists of all chosen vertices. -/
def cobraStep (D : Finset V) (r : Choices G k) : Finset V :=
  D.biUnion fun x => univ.image fun i => (r x i : V)

/-- COBRA after the rounds `l` (first round first), started from `C₀ = C`: the set `C_s` when
`l` lists the first `s` rounds. -/
def cobraRun (C : Finset V) (l : List (Choices G k)) : Finset V :=
  l.foldl cobraStep C

/-- One BIPS round with persistent source `v` (Section 1, "Biased Infection with Persistent
Source"): a vertex is infected next iff it is `v` or one of its `k` sampled neighbours is in the
current infected set `A`. -/
def bipsStep (v : V) (A : Finset V) (r : Choices G k) : Finset V :=
  insert v (univ.filter fun u => ∃ i, (r u i : V) ∈ A)

/-- BIPS with source `v` after the rounds `l` (first round first), started from the infected set
`A₀`; the paper's process starts from `A₀ = {v}`. -/
def bipsRun (v : V) (A₀ : Finset V) (l : List (Choices G k)) : Finset V :=
  l.foldl (bipsStep v) A₀

end Epidemics
