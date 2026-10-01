import Dynamics.Distribution
import Mathlib

/-! # Reed–Frost epidemics and bond percolation, pathwise (EPI-1)

The Reed–Frost (Independent Cascade) epidemic on a finite graph `G`: in every round, each infected
node infects each susceptible neighbour across the edge between them if that edge is *open*, and
then recovers for good. Every edge carries a single coin `ω e : Bool`, flipped once and for all
(`true` = open). The open edges form the percolated graph `perc G ω`.

Pathwise, for every coin assignment, the nodes infected in round `t` are exactly those at distance
`t` from the initial set `I₀` in `perc G ω`, and the recovered ones those at distance `< t`; the
epidemic is over after `card V` rounds, and its final recovered set is the set of nodes connected to
`I₀` by open edges. With i.i.d. Bernoulli(`p`) coins, the probability that a node is eventually
infected is the probability that bond percolation connects it to `I₀`.
-/

namespace Epidemics
open Finset Dynamics

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The percolated graph: the edges of `G` whose coin is `true`. -/
def perc (G : SimpleGraph V) (ω : Sym2 V → Bool) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ ω s(u, v) = true
  symm := ⟨fun u v h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
  loopless := ⟨fun u h => G.loopless.irrefl u h.1⟩

/-- Infected and recovered nodes; the others are susceptible. -/
structure SIR (V : Type*) where
  infected : Finset V
  recovered : Finset V

/-- One round: a susceptible node becomes infected if it has an infected neighbour across an open
edge; every infected node recovers. -/
def step (G : SimpleGraph V) [DecidableRel G.Adj] (ω : Sym2 V → Bool) (s : SIR V) : SIR V where
  infected := univ.filter fun v => v ∉ s.infected ∧ v ∉ s.recovered ∧ ∃ u ∈ s.infected, G.Adj u v ∧ ω s(u, v) = true
  recovered := s.recovered ∪ s.infected

/-- The epidemic started from the infected set `I₀`, with nobody recovered. -/
def run (G : SimpleGraph V) [DecidableRel G.Adj] (ω : Sym2 V → Bool) (I₀ : Finset V) : ℕ → SIR V
  | 0 => ⟨I₀, ∅⟩
  | t + 1 => step G ω (run G ω I₀ t)

/-- Distance from the set `I₀` in a graph `H` (`⊤` if `v` is not connected to `I₀`). -/
noncomputable def setDist (H : SimpleGraph V) (I₀ : Finset V) (v : V) : ℕ∞ :=
  ⨅ u ∈ I₀, H.edist u v

/-- Pathwise layers: the nodes infected in round `t` are those at percolation distance `t`. -/
theorem infected_iff (G : SimpleGraph V) [DecidableRel G.Adj] (ω : Sym2 V → Bool) (I₀ : Finset V)
    (t : ℕ) (v : V) :
    v ∈ (run G ω I₀ t).infected ↔ setDist (perc G ω) I₀ v = t := by
  sorry

/-- The nodes recovered by round `t` are those at percolation distance `< t`. -/
theorem recovered_iff (G : SimpleGraph V) [DecidableRel G.Adj] (ω : Sym2 V → Bool) (I₀ : Finset V)
    (t : ℕ) (v : V) :
    v ∈ (run G ω I₀ t).recovered ↔ setDist (perc G ω) I₀ v < t := by
  sorry

/-- The epidemic is over after `card V` rounds. -/
theorem extinct (G : SimpleGraph V) [DecidableRel G.Adj] (ω : Sym2 V → Bool) (I₀ : Finset V)
    (t : ℕ) (ht : Fintype.card V ≤ t) :
    (run G ω I₀ t).infected = ∅ := by
  sorry

/-- Final size: the eventually recovered nodes are those connected to `I₀` by open edges. -/
theorem final_recovered_iff (G : SimpleGraph V) [DecidableRel G.Adj] (ω : Sym2 V → Bool)
    (I₀ : Finset V) (v : V) :
    v ∈ (run G ω I₀ (Fintype.card V)).recovered ↔ ∃ u ∈ I₀, (perc G ω).Reachable u v := by
  sorry

/-- A biased coin: `true` with probability `p`. -/
noncomputable def bernoulli (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : Distribution Bool where
  weight b := if b then p else 1 - p
  nonneg b := by cases b <;> simp [h0, h1]
  sum_one := by simp

/-- Independent Bernoulli(`p`) coins, one per unordered pair of nodes. -/
noncomputable def coins (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : Distribution (Sym2 V → Bool) :=
  Distribution.independent fun _ => bernoulli p h0 h1

/-- The coin of a single pair is open with probability `p`. -/
theorem coins_prob_open (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (e : Sym2 V) :
    (coins (V := V) p h0 h1).prob (fun ω => ω e = true) = p := by
  sorry

/-- Reed–Frost ⇔ bond percolation: the probability that `v` is eventually infected equals the
probability that `v` is connected to `I₀` in the percolated graph. -/
theorem prob_infected_eq_prob_connected (G : SimpleGraph V) [DecidableRel G.Adj] (p : ℝ)
    (h0 : 0 ≤ p) (h1 : p ≤ 1) (I₀ : Finset V) (v : V) :
    (coins p h0 h1).prob (fun ω => v ∈ (run G ω I₀ (Fintype.card V)).recovered) =
      (coins p h0 h1).prob (fun ω => ∃ u ∈ I₀, (perc G ω).Reachable u v) := by
  sorry

/-- The epidemic cannot outlast the percolation distances: if every node connected to `I₀` is at
distance `< t`, nobody is infected in round `t`. -/
theorem extinct_of_dist_lt (G : SimpleGraph V) [DecidableRel G.Adj] (ω : Sym2 V → Bool)
    (I₀ : Finset V) (t : ℕ) (h : ∀ v, setDist (perc G ω) I₀ v ≠ ⊤ → setDist (perc G ω) I₀ v < t) :
    (run G ω I₀ t).infected = ∅ := by
  sorry

end Epidemics
