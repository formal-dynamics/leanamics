import Voter.Absorption

/-! # Propagation through the kernel support (Lemma 2.1 with a self-loop)

The propagation half of Lemma 2.1 (`Voter.Graph`) only uses rounds in which every vertex copies
a graph neighbour, so it needs a monochromatic edge to start, hence a nonbipartite graph. Here a
round is possible when every vertex samples a vertex of positive weight in its row of the
kernel. Self-loops are then allowed, and a vertex that keeps its own colour with positive
probability is a monochromatic region on its own: this is the Remark on p. 254 of Hassin and
Peleg. The propagation itself is `propagate_region_of_rel` (`Voter.Graph`), shared with graph
rounds, and the probabilistic half is `consensus_tendsto_of_kernelPossible` (`Voter.Absorption`).
-/

namespace Voter
open Finset Dynamics Filter Topology
variable {V C : Type*} [Fintype V] [DecidableEq V]

/-- Every finite distribution charges some point. -/
lemma exists_weight_pos {α : Type*} [Fintype α] (p : Distribution α) : ∃ a, 0 < p.weight a := by
  obtain ⟨a, -, ha⟩ := exists_ne_zero_of_sum_ne_zero (s := univ) (f := p.weight)
    (by rw [p.sum_one]; exact one_ne_zero)
  exact ⟨a, lt_of_le_of_ne (p.nonneg a) (Ne.symm ha)⟩

/-- **Lemma 2.1, propagation through the kernel support.** On a connected graph whose edges are
charged by `H`, a monochromatic region in which every vertex charges a vertex of the region
grows to consensus along a finite chain of rounds in the kernel support. -/
lemma propagate_kernel_region (G : SimpleGraph V) (hc : G.Connected) (H : Kernel V)
    (hsupport : ∀ i j, G.Adj i j → 0 < (H i).weight j) (s : Config V C) (S : Finset V) (c : C)
    (hne : S.Nonempty) (hcolor : ∀ i ∈ S, s i = c)
    (hinternal : ∀ i ∈ S, ∃ j ∈ S, 0 < (H i).weight j) :
    Relation.ReflTransGen (KernelPossible H) s (fun _ => c) :=
  propagate_region_of_rel G hc (fun i j => 0 < (H i).weight j) hsupport
    (fun i => exists_weight_pos (H i)) s S c hne hcolor hinternal

/-- **Remark on p. 254, possibility half.** If `v` keeps its colour with positive probability,
every configuration can reach consensus in the colour of `v` through rounds in the kernel
support, on any connected graph whose edges are charged by `H`. -/
lemma kernelPossible_consensus_of_selfLoop (G : SimpleGraph V) (hc : G.Connected)
    (H : Kernel V) (hsupport : ∀ i j, G.Adj i j → 0 < (H i).weight j)
    {v : V} (hv : 0 < (H v).weight v) (s : Config V C) :
    Relation.ReflTransGen (KernelPossible H) s (fun _ => s v) := by
  refine propagate_kernel_region G hc H hsupport s {v} (s v) (singleton_nonempty v) ?_ ?_
  · intro i hi
    rw [mem_singleton.mp hi]
  · intro i hi
    rw [mem_singleton.mp hi]
    exact ⟨v, mem_singleton_self v, hv⟩

/-- **Lemma 2.1 with the Remark on p. 254.** With a self-loop of positive weight, nonconsensus
probability tends to zero on every connected graph whose edges are charged by `H`, bipartite
or not. -/
theorem consensus_tendsto_of_selfLoop (G : SimpleGraph V) (hc : G.Connected)
    (H : Kernel V) (hsupport : ∀ i j, G.Adj i j → 0 < (H i).weight j)
    (hloop : ∃ v, 0 < (H v).weight v) (s : Config V Bool) :
    Tendsto (fun n => (transition H).iterate n survival s) atTop (𝓝 0) := by
  obtain ⟨v, hv⟩ := hloop
  exact consensus_tendsto_of_kernelPossible H
    (fun t => ⟨_, kernelPossible_consensus_of_selfLoop G hc H hsupport hv t⟩) s

end Voter
