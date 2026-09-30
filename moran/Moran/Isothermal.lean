import Dynamics.Absorption

/-! # The Moran process and the isothermal theorem (MOR-1, MOR-2)

Birth–death Moran process on a finite graph: mutants have fitness `r > 0`, residents
fitness `1`. In each step a parent is chosen with probability proportional to its fitness,
and its offspring replaces a uniformly random neighbour (an isolated parent replaces itself,
so nothing changes).

On a regular graph, in every configuration a step increases the number of mutants with
exactly `r` times the probability that it decreases it. Hence `(1/r)^(#mutants)` is invariant
in expectation, and on a connected regular graph the fixation probability from `k` mutants is
Moran's formula `(1 - r^{-k}) / (1 - r^{-n})` (for `r ≠ 1`), or `k/n` in the neutral case.
This is the "if" direction of the isothermal theorem of Lieberman, Hauert and Nowak (2005);
the complete graph gives Moran's classical formula (1958).
-/

namespace Moran
open Dynamics Finset Filter Topology

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A configuration marks each vertex as mutant (`true`) or resident (`false`). -/
abbrev Config (V : Type*) := V → Bool

/-- Number of mutants. -/
def mutants (s : Config V) : ℕ := (univ.filter fun i => s i = true).card

/-- Fitness: `r` for mutants, `1` for residents. -/
def fitness (r : ℝ) (s : Config V) (u : V) : ℝ := if s u then r else 1

/-- Total fitness of the population. -/
def totalFitness (r : ℝ) (s : Config V) : ℝ := ∑ u, fitness r s u

/-- Offspring placement: a uniformly random neighbour of the parent `u`, or `u` itself if it
has no neighbour. -/
noncomputable def target (G : SimpleGraph V) [DecidableRel G.Adj] (u w : V) : ℝ :=
  if G.degree u = 0 then (if w = u then 1 else 0)
  else (if G.Adj u w then (G.degree u : ℝ)⁻¹ else 0)

/-- The weights of (parent, offspring position) pairs are nonnegative. -/
theorem pair_weight_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℝ} (hr : 0 < r)
    (s : Config V) (p : V × V) :
    0 ≤ fitness r s p.1 / totalFitness r s * target G p.1 p.2 := by
  sorry

/-- The weights of (parent, offspring position) pairs sum to one. -/
theorem pair_weight_sum_one [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℝ}
    (hr : 0 < r) (s : Config V) :
    ∑ p : V × V, fitness r s p.1 / totalFitness r s * target G p.1 p.2 = 1 := by
  sorry

/-- Distribution of the (parent, offspring position) pair in one Birth–death step. -/
noncomputable def pairDist [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℝ)
    (hr : 0 < r) (s : Config V) : Distribution (V × V) where
  weight p := fitness r s p.1 / totalFitness r s * target G p.1 p.2
  nonneg p := pair_weight_nonneg G hr s p
  sum_one := pair_weight_sum_one G hr s

/-- The Birth–death Moran kernel: the offspring copies the parent's type. -/
noncomputable def moranKernel [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℝ)
    (hr : 0 < r) : Kernel (Config V) :=
  fun s => (pairDist G r hr s).map (fun p => Function.update s p.2 (s p.1))

/-- Indicator of fixation (every vertex is a mutant). -/
def allMutant (s : Config V) : ℝ := if s = fun _ => true then 1 else 0

/-- Indicator that neither type has taken over yet. -/
noncomputable def unfixed (s : Config V) : ℝ := by
  classical
  exact if ∃ c, s = fun _ => c then 0 else 1

/-- Fixation probability: the supremum of the finite-time fixation probabilities. -/
noncomputable def fixation (K : Kernel (Config V)) (s : Config V) : ℝ :=
  ⨆ t, K.iterate t allMutant s

/-- **Invariance.** On a regular graph, `(1/r)^(#mutants)` is preserved in expectation by one
Moran step. -/
theorem moran_potential_invariant [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hreg : ∀ i, G.degree i = d) {r : ℝ} (hr : 0 < r) (s : Config V) :
    (moranKernel G r hr).apply (fun t => (1 / r) ^ mutants t) s = (1 / r) ^ mutants s := by
  sorry

/-- **Neutral invariance.** On a regular graph with `r = 1`, the number of mutants is preserved
in expectation by one Moran step. -/
theorem moran_mutants_invariant [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hreg : ∀ i, G.degree i = d) (s : Config V) :
    (moranKernel G 1 one_pos).apply (fun t => (mutants t : ℝ)) s = mutants s := by
  sorry

/-- **Absorption.** On a connected graph, the probability that neither type has fixed tends to
zero. -/
theorem moran_unfixed_tendsto [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) {r : ℝ} (hr : 0 < r) (s : Config V) :
    Tendsto (fun t => (moranKernel G r hr).iterate t unfixed s) atTop (𝓝 0) := by
  sorry

/-- **Isothermal theorem ("if" direction).** On a connected regular graph, the fixation
probability from `k` mutants is Moran's formula `(1 - r^{-k}) / (1 - r^{-n})`. -/
theorem isothermal [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (d : ℕ) (hreg : ∀ i, G.degree i = d) {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) (s : Config V) :
    fixation (moranKernel G r hr) s =
      (1 - (1 / r) ^ mutants s) / (1 - (1 / r) ^ Fintype.card V) := by
  sorry

/-- **Neutral case.** On a connected regular graph with `r = 1`, the fixation probability is the
initial fraction of mutants. -/
theorem isothermal_neutral [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (d : ℕ) (hreg : ∀ i, G.degree i = d) (s : Config V) :
    fixation (moranKernel G 1 one_pos) s = (mutants s : ℝ) / Fintype.card V := by
  sorry

/-- **Moran's formula (1958).** On the complete graph, the fixation probability from `k`
mutants is `(1 - r^{-k}) / (1 - r^{-n})`. -/
theorem moran_formula [Nonempty V] {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) (s : Config V) :
    fixation (moranKernel (⊤ : SimpleGraph V) r hr) s =
      (1 - (1 / r) ^ mutants s) / (1 - (1 / r) ^ Fintype.card V) := by
  sorry

end Moran
