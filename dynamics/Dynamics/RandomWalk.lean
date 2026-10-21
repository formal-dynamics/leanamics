import Dynamics.GraphRounds
import Dynamics.Lazy

/-!
# Random-walk kernels on graphs

Kernels on the vertices of a finite simple graph `G` with no isolated vertex
(`hd : ∀ v, 0 < G.degree v`):

* `Kernel.uniformNeighbor G hd`: move to a uniformly random neighbour, `D⁻¹A`. Its support is
  the edge set (`uniformNeighbor_support`) and its expectations are neighbour averages
  (`uniformNeighbor_expect`, and `uniformNeighbor_expect_eq_avg` in the `avg` form of
  `Dynamics/GraphRounds.lean`).
* `Kernel.lazyNeighbor G hd = lazy (uniformNeighbor G hd)`: the lazy random walk `(I + D⁻¹A)/2`
  (`lazyNeighbor_weight`, `lazyNeighbor_expect`).
-/

namespace Dynamics
open Finset

namespace Kernel
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Uniform sampling among the neighbours: the simple random walk `D⁻¹A` on `G`. -/
noncomputable def uniformNeighbor (hd : ∀ i, 0 < G.degree i) : Kernel V := fun i => {
  weight := fun j => if G.Adj i j then (G.degree i : ℝ)⁻¹ else 0
  nonneg := fun j => by split <;> positivity
  sum_one := by
    rw [← Finset.sum_filter]
    have he : univ.filter (G.Adj i) = G.neighborFinset i := by ext j; simp
    rw [he]
    simp [ne_of_gt (hd i)] }

/-- The simple random walk charges exactly the edges. -/
theorem uniformNeighbor_support (hd : ∀ i, 0 < G.degree i) (i j : V) :
    0 < (uniformNeighbor G hd i).weight j ↔ G.Adj i j := by
  simp only [uniformNeighbor]
  split_ifs with h
  · simp [h, hd i]
  · simp [h]

variable {G}

/-- Expectation under uniform neighbour sampling is the average over the neighbours. -/
theorem uniformNeighbor_expect (hd : ∀ i, 0 < G.degree i) (x : V) (f : V → ℝ) :
    (uniformNeighbor G hd x).expect f =
      (∑ w ∈ G.neighborFinset x, f w) / G.degree x := by
  simp only [Distribution.expect, uniformNeighbor]
  have h (j : V) :
      (if G.Adj x j then (G.degree x : ℝ)⁻¹ else 0) * f j =
        if G.Adj x j then f j / G.degree x else 0 := by
    by_cases hj : G.Adj x j
    · simp [hj, div_eq_mul_inv, mul_comm]
    · simp [hj]
  simp_rw [h]
  rw [← Finset.sum_filter]
  have he : Finset.univ.filter (G.Adj x) = G.neighborFinset x := by
    ext j
    simp
  rw [he, ← Finset.sum_div]

/-- Expectation under uniform neighbour sampling is the uniform average `avg` over the
neighbour set. -/
theorem uniformNeighbor_expect_eq_avg (hd : ∀ i, 0 < G.degree i) (x : V) (f : V → ℝ) :
    (uniformNeighbor G hd x).expect f = avg (fun u : G.neighborSet x => f u) := by
  rw [uniformNeighbor_expect, avg_neighborSet]

variable (G) [DecidableEq V]

/-- The lazy random walk `(I + D⁻¹A)/2` on `G`: stay with probability `1/2`, otherwise move to
a uniformly random neighbour. -/
noncomputable def lazyNeighbor (hd : ∀ i, 0 < G.degree i) : Kernel V :=
  lazy (uniformNeighbor G hd)

/-- Entries of the lazy random walk: `(I + D⁻¹A)/2`. -/
theorem lazyNeighbor_weight (hd : ∀ i, 0 < G.degree i) (i j : V) :
    (lazyNeighbor G hd i).weight j =
      ((if i = j then 1 else 0) + (if G.Adj i j then (G.degree i : ℝ)⁻¹ else 0)) / 2 :=
  rfl

variable {G}

/-- Expectation under the lazy random walk: half the current value plus half the neighbour
average. -/
theorem lazyNeighbor_expect (hd : ∀ i, 0 < G.degree i) (x : V) (f : V → ℝ) :
    (lazyNeighbor G hd x).expect f =
      f x / 2 + (∑ w ∈ G.neighborFinset x, f w) / (2 * G.degree x) := by
  rw [lazyNeighbor, lazy_expect, uniformNeighbor_expect, div_div, mul_comm (G.degree x : ℝ)]

end Kernel
end Dynamics
