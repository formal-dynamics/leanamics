import Dynamics.Kernel

/-!
# Lazy kernels

The lazy version `(I + K)/2` of a finite kernel `K` stays put with probability `1/2` and
otherwise moves according to `K` (`Kernel.lazy`). It charges every self-loop with weight at
least `1/2` (`lazy_weight_self_ge_half`), charges everything `K` charges (`lazy_weight_pos`)
and has the same stationary distributions as `K` (`lazy_stationary_iff`). Laziness is the
standard way to make a walk aperiodic, e.g. the lazy random walk `(I + D⁻¹A)/2` on a graph
(`Kernel.lazyNeighbor` in `Dynamics/RandomWalk.lean`).
-/

namespace Dynamics
open Finset

namespace Kernel
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The lazy version `(I + K)/2` of a kernel: stay with probability `1/2`, otherwise move
according to `K`. -/
noncomputable def lazy (K : Kernel V) : Kernel V := fun i => {
  weight := fun j => ((if i = j then 1 else 0) + (K i).weight j) / 2
  nonneg := fun j => by
    have := (K i).nonneg j
    split <;> positivity
  sum_one := by
    rw [← sum_div, sum_add_distrib, (K i).sum_one, sum_ite_eq]
    norm_num }

/-- Entries of the lazy kernel: `(I + K)/2`. -/
theorem lazy_weight (K : Kernel V) (i j : V) :
    (lazy K i).weight j = ((if i = j then 1 else 0) + (K i).weight j) / 2 :=
  rfl

/-- Expectation under the lazy kernel: half the current value plus half the `K`-expectation. -/
theorem lazy_expect (K : Kernel V) (x : V) (f : V → ℝ) :
    (lazy K x).expect f = f x / 2 + (K x).expect f / 2 := by
  simp only [Distribution.expect, lazy_weight, add_div, add_mul, sum_add_distrib, ite_div,
    ite_mul, zero_div, zero_mul, sum_ite_eq, mem_univ, if_true, sum_div]
  congr 1
  · ring
  · exact sum_congr rfl fun _ _ => by ring

/-- Laziness does not change stationary distributions: `p (I + K)/2 = p ↔ p K = p`. -/
theorem lazy_stationary_iff (K : Kernel V) (p : Distribution V) :
    (lazy K).Stationary p ↔ K.Stationary p := by
  unfold Kernel.Stationary
  refine forall_congr' fun b => ?_
  simp only [lazy_weight, mul_div_assoc', ← sum_div, mul_add, sum_add_distrib, mul_ite,
    mul_one, mul_zero, sum_ite_eq', mem_univ, if_true]
  constructor <;> intro h <;> linarith

/-- The lazy kernel charges every self-loop with weight at least `1/2`. -/
theorem lazy_weight_self_ge_half (K : Kernel V) (v : V) : 1 / 2 ≤ (lazy K v).weight v := by
  rw [lazy_weight, if_pos rfl]
  have := (K v).nonneg v
  linarith

/-- The lazy kernel charges every self-loop. -/
theorem lazy_selfLoop_pos (K : Kernel V) (v : V) : 0 < (lazy K v).weight v :=
  lt_of_lt_of_le (by norm_num) (lazy_weight_self_ge_half K v)

/-- The lazy kernel charges everything `K` charges. -/
theorem lazy_weight_pos (K : Kernel V) {i j : V} (h : 0 < (K i).weight j) :
    0 < (lazy K i).weight j := by
  rw [lazy_weight]
  have : (0 : ℝ) ≤ if i = j then 1 else 0 := by split <;> norm_num
  positivity

end Kernel
end Dynamics
