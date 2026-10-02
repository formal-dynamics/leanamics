import Dynamics.Rounds
import Dynamics.Absorption
import Mathlib

/-! # The undecided-state dynamics (synchronous, binary, complete graph)

Each of `n` nodes holds opinion `a`, opinion `b`, or is undecided (`u`). In every round each node
samples a node uniformly at random (with replacement, possibly itself): an undecided node adopts
the sampled opinion; a decided node that samples the other opinion becomes undecided; otherwise
nothing changes.

With `a`, `b`, `q` the numbers of `a`-, `b`- and undecided nodes, one round gives, in expectation,
`a (n - b + q) / n` nodes with opinion `a`, `(q² + 2 a b) / n` undecided nodes, and hence a bias
`(a - b)(1 + q / n)`: the undecided nodes amplify the current majority. Every run is eventually
absorbed in one of the three monochromatic configurations.
-/

namespace Undecided
open Finset Dynamics Filter Topology

/-- Opinions: `a`, `b`, or undecided. -/
inductive Op
  | a
  | b
  | u
  deriving DecidableEq, Fintype

/-- New state of a node holding `x` that samples a node holding `y`. -/
def update : Op → Op → Op
  | .u, y => y
  | x, .u => x
  | .a, .a => .a
  | .b, .b => .b
  | .a, .b => .u
  | .b, .a => .u

/-- Configurations of `n` nodes. -/
abbrev Config (n : ℕ) := Fin n → Op

variable {n : ℕ}

/-- One synchronous round: node `v` samples node `r v`. -/
def step (x : Config n) (r : Fin n → Fin n) : Config n := fun v => update (x v) (x (r v))

/-- Number of nodes in state `o`. -/
def count (x : Config n) (o : Op) : ℕ := (univ.filter fun v => x v = o).card

/-- All nodes are in the same state. -/
def Mono (x : Config n) : Prop := ∃ o, ∀ v, x v = o

/-- Indicator of not yet being monochromatic. -/
noncomputable def notMono (x : Config n) : ℝ := by
  classical
  exact if Mono x then 0 else 1

variable [NeZero n]

/-- The dynamics as a Markov kernel on configurations (uniform i.i.d. rounds). -/
noncomputable def kernel (n : ℕ) [NeZero n] : Kernel (Config n) := Kernel.ofStep (step (n := n))

/-- Expected number of `a`-nodes after one round. -/
theorem expected_count_a (x : Config n) :
    avg (fun r : Fin n → Fin n => (count (step x r) .a : ℝ)) =
      count x .a * (n - count x .b + count x .u) / n := by
  sorry

/-- Expected number of `b`-nodes after one round. -/
theorem expected_count_b (x : Config n) :
    avg (fun r : Fin n → Fin n => (count (step x r) .b : ℝ)) =
      count x .b * (n - count x .a + count x .u) / n := by
  sorry

/-- Expected number of undecided nodes after one round. -/
theorem expected_count_u (x : Config n) :
    avg (fun r : Fin n → Fin n => (count (step x r) .u : ℝ)) =
      (count x .u ^ 2 + 2 * count x .a * count x .b) / n := by
  sorry

/-- The bias grows in expectation by the factor `1 + q / n`. -/
theorem expected_bias (x : Config n) :
    avg (fun r : Fin n → Fin n => (count (step x r) .a : ℝ) - count (step x r) .b) =
      (count x .a - count x .b) * (1 + count x .u / n) := by
  sorry

/-- Monochromatic configurations are fixed points. -/
theorem step_of_mono (x : Config n) (h : Mono x) (r : Fin n → Fin n) : step x r = x := by
  sorry

/-- Almost-sure absorption: the probability of not being monochromatic after `t` rounds tends
to zero, from every configuration. -/
theorem absorbed (x : Config n) :
    Tendsto (fun t => (kernel n).iterate t notMono x) atTop (𝓝 0) := by
  sorry

end Undecided
