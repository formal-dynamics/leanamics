import Mathlib.Combinatorics.SimpleGraph.Star
import Moran.Isothermal

/-! # The Birth–death Moran process on the star: definitions (MOR-3)

The star with `n` leaves is Mathlib's `SimpleGraph.starGraph c` on a vertex type `V` with
`Fintype.card V = n + 1`: the centre `c` is adjacent to every other vertex (a leaf), and the
leaves are adjacent only to `c`.

Following Broom and Rychtář (*An analysis of the fixation probability of a mutant on special
classes of non-directed graphs*, Proc. R. Soc. A 464, 2008, §5), the state of the Birth–death
process on the star is summarized by the number `i` of mutant leaves and the type of the centre.
The fixation probability increments in `i` are in the ratio
`q = (n + r) / (r (n r + 1))` (`starRatio`). With the centre weight
`κ = (n r + 1) / (r (n + r)) = 1 / (r ^ 2 q)` (`starCentreWeight`), the potential
`q ^ i * κ ^ [centre is mutant]` (`starPotential`) is invariant in expectation under one step,
the analogue on the star of the potential `(1/r) ^ (#mutants)` of the isothermal theorem.
-/

namespace Moran
open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Number of mutant leaves of the star centred at `c`, i.e. of mutants other than `c`
(the index `i` of Broom–Rychtář 2008, §5). -/
def leafMutants (c : V) (s : Config V) : ℕ := (univ.filter fun v => v ≠ c ∧ s v = true).card

/-- The ratio `q = (n + r) / (r (n r + 1))` of the star with `n` leaves (Broom–Rychtář 2008,
§5): consecutive increments of the fixation probability in the number of mutant leaves are in
ratio `q`. -/
noncomputable def starRatio (n : ℕ) (r : ℝ) : ℝ := (n + r) / (r * (n * r + 1))

/-- The weight `κ = (n r + 1) / (r (n + r))` of a mutant centre in the star potential; it
satisfies `r ^ 2 * q * κ = 1`. -/
noncomputable def starCentreWeight (n : ℕ) (r : ℝ) : ℝ := (n * r + 1) / (r * (n + r))

/-- The potential `q ^ (#mutant leaves) * κ ^ [centre is mutant]` of the star centred at `c`
with `n` leaves, invariant in expectation under the Birth–death Moran step. -/
noncomputable def starPotential (c : V) (n : ℕ) (r : ℝ) (s : Config V) : ℝ :=
  starRatio n r ^ leafMutants c s * (if s c then starCentreWeight n r else 1)

end Moran
