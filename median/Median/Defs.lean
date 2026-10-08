import Dynamics.Rounds
import Dynamics.Absorption
import Dynamics.Tail
import Mathlib

/-! # The median dynamics: definitions

Doerr, Goldberg, Minder, Sauerwald and Scheideler, *Stabilizing consensus with the power of two
choices* (SPAA 2011): every node holds a value from a linearly ordered set; in each round it
samples two nodes uniformly at random (independently, with replacement) and adopts the median of
its own value and the two sampled values. With two values this is the 2-Choices dynamics.
-/

namespace Median
open Finset Dynamics

/-- Median of three elements of a linear order. -/
def med3 {α : Type*} [LinearOrder α] (a b c : α) : α := max (min a b) (min (max a b) c)

/-- Configurations of `n` nodes with values in `α`. -/
abbrev Config (n : ℕ) (α : Type*) := Fin n → α

/-- A round: the two nodes sampled by every node. -/
abbrev Round (n : ℕ) := Fin n → Fin n × Fin n

variable {n : ℕ} {α : Type*} [LinearOrder α]

/-- One synchronous round of the median rule. -/
def step (x : Config n α) (r : Round n) : Config n α :=
  fun v => med3 (x v) (x (r v).1) (x (r v).2)

/-- The configuration after a list of rounds (the first round first). -/
def run (x : Config n α) (l : List (Round n)) : Config n α := l.foldl step x

/-- Number of nodes holding `true` (binary case, `false < true`). -/
def ones (x : Config n Bool) : ℕ := (univ.filter fun v => x v = true).card

/-- All nodes hold the same value. -/
def Consensus (x : Config n α) : Prop := ∃ c, ∀ v, x v = c

/-- Indicator of not yet being in consensus. -/
noncomputable def notConsensus (x : Config n α) : ℝ := by
  classical
  exact if Consensus x then 0 else 1

/-- The median dynamics as a Markov kernel (uniform i.i.d. rounds). -/
noncomputable def kernel (n : ℕ) [NeZero n] (α : Type*) [LinearOrder α] [Fintype α] :
    Kernel (Config n α) :=
  Kernel.ofStep (step (n := n) (α := α))

end Median
