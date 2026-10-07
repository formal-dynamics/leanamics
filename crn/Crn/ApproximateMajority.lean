import Crn.Protocol

/-!
# Worked instance: the approximate-majority CRN (CRN-1)

The approximate-majority CRN of Angluin, Aspnes and Eisenstat (2008), which Cardelli and
Csikász-Nagy (2012) identify with the cell-cycle switch, has species `X`, `Y` (the two
opinions) and `B` (blank, or undecided) and four reactions with a common rate constant:

`X + Y → X + B`, `X + Y → Y + B`, `B + X → X + X`, `B + Y → Y + Y`.

From counts `x` with `D = 2·#X·#Y + #B·(#X + #Y) > 0`, its jump chain fires each of the two
`X + Y` reactions with probability `#X·#Y / D`, `B + X → X + X` with probability `#B·#X / D` and
`B + Y → Y + Y` with probability `#B·#Y / D` (`network_jump_expect`). By CRN-1 this is the
sequential undecided-state dynamics on `n` agents, conditioned on the drawn pair reacting
(`network_jumpKernel_eq_ppKernel`); a drawn pair reacts with probability `D / (4·C(n, 2))`
(`network_reactProb_eq`).
-/

namespace Crn.ApproxMajority
open Dynamics

/-- Species of the approximate-majority CRN: the two opinions `X`, `Y` and the blank `B`. -/
inductive Species
  | X
  | Y
  | B
  deriving DecidableEq, Fintype

open Species

/-- `X + Y → X + B`: an `X` turns a `Y` blank. -/
def xyToXB : Reaction Species := ⟨s(X, Y), s(X, B)⟩

/-- `X + Y → Y + B`: a `Y` turns an `X` blank. -/
def xyToYB : Reaction Species := ⟨s(X, Y), s(Y, B)⟩

/-- `B + X → X + X`: an `X` recruits a blank. -/
def bxToXX : Reaction Species := ⟨s(B, X), s(X, X)⟩

/-- `B + Y → Y + Y`: a `Y` recruits a blank. -/
def byToYY : Reaction Species := ⟨s(B, Y), s(Y, Y)⟩

/-- The approximate-majority CRN. -/
def network : Network Species where
  reactions := {xyToXB, xyToYB, bxToXX, byToYY}
  nonempty := Finset.insert_nonempty _ _
  nontrivial := by decide

/-- The four reactions of the approximate-majority CRN. -/
lemma network_reactions : network.reactions = {xyToXB, xyToYB, bxToXX, byToYY} := rfl

/-- Propensity-weighted sums over the four reactions. -/
lemma network_sum (k : ℝ) {n : ℕ} (x : Counts Species n) (g : Counts Species n → ℝ) :
    ∑ r ∈ network.reactions, r.propensity k x * g (x.react r) =
      k * ((x.1 X * x.1 Y : ℝ) * g (x.react xyToXB) + (x.1 X * x.1 Y : ℝ) * g (x.react xyToYB) +
        (x.1 B * x.1 X : ℝ) * g (x.react bxToXX) + (x.1 B * x.1 Y : ℝ) * g (x.react byToYY)) := by
  rw [network_reactions, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    Reaction.propensity_of_ne k xyToXB x rfl (by decide),
    Reaction.propensity_of_ne k xyToYB x rfl (by decide),
    Reaction.propensity_of_ne k bxToXX x rfl (by decide),
    Reaction.propensity_of_ne k byToYY x rfl (by decide)]
  ring

/-- The total propensity of the approximate-majority CRN: `k·(2·#X·#Y + #B·(#X + #Y))`. -/
lemma network_totalPropensity (k : ℝ) {n : ℕ} (x : Counts Species n) :
    network.totalPropensity k x = k * (2 * x.1 X * x.1 Y + x.1 B * (x.1 X + x.1 Y) : ℝ) := by
  have h := network_sum k x fun _ => 1
  simp only [mul_one] at h
  rw [Network.totalPropensity, h]
  ring

/-- The jump chain of the approximate-majority CRN with rate constant `k`, from counts `x` with
`D = 2·#X·#Y + #B·(#X + #Y) > 0`: each `X + Y` reaction fires with probability `#X·#Y / D`,
`B + X → X + X` with probability `#B·#X / D` and `B + Y → Y + Y` with probability `#B·#Y / D`. -/
theorem network_jump_expect {k : ℝ} (hk : 0 < k) {n : ℕ} (x : Counts Species n)
    (hD : 0 < 2 * x.1 X * x.1 Y + x.1 B * (x.1 X + x.1 Y)) (f : Counts Species n → ℝ) :
    (network.jumpKernel k hk n x).expect f =
      ((x.1 X * x.1 Y : ℝ) * f (x.react xyToXB) + (x.1 X * x.1 Y : ℝ) * f (x.react xyToYB) +
          (x.1 B * x.1 X : ℝ) * f (x.react bxToXX) + (x.1 B * x.1 Y : ℝ) * f (x.react byToYY)) /
        (2 * x.1 X * x.1 Y + x.1 B * (x.1 X + x.1 Y) : ℝ) := by
  have hD' : (2 * x.1 X * x.1 Y + x.1 B * (x.1 X + x.1 Y) : ℝ) ≠ 0 := by
    exact_mod_cast hD.ne'
  have hmul := network.totalPropensity_mul_expect hk x f
  rw [network_totalPropensity, network_sum] at hmul
  rw [eq_div_iff hD']
  apply mul_left_cancel₀ hk.ne'
  linear_combination hmul

/-- In the population protocol of the approximate-majority CRN, the drawn pair reacts with
probability `(2·#X·#Y + #B·(#X + #Y)) / (4·C(n, 2))`. -/
theorem network_reactProb_eq {n : ℕ} (hn : 2 ≤ n) (c : Fin n → Species) :
    (sampleDist network hn).prob (Reacts network c) =
      (2 * (counts c).1 X * (counts c).1 Y + (counts c).1 B * ((counts c).1 X + (counts c).1 Y) :
          ℝ) / (4 * n.choose 2) := by
  have hcard : network.reactions.card = 4 := by decide
  rw [reactProb_eq network one_pos hn c, network_totalPropensity, hcard]
  push_cast
  ring

/-- CRN-1 for approximate majority: its jump chain is the population protocol conditioned on
the drawn pair reacting. -/
theorem network_jumpKernel_eq_ppKernel {k : ℝ} (hk : 0 < k) {n : ℕ} (hn : 2 ≤ n) :
    network.jumpKernel k hk n = ppKernel network hn := by
  exact jumpKernel_eq_ppKernel network hk hn

end Crn.ApproxMajority
