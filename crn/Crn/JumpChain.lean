import Dynamics.Relations
import Crn.ApproximateMajority

/-!
# CRN-1 as a statement about jump chains

The dictionary relation `jump-chain` ("the same chain once idle steps are removed") is
`Dynamics.Kernel.SameJumpChain`: the two kernels agree once each is conditioned on moving
(`Dynamics.Kernel.jump`). On count vectors, one interaction of the population protocol of a
network `N` is a kernel (`ppStepKernel`) that stays put when the drawn pair does not react. Its
jump chain is the jump chain of stochastic mass-action kinetics with a common rate constant
(`ppStepKernel_jump`), which is its own jump chain (`Network.jumpKernel_jump`): the protocol and
the network have the same jump chain. Conditioning on the drawn pair reacting, as in `ppKernel`,
is conditioning on moving (`ppStepKernel_jump_eq_ppKernel`), so this is CRN-1
(`jumpKernel_eq_ppKernel`) in the vocabulary of `Dynamics.Kernel`; for the approximate-majority
network it is `ApproxMajority.network_sameJumpChain`.
-/

namespace Crn
open Dynamics

variable {S : Type*} [Fintype S] [DecidableEq S] {n : ℕ}

/-- One interaction of the population protocol of `N`, as a kernel on count vectors: from `x`,
one interaction from some configuration with counts `x` (by `ppStep_expect`, the result depends
on the counts only). -/
noncomputable def ppStepKernel (N : Network S) (hn : 2 ≤ n) : Kernel (Counts S n) := fun x =>
  ppStep N hn (exists_counts_eq x).choose

/-- The jump chain of stochastic mass-action kinetics is its own jump chain (in the sense of
`Dynamics.Kernel.jump`): it stays put only at terminal states. -/
theorem Network.jumpKernel_jump (N : Network S) {k : ℝ} (hk : 0 < k) :
    (N.jumpKernel k hk n).jump = N.jumpKernel k hk n := by
  refine Kernel.jump_eq_self _ fun x => ?_
  by_cases h : N.totalPropensity k x = 0
  · right
    simp [Network.jumpKernel, dif_pos h, Distribution.point]
  · exact Or.inl (N.jumpKernel_weight_self hk x h)

/-- **CRN-1, jump-chain form.** The jump chain of the population protocol of `N` on count vectors
(an interaction conditioned on changing the counts) is the jump chain of stochastic mass-action
kinetics with a common rate constant `k`. -/
theorem ppStepKernel_jump (N : Network S) {k : ℝ} (hk : 0 < k) (hn : 2 ≤ n) :
    (ppStepKernel N hn).jump = N.jumpKernel k hk n := by
  refine (Kernel.sameJumpChain_of_weight fun x => ?_).trans (N.jumpKernel_jump hk)
  classical
  obtain ⟨c, hc⟩ : ∃ c, (exists_counts_eq x).choose = c := ⟨_, rfl⟩
  have hcx : counts c = x := hc ▸ (exists_counts_eq x).choose_spec
  -- off the diagonal, the protocol moves as the network's jump chain, with the probability `ρ`
  -- that the drawn pair reacts
  have hw (y : Counts S n) (hy : y ≠ x) : (ppStepKernel N hn x).weight y =
      (sampleDist N hn).prob (Reacts N c) * (N.jumpKernel k hk n x).weight y := by
    rw [Distribution.weight_eq_expect_ite, ppStepKernel, hc, ppStep_expect N hk hn c, hcx,
      if_neg (Ne.symm hy), ← Distribution.weight_eq_expect_ite]
    ring
  rcases ((sampleDist N hn).prob_nonneg (Reacts N c)).lt_or_eq with hpos | hzero
  · exact ⟨_, hpos, hw⟩
  · refine ⟨1, one_pos, fun y hy => ?_⟩
    have ha : N.totalPropensity k x = 0 := by
      have hρ := reactProb_eq N hk hn c
      rw [← hzero, hcx, eq_comm, div_eq_zero_iff] at hρ
      refine hρ.resolve_right ?_
      have hC := choose_two_pos hn
      have hR : (0 : ℝ) < N.reactions.card := by exact_mod_cast N.nonempty.card_pos
      positivity
    rw [hw y hy, ← hzero, zero_mul, Network.jumpKernel, dif_pos ha]
    simp [Distribution.point, hy]

/-- The protocol conditioned on the drawn pair reacting (`ppKernel`) is the jump chain of the
protocol. -/
theorem ppStepKernel_jump_eq_ppKernel (N : Network S) (hn : 2 ≤ n) :
    (ppStepKernel N hn).jump = ppKernel N hn :=
  (ppStepKernel_jump N one_pos hn).trans (jumpKernel_eq_ppKernel N one_pos hn)

/-- The population protocol of `N` and stochastic mass-action kinetics have the same jump chain
(the relation `jump-chain` of the dictionary, row `population-protocols`). -/
theorem ppStepKernel_sameJumpChain (N : Network S) {k : ℝ} (hk : 0 < k) (hn : 2 ≤ n) :
    (ppStepKernel N hn).SameJumpChain (N.jumpKernel k hk n) :=
  (ppStepKernel_jump N hk hn).trans (N.jumpKernel_jump hk).symm

namespace ApproxMajority

/-- **CRN-1 for approximate majority, jump-chain form** (`network_jumpKernel_eq_ppKernel` with
`Dynamics.Kernel.SameJumpChain`). The population protocol of the approximate-majority network on
count vectors and the approximate-majority CRN with rate constant `k` have the same jump chain:
once the interactions in which the drawn pair does not react are removed, the protocol is the
CRN's jump chain. -/
theorem network_sameJumpChain {k : ℝ} (hk : 0 < k) {n : ℕ} (hn : 2 ≤ n) :
    (ppStepKernel network hn).SameJumpChain (network.jumpKernel k hk n) :=
  ppStepKernel_sameJumpChain network hk hn

end ApproxMajority

end Crn
