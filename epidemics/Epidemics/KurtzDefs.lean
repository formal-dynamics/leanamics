import Dynamics.Rounds
import Epidemics.KermackMcKendrickDefs

/-! # Kurtz's law of large numbers for SIR in discrete time: the chain (CRN-2)

The stochastic SIR epidemic of the roadmap (row CRN-2) is the continuous-time Markov chain on
`N` agents with reactions `S + I → 2I` at rate `β S I / N` and `I → R` at rate `γ I`. Its total
jump rate is at most `Λ = (β + γ) N`; uniformizing at rate `Λ`, each ring of a rate-`Λ` Poisson
clock is an infection with probability `β S I / (N Λ)`, a recovery with probability `γ I / Λ`, and
otherwise nothing. We formalize this discrete-time chain (the jump chain of the uniformization),
with one step per unit `1 / ((β + γ) N)` of time:

* a `Round` draws an ordered pair `(u, v)` of agents uniformly *with replacement* and one of
  `β + γ` equally likely clocks: `β` infection clocks (`Sum.inl`) and `γ` recovery clocks
  (`Sum.inr`), so `β, γ` are natural numbers (rates with a rational ratio, up to a time change);
* `step`: on an infection clock, if `u` is infected and `v` susceptible then `v` becomes infected;
  on a recovery clock, if `u` is infected then `u` recovers; otherwise nothing changes.

Then the expected increment of the scaled counts `scaled x = (S, I, R) / N` is exactly
`sirField β γ (scaled x) / ((β + γ) N)`, the Kermack–McKendrick field of EPI-7
(`Epidemics.KermackMcKendrickDefs`) times the time step, and each step moves `scaled x` by at
most `1 / N` (`Epidemics.KurtzDrift`). The chain is the kernel `Dynamics.Kernel.ofStep (step β γ)`;
path probabilities are `Dynamics.expList` averages over i.i.d. uniform rounds, the state after the
rounds `l` being `l.foldl (step β γ) x₀`. `deviationProb` is the probability that the chain leaves
a tube around a curve during a finite horizon; the law of large numbers is in `Epidemics.Kurtz`.
-/

namespace Epidemics.Kurtz

open Dynamics

/-- The three compartments of the SIR model. -/
inductive Compartment
  | susceptible
  | infected
  | recovered
  deriving DecidableEq, Fintype

/-- A configuration of `N` agents: the compartment of every agent. -/
abbrev Config (N : ℕ) := Fin N → Compartment

/-- The number of agents of the configuration `x` in the compartment `c`. -/
def count {N : ℕ} (c : Compartment) (x : Config N) : ℕ :=
  (Finset.univ.filter fun v ↦ x v = c).card

/-- The scaled counts `(S / N, I / N, R / N)` of a configuration, as a point of the state space
`ℝ × ℝ × ℝ` of the Kermack–McKendrick field `sirField`. -/
noncomputable def scaled {N : ℕ} (x : Config N) : ℝ × ℝ × ℝ :=
  ((count .susceptible x : ℝ) / N, (count .infected x : ℝ) / N, (count .recovered x : ℝ) / N)

/-- The randomness of one step: an ordered pair `(u, v)` of agents, drawn with replacement, and
one of `β + γ` equally likely clocks, `β` infection clocks (`Sum.inl`) and `γ` recovery clocks
(`Sum.inr`). -/
abbrev Round (N β γ : ℕ) := Fin N × Fin N × (Fin β ⊕ Fin γ)

/-- One step of the uniformized SIR chain with infection weight `β` and recovery weight `γ`: on an
infection clock, an infected `u` infects a susceptible `v`; on a recovery clock, an infected `u`
recovers; otherwise nothing changes. A uniform round thus infects with probability
`β / (β + γ) · (I / N) · (S / N)` and recovers with probability `γ / (β + γ) · I / N`, the jump
probabilities of the continuous-time chain (`S + I → 2I` at rate `β S I / N`, `I → R` at rate
`γ I`) uniformized at rate `(β + γ) N`. -/
def step (β γ : ℕ) {N : ℕ} (x : Config N) (ρ : Round N β γ) : Config N :=
  match ρ with
  | (u, v, .inl _) =>
    if x u = .infected ∧ x v = .susceptible then Function.update x v .infected else x
  | (u, _, .inr _) => if x u = .infected then Function.update x u .recovered else x

/-- The uniformized SIR chain as a finite Markov kernel on configurations: one uniformly random
`Round` of `step`. -/
noncomputable def chain (β γ N : ℕ) [Nonempty (Round N β γ)] : Dynamics.Kernel (Config N) :=
  Dynamics.Kernel.ofStep (step β γ)

/-- The probability that the SIR chain started at `x₀` is, at some step `k ≤ n`, at distance more
than `δ` from the curve `x` at the matching time `k / ((β + γ) N)`. The `n` rounds are i.i.d.
uniform (`Dynamics.expList`), the state after `k` of them is `(l.take k).foldl (step β γ) x₀`, and
`dist` on `ℝ × ℝ × ℝ` is the sup distance (`Prod.dist_eq`). -/
noncomputable def deviationProb (β γ : ℕ) {N : ℕ} (x₀ : Config N) (x : ℝ → ℝ × ℝ × ℝ)
    (δ : ℝ) (n : ℕ) : ℝ :=
  expList (Round N β γ) n fun l ↦
    if ∃ k ≤ n, δ < dist (scaled ((l.take k).foldl (step β γ) x₀))
        (x ((k : ℝ) / ((β + γ) * N)))
    then 1 else 0

end Epidemics.Kurtz
