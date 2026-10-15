import Undecided.Basic
import Dynamics.GraphRounds

/-! # The sequential undecided-state dynamics (approximate majority)

The population-protocol version of the undecided-state dynamics is the 3-state *approximate
majority* protocol of Angluin, Aspnes and Eisenstat, *A simple population protocol for fast robust
approximate majority*, Distributed Computing 21 (2008) [AAE08]. Following [AAE08, §2], each step
draws an ordered pair `(initiator, responder)` of distinct agents uniformly at random among the
`n (n - 1)` such pairs, independently of the past; only the responder changes state (the protocol
is one-way). The transition table of [AAE08, §3], initiator first:

* `(x, y) → (x, b)` and `(y, x) → (y, b)`: a decided responder that meets the other opinion
  becomes blank;
* `(x, b) → (x, x)` and `(y, b) → (y, y)`: a blank responder adopts the initiator's opinion;
* every other interaction changes nothing.

The responder's new state is the synchronous rule `Undecided.update` applied to the responder and
the initiator, so the opinions, configurations and counts are those of `Undecided.Basic`, with the
dictionary `x ↦ Op.a`, `y ↦ Op.b` and blank `b ↦ Op.u`.

The state after `T` interactions is `run s l` for a list `l` of `T` interactions, and probabilities
over `T` i.i.d. uniform interactions are `Dynamics.expList (Interaction n) T`. When `2 ≤ n` this is
the kernel `Dynamics.Kernel.ofStep step`, by `Dynamics.Kernel.iterate_ofStep`. An interaction is
an oriented edge of the complete graph (`interactionEquiv`), so a uniform interaction is the core's
uniform `Dynamics.EdgeRound ⊤`.
-/

namespace Undecided.Sequential

variable {n : ℕ}

/-- An interaction of [AAE08, §2]: an ordered pair `(initiator, responder)` of distinct agents,
i.e. an arc of the complete directed graph without self-loops. -/
abbrev Interaction (n : ℕ) := {p : Fin n × Fin n // p.1 ≠ p.2}

/-- The interactions are the oriented edges of the complete graph on the agents: `Interaction n`
is the core's round type `Dynamics.EdgeRound ⊤` (`Dynamics.edgeRoundTopEquiv`). -/
def interactionEquiv : Interaction n ≃ Dynamics.EdgeRound (⊤ : SimpleGraph (Fin n)) :=
  Dynamics.edgeRoundTopEquiv.symm

/-- The configuration after the interaction `p` [AAE08, §3]: the responder `p.1.2` updates its
state against the initiator `p.1.1` by `Undecided.update`; all other agents keep their states. -/
def step (s : Config n) (p : Interaction n) : Config n :=
  Function.update s p.1.2 (update (s p.1.2) (s p.1.1))

/-- The configuration after performing the interactions of `l` in order. For a list of `T` i.i.d.
uniform interactions, this is the configuration `(x_T, y_T, b_T)` of [AAE08, §4.1]. -/
def run (s : Config n) (l : List (Interaction n)) : Config n := l.foldl step s

/-- The interaction step is the core's one-way protocol step `Dynamics.oneWayStep` with the rule
`Undecided.update`, on the complete graph. -/
lemma step_eq_oneWayStep (s : Config n) (p : Interaction n) :
    step s p = Dynamics.oneWayStep update s (interactionEquiv p) := rfl

end Undecided.Sequential
