import Crn.StableBoolean
import Crn.StableThresholdProtocol

/-!
# Threshold predicates are stably computable (CRN-3)

[AADFP06, Lemma 5(1)]: for integer constants `aᵢ`, `c`, the predicate `∑ᵢ aᵢ xᵢ < c` on input
counts is stably computable. In AADFP06's protocol each agent holds a leader bit, an output bit
and a count `u ∈ [-s, s]`, `s = max(|c| + 1, maxᵢ |aᵢ|)`, starting from `u = aᵢ`; an encounter
involving a leader merges the leaders into the initiator, which takes as much of the sum of the
two counts as fits in `[-s, s]`, and both agents set their output bit to whether the
initiator's count is `< c`. The roadmap's form `∑ᵢ aᵢ xᵢ ≥ c` is the negation.

The protocol and its correctness proof are in `StableThresholdProtocol.lean` (an instance of
the leader protocols of `StableLeader.lean`); unlike AADFP06, an input starts with output bit
`[aᵢ < c]`, which is needed for a population of one agent.
-/

namespace Crn

variable {X : Type*} [Fintype X]

/-- The threshold predicate `∑ᵢ aᵢ xᵢ < c` on input counts `x` [AADFP06, Lemma 5(1)], with
integer coefficients `aᵢ` and integer constant `c`. -/
def threshold (a : X → ℤ) (c : ℤ) (x : X → ℕ) : Bool :=
  decide (∑ i, a i * (x i : ℤ) < c)

variable [DecidableEq X]

/-- **[AADFP06, Lemma 5(1)]** Every threshold predicate `∑ᵢ aᵢ xᵢ < c` is stably computable. -/
theorem stablyComputable_threshold (a : X → ℤ) (c : ℤ) : StablyComputable (threshold a c) :=
  ⟨_, inferInstance, ThresholdProtocol.protocol a c, ThresholdProtocol.stablyComputes a c⟩

/-- **Roadmap CRN-3** (threshold predicates in the form `∑ᵢ aᵢ xᵢ ≥ c`, the negation of
[AADFP06, Lemma 5(1)]): they are stably computable. -/
theorem stablyComputable_le_sum (a : X → ℤ) (c : ℤ) :
    StablyComputable fun x => decide (c ≤ ∑ i, a i * (x i : ℤ)) := by
  have h : (fun x => decide (c ≤ ∑ i, a i * (x i : ℤ))) = fun x => !threshold a c x :=
    funext fun x => by rw [threshold, ← decide_not]; exact decide_eq_decide.2 not_lt.symm
  rw [h]
  exact (stablyComputable_threshold a c).not

end Crn
