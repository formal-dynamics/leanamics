import Crn.StableBoolean
import Crn.StableRemainderProtocol

/-!
# Remainder predicates are stably computable (CRN-3)

[AADFP06, Lemma 5(2)]: for integer constants `aᵢ`, `c` and a modulus `m`, the predicate
`∑ᵢ aᵢ xᵢ ≡ c (mod m)` on input counts is stably computable. In AADFP06's protocol each agent
holds a leader bit, an output bit and a count, starting from `aᵢ`; an encounter involving a
leader merges the leaders into the initiator, which takes the sum of the two counts mod `m`
(the responder gets `0`), and both agents set their output bit to whether that sum is `≡ c`.

The protocol and its correctness proof are in `StableRemainderProtocol.lean` (values in
`ZMod m`); an input starts with output bit `[aᵢ ≡ c]`, needed for a single agent.
-/

namespace Crn

variable {X : Type*} [Fintype X]

/-- The remainder predicate `∑ᵢ aᵢ xᵢ ≡ c (mod m)` on input counts `x` [AADFP06, Lemma 5(2)],
with integer coefficients `aᵢ`, integer constant `c` and modulus `m`. -/
def remainder (a : X → ℤ) (c : ℤ) (m : ℕ) (x : X → ℕ) : Bool :=
  decide (∑ i, a i * (x i : ℤ) ≡ c [ZMOD m])

variable [DecidableEq X]

/-- **[AADFP06, Lemma 5(2)]** Every remainder predicate `∑ᵢ aᵢ xᵢ ≡ c (mod m)` with a positive
modulus is stably computable (AADFP06 assume `m ≥ 2`; `m = 1` gives the constant `true`). -/
theorem stablyComputable_remainder (a : X → ℤ) (c : ℤ) {m : ℕ} (hm : 0 < m) :
    StablyComputable (remainder a c m) := by
  haveI : NeZero m := ⟨hm.ne'⟩
  exact ⟨_, inferInstance, RemainderProtocol.protocol a c m,
    RemainderProtocol.stablyComputes a c m⟩

end Crn
