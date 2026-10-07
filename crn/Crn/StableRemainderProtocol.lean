import Crn.StableLeader

/-!
# The remainder protocol (CRN-3)

The protocol of [AADFP06, proof of Lemma 5(2)] for `∑ᵢ aᵢ xᵢ ≡ c (mod m)`, as a leader protocol
(`Leader.protocol`) with values in `ZMod m` (AADFP06 store `(u + u') mod m` in an integer field;
the residues are the same). Input `i` starts with value `aᵢ mod m` and output bit
`[aᵢ ≡ c]` (needed for a single agent, Deviation 2 of `PROGRESS-CRN3.md`); a leader encounter
gives the initiator the sum of the two values and the responder `0`, and the output test is
`t(u) = [u = c]`.

Correctness (`stablyComputes`): the sum of the values is `∑ᵢ aᵢ xᵢ mod m` and non-leaders hold
`0`, so once the leaders are merged the leader holds `∑ᵢ aᵢ xᵢ mod m`, and its test is the
predicate's value.
-/

namespace Crn

namespace RemainderProtocol

open Finset

variable {X : Type*} [Fintype X]

/-- The remainder protocol for `∑ᵢ aᵢ xᵢ ≡ c (mod m)` [AADFP06, proof of Lemma 5(2)]. -/
def protocol (a : X → ℤ) (c : ℤ) (m : ℕ) : Protocol X (Bool × Bool × ZMod m) :=
  Leader.protocol (fun i => (a i : ZMod m)) (· + ·) (fun _ _ => 0)
    (fun u => decide (u = (c : ZMod m)))

/-- **[AADFP06, Lemma 5(2)]** The remainder protocol stably computes
`∑ᵢ aᵢ xᵢ ≡ c (mod m)`. -/
theorem stablyComputes [DecidableEq X] (a : X → ℤ) (c : ℤ) (m : ℕ) :
    (protocol a c m).StablyComputes fun x => decide (∑ i, a i * (x i : ℤ) ≡ c [ZMOD m]) := by
  intro n hn ι C hC
  show ∃ D, _ ∧ (protocol a c m).OutputStable
    (decide (∑ i, a i * ((counts ι).1 i : ℤ) ≡ c [ZMOD m])) D
  obtain ⟨T, hT⟩ : ∃ T, ∑ i, a i * ((counts ι).1 i : ℤ) = T := ⟨_, rfl⟩
  rw [hT]
  -- invariants of the reachable configurations
  have hinv : ∀ D, (protocol a c m).Reaches ((protocol a c m).input ∘ ι) D →
      Leader.HasLeader D ∧ Leader.LeadOut (fun u => decide (u = (c : ZMod m))) D ∧
        Leader.NonLeaderVal 0 D ∧ ∑ w, (D w).2.2 = (T : ZMod m) := by
    intro D hD
    refine hD.invariant (I := fun D => Leader.HasLeader D ∧
      Leader.LeadOut (fun u => decide (u = (c : ZMod m))) D ∧ Leader.NonLeaderVal 0 D ∧
        ∑ w, (D w).2.2 = (T : ZMod m)) ?_
      ⟨Leader.hasLeader_input hn ι, Leader.leadOut_input ι, Leader.nonLeaderVal_input 0 ι, ?_⟩
    · rintro D D' ⟨h1, h2, h3, h4⟩ hst
      exact ⟨Leader.hasLeader_step hst h1, Leader.leadOut_step h2 hst,
        Leader.nonLeaderVal_step (fun _ _ => rfl) h3 hst,
        (Leader.sum_step (F := id) (fun _ _ => add_zero _) hst).trans h4⟩
    · refine (Leader.sum_input (q := (· + ·)) (r := fun _ _ => 0)
        (t := fun u => decide (u = (c : ZMod m))) id ι).trans ?_
      rw [← hT]
      push_cast
      exact sum_congr rfl fun i _ => by rw [nsmul_eq_mul, mul_comm]; rfl
  -- merge the leaders; the leader then holds the sum
  obtain ⟨C₁, hC₁, h1⟩ := Leader.exists_reaches_atMostOne (init := fun i => (a i : ZMod m))
    (q := (· + ·)) (r := fun _ _ => 0) (t := fun u => decide (u = (c : ZMod m))) C
  obtain ⟨⟨ℓ, hℓ⟩, hlo, hnl, hsum⟩ := hinv C₁ (hC.trans hC₁)
  obtain ⟨L, hL⟩ : ∃ L, (C₁ ℓ).2.2 = L := ⟨_, rfl⟩
  have hTL : (T : ZMod m) = L := by
    rw [← hsum, ← add_sum_erase _ _ (mem_univ ℓ), sum_eq_zero fun w hw => ?_, add_zero, hL]
    refine hnl w ?_
    cases h : (C₁ w).1
    · rfl
    · exact absurd (h1 _ _ h hℓ) (mem_erase.1 hw).1
  have good : Leader.Good (fun u => decide (u = (c : ZMod m))) L (· = 0) C₁ :=
    ⟨⟨ℓ, hℓ⟩, h1, fun w hw => by rw [h1 _ _ hw hℓ, hlo ℓ hℓ, hL]; exact ⟨rfl, rfl⟩, hnl⟩
  obtain ⟨D, hD, hDs⟩ := Leader.Good.exists_outputStable (init := fun i => (a i : ZMod m))
    (q := (· + ·)) (r := fun _ _ => 0) (fun y hy => by subst hy; simp) good
  refine ⟨D, hC₁.trans hD, ?_⟩
  have ht : decide (L = (c : ZMod m)) = decide (T ≡ c [ZMOD m]) :=
    decide_eq_decide.2 (by rw [← hTL]; exact ZMod.intCast_eq_intCast_iff T c m)
  rw [← ht]
  exact hDs

end RemainderProtocol

end Crn
