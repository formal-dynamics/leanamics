import Median.Basic
import Median.Binary

/-! # Any start: auxiliary lemmas

Auxiliary material for `Median/AnyStart.lean`:

* `notConsensus` lies in `[0, 1]` (from `notConsensus_cases` of `Median/Basic.lean`);
* values never leave the set of initial values (`run_mem`);
* consensus absorbs along a list of rounds (`run_consensus`), so the probability of
  *not* being in consensus is non-increasing in time (`expList_run_anti`,
  `expList_run_mono`); a per-binary-configuration failure bound at `T` rounds then amplifies
  to a bound at `k * T` rounds (the core `Dynamics.missProb_amplify`).

These feed the reduction to two values (`consensus_of_binary`, via the threshold
configurations `y b = decide (b ≤ x ·)`) and the main theorem
(`median_consensus_any`).
-/

namespace Median
open Finset Dynamics

variable {n : ℕ} {α : Type*} [LinearOrder α]

/-! ### The `notConsensus` indicator -/

omit [LinearOrder α] in
/-- `notConsensus` is nonnegative. -/
lemma notConsensus_nonneg (y : Config n α) : 0 ≤ notConsensus y := by
  rcases notConsensus_cases y with h | h <;> simp [h]

omit [LinearOrder α] in
/-- `notConsensus` is at most `1`. -/
lemma notConsensus_le_one (y : Config n α) : notConsensus y ≤ 1 := by
  rcases notConsensus_cases y with h | h <;> simp [h]

/-! ### Values stay in the initial set -/

/-- The value at any node after any run is an initial value. -/
lemma run_mem (x : Config n α) (l : List (Round n)) (v : Fin n) :
    ∃ u, run x l v = x u := by
  induction l generalizing x with
  | nil => exact ⟨v, rfl⟩
  | cons r l ih =>
      obtain ⟨w, hw⟩ := ih (step x r)
      obtain ⟨u, hu⟩ := step_mem x r w
      exact ⟨u, hw.trans hu⟩

/-- After any run, every node holds an initial value. -/
lemma run_mem_image (x : Config n α) (l : List (Round n)) (v : Fin n) :
    run x l v ∈ univ.image x := by
  obtain ⟨u, hu⟩ := run_mem x l v
  rw [hu]
  exact Finset.mem_image_of_mem x (Finset.mem_univ u)

/-! ### Consensus absorbs -/

/-- One more round after a list of rounds. -/
lemma run_cons (x : Config n α) (r : Round n) (l : List (Round n)) :
    run x (r :: l) = run (step x r) l := rfl

/-- A run splits at any point. -/
lemma run_append (x : Config n α) (l₁ l₂ : List (Round n)) :
    run x (l₁ ++ l₂) = run (run x l₁) l₂ := List.foldl_append

/-- From a consensus configuration, every further run stays there. -/
lemma run_consensus (z : Config n α) (h : Consensus z) (l : List (Round n)) : run z l = z := by
  induction l with
  | nil => rfl
  | cons r l ih =>
      rw [run_cons, step_of_consensus z h r]
      exact ih

/-- A consensus of a prefix is preserved to the end. -/
lemma notConsensus_run_append_le (x : Config n α) (l₁ l₂ : List (Round n)) :
    notConsensus (run x (l₁ ++ l₂)) ≤ notConsensus (run x l₁) := by
  rw [run_append]
  by_cases h : Consensus (run x l₁)
  · rw [run_consensus _ h l₂]
  · rw [notConsensus_noncons h]
    exact notConsensus_le_one _

/-- The failure probability is non-increasing in the number of rounds. -/
lemma expList_run_anti [NeZero n] (x : Config n α) (T₁ T₂ : ℕ) :
    expList (Round n) (T₁ + T₂) (fun l => notConsensus (run x l))
      ≤ expList (Round n) T₁ (fun l => notConsensus (run x l)) := by
  have hne : Nonempty (Round n) := ⟨fun _ => ((0 : Fin n), (0 : Fin n))⟩
  rw [expList_append]
  refine expList_le_expList fun l₁ => ?_
  have h1 : expList (Round n) T₂ (fun l₂ => notConsensus (run x (l₁ ++ l₂)))
      ≤ expList (Round n) T₂ (fun _ => notConsensus (run x l₁)) :=
    expList_le_expList fun l₂ => notConsensus_run_append_le x l₁ l₂
  have h2 : expList (Round n) T₂ (fun _ => notConsensus (run x l₁))
      = notConsensus (run x l₁) := expList_const _ _
  exact h1.trans (le_of_eq h2)

/-- **More rounds never hurt**: the failure probability is antitone in the number of rounds. -/
lemma expList_run_mono [NeZero n] (x : Config n α) {T₁ T₂ : ℕ} (h : T₁ ≤ T₂) :
    expList (Round n) T₂ (fun l => notConsensus (run x l))
      ≤ expList (Round n) T₁ (fun l => notConsensus (run x l)) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  exact expList_run_anti x T₁ d

end Median
