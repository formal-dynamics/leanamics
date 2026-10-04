import Median.Basic
import Median.Binary

/-! # Any start: auxiliary lemmas

Auxiliary material for `Median/AnyStart.lean`:

* `notConsensus` takes only the values `0` and `1`, and is `0` exactly on consensus
  configurations (the corresponding lemmas of `Median/Basic.lean` are private);
* values never leave the set of initial values (`run_mem`);
* consensus absorbs along a list of rounds (`run_consensus`), so the probability of
  *not* being in consensus is non-increasing in time (`expList_run_anti`) and
  submultiplicative over consecutive blocks (`notConsensus_run_append_mul`);
* a per-binary-configuration failure bound at `T` rounds amplifies to a bound at
  `k * T` rounds (`expList_amplify`).

These feed the reduction to two values (`consensus_of_binary`, via the threshold
configurations `y b = decide (b ≤ x ·)`) and the main theorem
(`median_consensus_any`).
-/

namespace Median
open Finset Dynamics

variable {n : ℕ} {α : Type*} [LinearOrder α]

/-! ### The `notConsensus` indicator -/

omit [LinearOrder α] in
lemma notConsensus_cons' {y : Config n α} (h : Consensus y) : notConsensus y = 0 := by
  unfold notConsensus
  rw [if_pos h]

omit [LinearOrder α] in
lemma notConsensus_noncons' {y : Config n α} (h : ¬ Consensus y) : notConsensus y = 1 := by
  unfold notConsensus
  rw [if_neg h]

omit [LinearOrder α] in
lemma notConsensus_cases' (y : Config n α) : notConsensus y = 0 ∨ notConsensus y = 1 := by
  by_cases h : Consensus y
  · exact Or.inl (notConsensus_cons' h)
  · exact Or.inr (notConsensus_noncons' h)

omit [LinearOrder α] in
lemma notConsensus_nonneg' (y : Config n α) : 0 ≤ notConsensus y := by
  rcases notConsensus_cases' y with h | h <;> simp [h]

omit [LinearOrder α] in
lemma notConsensus_le_one' (y : Config n α) : notConsensus y ≤ 1 := by
  rcases notConsensus_cases' y with h | h <;> simp [h]

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
  · rw [notConsensus_noncons' h]
    exact notConsensus_le_one' _

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

/-- A failure of the second block only matters if the first block has failed. -/
lemma notConsensus_run_append_mul (y : Config n α) (l₁ l₂ : List (Round n)) :
    notConsensus (run y (l₁ ++ l₂))
      ≤ notConsensus (run y l₁) * notConsensus (run (run y l₁) l₂) := by
  rw [run_append]
  by_cases h : Consensus (run y l₁)
  · rw [run_consensus _ h l₂, notConsensus_cons' h]
    simp
  · rw [notConsensus_noncons' h, one_mul]

/-- **Amplification.** A per-configuration failure bound `p` at `T` rounds implies a
bound `p ^ k` at `k * T` rounds: three blocks amplify a `C/n` bound to `≤ (C/n)³`,
which a union bound over the values can afford. -/
lemma expList_amplify [NeZero n] {T : ℕ} {p : ℝ}
    (hbin : ∀ y : Config n Bool, expList (Round n) T (fun l => notConsensus (run y l)) ≤ p)
    (k : ℕ) (y : Config n Bool) :
    expList (Round n) (k * T) (fun l => notConsensus (run y l)) ≤ p ^ k := by
  -- `hbin` forces `0 ≤ p`, since the left-hand side is nonnegative
  have hp : 0 ≤ p :=
    le_trans (expList_nonneg fun l => notConsensus_nonneg' _) (hbin (fun _ => false))
  induction k with
  | zero =>
      rw [Nat.zero_mul, expList_zero]
      show notConsensus (run y []) ≤ p ^ 0
      rw [pow_zero]
      exact notConsensus_le_one' _
  | succ k ih =>
      have hsplit : (k + 1) * T = k * T + T := by ring
      rw [hsplit, expList_append, pow_succ]
      have hinner : ∀ l₁ : List (Round n),
          expList (Round n) T (fun l₂ => notConsensus (run y (l₁ ++ l₂)))
            ≤ notConsensus (run y l₁) * p := by
        intro l₁
        have h1 : expList (Round n) T (fun l₂ => notConsensus (run y (l₁ ++ l₂)))
            ≤ expList (Round n) T
              (fun l₂ => notConsensus (run y l₁) * notConsensus (run (run y l₁) l₂)) :=
          expList_le_expList fun l₂ => notConsensus_run_append_mul y l₁ l₂
        have h2 : expList (Round n) T
              (fun l₂ => notConsensus (run y l₁) * notConsensus (run (run y l₁) l₂))
            = notConsensus (run y l₁)
              * expList (Round n) T (fun l₂ => notConsensus (run (run y l₁) l₂)) :=
          expList_const_mul _ _ _
        have h3 : expList (Round n) T (fun l₂ => notConsensus (run (run y l₁) l₂)) ≤ p :=
          hbin _
        have hmul : notConsensus (run y l₁)
              * expList (Round n) T (fun l₂ => notConsensus (run (run y l₁) l₂))
            ≤ notConsensus (run y l₁) * p :=
          mul_le_mul_of_nonneg_left h3 (notConsensus_nonneg' _)
        exact h1.trans ((le_of_eq h2).trans hmul)
      refine le_trans (expList_le_expList hinner) ?_
      have hswap : expList (Round n) (k * T)
          (fun l₁ : List (Round n) => notConsensus (run y l₁) * p)
          = expList (Round n) (k * T) (fun l : List (Round n) => notConsensus (run y l)) * p := by
        have hcm := expList_const_mul (k * T) p (fun l : List (Round n) => notConsensus (run y l))
        calc expList (Round n) (k * T) (fun l₁ : List (Round n) => notConsensus (run y l₁) * p)
            = expList (Round n) (k * T)
              (fun l₁ : List (Round n) => p * notConsensus (run y l₁)) :=
              congrArg _ (funext fun l₁ => (mul_comm _ _).symm)
          _ = p * expList (Round n) (k * T)
              (fun l : List (Round n) => notConsensus (run y l)) := hcm
          _ = expList (Round n) (k * T)
              (fun l : List (Round n) => notConsensus (run y l)) * p := mul_comm _ _
      rw [hswap]
      exact mul_le_mul_of_nonneg_right ih hp

end Median
