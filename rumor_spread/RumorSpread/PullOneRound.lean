import RumorSpread.PullIndep
import RumorSpread.PullModel

/-!
# One-round picture of PULL and PUSH–PULL

Exact one-round expectations that make the classical picture of [KSSV00, §2] visible, with the
partner of every caller uniform among the other `n - 1` nodes (`Tgt n`). Write `m = |I|` for the
informed and `u = n - m` for the uninformed nodes. An uninformed caller `v` pulls the rumor iff
its callee lies in `I`, which has probability `m / (n - 1)`, independently over the callers.

* `pull_prob_stuck_singleton` — the *startup* of PULL is unpredictable [KSSV00, §2]: from one
  informed node the round informs nobody with probability `(1 - 1/(n-1))^(n-1) ≈ 1/e`.
* `pull_avg_card_step` — expected PULL growth `m + u · m/(n-1)`: while `m ≪ n` the informed set
  roughly doubles in expectation.
* `pull_avg_uninformed`, `pull_avg_uninformed_le` — the *quadratic shrinking* of PULL
  [KSSV00, §2]: the expected number of uninformed nodes after one round is exactly
  `u (u - 1)/(n - 1) ≤ u² / n`, i.e. the uninformed fraction `s = u/n` satisfies `𝔼 s' ≤ s²`.
* `pushPull_avg_uninformed` — PUSH–PULL combines both effects: an uninformed node stays
  uninformed iff it pulls from an uninformed node *and* is pushed to by nobody, so the expected
  number of uninformed nodes is `u (u - 1)/(n - 1) · (1 - 1/(n-1))^m` (for `m ≪ n` this is
  `≈ n - 3m`, the tripling behind `log₃ n` in [KSSV00, Thm 2.1]).
-/

namespace RumorPush

open Finset

variable {n : ℕ}

/-! ### Counting identities -/

/-- Size of a PULL round: `I` plus the uninformed callers whose callee is in `I`. -/
lemma card_pullStep (I : Finset (Fin n)) (r : Tgt n) :
    ((pullStep I r).card : ℝ)
      = I.card + ∑ v ∈ Iᶜ, if ((r v) : Fin n) ∈ I then (1 : ℝ) else 0 := by
  have hsplit : (pullStep I r \ I).card + I.card = (pullStep I r).card :=
    card_sdiff_add_card_eq_card (subset_pullStep I r)
  have hfilter : pullStep I r \ I = Iᶜ.filter fun v => ((r v) : Fin n) ∈ I := by
    ext v
    simp only [mem_sdiff, mem_pullStep, mem_filter, mem_compl]
    tauto
  rw [sum_boole, ← hfilter]
  push_cast [← hsplit]
  ring

/-- The uninformed count after a round `S ⊇ I`, as a sum over the nodes uninformed before. -/
lemma uninformed_eq_sum {I S : Finset (Fin n)} (h : I ⊆ S) :
    (n : ℝ) - S.card = ∑ v ∈ Iᶜ, if v ∈ S then (0 : ℝ) else 1 := by
  have h1 : ∑ v ∈ Iᶜ, (if v ∈ S then (0 : ℝ) else 1)
      = ∑ v ∈ Iᶜ, if v ∉ S then (1 : ℝ) else 0 :=
    sum_congr rfl fun v _ => by by_cases hv : v ∈ S <;> simp [hv]
  have hf : Iᶜ.filter (fun v => v ∉ S) = Sᶜ := by
    ext v
    simp only [mem_filter, mem_compl]
    exact ⟨fun h' => h'.2, fun h' => ⟨fun hv => h' (h hv), h'⟩⟩
  have hS : S.card ≤ n := by simpa using card_le_univ S
  rw [h1, sum_boole, hf, card_compl, Fintype.card_fin, Nat.cast_sub hS]

lemma cast_card_compl {I : Finset (Fin n)} : ((Iᶜ).card : ℝ) = (n : ℝ) - I.card := by
  have hI : I.card ≤ n := by simpa using card_le_univ I
  rw [card_compl, Fintype.card_fin, Nat.cast_sub hI]

/-- A caller `v ∉ I` of a uniform round calls into `I` with probability `|I|/(n-1)`. -/
lemma avg_tgt_call_mem (hn : 2 ≤ n) {v : Fin n} {I : Finset (Fin n)} (hv : v ∉ I) :
    avg (fun r : Tgt n => if ((r v) : Fin n) ∈ I then (1 : ℝ) else 0)
      = I.card / ((n : ℝ) - 1) :=
  (avg_tgt_coord hn v fun y => if y ∈ I then (1 : ℝ) else 0).trans (avg_call_mem hn hv)

/-- Expected number of uninformed callers that pull the rumor in one round:
`(n - |I|) · |I|/(n-1)`. -/
lemma pull_avg_new (hn : 2 ≤ n) (I : Finset (Fin n)) :
    avg (fun r : Tgt n => ∑ v ∈ Iᶜ, if ((r v) : Fin n) ∈ I then (1 : ℝ) else 0)
      = ((n : ℝ) - I.card) * (I.card / ((n : ℝ) - 1)) := by
  rw [avg_sum, sum_congr rfl fun v hv => avg_tgt_call_mem hn (mem_compl.1 hv), sum_const,
    nsmul_eq_mul, cast_card_compl]

/-- **PULL startup stalls with constant probability** [KSSV00, §2]: from a single informed node
`v₀`, a PULL round informs no new node (nobody calls `v₀`) with probability exactly
`(1 - 1/(n-1))^(n-1)`, which tends to `1/e`. -/
theorem pull_prob_stuck_singleton (hn : 2 ≤ n) (v₀ : Fin n) :
    avg (fun r : Tgt n => if pullStep {v₀} r = {v₀} then (1 : ℝ) else 0)
      = (1 - 1 / ((n : ℝ) - 1)) ^ (n - 1) := by
  have hcard : ({v₀}ᶜ : Finset (Fin n)).card = n - 1 := by
    rw [card_compl, card_singleton, Fintype.card_fin]
  have h := avg_not_contacted hn {v₀}ᶜ v₀ (by simp)
  rw [hcard] at h
  rw [← h]
  congr 1
  funext r
  have hiff : pullStep {v₀} r = {v₀} ↔ v₀ ∉ step {v₀}ᶜ r := by
    constructor
    · intro hst hmem
      rcases mem_step.1 hmem with h' | ⟨w, hw, e⟩
      · simp at h'
      · have hw' : w ∈ pullStep {v₀} r := mem_pullStep.2 (Or.inr (mem_singleton.2 e))
        rw [hst, mem_singleton] at hw'
        exact mem_compl.1 hw (mem_singleton.2 hw')
    · intro hnot
      refine Subset.antisymm (fun w hw => ?_) (subset_pullStep _ r)
      rcases mem_pullStep.1 hw with h' | h'
      · exact h'
      · by_contra hwv
        exact hnot (mem_step.2 (Or.inr ⟨w, mem_compl.2 hwv, mem_singleton.1 h'⟩))
  by_cases hp : pullStep {v₀} r = {v₀}
  · rw [if_pos hp, if_neg (hiff.1 hp)]
  · rw [if_neg hp, if_pos (not_not.1 (mt hiff.2 hp))]

/-- **Expected PULL growth** (exact): each of the `n - |I|` uninformed nodes calls an informed
node with probability `|I|/(n-1)`; for `|I| ≪ n` the informed set roughly doubles in
expectation [KSSV00, §2]. -/
theorem pull_avg_card_step (hn : 2 ≤ n) (I : Finset (Fin n)) :
    avg (fun r : Tgt n => ((pullStep I r).card : ℝ))
      = I.card + ((n : ℝ) - I.card) * (I.card / ((n : ℝ) - 1)) := by
  haveI := tgt_nonempty hn
  rw [show (fun r : Tgt n => ((pullStep I r).card : ℝ)) = fun r : Tgt n =>
      (I.card : ℝ) + ∑ v ∈ Iᶜ, (if ((r v) : Fin n) ∈ I then (1 : ℝ) else 0)
    from funext (card_pullStep I), avg_add, avg_const, pull_avg_new hn I]

/-- **Quadratic shrinking of PULL, exact form** [KSSV00, §2]: an uninformed node stays
uninformed iff it calls one of the other `u - 1` uninformed nodes, so with `u = n - |I|` the
expected number of uninformed nodes after one PULL round is `u (u - 1)/(n - 1)`. -/
theorem pull_avg_uninformed (hn : 2 ≤ n) (I : Finset (Fin n)) :
    avg (fun r : Tgt n => (n : ℝ) - (pullStep I r).card)
      = ((n : ℝ) - I.card) * ((n : ℝ) - I.card - 1) / ((n : ℝ) - 1) := by
  haveI := tgt_nonempty hn
  rw [show (fun r : Tgt n => (n : ℝ) - ((pullStep I r).card : ℝ))
      = fun r : Tgt n => (fun _ : Tgt n => (n : ℝ)) r
          - (fun r : Tgt n => ((pullStep I r).card : ℝ)) r from rfl,
    avg_sub, avg_const, pull_avg_card_step hn I]
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  field_simp
  ring

/-- **Quadratic shrinking of PULL** [KSSV00, §2]: with `u = n - |I|` uninformed nodes, the
expected number of uninformed nodes after one PULL round is at most `u² / n`; equivalently the
uninformed fraction `s = u/n` satisfies `𝔼 s' ≤ s²`. -/
theorem pull_avg_uninformed_le (hn : 2 ≤ n) (I : Finset (Fin n)) :
    avg (fun r : Tgt n => (n : ℝ) - (pullStep I r).card)
      ≤ ((n : ℝ) - I.card) ^ 2 / n := by
  rw [pull_avg_uninformed hn I]
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hm : (I.card : ℝ) ≤ n := by exact_mod_cast (by simpa using card_le_univ I)
  have hm0 : (0 : ℝ) ≤ I.card := Nat.cast_nonneg _
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_nonneg (sub_nonneg.2 hm) hm0]

/-- **One PUSH–PULL round, exact form** [KSSV00, §2]: an uninformed node stays uninformed iff
its own call goes to an uninformed node (probability `(u - 1)/(n - 1)`) and none of the `|I|`
informed nodes calls it (probability `(1 - 1/(n-1))^|I|`, independent of the former). Hence the
expected number of uninformed nodes after one round is `u (u - 1)/(n - 1) · (1 - 1/(n-1))^|I|`,
with `u = n - |I|`. -/
theorem pushPull_avg_uninformed (hn : 2 ≤ n) (I : Finset (Fin n)) :
    avg (fun r : Tgt n => (n : ℝ) - (pushPullStep I r).card)
      = ((n : ℝ) - I.card) * ((n : ℝ) - I.card - 1) / ((n : ℝ) - 1)
          * (1 - 1 / ((n : ℝ) - 1)) ^ I.card := by
  have key : ∀ r : Tgt n, ∀ v ∉ I, (if v ∈ pushPullStep I r then (0 : ℝ) else 1)
      = (if ((r v) : Fin n) ∈ I then (0 : ℝ) else 1)
          * ∏ w ∈ I, (if ((r w) : Fin n) = v then (0 : ℝ) else 1) := by
    intro r v hv
    by_cases h1 : ((r v) : Fin n) ∈ I
    · rw [if_pos (mem_pushPullStep.2 (Or.inr (mem_pullStep.2 (Or.inr h1)))), if_pos h1,
        zero_mul]
    · by_cases h2 : ∃ w ∈ I, ((r w) : Fin n) = v
      · obtain ⟨w, hw, hwv⟩ := h2
        rw [if_pos (mem_pushPullStep.2 (Or.inl (mem_step.2 (Or.inr ⟨w, hw, hwv⟩)))),
          prod_eq_zero (f := fun w => if ((r w) : Fin n) = v then (0 : ℝ) else 1) hw
            (if_pos hwv), mul_zero]
      · simp only [not_exists, not_and] at h2
        have hnot : v ∉ pushPullStep I r := by
          intro h
          rcases mem_pushPullStep.1 h with h | h
          · rcases mem_step.1 h with h | ⟨w, hw, e⟩
            · exact hv h
            · exact h2 w hw e
          · rcases mem_pullStep.1 h with h | h
            · exact hv h
            · exact h1 h
        rw [if_neg hnot, if_neg h1, one_mul, prod_eq_one fun w hw => if_neg (h2 w hw)]
  have hpt : (fun r : Tgt n => (n : ℝ) - (pushPullStep I r).card)
      = fun r : Tgt n => ∑ v ∈ Iᶜ, (if ((r v) : Fin n) ∈ I then (0 : ℝ) else 1)
          * ∏ w ∈ I, (if ((r w) : Fin n) = v then (0 : ℝ) else 1) := by
    funext r
    rw [uninformed_eq_sum (subset_pushPullStep I r)]
    exact sum_congr rfl fun v hv => key r v (mem_compl.1 hv)
  have hv : ∀ v ∈ Iᶜ, avg (fun r : Tgt n => (if ((r v) : Fin n) ∈ I then (0 : ℝ) else 1)
        * ∏ w ∈ I, (if ((r w) : Fin n) = v then (0 : ℝ) else 1))
      = ((n : ℝ) - 1 - I.card) / ((n : ℝ) - 1) * (1 - 1 / ((n : ℝ) - 1)) ^ I.card := by
    intro v hv
    have hv' := mem_compl.1 hv
    rw [avg_tgt_mul_prod hn hv' (fun y => if y ∈ I then (0 : ℝ) else 1)
        (fun _ y => if y = v then (0 : ℝ) else 1), avg_call_not_mem hn hv',
      prod_congr rfl fun w hw => avg_call_ne hn (v := v) (w := w) (by rintro rfl; exact hv' hw),
      prod_const]
  rw [hpt, avg_sum, sum_congr rfl hv, sum_const, nsmul_eq_mul, cast_card_compl]
  ring

end RumorPush
