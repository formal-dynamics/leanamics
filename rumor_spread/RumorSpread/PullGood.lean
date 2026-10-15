import RumorSpread.PullOneRound
import RumorSpread.PullPhases
import Dynamics.Moments

/-!
# The two one-round inputs of the PULL proof

`notAllOf_le_two_div` (`PullPhases.lean`) needs two facts about the PULL step:

* `pull_prob_goodRound` — a PULL round is good (grows the informed set by `9/8`, or starts above
  `n/2`) with probability `≥ 1/8`. Unlike PUSH, a PULL round can inform many more than `|I|` new
  nodes, so the reverse-Markov argument of `prob_goodRound` does not apply. We use a second
  moment instead: the number `X` of uninformed callers that call into `I` has mean
  `μ = (n - m) m/(n-1) ≥ max(m/2, 1/2)` and, the calls being pairwise independent,
  `𝔼X² ≤ μ + μ²` (`pull_avg_new_sq_le`, from the shared `Dynamics.avg_sq_sum_le_of_pairwise`).
  The shared one-sided Paley–Zygmund bound `Dynamics.avg_pz_one_sided` at `θ = 1/4` then gives
  `P(X > μ/4) ≥ (9/16) μ²/(μ + μ²) ≥ 3/16`, and `X > μ/4 ≥ |I|/8` makes the round good.
* `pull_avg_uninformed_contract` — above half, the expected uninformed count contracts by `2/3`
  (from the exact formula `pull_avg_uninformed`; the true factor is `≤ 1/2`).
-/

namespace RumorPush

open Finset Dynamics

variable {n : ℕ}

/-- **Second moment** of the number of uninformed callers that call into `I`:
`𝔼X² ≤ μ + μ²` with `μ = (n - |I|) · |I|/(n-1)`. -/
lemma pull_avg_new_sq_le (hn : 2 ≤ n) (I : Finset (Fin n)) :
    avg (fun r : Tgt n => (∑ v ∈ Iᶜ, if ((r v) : Fin n) ∈ I then (1 : ℝ) else 0) ^ 2)
      ≤ ((n : ℝ) - I.card) * (I.card / ((n : ℝ) - 1))
          + (((n : ℝ) - I.card) * (I.card / ((n : ℝ) - 1))) ^ 2 := by
  -- pairwise independent indicators of calling into `I`, each with mean `|I|/(n-1)`
  have hμ : ∑ v ∈ Iᶜ, avg (fun r : Tgt n => if ((r v) : Fin n) ∈ I then (1 : ℝ) else 0)
      = ((n : ℝ) - I.card) * (I.card / ((n : ℝ) - 1)) := by
    rw [sum_congr rfl fun v hv => avg_tgt_call_mem hn (mem_compl.1 hv), sum_const, nsmul_eq_mul,
      cast_card_compl]
  have key := avg_sq_sum_le_of_pairwise (Ω := Tgt n) Iᶜ
    (fun v r => if ((r v) : Fin n) ∈ I then (1 : ℝ) else 0)
    (fun v r => by split_ifs <;> simp) fun v hv w hw hvw => by
      have h := avg_tgt_mul_prod hn (v := v) (S := {w}) (by simpa using hvw)
        (fun y => if y ∈ I then (1 : ℝ) else 0) (fun _ y => if y ∈ I then (1 : ℝ) else 0)
      simp only [prod_singleton] at h
      rw [h, avg_call_mem hn (mem_compl.1 hv), avg_call_mem hn (mem_compl.1 hw),
        avg_tgt_call_mem hn (mem_compl.1 hv), avg_tgt_call_mem hn (mem_compl.1 hw)]
  rwa [hμ] at key

/-- **A PULL round is good with probability at least `1/8`** (second-moment argument). -/
lemma pull_prob_goodRound (hn : 2 ≤ n) (I : Finset (Fin n)) (hI : I.Nonempty) :
    (1 : ℝ) / 8 ≤ avg (fun r : Tgt n => if goodRoundOf pullStep I r then (1 : ℝ) else 0) := by
  haveI := tgt_nonempty hn
  by_cases hbig : n < 2 * I.card
  · rw [show (fun r : Tgt n => if goodRoundOf pullStep I r then (1 : ℝ) else 0)
        = fun _ : Tgt n => (1 : ℝ) from funext fun r => if_pos (Or.inr hbig), avg_const]
    norm_num
  · push Not at hbig
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hm1 : (1 : ℝ) ≤ I.card := by exact_mod_cast hI.card_pos
    have hmn : (2 : ℝ) * I.card ≤ n := by exact_mod_cast hbig
    set X : Tgt n → ℝ := fun r => ∑ v ∈ Iᶜ, if ((r v) : Fin n) ∈ I then (1 : ℝ) else 0
      with hX
    set μ : ℝ := ((n : ℝ) - I.card) * (I.card / ((n : ℝ) - 1)) with hμ
    have hEX : avg X = μ := pull_avg_new hn I
    have hEX2 : avg (fun r => X r ^ 2) ≤ μ + μ ^ 2 := pull_avg_new_sq_le hn I
    have hμm : (I.card : ℝ) / 2 ≤ μ := by
      rw [hμ, mul_div_assoc', le_div_iff₀ (by linarith)]
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ ((n : ℝ) + 1) / 2 - I.card)
        (Nat.cast_nonneg (α := ℝ) I.card)]
    have hμ1 : (1 : ℝ) / 2 ≤ μ := by linarith
    -- one-sided Paley-Zygmund at `θ = 1/4`: `(9/16) μ² ≤ 𝔼X² P(X > μ/4)`
    have hpz := avg_pz_one_sided X (by linarith) (θ := 1 / 4) (by norm_num) (by norm_num)
    rw [hEX] at hpz
    set P := avg (fun r => if 1 / 4 * μ < X r then (1 : ℝ) else 0)
    have hP0 : 0 ≤ P := avg_nonneg fun r => by split_ifs <;> norm_num
    -- `X > μ/4 ≥ |I|/8` makes the round good
    have hgood : P ≤ avg (fun r : Tgt n => if goodRoundOf pullStep I r then (1 : ℝ) else 0) := by
      refine avg_le_avg fun r => ?_
      by_cases hx : 1 / 4 * μ < X r
      · have hcard : ((pullStep I r).card : ℝ) = I.card + X r := card_pullStep I r
        have hle : (9 : ℝ) * I.card ≤ 8 * (pullStep I r).card := by linarith
        have hg : goodRoundOf pullStep I r := Or.inl (by exact_mod_cast hle)
        rw [if_pos hx, if_pos hg]
      · rw [if_neg hx]
        split_ifs <;> norm_num
    have h2 : 9 / 16 * μ ^ 2 ≤ (μ + μ ^ 2) * P := by
      calc 9 / 16 * μ ^ 2 = (1 - 1 / 4) ^ 2 * μ ^ 2 := by norm_num
        _ ≤ avg (fun r => X r ^ 2) * P := hpz
        _ ≤ (μ + μ ^ 2) * P := mul_le_mul_of_nonneg_right hEX2 hP0
    nlinarith

/-- **PULL contraction above one half**: once `|I| ≥ n/2`, the expected number of uninformed
nodes shrinks by a factor `2/3` in one round. -/
lemma pull_avg_uninformed_contract (hn : 2 ≤ n) (I : Finset (Fin n)) (hI : n ≤ 2 * I.card) :
    avg (fun r : Tgt n => (n : ℝ) - (pullStep I r).card) ≤ 2 / 3 * ((n : ℝ) - I.card) := by
  rw [pull_avg_uninformed hn I]
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hmn : (n : ℝ) ≤ 2 * I.card := by exact_mod_cast hI
  have hm : (I.card : ℝ) ≤ n := by exact_mod_cast (by simpa using card_le_univ I)
  rw [div_le_iff₀ (by linarith)]
  nlinarith [mul_nonneg (sub_nonneg.2 hm)
    (by linarith : (0 : ℝ) ≤ 2 / 3 * ((n : ℝ) - 1) - ((n : ℝ) - I.card - 1))]

end RumorPush
