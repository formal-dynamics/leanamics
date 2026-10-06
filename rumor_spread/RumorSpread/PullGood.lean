import RumorSpread.PullOneRound
import RumorSpread.PullPhases

/-!
# The two one-round inputs of the PULL proof

`notAllOf_le_two_div` (`PullPhases.lean`) needs two facts about the PULL step:

* `pull_prob_goodRound` — a PULL round is good (grows the informed set by `9/8`, or starts above
  `n/2`) with probability `≥ 1/8`. Unlike PUSH, a PULL round can inform many more than `|I|` new
  nodes, so the reverse-Markov argument of `prob_goodRound` does not apply. We use a second
  moment instead: the number `X` of uninformed callers that call into `I` has mean
  `μ = (n - m) m/(n-1) ≥ max(m/2, 1/2)` and, the calls being pairwise independent,
  `𝔼X² ≤ μ + μ²` (`pull_avg_new_sq_le`). The Paley–Zygmund bound is then obtained from the
  pointwise inequality `X ≤ μ/4 + X²/(2t) + (t/2)·1[good]` with `t = 4(1+μ)/3`.
* `pull_avg_uninformed_contract` — above half, the expected uninformed count contracts by `2/3`
  (from the exact formula `pull_avg_uninformed`; the true factor is `≤ 1/2`).
-/

namespace RumorPush

open Finset

variable {n : ℕ}

/-- **Second moment** of the number of uninformed callers that call into `I`:
`𝔼X² ≤ μ + μ²` with `μ = (n - |I|) · |I|/(n-1)`. -/
lemma pull_avg_new_sq_le (hn : 2 ≤ n) (I : Finset (Fin n)) :
    avg (fun r : Tgt n => (∑ v ∈ Iᶜ, if ((r v) : Fin n) ∈ I then (1 : ℝ) else 0) ^ 2)
      ≤ ((n : ℝ) - I.card) * (I.card / ((n : ℝ) - 1))
          + (((n : ℝ) - I.card) * (I.card / ((n : ℝ) - 1))) ^ 2 := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp0 : (0 : ℝ) ≤ I.card / ((n : ℝ) - 1) :=
    div_nonneg (Nat.cast_nonneg _) (by linarith)
  have hsq : ∀ r : Tgt n, (∑ v ∈ Iᶜ, if ((r v) : Fin n) ∈ I then (1 : ℝ) else 0) ^ 2
      = ∑ v ∈ Iᶜ, ∑ w ∈ Iᶜ, (if ((r v) : Fin n) ∈ I then (1 : ℝ) else 0)
          * (if ((r w) : Fin n) ∈ I then (1 : ℝ) else 0) :=
    fun r => by rw [sq, sum_mul_sum]
  have hpair : ∀ v ∈ Iᶜ, ∀ w ∈ Iᶜ,
      avg (fun r : Tgt n => (if ((r v) : Fin n) ∈ I then (1 : ℝ) else 0)
          * (if ((r w) : Fin n) ∈ I then (1 : ℝ) else 0))
        ≤ (if v = w then I.card / ((n : ℝ) - 1) else 0) + (I.card / ((n : ℝ) - 1)) ^ 2 := by
    intro v hv w hw
    have hv' := mem_compl.1 hv
    have hw' := mem_compl.1 hw
    by_cases hvw : v = w
    · rw [if_pos hvw, ← hvw]
      have hidem : (fun r : Tgt n => (if ((r v) : Fin n) ∈ I then (1 : ℝ) else 0)
          * (if ((r v) : Fin n) ∈ I then (1 : ℝ) else 0))
          = fun r : Tgt n => if ((r v) : Fin n) ∈ I then (1 : ℝ) else 0 := by
        funext r
        by_cases h : ((r v) : Fin n) ∈ I <;> simp [h]
      rw [hidem, avg_tgt_call_mem hn hv']
      nlinarith [sq_nonneg (I.card / ((n : ℝ) - 1))]
    · rw [if_neg hvw, zero_add]
      have h := avg_tgt_mul_prod hn (v := v) (S := {w}) (by simpa using hvw)
        (fun y => if y ∈ I then (1 : ℝ) else 0) (fun _ y => if y ∈ I then (1 : ℝ) else 0)
      simp only [prod_singleton] at h
      rw [h, avg_call_mem hn hv', avg_call_mem hn hw', sq]
  rw [show (fun r : Tgt n => (∑ v ∈ Iᶜ, if ((r v) : Fin n) ∈ I then (1 : ℝ) else 0) ^ 2)
      = fun r : Tgt n => ∑ v ∈ Iᶜ, ∑ w ∈ Iᶜ, (if ((r v) : Fin n) ∈ I then (1 : ℝ) else 0)
          * (if ((r w) : Fin n) ∈ I then (1 : ℝ) else 0) from funext hsq, avg_sum]
  calc ∑ v ∈ Iᶜ, avg (fun r : Tgt n => ∑ w ∈ Iᶜ,
          (if ((r v) : Fin n) ∈ I then (1 : ℝ) else 0)
            * (if ((r w) : Fin n) ∈ I then (1 : ℝ) else 0))
      = ∑ v ∈ Iᶜ, ∑ w ∈ Iᶜ, avg (fun r : Tgt n =>
          (if ((r v) : Fin n) ∈ I then (1 : ℝ) else 0)
            * (if ((r w) : Fin n) ∈ I then (1 : ℝ) else 0)) :=
        sum_congr rfl fun v _ => avg_sum _ _
    _ ≤ ∑ v ∈ Iᶜ, ∑ w ∈ Iᶜ, ((if v = w then I.card / ((n : ℝ) - 1) else 0)
          + (I.card / ((n : ℝ) - 1)) ^ 2) :=
        sum_le_sum fun v hv => sum_le_sum fun w hw => hpair v hv w hw
    _ = ∑ v ∈ Iᶜ, (I.card / ((n : ℝ) - 1)
          + ((Iᶜ).card : ℝ) * (I.card / ((n : ℝ) - 1)) ^ 2) := by
        refine sum_congr rfl fun v hv => ?_
        rw [sum_add_distrib, sum_ite_eq, if_pos hv, sum_const, nsmul_eq_mul]
    _ = _ := by
        rw [sum_const, nsmul_eq_mul, cast_card_compl]
        ring

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
    set G : Tgt n → ℝ := fun r => if goodRoundOf pullStep I r then (1 : ℝ) else 0 with hG
    set μ : ℝ := ((n : ℝ) - I.card) * (I.card / ((n : ℝ) - 1)) with hμ
    have hEX : avg X = μ := pull_avg_new hn I
    have hEX2 : avg (fun r => X r ^ 2) ≤ μ + μ ^ 2 := pull_avg_new_sq_le hn I
    have hμm : (I.card : ℝ) / 2 ≤ μ := by
      rw [hμ, mul_div_assoc', le_div_iff₀ (by linarith)]
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ ((n : ℝ) + 1) / 2 - I.card)
        (Nat.cast_nonneg (α := ℝ) I.card)]
    have hμ1 : (1 : ℝ) / 2 ≤ μ := by linarith
    set t : ℝ := 4 * (1 + μ) / 3 with ht
    have ht0 : 0 < t := by rw [ht]; linarith
    have hpt : ∀ r : Tgt n, X r ≤ μ / 4 + 1 / (2 * t) * X r ^ 2 + t / 2 * G r := by
      intro r
      by_cases hg : goodRoundOf pullStep I r
      · have hGr : G r = 1 := if_pos hg
        rw [hGr]
        have hamgm : X r ≤ 1 / (2 * t) * X r ^ 2 + t / 2 := by
          have hkey : 1 / (2 * t) * X r ^ 2 + t / 2 - X r = (X r - t) ^ 2 / (2 * t) := by
            field_simp
            ring
          have : 0 ≤ (X r - t) ^ 2 / (2 * t) := by positivity
          linarith
        linarith
      · have hGr : G r = 0 := if_neg hg
        rw [hGr, mul_zero, add_zero]
        have hlt : 8 * (pullStep I r).card < 9 * I.card := by
          by_contra h
          push Not at h
          exact hg (Or.inl h)
        have hcard : ((pullStep I r).card : ℝ) = I.card + X r := card_pullStep I r
        have hlt' : (8 : ℝ) * (pullStep I r).card < 9 * I.card := by exact_mod_cast hlt
        have hsq : 0 ≤ 1 / (2 * t) * X r ^ 2 := by positivity
        linarith
    have havg := avg_le_avg hpt
    rw [avg_add, avg_add, avg_const, avg_const_mul, avg_const_mul, hEX] at havg
    have h1 : 1 / (2 * t) * avg (fun r => X r ^ 2) ≤ 3 * μ / 8 := by
      calc 1 / (2 * t) * avg (fun r => X r ^ 2) ≤ 1 / (2 * t) * (μ + μ ^ 2) :=
            mul_le_mul_of_nonneg_left hEX2 (by positivity)
        _ = 3 * μ / 8 := by
            rw [ht]
            field_simp
            ring
    have hP : 3 / 8 * μ ≤ t / 2 * avg G := by linarith
    rw [ht] at hP
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
