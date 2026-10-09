import Epidemics.Revisited.LowerFinal

/-! # Final phase of push (EPI-8, Theorem 38 with `ρ = 1`)

Round-by-round lower envelope of the number of uninformed nodes along the explicit targets
`g i = q_i^3 (q_i - 20)`, where `q_i = (u e^{-i})^{1/4} = exp((ln u - i) / 4)` is the fourth
root of the reference level `u e^{-i}` and `u` is the initial number of uninformed nodes
(`pushRoot`, `pushTarget`). The one-round lemma `push_round_lower_proof` at the level
`v = g i` gives the step `g (i + 1) ≤ g i / e - (g i)^{3/4}` (`pushTarget_step`; the slack
constant `20` absorbs the loss `(g i)^{3/4} ≤ q_i^3` and needs only `e^{1/4} ≥ 5/4` and
`e ≤ 3`). While `q_i ≥ 40`, the failure probability of round `i` is at most `2 / q_i^2`, and
these sum to at most `4 e^{(t - ln u)/2}`. When `q_t < 40`, the claimed bound
`1600 e^{(t - ln u)/2} = 1600 / q_t^2` exceeds `1`.
-/

namespace Epidemics.Revisited
open Finset Dynamics RumorProcess Real

variable {n : ℕ}

/-- The push target as a function of the fourth root `q` of the reference level `q^4`. -/
noncomputable def pushTarget (q : ℝ) : ℝ := q ^ 3 * (q - 20)

lemma pushTarget_le_pow_four {q : ℝ} (hq : 0 ≤ q) : pushTarget q ≤ q ^ 4 := by
  unfold pushTarget
  nlinarith [pow_nonneg hq 3]

lemma pushTarget_nonneg {q : ℝ} (hq : 20 ≤ q) : 0 ≤ pushTarget q :=
  mul_nonneg (pow_nonneg (by linarith) 3) (by linarith)

/-- For `q ≥ 40` the target is at least half the reference level. -/
lemma pushTarget_ge_half {q : ℝ} (hq : 40 ≤ q) : q ^ 4 / 2 ≤ pushTarget q := by
  unfold pushTarget
  have h3 : 0 ≤ q ^ 3 := pow_nonneg (by linarith) 3
  have hle := mul_le_mul_of_nonneg_left (show q / 2 ≤ q - 20 by linarith) h3
  calc q ^ 4 / 2 = q ^ 3 * (q / 2) := by ring
    _ ≤ q ^ 3 * (q - 20) := hle

lemma exp_quarter_ge : (5 / 4 : ℝ) ≤ exp (1 / 4) := by
  have := add_one_le_exp (1 / 4 : ℝ)
  linarith

lemma exp_quarter_pow_four : exp (1 / 4 : ℝ) ^ 4 = exp 1 := by
  rw [← exp_nat_mul]
  norm_num

/-- The key step of the envelope: `g(q e^{-1/4}) ≤ g(q) / e - g(q)^{3/4}` for `q ≥ 20`. -/
lemma pushTarget_step {q : ℝ} (hq : 20 ≤ q) :
    pushTarget (q / exp (1 / 4)) ≤ pushTarget q / exp 1 - pushTarget q ^ (3 / 4 : ℝ) := by
  have hq0 : 0 ≤ q := by linarith
  have h34 : pushTarget q ^ (3 / 4 : ℝ) ≤ q ^ 3 := by
    have hpow : (q ^ 4) ^ (3 / 4 : ℝ) = q ^ 3 := by
      rw [← rpow_natCast q 4, ← rpow_mul hq0]
      norm_num
    calc pushTarget q ^ (3 / 4 : ℝ) ≤ (q ^ 4) ^ (3 / 4 : ℝ) :=
          rpow_le_rpow (pushTarget_nonneg hq) (pushTarget_le_pow_four hq0) (by norm_num)
      _ = q ^ 3 := hpow
  obtain ⟨c, hc⟩ : ∃ c, c = exp (1 / 4 : ℝ) := ⟨_, rfl⟩
  have hc0 : 0 < c := hc ▸ exp_pos _
  have hc1 : (5 / 4 : ℝ) ≤ c := hc ▸ exp_quarter_ge
  have hc4 : exp 1 = c ^ 4 := by rw [hc, exp_quarter_pow_four]
  have he3 : c ^ 4 ≤ 3 := by
    rw [← hc4]
    exact (lt_trans exp_one_lt_d9 (by norm_num)).le
  rw [← hc, hc4]
  suffices h : pushTarget (q / c) ≤ pushTarget q / c ^ 4 - q ^ 3 by linarith
  unfold pushTarget
  have hkey : q ^ 3 * (q - 20) / c ^ 4 - q ^ 3 - (q / c) ^ 3 * (q / c - 20) =
      q ^ 3 * (20 * c - 20 - c ^ 4) / c ^ 4 := by
    field_simp
    ring
  have hnn : 0 ≤ q ^ 3 * (20 * c - 20 - c ^ 4) / c ^ 4 :=
    div_nonneg (mul_nonneg (pow_nonneg hq0 3) (by linarith)) (pow_nonneg hc0.le 4)
  linarith

/-- `v^{-1/2} ≤ 2 / q^2` whenever `q^4 / 4 ≤ v`. -/
lemma rpow_neg_half_le {q v : ℝ} (hq : 0 < q) (hv : q ^ 4 / 4 ≤ v) :
    v ^ (-(1 / 2 : ℝ)) ≤ 2 / q ^ 2 := by
  have hv0 : 0 < v := lt_of_lt_of_le (by positivity) hv
  rw [rpow_neg hv0.le, ← sqrt_eq_rpow]
  have hpos : 0 < q ^ 2 / 2 := by positivity
  have hsq : q ^ 2 / 2 ≤ sqrt v := by
    rw [show q ^ 4 / 4 = (q ^ 2 / 2) ^ 2 by ring] at hv
    calc q ^ 2 / 2 = sqrt ((q ^ 2 / 2) ^ 2) := (sqrt_sq hpos.le).symm
      _ ≤ sqrt v := sqrt_le_sqrt hv
  calc (sqrt v)⁻¹ ≤ (q ^ 2 / 2)⁻¹ := inv_anti₀ hpos hsq
    _ = 2 / q ^ 2 := by rw [inv_div]

/-- One round along the targets: from at least `g(q)` uninformed nodes (`q ≥ 40`), fewer than
`g(q e^{-1/4})` stay uninformed with probability at most `2 / q^2`. -/
lemma push_target_round {q : ℝ} (hq : 40 ≤ q) (a : Finset (Fin n))
    (ha : pushTarget q ≤ (n : ℝ) - a.card) :
    ((push n).K a).prob (fun b => (n : ℝ) - b.card < pushTarget (q / exp (1 / 4))) ≤
      2 / q ^ 2 := by
  have hhalf := pushTarget_ge_half hq
  have hq4 : (40 : ℝ) ^ 4 ≤ q ^ 4 := pow_le_pow_left₀ (by norm_num) hq 4
  have hv : (4 : ℝ) ≤ pushTarget q := by linarith
  have hround := push_round_lower_proof a hv ha
  have hmono : ((push n).K a).prob (fun b => (n : ℝ) - b.card < pushTarget (q / exp (1 / 4))) ≤
      ((push n).K a).prob (fun b => (n : ℝ) - b.card <
        pushTarget q / exp 1 - pushTarget q ^ (3 / 4 : ℝ)) :=
    prob_mono _ fun b hb => lt_of_lt_of_le hb (pushTarget_step (by linarith))
  have hfin := rpow_neg_half_le (by linarith : (0 : ℝ) < q)
    (show q ^ 4 / 4 ≤ pushTarget q by linarith [pow_nonneg (by linarith : (0 : ℝ) ≤ q) 4])
  linarith

/-- Fourth root of the reference level after `i` rounds: `q_i = exp((L - i) / 4)`, where
`L = ln u`. -/
noncomputable def pushRoot (L : ℝ) (i : ℕ) : ℝ := exp ((L - i) / 4)

lemma pushRoot_succ (L : ℝ) (i : ℕ) : pushRoot L (i + 1) = pushRoot L i / exp (1 / 4) := by
  unfold pushRoot
  rw [← exp_sub]
  congr 1
  push_cast
  ring

lemma pushRoot_anti (L : ℝ) {i j : ℕ} (hij : i ≤ j) : pushRoot L j ≤ pushRoot L i := by
  unfold pushRoot
  apply exp_le_exp.mpr
  have : (i : ℝ) ≤ j := by exact_mod_cast hij
  linarith

lemma two_div_pushRoot_sq (L : ℝ) (i : ℕ) :
    2 / pushRoot L i ^ 2 = 2 * exp (-L / 2) * exp (1 / 2) ^ i := by
  unfold pushRoot
  rw [← exp_nat_mul, ← exp_nat_mul, mul_assoc, ← exp_add, div_eq_mul_inv, ← exp_neg]
  congr 2
  push_cast
  ring

/-- Final phase of push with explicit constants `C = 1600`, `κ = 1/2`. -/
theorem push_final_lower_explicit (n : ℕ) (S : Finset (Fin n)) (t : ℕ) :
    1 - (push n).notYet n t S ≤
      1600 * exp ((1 / 2 : ℝ) * ((t : ℝ) - log ((n : ℝ) - S.card))) := by
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (n : ℝ) - S.card := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by
    rw [hu]
    linarith [card_le_n S]
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = log u := ⟨_, rfl⟩
  rw [← hu, ← hL]
  have hrhs : exp ((1 / 2 : ℝ) * ((t : ℝ) - L)) = 1 / pushRoot L t ^ 2 := by
    unfold pushRoot
    rw [← exp_nat_mul, eq_div_iff (exp_pos _).ne', ← exp_add, exp_eq_one_iff]
    push_cast
    ring
  have hreach0 := notYet_le_one (push n) n t S
  by_cases hbig : 40 ≤ pushRoot L t
  · have hupos : 0 < u := by
      rcases hu0.eq_or_lt with h | h
      · exfalso
        have hL0 : L = 0 := by rw [hL, ← h, log_zero]
        have hle : pushRoot L t ≤ 1 := by
          unfold pushRoot
          rw [hL0, ← exp_zero]
          apply exp_le_exp.mpr
          have : (0 : ℝ) ≤ t := Nat.cast_nonneg t
          linarith
        linarith
      · exact h
    have hroot0 : pushRoot L 0 ^ 4 = u := by
      unfold pushRoot
      rw [← exp_nat_mul, Nat.cast_zero, sub_zero, hL]
      push_cast
      rw [mul_div_cancel₀ _ (by norm_num : (4 : ℝ) ≠ 0), exp_log hupos]
    let δ : ℕ → ℝ := fun i => if 40 ≤ pushRoot L i then 2 / pushRoot L i ^ 2 else 1
    have hδ : ∀ i, 0 ≤ δ i := by
      intro i
      dsimp only [δ]
      split_ifs <;> positivity
    have hstep : ∀ i (a : Finset (Fin n)), pushTarget (pushRoot L i) ≤ (n : ℝ) - (a.card : ℝ) →
        ((push n).K a).prob
          (fun b => (n : ℝ) - (b.card : ℝ) < pushTarget (pushRoot L (i + 1))) ≤ δ i := by
      intro i a ha
      dsimp only [δ]
      split_ifs with h
      · rw [pushRoot_succ]
        exact push_target_round h a ha
      · exact ((push n).K a).prob_le_one _
    have hstart : pushTarget (pushRoot L 0) ≤ (n : ℝ) - (S.card : ℝ) := by
      rw [← hu, ← hroot0]
      exact pushTarget_le_pow_four (exp_pos _).le
    have hgt : 0 < pushTarget (pushRoot L t) := by
      unfold pushTarget
      have h1 : 0 < pushRoot L t := exp_pos _
      have h2 : 0 < pushRoot L t - 20 := by linarith
      positivity
    have henv := reach_le_envelope (push n) (fun i => pushTarget (pushRoot L i)) δ hδ hstep
      t S hstart hgt
    have hsum : ∑ i ∈ range t, δ i = ∑ i ∈ range t, 2 * exp (-L / 2) * exp (1 / 2) ^ i := by
      apply sum_congr rfl
      intro i hi
      have h40 : 40 ≤ pushRoot L i := le_trans hbig (pushRoot_anti L (mem_range.mp hi).le)
      dsimp only [δ]
      rw [if_pos h40, two_div_pushRoot_sq]
    have hhalf : (1 / 2 : ℝ) ≤ exp (1 / 2) - 1 := by
      linarith [add_one_le_exp (1 / 2 : ℝ)]
    have hgeom : ∑ i ∈ range t, 2 * exp (-L / 2) * exp (1 / 2) ^ i ≤
        2 * exp (-L / 2) * (exp (1 / 2) ^ t / (exp (1 / 2) - 1)) := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left (geom_sum_le_div (by linarith) t) (by positivity)
    have hdiv : exp (1 / 2) ^ t / (exp (1 / 2) - 1) ≤ 2 * exp (1 / 2) ^ t := by
      rw [div_le_iff₀ (by linarith)]
      have hp : 0 ≤ exp (1 / 2 : ℝ) ^ t := pow_nonneg (exp_pos _).le t
      nlinarith [mul_le_mul_of_nonneg_left hhalf hp]
    have hE : exp (-L / 2) * exp (1 / 2) ^ t = exp ((1 / 2 : ℝ) * ((t : ℝ) - L)) := by
      rw [← exp_nat_mul, ← exp_add]
      congr 1
      ring
    have hfour : 2 * exp (-L / 2) * (exp (1 / 2) ^ t / (exp (1 / 2) - 1)) ≤
        4 * exp ((1 / 2 : ℝ) * ((t : ℝ) - L)) := by
      rw [← hE]
      have := mul_le_mul_of_nonneg_left hdiv (by positivity : (0 : ℝ) ≤ 2 * exp (-L / 2))
      linarith
    have hpos : 0 ≤ exp ((1 / 2 : ℝ) * ((t : ℝ) - L)) := (exp_pos _).le
    linarith
  · have hpos : 0 < pushRoot L t := exp_pos _
    have hlt : pushRoot L t ^ 2 < 1600 := by nlinarith
    have hone : 1 ≤ 1600 * (1 / pushRoot L t ^ 2) := by
      rw [mul_one_div, le_div_iff₀ (by positivity)]
      linarith
    have hnn := notYet_nonneg (push n) n t S
    rw [hrhs]
    linarith

end Epidemics.Revisited
