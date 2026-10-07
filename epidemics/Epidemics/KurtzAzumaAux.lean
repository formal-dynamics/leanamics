import Dynamics.Uniform

/-! # Hoeffding's lemma and Ville's maximal inequality along uniform rounds (CRN-2, helpers)

Ingredients of the maximal Azuma–Hoeffding inequality `Epidemics.Kurtz.expList_azuma`:

* `avg_exp_mul_le`: **Hoeffding's lemma** for a centred variable bounded by `c` under a uniform
  draw, `avg (exp (θ f)) ≤ exp (θ² c² / 2)` (convexity of `exp`, then
  `Real.cosh_le_exp_half_sq`);
* `expList_ville`: **Ville's maximal inequality** for a multiplicative process
  `exp (M x l)` with `M x (a :: l) = E x a + M (step x a) l` and `avg (exp (E y ·)) ≤ 1` (a
  nonnegative supermartingale started at `1`): it reaches `μ > 0` within `n` rounds with
  probability at most `1 / μ`. Proved by induction on `n`, peeling off the first round.
-/

namespace Epidemics.Kurtz

open Dynamics Real

variable {σ R : Type*} [Fintype R]

/-- An indicator is monotone in its event. -/
lemma ite_one_zero_le_of_imp {P Q : Prop} [Decidable P] [Decidable Q] (h : P → Q) :
    (if P then (1 : ℝ) else 0) ≤ if Q then 1 else 0 := by
  by_cases hP : P
  · rw [if_pos hP, if_pos (h hP)]
  · rw [if_neg hP]
    split_ifs <;> norm_num

/-- A uniform average of values at most one is at most one (also on an empty type). -/
lemma avg_le_one {f : R → ℝ} (h : ∀ a, f a ≤ 1) : avg f ≤ 1 := by
  rcases isEmpty_or_nonempty R with hR | hR
  · simp [avg]
  · simpa [avg_const] using avg_le_avg h

/-- An `expList` average of values at most one is at most one. -/
lemma expList_le_one {T : ℕ} {F : List R → ℝ} (h : ∀ l, F l ≤ 1) : expList R T F ≤ 1 := by
  induction T generalizing F with
  | zero => exact h []
  | succ T ih => exact avg_le_one fun a ↦ ih fun l ↦ h (a :: l)

/-- `expList` is monotone as soon as the comparison holds on lists of the right length. -/
lemma expList_le_expList_of_length {T : ℕ} {F G : List R → ℝ}
    (h : ∀ l : List R, l.length = T → F l ≤ G l) : expList R T F ≤ expList R T G := by
  induction T generalizing F G with
  | zero => exact h [] rfl
  | succ T ih => exact avg_le_avg fun a ↦ ih fun l hl ↦ h (a :: l) (by simp [hl])

/-- **Hoeffding's lemma** (Hoeffding 1963, (4.16)) for a uniform draw: if `f` has mean zero and
`|f| ≤ c`, then `avg (exp (θ f)) ≤ exp (θ² c² / 2)`. -/
lemma avg_exp_mul_le {f : R → ℝ} {c : ℝ} (hmean : avg f = 0) (hb : ∀ a, |f a| ≤ c) (θ : ℝ) :
    avg (fun a ↦ exp (θ * f a)) ≤ exp (θ ^ 2 * c ^ 2 / 2) := by
  rcases isEmpty_or_nonempty R with hR | hR
  · simp only [avg, Finset.univ_eq_empty, Finset.sum_empty, zero_div]
    positivity
  have hc : 0 ≤ c := (abs_nonneg _).trans (hb (Classical.arbitrary R))
  rcases hc.eq_or_lt with rfl | hc
  · have h0 (a : R) : f a = 0 := abs_nonpos_iff.mp (hb a)
    simp [h0, avg_const]
  -- convexity of `exp` on the segment `[-θc, θc]`
  have key (a : R) : exp (θ * f a)
      ≤ (exp (-(θ * c)) + exp (θ * c)) / 2 + (exp (θ * c) - exp (-(θ * c))) / (2 * c) * f a := by
    have hfa := abs_le.mp (hb a)
    have h1 : 0 ≤ (c - f a) / (2 * c) := div_nonneg (by linarith) (by positivity)
    have h2 : 0 ≤ (c + f a) / (2 * c) := div_nonneg (by linarith) (by positivity)
    have h12 : (c - f a) / (2 * c) + (c + f a) / (2 * c) = 1 := by field_simp; ring
    have hconv := convexOn_exp.2 (Set.mem_univ (-(θ * c))) (Set.mem_univ (θ * c)) h1 h2 h12
    simp only [smul_eq_mul] at hconv
    have hl : (c - f a) / (2 * c) * -(θ * c) + (c + f a) / (2 * c) * (θ * c) = θ * f a := by
      field_simp
      ring
    have hr : (c - f a) / (2 * c) * exp (-(θ * c)) + (c + f a) / (2 * c) * exp (θ * c)
        = (exp (-(θ * c)) + exp (θ * c)) / 2
          + (exp (θ * c) - exp (-(θ * c))) / (2 * c) * f a := by
      field_simp
      ring
    rw [hl, hr] at hconv
    exact hconv
  calc avg (fun a ↦ exp (θ * f a))
      ≤ avg (fun a ↦ (exp (-(θ * c)) + exp (θ * c)) / 2
          + (exp (θ * c) - exp (-(θ * c))) / (2 * c) * f a) := avg_le_avg key
    _ = cosh (θ * c) := by
        rw [avg_add, avg_const, avg_const_mul, hmean, mul_zero, add_zero, cosh_eq, add_comm]
    _ ≤ exp ((θ * c) ^ 2 / 2) := cosh_le_exp_half_sq _
    _ = exp (θ ^ 2 * c ^ 2 / 2) := by ring_nf

/-- **Ville's maximal inequality** along i.i.d. uniform rounds (finite horizon). Let
`M x (a :: l) = E x a + M (step x a) l`, `M x [] = 0`, with `avg (exp (E y ·)) ≤ 1` for every
`y`, so that `k ↦ exp (M x (l.take k))` is a nonnegative supermartingale started at `1`. Then it
reaches `μ > 0` at some step `k ≤ n` with probability at most `1 / μ`. -/
lemma expList_ville (step : σ → R → σ) (E : σ → R → ℝ) (M : σ → List R → ℝ)
    (hM0 : ∀ x, M x [] = 0) (hM : ∀ x a l, M x (a :: l) = E x a + M (step x a) l)
    (hE : ∀ y, avg (fun a ↦ exp (E y a)) ≤ 1) (n : ℕ) :
    ∀ (x : σ) {μ : ℝ}, 0 < μ →
      expList R n (fun l ↦ if ∃ k ≤ n, μ ≤ exp (M x (l.take k)) then 1 else 0) ≤ 1 / μ := by
  induction n with
  | zero =>
    intro x μ hμ
    simp only [expList_zero]
    split_ifs with h
    · obtain ⟨k, -, hk⟩ := h
      rw [List.take_nil, hM0, exp_zero] at hk
      rw [le_div_iff₀ hμ]
      linarith
    · positivity
  | succ n ih =>
    intro x μ hμ
    rcases le_or_gt μ 1 with hμ1 | hμ1
    · calc _ ≤ (1 : ℝ) := expList_le_one fun l ↦ by split_ifs <;> norm_num
        _ ≤ 1 / μ := by rw [le_div_iff₀ hμ]; linarith
    rw [expList_succ]
    have hpt (a : R) : expList R n (fun l ↦
          if ∃ k ≤ n + 1, μ ≤ exp (M x ((a :: l).take k)) then (1 : ℝ) else 0)
        ≤ exp (E x a) / μ := by
      have hμ' : 0 < μ / exp (E x a) := by positivity
      calc _ ≤ expList R n (fun l ↦
              if ∃ k ≤ n, μ / exp (E x a) ≤ exp (M (step x a) (l.take k)) then (1 : ℝ) else 0) :=
            expList_le_expList fun l ↦ ite_one_zero_le_of_imp fun ⟨k, hk, hle⟩ ↦ by
              rcases k with _ | k
              · rw [List.take_zero, hM0, exp_zero] at hle
                linarith
              · refine ⟨k, by omega, ?_⟩
                rw [List.take_succ_cons, hM, exp_add] at hle
                rw [div_le_iff₀ (exp_pos _)]
                linarith
        _ ≤ 1 / (μ / exp (E x a)) := ih (step x a) hμ'
        _ = exp (E x a) / μ := by rw [one_div_div]
    calc avg (fun a ↦ expList R n (fun l ↦
            if ∃ k ≤ n + 1, μ ≤ exp (M x ((a :: l).take k)) then (1 : ℝ) else 0))
        ≤ avg (fun a ↦ exp (E x a) / μ) := avg_le_avg hpt
      _ = avg (fun a ↦ exp (E x a)) / μ := by
          simp only [div_eq_mul_inv, mul_comm _ μ⁻¹, avg_const_mul]
      _ ≤ 1 / μ := div_le_div_of_nonneg_right (hE x) hμ.le

end Epidemics.Kurtz
