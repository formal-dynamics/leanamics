import Median.ExpanderGeneralDefs

/-! # Theorem 2: from the explicit bound to the `O(log n)` form

The bookkeeping of the paper's Theorem 2 (Cooper, Elsässer and Radzik, ICALP 2014,
arXiv:1404.7479) with `K = 4000` and `C = 2 · 10¹⁰`: after `⌈C log n⌉` rounds, Phase I takes
`T₁ = phaseIRounds ν₀ (1/20) ≤ 5 log n + 7` rounds and the remaining `T₂ = ⌈C log n⌉ − T₁`
rounds make the term `(24/25)^{T₂} n` at most `1/n`.
-/

namespace Median.ExpanderGeneral
open Finset Dynamics Real

/-- The imbalance is at most `1`: `A − B ≤ A + B = n`. -/
theorem imbalance_le_one {V : Type*} [Fintype V] (a : Bool) (x : V → Bool) :
    imbalance a x ≤ 1 := by
  unfold imbalance
  have h := majority_add_minority a x
  have hn : (majority a x : ℝ) + minority a x = Fintype.card V := by exact_mod_cast h
  rcases (Nat.cast_nonneg (α := ℝ) (Fintype.card V)).eq_or_lt with h0 | h0
  · rw [← h0, div_zero]
    norm_num
  · rw [div_le_one h0]
    have : (0 : ℝ) ≤ minority a x := Nat.cast_nonneg _
    linarith

/-- A positive imbalance forces `n > 0` and is at least `1/n`, as `n ν = A − B` is a positive
integer. -/
theorem one_div_card_le_imbalance {V : Type*} [Fintype V] {a : Bool} {x : V → Bool}
    (h : 0 < imbalance a x) :
    0 < (Fintype.card V : ℝ) ∧ 1 / (Fintype.card V : ℝ) ≤ imbalance a x := by
  unfold imbalance at h ⊢
  have hn : 0 < (Fintype.card V : ℝ) := by
    rcases (Nat.cast_nonneg (α := ℝ) (Fintype.card V)).eq_or_lt with h0 | h0
    · rw [← h0, div_zero] at h
      exact absurd h (lt_irrefl 0)
    · exact h0
  refine ⟨hn, div_le_div_of_nonneg_right ?_ hn.le⟩
  have h1 : minority a x < majority a x := by
    have := (div_pos_iff_of_pos_right hn).mp h
    exact_mod_cast (show (minority a x : ℝ) < majority a x by linarith)
  have h2 : minority a x + 1 ≤ majority a x := h1
  have : (minority a x : ℝ) + 1 ≤ majority a x := by exact_mod_cast h2
  linarith

/-- A `d`-regular graph with `d > 0` and a vertex `v` has at least two vertices. -/
theorem two_le_card {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hd : 0 < d) (hreg : G.IsRegularOfDegree d) (v : V) : 2 ≤ Fintype.card V := by
  have : 0 < G.degree v := by rw [hreg v]; exact hd
  obtain ⟨u, hu⟩ := (G.degree_pos_iff_exists_adj v).mp this
  exact Fintype.one_lt_card_iff.mpr ⟨v, u, G.ne_of_adj hu⟩

/-- Phase I is short: if `1/n ≤ ν`, then `phaseIRounds ν (1/20) ≤ 5 log n + 7`. -/
theorem phaseIRounds_le {ν n : ℝ} (hν : 0 < ν) (hn : 1 ≤ n) (hνn : 1 / n ≤ ν) :
    (phaseIRounds ν (1 / 20) : ℝ) ≤ 5 * log n + 7 := by
  have hlog0 : 0 ≤ log n := Real.log_nonneg hn
  have hL : 1 / 5 ≤ log (5 / 4 : ℝ) := by
    have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 5 / 4 by norm_num)
    norm_num at this ⊢
    linarith
  have h1 : (⌈log (1 / (2 * ν)) / log (5 / 4)⌉₊ : ℝ) ≤ 5 * log n + 1 := by
    have hνn' : 1 ≤ ν * n := by rwa [div_le_iff₀ (by linarith)] at hνn
    have hy : log (1 / (2 * ν)) ≤ log n := by
      refine Real.log_le_log (by positivity) ?_
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have hle : log (1 / (2 * ν)) / log (5 / 4) ≤ 5 * log n := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have hc := Nat.ceil_lt_add_one (show 0 ≤ 5 * log n by positivity)
    have hm : (⌈log (1 / (2 * ν)) / log (5 / 4)⌉₊ : ℝ) ≤ ⌈5 * log n⌉₊ := by
      exact_mod_cast Nat.ceil_mono hle
    linarith
  have h2 : ⌈log (1 / (4 * (1 / 20 : ℝ))) / log (4 / 3)⌉₊ ≤ 6 := by
    rw [Nat.ceil_le, div_le_iff₀ (Real.log_pos (by norm_num))]
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 5) (show (5 : ℝ) ≤ (4 / 3) ^ 6 by norm_num)
    rw [Real.log_pow] at this
    norm_num at this ⊢
    linarith
  have h2' : (⌈log (1 / (4 * (1 / 20 : ℝ))) / log (4 / 3)⌉₊ : ℝ) ≤ 6 := by exact_mod_cast h2
  unfold phaseIRounds
  push_cast
  linarith

/-- The arithmetic of Theorem 2, with `C = 2 · 10¹⁰` and `P T` standing for the success
probability after `T` rounds. -/
theorem general_arith {n ν : ℝ} {T₁ : ℕ} (P : ℕ → ℝ) (hn : 2 ≤ n) (hν0 : 0 < ν) (hν1 : ν ≤ 1)
    (hT₁ : (T₁ : ℝ) ≤ 5 * log n + 7)
    (h : ∀ T₂ : ℕ,
      1 - ((T₁ : ℝ) * (exp (-((ν / 4000) ^ 2 * (1 / 20) * n / 6))
              + exp (-((ν / 4000) ^ 2 * (1 / 20) ^ 2 * n / 2)))
          + (24 / 25 : ℝ) ^ T₂ * n + ((T₁ : ℝ) + T₂) * exp (-(n / 97000)))
        ≤ P (T₁ + T₂)) :
    1 - (1 / n + (2 * (2 * 10 ^ 10) * log n + 2 * 10 ^ 10)
          * exp (-(ν ^ 2 * n / (2 * 10 ^ 10))))
      ≤ P ⌈(2 * 10 ^ 10) * log n⌉₊ := by
  have hn0 : 0 < n := by linarith
  have hl : 1 / 2 < log n := by
    have h1 := Real.log_two_gt_d9
    have h2 := Real.log_le_log (by norm_num) hn
    norm_num at h1
    linarith
  set T := ⌈(2 * 10 ^ 10) * log n⌉₊
  have hTlo : (2 * 10 ^ 10) * log n ≤ T := Nat.le_ceil _
  have hThi : (T : ℝ) < (2 * 10 ^ 10) * log n + 1 := Nat.ceil_lt_add_one (by positivity)
  have hT₁T : T₁ ≤ T := by exact_mod_cast (show (T₁ : ℝ) ≤ T by linarith)
  have h2 := h (T - T₁)
  rw [Nat.add_sub_cancel' hT₁T, Nat.cast_sub hT₁T] at h2
  -- the contraction term
  have hq : (24 / 25 : ℝ) ^ (T - T₁) * n ≤ 1 / n := by
    have hT₂ : 50 * log n ≤ ((T - T₁ : ℕ) : ℝ) := by
      rw [Nat.cast_sub hT₁T]
      linarith
    have h1 : (24 / 25 : ℝ) ^ (T - T₁) ≤ exp (-((T - T₁ : ℕ) / 25)) := by
      have : (24 / 25 : ℝ) ≤ exp (-(1 / 25)) := by
        have := add_one_le_exp (-(1 / 25 : ℝ))
        linarith
      calc (24 / 25 : ℝ) ^ (T - T₁) ≤ exp (-(1 / 25)) ^ (T - T₁) :=
            pow_le_pow_left₀ (by norm_num) this _
        _ = exp (-((T - T₁ : ℕ) / 25)) := by rw [← Real.exp_nat_mul]; ring_nf
    have h3 : exp (-((T - T₁ : ℕ) / 25)) ≤ exp (-(2 * log n)) := by
      rw [exp_le_exp]
      linarith
    have h4 : exp (-(2 * log n)) = 1 / (n * n) := by
      rw [exp_neg, two_mul, exp_add, exp_log hn0, one_div]
    calc (24 / 25 : ℝ) ^ (T - T₁) * n ≤ 1 / (n * n) * n :=
          mul_le_mul_of_nonneg_right (h1.trans (h3.trans h4.le)) hn0.le
      _ = 1 / n := by field_simp
  -- every exponential is at most `E`
  set E := exp (-(ν ^ 2 * n / (2 * 10 ^ 10))) with hE
  have hνn : 0 ≤ ν ^ 2 * n := by positivity
  have hν2 : ν ^ 2 * n ≤ n := by
    have : ν ^ 2 ≤ 1 := pow_le_one₀ hν0.le hν1
    nlinarith
  have he1 : exp (-((ν / 4000) ^ 2 * (1 / 20) * n / 6)) ≤ E := by
    rw [hE, exp_le_exp]
    linarith
  have he2 : exp (-((ν / 4000) ^ 2 * (1 / 20) ^ 2 * n / 2)) ≤ E := by
    rw [hE, exp_le_exp]
    linarith
  have he3 : exp (-(n / 97000)) ≤ E := by
    rw [hE, exp_le_exp]
    linarith
  have hE0 : 0 < E := exp_pos _
  have hA : (T₁ : ℝ) * (exp (-((ν / 4000) ^ 2 * (1 / 20) * n / 6))
      + exp (-((ν / 4000) ^ 2 * (1 / 20) ^ 2 * n / 2))) ≤ T₁ * (2 * E) :=
    mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
  have hB : ((T₁ : ℝ) + (T - T₁)) * exp (-(n / 97000)) ≤ T * E := by
    rw [add_sub_cancel]
    exact mul_le_mul_of_nonneg_left he3 (Nat.cast_nonneg _)
  have hC : (2 * T₁ + T : ℝ) * E ≤ (2 * (2 * 10 ^ 10) * log n + 2 * 10 ^ 10) * E :=
    mul_le_mul_of_nonneg_right (by linarith) hE0.le
  linarith

/-- **Theorem 2 from its explicit form**, for one graph and one configuration. -/
theorem general_of_explicit {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {d : ℕ} (hd : 0 < d) (hreg : G.IsRegularOfDegree d) (a : Bool)
    (x : V → Bool) (hlam : 4000 * lambdaG G d ≤ imbalance a x)
    (hexp : 0 < imbalance a x → ∀ T₂ : ℕ,
      1 - ((phaseIRounds (imbalance a x) (1 / 20) : ℝ)
            * (exp (-((imbalance a x / 4000) ^ 2 * (1 / 20) * Fintype.card V / 6))
              + exp (-((imbalance a x / 4000) ^ 2 * (1 / 20) ^ 2 * Fintype.card V / 2)))
          + (24 / 25 : ℝ) ^ T₂ * Fintype.card V
          + ((phaseIRounds (imbalance a x) (1 / 20) : ℝ) + T₂)
            * exp (-((Fintype.card V : ℝ) / 97000)))
        ≤ expList (GraphRound G) (phaseIRounds (imbalance a x) (1 / 20) + T₂)
            (fun l => if graphRun G x l = fun _ => a then (1 : ℝ) else 0)) :
    1 - (1 / (Fintype.card V : ℝ) + (2 * (2 * 10 ^ 10) * log (Fintype.card V) + 2 * 10 ^ 10)
          * exp (-(imbalance a x ^ 2 * Fintype.card V / (2 * 10 ^ 10))))
      ≤ expList (GraphRound G) ⌈(2 * 10 ^ 10) * log (Fintype.card V)⌉₊
          (fun l => if graphRun G x l = fun _ => a then (1 : ℝ) else 0) := by
  have hL := lambdaG_nonneg G d
  rcases (show 0 ≤ imbalance a x by linarith).eq_or_lt with h0 | hpos
  · -- `ν₀ = 0`: the bound is negative
    rw [← h0]
    refine le_trans ?_ (expList_nonneg fun l => by split_ifs <;> norm_num)
    have h1 : exp (-((0 : ℝ) ^ 2 * Fintype.card V / (2 * 10 ^ 10))) = 1 := by simp
    have h2 : 0 ≤ log (Fintype.card V : ℝ) := Real.log_natCast_nonneg _
    have h3 : 0 ≤ 1 / (Fintype.card V : ℝ) := by positivity
    rw [h1]
    linarith
  · obtain ⟨hn, hνn⟩ := one_div_card_le_imbalance hpos
    obtain ⟨v⟩ := Fintype.card_pos_iff.mp (by exact_mod_cast hn)
    have h2 : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast two_le_card G hd hreg v
    exact general_arith (fun T => expList (GraphRound G) T
        fun l => if graphRun G x l = fun _ => a then (1 : ℝ) else 0) h2 hpos
      (imbalance_le_one a x) (phaseIRounds_le hpos (by linarith) hνn) (hexp hpos)

end Median.ExpanderGeneral
