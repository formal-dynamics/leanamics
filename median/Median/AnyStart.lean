import Median.Basic
import Median.Binary
import Median.AnyStartAux

/-! # Consensus from any configuration (median dynamics)

The main theorem of Doerr, Goldberg, Minder, Sauerwald and Scheideler (SPAA 2011, Theorem 1 of the
full version): without an adversary, from **any** configuration, with any number of distinct
values, the median dynamics reaches consensus within `O(log n)` rounds with high probability.

The proof here goes through two values. The threshold reduction (the paper's Lemma 17, our
`threshold_run`) and a union bound over the at most `n - 1` thresholds (`consensus_of_binary`)
turn a failure bound for every binary configuration into one for every configuration; amplifying
a `C/n` failure bound to `≤ (C/n)³` by running three blocks (consensus absorbs) makes the union
bound affordable. What remains is the binary dynamics (2-Choices) from an arbitrary, possibly
perfectly balanced, start (`binary_any_start`, the paper's Lemmas 13-16 followed by
`consensus_whp`): symmetry breaking until the gap reaches order `√(n log n)`.
-/

namespace Median
open Finset Dynamics

/-- **2-Choices from any start.** From any binary configuration, all nodes agree after
`⌈C log n⌉` rounds except with probability at most `C/n`. -/
theorem binary_any_start : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) [NeZero n], C ≤ Real.log n →
    ∀ x : Config n Bool,
      expList (Round n) ⌈C * Real.log n⌉₊ (fun l => notConsensus (run x l)) ≤ C / n := by
  /- The proof follows a fixed-time drift argument. The potential
  `pot y = exp (-|gap y| / (256 √n))` contracts in expectation by `exp (-1/65536)` per round
  (up to a tiny additive error), by Hoeffding's lemma away from balance and by a two-sided
  Paley-Zygmund bound near balance. After `⌈2¹⁷ log n⌉` rounds, Markov's inequality puts the
  gap above `128 √(n log n)` in absolute value except with probability `2/n`; then
  `binary_consensus` (on the configuration or its flip) finishes within `⌈128 log n⌉` rounds
  except with probability `128/n`. -/
  refine ⟨262144, by norm_num, fun n _ => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  /- ### Moments of sums of independent coordinates -/
  -- Paley-Zygmund for a sum of independent centered coordinates bounded by `1`
  have pz_sum : ∀ f : Fin n → Fin n × Fin n → ℝ, (∀ v, avg (f v) = 0) → (∀ v q, |f v q| ≤ 1) →
      1 ≤ ∑ v, avg (fun q => f v q ^ 2) →
      9 / 64 ≤ avg (fun r : Round n =>
        if ∑ v, avg (fun q => f v q ^ 2) ≤ 4 * (∑ v, f v (r v)) ^ 2 then (1 : ℝ) else 0) := by
    -- Cauchy-Schwarz for averages over rounds
    have avg_cauchy : ∀ Z W : Round n → ℝ,
        avg (fun r => Z r * W r) ^ 2 ≤ avg (fun r => Z r ^ 2) * avg (fun r => W r ^ 2) := by
      intro Z W
      unfold avg
      have h := Finset.sum_mul_sq_le_sq_mul_sq univ Z W
      calc ((∑ r, Z r * W r) / (Fintype.card (Round n) : ℝ)) ^ 2
          = (∑ r, Z r * W r) ^ 2 / (Fintype.card (Round n) : ℝ) ^ 2 := by rw [div_pow]
        _ ≤ ((∑ r, Z r ^ 2) * ∑ r, W r ^ 2) / (Fintype.card (Round n) : ℝ) ^ 2 := by gcongr
        _ = (∑ r, Z r ^ 2) / (Fintype.card (Round n) : ℝ)
              * ((∑ r, W r ^ 2) / (Fintype.card (Round n) : ℝ)) := by
            rw [div_mul_div_comm, sq]
    -- independence of the head and the tail of a product of coordinates
    have avg_head_tail : ∀ {k : ℕ} (F : Fin n × Fin n → ℝ) (G : (Fin k → Fin n × Fin n) → ℝ),
        avg (fun ω : Fin (k + 1) → Fin n × Fin n => F (ω 0) * G (Fin.tail ω))
          = avg F * avg G := by
      intro k F G
      have h := avg_equiv (Fin.consEquiv (fun _ : Fin (k + 1) => Fin n × Fin n)).symm
        (fun p : (Fin n × Fin n) × (Fin k → Fin n × Fin n) => F p.1 * G p.2)
      rw [← avg_mul_prod, ← h]
      rfl
    have avg_tail : ∀ {k : ℕ} (G : (Fin k → Fin n × Fin n) → ℝ),
        avg (fun ω : Fin (k + 1) → Fin n × Fin n => G (Fin.tail ω)) = avg G := by
      intro k G
      have h := avg_head_tail (k := k) (fun _ => (1 : ℝ)) G
      rw [avg_const, one_mul] at h
      rw [← h]
      simp
    have sum_head_tail : ∀ {k : ℕ} (f : Fin (k + 1) → Fin n × Fin n → ℝ)
        (ω : Fin (k + 1) → Fin n × Fin n),
        ∑ i, f i (ω i) = f 0 (ω 0) + ∑ i : Fin k, f i.succ (Fin.tail ω i) :=
      fun f ω => Fin.sum_univ_succ _
    have avg_sum_coords : ∀ {k : ℕ} (f : Fin k → Fin n × Fin n → ℝ),
        avg (fun ω : Fin k → Fin n × Fin n => ∑ i, f i (ω i)) = ∑ i, avg (f i) := by
      intro k f
      rw [avg_sum]
      exact Finset.sum_congr rfl fun i _ => avg_eval k i (f i)
    -- second moment of a sum of independent centered coordinates
    have avg_sum_sq : ∀ (k : ℕ) (f : Fin k → Fin n × Fin n → ℝ), (∀ i, avg (f i) = 0) →
        avg (fun ω : Fin k → Fin n × Fin n => (∑ i, f i (ω i)) ^ 2)
          = ∑ i, avg (fun y => f i y ^ 2) := by
      intro k
      induction k with
      | zero => intro f _; simp [avg]
      | succ k ih =>
        intro f hf0
        obtain ⟨Tl, hTl⟩ : ∃ Tl : (Fin k → Fin n × Fin n) → ℝ,
            Tl = fun t => ∑ i : Fin k, f i.succ (t i) := ⟨_, rfl⟩
        have hT0 : avg Tl = 0 := by
          rw [hTl, avg_sum_coords]
          simp [hf0]
        have hT2 : avg (fun t => Tl t ^ 2) = ∑ i : Fin k, avg (fun y => f i.succ y ^ 2) := by
          rw [hTl]
          exact ih (fun i => f i.succ) (fun i => hf0 i.succ)
        have hpt : ∀ ω : Fin (k + 1) → Fin n × Fin n, (∑ i, f i (ω i)) ^ 2
            = (f 0 (ω 0) ^ 2 + 2 * f 0 (ω 0) * Tl (Fin.tail ω)) + Tl (Fin.tail ω) ^ 2 := by
          intro ω
          rw [sum_head_tail, hTl]
          ring
        have hA : avg (fun ω : Fin (k + 1) → Fin n × Fin n => f 0 (ω 0) ^ 2)
            = avg (fun y => f 0 y ^ 2) := avg_eval (k + 1) 0 (fun y => f 0 y ^ 2)
        have hB : avg (fun ω : Fin (k + 1) → Fin n × Fin n => 2 * f 0 (ω 0) * Tl (Fin.tail ω))
            = 0 := by
          rw [avg_head_tail (fun y => 2 * f 0 y) Tl, hT0, mul_zero]
        have hC : avg (fun ω : Fin (k + 1) → Fin n × Fin n => Tl (Fin.tail ω) ^ 2)
            = ∑ i : Fin k, avg (fun y => f i.succ y ^ 2) := by
          rw [avg_tail (fun t => Tl t ^ 2), hT2]
        rw [show (fun ω : Fin (k + 1) → Fin n × Fin n => (∑ i, f i (ω i)) ^ 2)
            = fun ω => (f 0 (ω 0) ^ 2 + 2 * f 0 (ω 0) * Tl (Fin.tail ω)) + Tl (Fin.tail ω) ^ 2
            from funext hpt]
        rw [avg_add, avg_add, hA, hB, hC, Fin.sum_univ_succ]
        ring
    -- fourth moment: `𝔼S⁴ ≤ σ² + 3σ⁴` for summands bounded by `1`
    have avg_sum_fourth_le : ∀ (k : ℕ) (f : Fin k → Fin n × Fin n → ℝ), (∀ i, avg (f i) = 0) →
        (∀ i y, |f i y| ≤ 1) →
        avg (fun ω : Fin k → Fin n × Fin n => (∑ i, f i (ω i)) ^ 4)
          ≤ (∑ i, avg (fun y => f i y ^ 2)) + 3 * (∑ i, avg (fun y => f i y ^ 2)) ^ 2 := by
      intro k
      induction k with
      | zero => intro f _ _; simp [avg]
      | succ k ih =>
        intro f hf0 hfb
        obtain ⟨Tl, hTl⟩ : ∃ Tl : (Fin k → Fin n × Fin n) → ℝ,
            Tl = fun t => ∑ i : Fin k, f i.succ (t i) := ⟨_, rfl⟩
        obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = ∑ i : Fin k, avg (fun y => f i.succ y ^ 2) := ⟨_, rfl⟩
        obtain ⟨a, ha⟩ : ∃ a : ℝ, a = avg (fun y => f 0 y ^ 2) := ⟨_, rfl⟩
        have hT0 : avg Tl = 0 := by
          rw [hTl, avg_sum_coords]
          simp [hf0]
        have hT2 : avg (fun t => Tl t ^ 2) = σ := by
          rw [hTl, hσ]
          exact avg_sum_sq k (fun i => f i.succ) (fun i => hf0 i.succ)
        have hT4 : avg (fun t => Tl t ^ 4) ≤ σ + 3 * σ ^ 2 := by
          rw [hTl, hσ]
          exact ih (fun i => f i.succ) (fun i => hf0 i.succ) (fun i y => hfb i.succ y)
        have hpt : ∀ ω : Fin (k + 1) → Fin n × Fin n, (∑ i, f i (ω i)) ^ 4
            = f 0 (ω 0) ^ 4 + 4 * f 0 (ω 0) ^ 3 * Tl (Fin.tail ω)
              + 6 * f 0 (ω 0) ^ 2 * Tl (Fin.tail ω) ^ 2
              + 4 * f 0 (ω 0) * Tl (Fin.tail ω) ^ 3 + Tl (Fin.tail ω) ^ 4 := by
          intro ω
          rw [sum_head_tail, hTl]
          ring
        have hA : avg (fun ω : Fin (k + 1) → Fin n × Fin n => f 0 (ω 0) ^ 4)
            = avg (fun y => f 0 y ^ 4) := avg_eval (k + 1) 0 (fun y => f 0 y ^ 4)
        have hB : avg (fun ω : Fin (k + 1) → Fin n × Fin n =>
            4 * f 0 (ω 0) ^ 3 * Tl (Fin.tail ω)) = 0 := by
          rw [avg_head_tail (fun y => 4 * f 0 y ^ 3) Tl, hT0, mul_zero]
        have hC : avg (fun ω : Fin (k + 1) → Fin n × Fin n =>
            6 * f 0 (ω 0) ^ 2 * Tl (Fin.tail ω) ^ 2) = 6 * a * σ := by
          rw [avg_head_tail (fun y => 6 * f 0 y ^ 2) (fun t => Tl t ^ 2), hT2, avg_const_mul, ha]
        have hD : avg (fun ω : Fin (k + 1) → Fin n × Fin n =>
            4 * f 0 (ω 0) * Tl (Fin.tail ω) ^ 3) = 0 := by
          rw [avg_head_tail (fun y => 4 * f 0 y) (fun t => Tl t ^ 3), avg_const_mul, hf0 0]
          ring
        have hE : avg (fun ω : Fin (k + 1) → Fin n × Fin n => Tl (Fin.tail ω) ^ 4)
            = avg (fun t => Tl t ^ 4) := avg_tail (fun t => Tl t ^ 4)
        rw [show (fun ω : Fin (k + 1) → Fin n × Fin n => (∑ i, f i (ω i)) ^ 4)
            = fun ω => f 0 (ω 0) ^ 4 + 4 * f 0 (ω 0) ^ 3 * Tl (Fin.tail ω)
              + 6 * f 0 (ω 0) ^ 2 * Tl (Fin.tail ω) ^ 2
              + 4 * f 0 (ω 0) * Tl (Fin.tail ω) ^ 3 + Tl (Fin.tail ω) ^ 4
            from funext hpt]
        rw [avg_add, avg_add, avg_add, avg_add, hA, hB, hC, hD, hE, Fin.sum_univ_succ, ← ha, ← hσ]
        have h4 : avg (fun y => f 0 y ^ 4) ≤ a := by
          rw [ha]
          refine avg_le_avg fun y => ?_
          have h1 : f 0 y ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).mpr (hfb 0 y)
          have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg (f 0 y))
          linarith
        linarith [sq_nonneg a]
    -- two-sided Paley-Zygmund: `𝔼Z² = s > 0`, `𝔼Z⁴ ≤ 4s²` give `P(s ≤ 4Z²) ≥ 9/64`
    have avg_pz : ∀ (Z : Round n → ℝ) (s : ℝ), 0 < s → avg (fun r => Z r ^ 2) = s →
        avg (fun r => Z r ^ 4) ≤ 4 * s ^ 2 →
        9 / 64 ≤ avg (fun r => if s ≤ 4 * Z r ^ 2 then (1 : ℝ) else 0) := by
      intro Z s hs h2 h4
      have hpt : ∀ r, Z r ^ 2
          ≤ s / 4 + Z r ^ 2 * (if s ≤ 4 * Z r ^ 2 then (1 : ℝ) else 0) := by
        intro r
        split_ifs with h
        · linarith
        · push Not at h
          linarith
      have h1 : s ≤ s / 4
          + avg (fun r => Z r ^ 2 * (if s ≤ 4 * Z r ^ 2 then (1 : ℝ) else 0)) := by
        have := avg_le_avg hpt
        rw [avg_add, avg_const, h2] at this
        exact this
      have hcs := avg_cauchy (fun r => Z r ^ 2) (fun r => if s ≤ 4 * Z r ^ 2 then (1 : ℝ) else 0)
      have hind : (fun r => (if s ≤ 4 * Z r ^ 2 then (1 : ℝ) else 0) ^ 2)
          = fun r => if s ≤ 4 * Z r ^ 2 then (1 : ℝ) else 0 := by
        funext r
        split_ifs <;> norm_num
      have hz4 : (fun r => (Z r ^ 2) ^ 2) = fun r => Z r ^ 4 := by
        funext r
        ring
      rw [hind, hz4] at hcs
      obtain ⟨B, hB⟩ : ∃ B, B = avg (fun r => Z r ^ 2 * (if s ≤ 4 * Z r ^ 2 then (1 : ℝ) else 0)) :=
        ⟨_, rfl⟩
      obtain ⟨P, hP⟩ : ∃ P, P = avg (fun r => if s ≤ 4 * Z r ^ 2 then (1 : ℝ) else 0) := ⟨_, rfl⟩
      rw [← hB, ← hP] at hcs
      rw [← hB] at h1
      rw [← hP]
      have hP0 : 0 ≤ P := by
        rw [hP]
        exact avg_nonneg fun r => by split_ifs <;> norm_num
      have hB34 : 3 / 4 * s ≤ B := by linarith
      have hsq : (3 / 4 * s) ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (by positivity) hB34 2
      have h4P : avg (fun r => Z r ^ 4) * P ≤ 4 * s ^ 2 * P := mul_le_mul_of_nonneg_right h4 hP0
      have hs2 : 0 < 4 * s ^ 2 := by positivity
      by_contra hlt
      push Not at hlt
      have := mul_lt_mul_of_pos_left hlt hs2
      linarith
    intro f hf0 hfb hσ1
    have hS4 : avg (fun r : Round n => (∑ v, f v (r v)) ^ 4)
        ≤ 4 * (∑ v, avg (fun q => f v q ^ 2)) ^ 2 := by
      have := avg_sum_fourth_le n f hf0 hfb
      have h1 := mul_le_mul_of_nonneg_left hσ1 (le_trans zero_le_one hσ1)
      linarith
    exact avg_pz (fun r : Round n => ∑ v, f v (r v)) _ (by linarith) (avg_sum_sq n f hf0) hS4
  /- ### Flipping every opinion -/
  have step_neg : ∀ (y : Config n Bool) (r : Round n),
      step (fun v => !y v) r = fun v => !step y r v := by
    intro y r
    funext v
    show med3 (!y v) (!y (r v).1) (!y (r v).2) = !med3 (y v) (y (r v).1) (y (r v).2)
    cases y v <;> cases y (r v).1 <;> cases y (r v).2 <;> rfl
  have run_neg : ∀ (l : List (Round n)) (y : Config n Bool),
      run (fun v => !y v) l = fun v => !run y l v := by
    intro l
    induction l with
    | nil => intro y; rfl
    | cons r l ih =>
      intro y
      show run (step (fun v => !y v) r) l = fun v => !run (step y r) l v
      rw [step_neg, ih]
  have gap_neg : ∀ y : Config n Bool, gapR (fun v => !y v) = -gapR y := by
    intro y
    have h : (ones (fun v => !y v) : ℝ) = falsesR y := by
      rw [ones_eq_sum, falsesR_eq_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      cases y v <;> simp
    simp only [gapR, falsesR] at h ⊢
    rw [h]
    ring
  /- ### The potential and the gap after one round -/
  obtain ⟨pot, hpot⟩ : ∃ pot : Config n Bool → ℝ,
      ∀ y, pot y = Real.exp (-(|gapR y| / (256 * √(n : ℝ)))) := ⟨_, fun y => rfl⟩
  have pot_pos : ∀ y, 0 < pot y := fun y => by rw [hpot]; exact Real.exp_pos _
  have pot_le_one : ∀ y, pot y ≤ 1 := by
    intro y
    rw [hpot, Real.exp_le_one_iff, neg_nonpos]
    positivity
  /- ### One round of the potential -/
  have pot_step : (10 : ℝ) ≤ n → ∀ y : Config n Bool,
      avg (fun r : Round n => pot (step y r))
        ≤ Real.exp (-(1 / 65536)) * pot y + Real.exp (1 / 131072 - √(n : ℝ) / 512) := by
    have pot_neg : ∀ y, pot (fun v => !y v) = pot y := by
      intro y
      rw [hpot, hpot, gap_neg, abs_neg]
    have gapR_eq_two : ∀ y : Config n Bool, gapR y = 2 * (ones y : ℝ) - n := by
      intro y
      simp only [gapR, falsesR]
      ring
    have gapR_step : ∀ (y : Config n Bool) (r : Round n),
        gapR (step y r) = 2 * ∑ v, coord y v (r v) - n := by
      intro y r
      rw [gapR_eq_two, ones_step_sum]
    have two_sum_avg_coord : ∀ y : Config n Bool,
        2 * ∑ v, avg (coord y v) - n
          = gapR y + 2 * ((ones y : ℝ) * falsesR y) * gapR y / n ^ 2 := by
      intro y
      rw [sum_avg_coord, gapR_eq_two]
      ring
    have le_two_sum_avg_coord : ∀ y : Config n Bool, 0 ≤ gapR y →
        gapR y ≤ 2 * ∑ v, avg (coord y v) - n := by
      intro y hg
      rw [two_sum_avg_coord]
      have h1 : 0 ≤ (ones y : ℝ) * falsesR y := mul_nonneg (Nat.cast_nonneg _) (falsesR_nonneg y)
      have h2 : 0 ≤ 2 * ((ones y : ℝ) * falsesR y) * gapR y / n ^ 2 := by positivity
      linarith
    have abs_two_sum_avg_coord_le : ∀ y : Config n Bool,
        |2 * ∑ v, avg (coord y v) - n| ≤ 3 / 2 * |gapR y| := by
      intro y
      rw [two_sum_avg_coord]
      have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
      have h1 : 0 ≤ (ones y : ℝ) * falsesR y := mul_nonneg (Nat.cast_nonneg _) (falsesR_nonneg y)
      have h2 : (ones y : ℝ) * falsesR y ≤ (n : ℝ) ^ 2 / 4 := by
        rw [ones_mul_falses]
        linarith [sq_nonneg (gapR y)]
      have hc : 2 * ((ones y : ℝ) * falsesR y) / n ^ 2 ≤ 1 / 2 := by
        rw [div_le_iff₀ hn2]
        linarith
      have hc0 : 0 ≤ 2 * ((ones y : ℝ) * falsesR y) / n ^ 2 := by positivity
      have heq : gapR y + 2 * ((ones y : ℝ) * falsesR y) * gapR y / n ^ 2
          = gapR y * (1 + 2 * ((ones y : ℝ) * falsesR y) / n ^ 2) := by
        ring
      rw [heq, abs_mul,
        abs_of_pos (by linarith : (0 : ℝ) < 1 + 2 * ((ones y : ℝ) * falsesR y) / n ^ 2)]
      have := mul_le_mul_of_nonneg_left
        (by linarith : 1 + 2 * ((ones y : ℝ) * falsesR y) / n ^ 2 ≤ 3 / 2) (abs_nonneg (gapR y))
      linarith
    -- the expected potential through the exponential moment of the gap
    have avg_pot_le_mgf : ∀ y : Config n Bool,
        avg (fun r : Round n => pot (step y r))
          ≤ Real.exp (-((2 * ∑ v, avg (coord y v) - n) / (256 * √(n : ℝ))) + 1 / 131072) := by
      -- Hoeffding's lemma for every node, any real `t`
      have avg_exp_le : ∀ (y : Config n Bool) (t : ℝ),
          avg (fun r : Round n => Real.exp (t * ∑ v, coord y v (r v)))
            ≤ Real.exp (t * ∑ v, avg (coord y v) + n * (t ^ 2 / 8)) := by
        intro y t
        rw [avg_exp_sum (coord y) t]
        have hone (i : Fin n) : avg (fun q => Real.exp (t * coord y i q))
            ≤ Real.exp (t * avg (coord y i) + t ^ 2 / 8) := by
          have hpt (q : Fin n × Fin n) :
              Real.exp (t * coord y i q) = 1 + (Real.exp t - 1) * coord y i q := by
            rcases coord_zero_one y i q with h | h <;> simp [h]
          simp_rw [hpt]
          have hsplit : avg (fun q => 1 + (Real.exp t - 1) * coord y i q)
              = 1 + (Real.exp t - 1) * avg (coord y i) := by
            rw [avg_add, avg_const, avg_const_mul]
          rw [hsplit]
          have hp0 : 0 ≤ avg (coord y i) := avg_nonneg fun q => coord_nonneg y i q
          have hp1 : avg (coord y i) ≤ 1 := by
            calc avg (coord y i) ≤ avg (fun _ : Fin n × Fin n => (1 : ℝ)) :=
                  avg_le_avg fun q => by rcases coord_zero_one y i q with h | h <;> simp [h]
              _ = 1 := avg_const 1
          have := one_sub_add_mul_exp_le hp0 hp1 t
          rw [mul_comm t (avg (coord y i))]
          linarith
        calc ∏ i, avg (fun q => Real.exp (t * coord y i q))
            ≤ ∏ i : Fin n, Real.exp (t * avg (coord y i) + t ^ 2 / 8) :=
              prod_le_prod (fun i _ => avg_nonneg fun q => (Real.exp_pos _).le) (fun i _ => hone i)
          _ = Real.exp (t * ∑ v, avg (coord y v) + n * (t ^ 2 / 8)) := by
              rw [← Real.exp_sum, sum_add_distrib, ← mul_sum, sum_const, card_univ,
                Fintype.card_fin, nsmul_eq_mul]
      intro y
      have hs : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hn0
      have hss : √(n : ℝ) ^ 2 = n := Real.sq_sqrt hn0.le
      obtain ⟨s, hsdef⟩ : ∃ s, s = √(n : ℝ) := ⟨_, rfl⟩
      rw [← hsdef] at hs hss ⊢
      obtain ⟨μ, hμ⟩ : ∃ μ, μ = ∑ v, avg (coord y v) := ⟨_, rfl⟩
      rw [← hμ]
      have hpt : ∀ r : Round n, pot (step y r)
          ≤ Real.exp (n / (256 * s)) * Real.exp (-(1 / (128 * s)) * ∑ v, coord y v (r v)) := by
        intro r
        rw [hpot, ← hsdef, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have h1 : gapR (step y r) / (256 * s) ≤ |gapR (step y r)| / (256 * s) :=
          div_le_div_of_nonneg_right (le_abs_self _) (by positivity)
        have h2 : n / (256 * s) + -(1 / (128 * s)) * ∑ v, coord y v (r v)
            = -(gapR (step y r) / (256 * s)) := by
          rw [gapR_step]
          field_simp
          ring
        linarith
      have hmgf := avg_exp_le y (-(1 / (128 * s)))
      calc avg (fun r : Round n => pot (step y r))
          ≤ avg (fun r : Round n => Real.exp (n / (256 * s))
              * Real.exp (-(1 / (128 * s)) * ∑ v, coord y v (r v))) := avg_le_avg hpt
        _ = Real.exp (n / (256 * s))
              * avg (fun r : Round n => Real.exp (-(1 / (128 * s)) * ∑ v, coord y v (r v))) :=
            avg_const_mul _ _
        _ ≤ Real.exp (n / (256 * s))
              * Real.exp (-(1 / (128 * s)) * μ + n * ((-(1 / (128 * s))) ^ 2 / 8)) := by
            rw [hμ]
            exact mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
        _ = Real.exp (-((2 * μ - n) / (256 * s)) + 1 / 131072) := by
            rw [← Real.exp_add]
            congr 1
            have hn' : (n : ℝ) = s ^ 2 := hss.symm
            rw [hn']
            field_simp
            ring
    -- contraction for `√n/64 ≤ g ≤ n/2`
    have avg_pot_far : ∀ y : Config n Bool, √(n : ℝ) / 64 ≤ gapR y → gapR y ≤ n / 2 →
        avg (fun r : Round n => pot (step y r)) ≤ Real.exp (-(1 / 65536)) * pot y := by
      intro y hg1 hg2
      have hs : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hn0
      have hg0 : 0 ≤ gapR y := le_trans (by positivity) hg1
      have hE := expones_ge y hg0 hg2
      refine (avg_pot_le_mgf y).trans ?_
      rw [hpot, ← Real.exp_add, abs_of_nonneg hg0]
      apply Real.exp_le_exp.mpr
      have hd : 0 < 256 * √(n : ℝ) := by positivity
      have h1 : 11 / 8 * (gapR y / (256 * √(n : ℝ)))
          ≤ (2 * ∑ v, avg (coord y v) - n) / (256 * √(n : ℝ)) := by
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right (by linarith) hd.le
      have h2 : 1 / 16384 ≤ gapR y / (256 * √(n : ℝ)) := by
        rw [le_div_iff₀ hd]
        linarith
      linarith
    -- the additive error for `g > n/2`
    have avg_pot_huge : ∀ y : Config n Bool, (n : ℝ) / 2 < gapR y →
        avg (fun r : Round n => pot (step y r)) ≤ Real.exp (1 / 131072 - √(n : ℝ) / 512) := by
      intro y hg
      have hs : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hn0
      have hss : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hn0.le
      have hg0 : 0 ≤ gapR y := le_trans (by positivity) hg.le
      have hE := le_two_sum_avg_coord y hg0
      refine (avg_pot_le_mgf y).trans ?_
      apply Real.exp_le_exp.mpr
      have hd : 0 < 256 * √(n : ℝ) := by positivity
      have h1 : √(n : ℝ) / 512 ≤ (2 * ∑ v, avg (coord y v) - n) / (256 * √(n : ℝ)) := by
        rw [le_div_iff₀ hd]
        linarith
      linarith
    -- symmetry breaking: from `|g| ≤ √n/64`, `|g'| ≥ √n/4` with probability `≥ 9/64`
    have avg_pot_near : (10 : ℝ) ≤ n → ∀ y : Config n Bool, |gapR y| ≤ √(n : ℝ) / 64 →
        avg (fun r : Round n => pot (step y r)) ≤ 1 - 9 / 64 * (1 - Real.exp (-(1 / 1024))) := by
      have sq_mul_one_sub_sq_ge : ∀ z : ℝ, 3 / 8 ≤ z → z ≤ 5 / 8 → 1 / 10 ≤ z ^ 2 * (1 - z ^ 2) := by
        intro z h1 h2
        have hw1 : 9 / 64 ≤ z ^ 2 := by
          have := mul_le_mul h1 h1 (by norm_num) (by linarith)
          linarith
        have hw2 : z ^ 2 ≤ 25 / 64 := by
          have := mul_le_mul h2 h2 (by linarith) (by norm_num)
          linarith
        linarith [mul_nonneg (sub_nonneg.mpr hw1) (sub_nonneg.mpr hw2)]
      have avg_coord_centered_sq : ∀ (y : Config n Bool) (v : Fin n),
          avg (fun q => (coord y v q - avg (coord y v)) ^ 2)
            = avg (coord y v) * (1 - avg (coord y v)) := by
        intro y v
        obtain ⟨p, hp⟩ : ∃ p, p = avg (coord y v) := ⟨_, rfl⟩
        rw [← hp]
        have hpt : ∀ q, (coord y v q - p) ^ 2 = (1 - 2 * p) * coord y v q + p ^ 2 := by
          intro q
          rcases coord_zero_one y v q with h | h <;> rw [h] <;> ring
        simp_rw [hpt]
        rw [avg_add, avg_const_mul, avg_const, ← hp]
        ring
      have var_coord_ge : ∀ y : Config n Bool, |gapR y| ≤ n / 4 → ∀ v : Fin n,
          1 / 10 ≤ avg (fun q => (coord y v q - avg (coord y v)) ^ 2) := by
        intro y hg v
        rw [avg_coord_centered_sq]
        have hsum := falses_plus_ones y
        have hgap := gapR_eq y
        have hab := abs_le.mp hg
        cases hv : y v with
        | true =>
          rw [avg_coord_of_true y hv]
          have h1 : 3 / 8 ≤ falsesR y / n := by
            rw [le_div_iff₀ hn0]
            linarith
          have h2 : falsesR y / n ≤ 5 / 8 := by
            rw [div_le_iff₀ hn0]
            linarith
          have := sq_mul_one_sub_sq_ge _ h1 h2
          linarith
        | false =>
          rw [avg_coord_of_false y hv]
          have h1 : 3 / 8 ≤ (ones y : ℝ) / n := by
            rw [le_div_iff₀ hn0]
            linarith
          have h2 : (ones y : ℝ) / n ≤ 5 / 8 := by
            rw [div_le_iff₀ hn0]
            linarith
          have := sq_mul_one_sub_sq_ge _ h1 h2
          linarith
      intro hn y hg
      have hs : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hn0
      have hss : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hn0.le
      have hsn : √(n : ℝ) ≤ n := by
        have h1 : 1 ≤ √(n : ℝ) := Real.one_le_sqrt.mpr (by linarith)
        have := mul_le_mul_of_nonneg_left h1 hs.le
        linarith
      obtain ⟨f, hf⟩ : ∃ f : Fin n → Fin n × Fin n → ℝ,
          f = fun v q => coord y v q - avg (coord y v) := ⟨_, rfl⟩
      have hf0 : ∀ v, avg (f v) = 0 := by
        intro v
        rw [hf]
        show avg (fun q => coord y v q - avg (coord y v)) = 0
        rw [avg_sub, avg_const, sub_self]
      have hfb : ∀ v q, |f v q| ≤ 1 := by
        intro v q
        rw [hf]
        have hp0 : 0 ≤ avg (coord y v) := avg_nonneg fun q => coord_nonneg y v q
        have hp1 : avg (coord y v) ≤ 1 := by
          calc avg (coord y v) ≤ avg (fun _ : Fin n × Fin n => (1 : ℝ)) :=
                avg_le_avg fun q => by rcases coord_zero_one y v q with h | h <;> simp [h]
            _ = 1 := avg_const 1
        rw [abs_le]
        rcases coord_zero_one y v q with h | h <;> simp only [h] <;> constructor <;> linarith
      obtain ⟨σ2, hσ2⟩ : ∃ σ2, σ2 = ∑ v, avg (fun q => f v q ^ 2) := ⟨_, rfl⟩
      have hσ : (n : ℝ) / 10 ≤ σ2 := by
        have hg4 : |gapR y| ≤ n / 4 := by linarith
        have h1 : ∑ _v : Fin n, (1 / 10 : ℝ) ≤ σ2 := by
          rw [hσ2, hf]
          exact Finset.sum_le_sum fun v _ => var_coord_ge y hg4 v
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
        linarith
      have hσ1 : 1 ≤ σ2 := by linarith
      have hpz : 9 / 64 ≤ avg (fun r : Round n =>
          if σ2 ≤ 4 * (∑ v, f v (r v)) ^ 2 then (1 : ℝ) else 0) := by
        rw [hσ2]
        exact pz_sum f hf0 hfb (by rw [← hσ2]; exact hσ1)
      have hgS : ∀ r : Round n,
          gapR (step y r) = 2 * ∑ v, f v (r v) + (2 * ∑ v, avg (coord y v) - n) := by
        intro r
        rw [gapR_step, hf]
        simp only [Finset.sum_sub_distrib]
        ring
      have hEg : |2 * ∑ v, avg (coord y v) - n| ≤ 3 / 2 * (√(n : ℝ) / 64) :=
        (abs_two_sum_avg_coord_le y).trans (by linarith)
      have hpt : ∀ r : Round n, pot (step y r)
          ≤ 1 - (1 - Real.exp (-(1 / 1024)))
              * (if σ2 ≤ 4 * (∑ v, f v (r v)) ^ 2 then (1 : ℝ) else 0) := by
        intro r
        split_ifs with hA
        · have hbig : √(n : ℝ) / 4 ≤ |gapR (step y r)| := by
            by_contra hlt
            push Not at hlt
            rw [hgS r] at hlt
            have h1 : |2 * ∑ v, f v (r v)| < 35 / 128 * √(n : ℝ) := by
              have := abs_sub_abs_le_abs_sub (2 * ∑ v, f v (r v))
                (-(2 * ∑ v, avg (coord y v) - n))
              rw [sub_neg_eq_add, abs_neg] at this
              linarith
            have h2 : (2 * ∑ v, f v (r v)) ^ 2 < (35 / 128 * √(n : ℝ)) ^ 2 := by
              rw [← sq_abs]
              exact pow_lt_pow_left₀ h1 (abs_nonneg _) (by norm_num)
            linarith
          rw [hpot, mul_one, sub_sub_cancel]
          apply Real.exp_le_exp.mpr
          rw [neg_le_neg_iff, le_div_iff₀ (by positivity)]
          linarith
        · rw [mul_zero, sub_zero]
          exact pot_le_one _
      calc avg (fun r : Round n => pot (step y r))
          ≤ avg (fun r : Round n => 1 - (1 - Real.exp (-(1 / 1024)))
              * (if σ2 ≤ 4 * (∑ v, f v (r v)) ^ 2 then (1 : ℝ) else 0)) := avg_le_avg hpt
        _ = 1 - (1 - Real.exp (-(1 / 1024)))
              * avg (fun r : Round n => if σ2 ≤ 4 * (∑ v, f v (r v)) ^ 2 then (1 : ℝ) else 0) := by
            rw [avg_sub, avg_const, avg_const_mul]
        _ ≤ 1 - 9 / 64 * (1 - Real.exp (-(1 / 1024))) := by
            have hc : 0 ≤ 1 - Real.exp (-(1 / 1024 : ℝ)) := by
              rw [sub_nonneg, Real.exp_le_one_iff]
              norm_num
            have := mul_le_mul_of_nonneg_left hpz hc
            linarith
    have near_const_le :
        1 - 9 / 64 * (1 - Real.exp (-(1 / 1024 : ℝ))) ≤ Real.exp (-(5 / 65536)) := by
      have h1 : Real.exp (-(1 / 1024 : ℝ)) ≤ 1024 / 1025 := by
        have h := Real.add_one_le_exp (1 / 1024 : ℝ)
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
        linarith
      have h2 := Real.add_one_le_exp (-(5 / 65536 : ℝ))
      linarith
    have pot_step_nonneg : (10 : ℝ) ≤ n → ∀ y : Config n Bool, 0 ≤ gapR y →
        avg (fun r : Round n => pot (step y r))
          ≤ Real.exp (-(1 / 65536)) * pot y + Real.exp (1 / 131072 - √(n : ℝ) / 512) := by
      intro hn y hg
      have hs : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hn0
      have hε : 0 ≤ Real.exp (1 / 131072 - √(n : ℝ) / 512) := (Real.exp_pos _).le
      have hρ : 0 ≤ Real.exp (-(1 / 65536 : ℝ)) * pot y :=
        mul_nonneg (Real.exp_pos _).le (pot_pos y).le
      rcases le_or_gt (gapR y) (√(n : ℝ) / 64) with h1 | h1
      · have habs : |gapR y| ≤ √(n : ℝ) / 64 := by rw [abs_of_nonneg hg]; exact h1
        have hpot1 : Real.exp (-(1 / 16384 : ℝ)) ≤ pot y := by
          rw [hpot]
          apply Real.exp_le_exp.mpr
          rw [neg_le_neg_iff, div_le_iff₀ (by positivity)]
          linarith
        have hchain : Real.exp (-(5 / 65536 : ℝ))
            = Real.exp (-(1 / 65536)) * Real.exp (-(1 / 16384)) := by
          rw [← Real.exp_add]
          norm_num
        calc avg (fun r : Round n => pot (step y r))
            ≤ 1 - 9 / 64 * (1 - Real.exp (-(1 / 1024))) := avg_pot_near hn y habs
          _ ≤ Real.exp (-(5 / 65536)) := near_const_le
          _ = Real.exp (-(1 / 65536)) * Real.exp (-(1 / 16384)) := hchain
          _ ≤ Real.exp (-(1 / 65536)) * pot y :=
              mul_le_mul_of_nonneg_left hpot1 (Real.exp_pos _).le
          _ ≤ _ := le_add_of_nonneg_right hε
      · rcases le_or_gt (gapR y) (n / 2) with h2 | h2
        · exact (avg_pot_far y h1.le h2).trans (le_add_of_nonneg_right hε)
        · exact (avg_pot_huge y h2).trans (le_add_of_nonneg_left hρ)
    intro hn y
    rcases le_total 0 (gapR y) with hg | hg
    · exact pot_step_nonneg hn y hg
    · have hg' : 0 ≤ gapR (fun v => !y v) := by rw [gap_neg]; linarith
      have h := pot_step_nonneg hn (fun v => !y v) hg'
      rw [pot_neg] at h
      have hfun : (fun r : Round n => pot (step (fun v => !y v) r))
          = fun r : Round n => pot (step y r) := by
        funext r
        rw [step_neg, pot_neg]
      rwa [hfun] at h
  -- fixed-time drift: `𝔼[pot after T rounds] ≤ ρ^T pot x + T ε`
  have drift : (10 : ℝ) ≤ n → ∀ (T : ℕ) (x : Config n Bool),
      expList (Round n) T (fun l => pot (run x l))
        ≤ Real.exp (-(1 / 65536)) ^ T * pot x
          + T * Real.exp (1 / 131072 - √(n : ℝ) / 512) := by
    intro hn T
    have hρ0 : 0 ≤ Real.exp (-(1 / 65536 : ℝ)) := (Real.exp_pos _).le
    have hρ1 : Real.exp (-(1 / 65536 : ℝ)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      norm_num
    have hε : 0 ≤ Real.exp (1 / 131072 - √(n : ℝ) / 512) := (Real.exp_pos _).le
    induction T with
    | zero => intro x; simp [run]
    | succ T ih =>
      intro x
      rw [expList_succ]
      have hρT1 : Real.exp (-(1 / 65536 : ℝ)) ^ T ≤ 1 := pow_le_one₀ hρ0 hρ1
      have hρT0 : 0 ≤ Real.exp (-(1 / 65536 : ℝ)) ^ T := pow_nonneg hρ0 T
      calc avg (fun r : Round n => expList (Round n) T (fun l => pot (run x (r :: l))))
          ≤ avg (fun r : Round n => Real.exp (-(1 / 65536)) ^ T * pot (step x r)
              + T * Real.exp (1 / 131072 - √(n : ℝ) / 512)) :=
            avg_le_avg fun r => ih (step x r)
        _ = Real.exp (-(1 / 65536)) ^ T * avg (fun r : Round n => pot (step x r))
              + T * Real.exp (1 / 131072 - √(n : ℝ) / 512) := by
            rw [avg_add, avg_const_mul, avg_const]
        _ ≤ Real.exp (-(1 / 65536)) ^ T * (Real.exp (-(1 / 65536)) * pot x
              + Real.exp (1 / 131072 - √(n : ℝ) / 512))
              + T * Real.exp (1 / 131072 - √(n : ℝ) / 512) := by
            gcongr
            exact pot_step hn x
        _ ≤ Real.exp (-(1 / 65536)) ^ (T + 1) * pot x
              + ((T + 1 : ℕ) : ℝ) * Real.exp (1 / 131072 - √(n : ℝ) / 512) := by
            have : Real.exp (-(1 / 65536 : ℝ)) ^ T * Real.exp (1 / 131072 - √(n : ℝ) / 512)
                ≤ Real.exp (1 / 131072 - √(n : ℝ) / 512) := mul_le_of_le_one_left hε hρT1
            rw [pow_succ]
            push_cast
            linarith
  /- ### The consensus phase -/
  have finish_bound : (128 : ℝ) ≤ Real.log n → ∀ y : Config n Bool,
      expList (Round n) ⌈128 * Real.log n⌉₊ (fun l => notConsensus (run y l))
        ≤ 128 / n + (if |gapR y| < 128 * √((n : ℝ) * Real.log n) then (1 : ℝ) else 0) := by
    have expList_one_sub : ∀ (T : ℕ) (F : List (Round n) → ℝ),
        expList (Round n) T (fun l => 1 - F l) = 1 - expList (Round n) T F := by
      intro T F
      have h := expList_add T (fun l => 1 - F l) F
      simp only [sub_add_cancel] at h
      rw [expList_const] at h
      linarith
    intro hL y
    split_ifs with h
    · calc expList (Round n) ⌈128 * Real.log n⌉₊ (fun l => notConsensus (run y l))
          ≤ expList (Round n) ⌈128 * Real.log n⌉₊ (fun _ => (1 : ℝ)) :=
            expList_le_expList fun l => notConsensus_le_one' _
        _ = 1 := expList_const _ _
        _ ≤ 128 / n + 1 := by
            have : (0 : ℝ) ≤ 128 / n := by positivity
            linarith
    · rw [add_zero]
      push Not at h
      rcases le_or_gt 0 (gapR y) with hg | hg
      · have hgap : 128 * √((n : ℝ) * Real.log n) ≤ gapR y := by
          rwa [abs_of_nonneg hg] at h
        have hc := binary_consensus hL y hgap
        have hpt : ∀ l, notConsensus (run y l)
            ≤ 1 - (if run y l = (fun _ => true) then (1 : ℝ) else 0) := by
          intro l
          split_ifs with h'
          · rw [notConsensus_cons' ⟨true, fun v => by rw [h']⟩]
            norm_num
          · rw [sub_zero]
            exact notConsensus_le_one' _
        calc expList (Round n) ⌈128 * Real.log n⌉₊ (fun l => notConsensus (run y l))
            ≤ expList (Round n) ⌈128 * Real.log n⌉₊
                (fun l => 1 - (if run y l = (fun _ => true) then (1 : ℝ) else 0)) :=
              expList_le_expList hpt
          _ = 1 - expList (Round n) ⌈128 * Real.log n⌉₊
                (fun l => if run y l = (fun _ => true) then (1 : ℝ) else 0) :=
              expList_one_sub _ _
          _ ≤ 128 / n := by linarith
      · have hgap : 128 * √((n : ℝ) * Real.log n) ≤ gapR (fun v => !y v) := by
          rw [gap_neg]
          rwa [abs_of_neg hg] at h
        have hc := binary_consensus hL (fun v => !y v) hgap
        have hpt : ∀ l, notConsensus (run y l)
            ≤ 1 - (if run (fun v => !y v) l = (fun _ => true) then (1 : ℝ) else 0) := by
          intro l
          rw [run_neg]
          split_ifs with h'
          · have hc' : Consensus (run y l) := ⟨false, fun v => by
              have := congrFun h' v
              simpa using this⟩
            rw [notConsensus_cons' hc']
            norm_num
          · rw [sub_zero]
            exact notConsensus_le_one' _
        calc expList (Round n) ⌈128 * Real.log n⌉₊ (fun l => notConsensus (run y l))
            ≤ expList (Round n) ⌈128 * Real.log n⌉₊
                (fun l => 1 - (if run (fun v => !y v) l = (fun _ => true) then (1 : ℝ) else 0)) :=
              expList_le_expList hpt
          _ = 1 - expList (Round n) ⌈128 * Real.log n⌉₊
                (fun l => if run (fun v => !y v) l = (fun _ => true) then (1 : ℝ) else 0) :=
              expList_one_sub _ _
          _ ≤ 128 / n := by linarith
  /- ### The escape phase -/
  have escape_bound : (8192 : ℝ) ≤ Real.log n → ∀ x : Config n Bool,
      expList (Round n) ⌈131072 * Real.log n⌉₊
          (fun l => if |gapR (run x l)| < 128 * √((n : ℝ) * Real.log n) then (1 : ℝ) else 0)
        ≤ 2 / n := by
    intro hL x
    clear pz_sum step_neg run_neg gap_neg pot_step finish_bound
    have hexpL : Real.exp (Real.log n) = n := Real.exp_log hn0
    obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log n := ⟨_, rfl⟩
    rw [← hLdef] at hL hexpL ⊢
    have hL0 : 0 ≤ L := by linarith
    have hn4 : L ^ 4 / 24 ≤ n := by
      have h := exp_ge_pow' hL0 4
      rw [hexpL] at h
      have hf : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
      rwa [hf] at h
    have hL3 : (8192 : ℝ) ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ (by norm_num) hL 3
    have hL4 : (8192 : ℝ) ^ 3 * L ≤ L ^ 4 := by
      have := mul_le_mul_of_nonneg_left hL3 hL0
      linarith
    have hn10 : (10 : ℝ) ≤ n := by linarith
    obtain ⟨T, hTdef⟩ : ∃ T, T = ⌈131072 * L⌉₊ := ⟨_, rfl⟩
    rw [← hTdef]
    have hT1 : 131072 * L ≤ (T : ℝ) := by rw [hTdef]; exact Nat.le_ceil _
    have hT2 : (T : ℝ) < 131072 * L + 1 := by
      rw [hTdef]
      exact Nat.ceil_lt_add_one (by positivity)
    have hTn : (T : ℝ) ≤ n := by linarith
    have hs : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hn0
    have hsL : √((n : ℝ) * L) = √(n : ℝ) * √L := Real.sqrt_mul hn0.le L
    have hLs : √L * √L = L := Real.mul_self_sqrt hL0
    have hL1 : 1 ≤ √L := Real.one_le_sqrt.mpr (by linarith)
    have hsqL : √L / 2 ≤ L := by
      have := mul_le_mul_of_nonneg_left hL1 (Real.sqrt_nonneg L)
      linarith
    have hsn : L ^ 2 / 5 ≤ √(n : ℝ) := by
      apply Real.le_sqrt_of_sq_le
      linarith [sq_nonneg (L ^ 2)]
    have hLL : 8192 * L ≤ L ^ 2 := by
      rw [sq]
      exact mul_le_mul_of_nonneg_right hL hL0
    have hdrift := drift hn10 T x
    have hind : ∀ y : Config n Bool,
        (if |gapR y| < 128 * √((n : ℝ) * L) then (1 : ℝ) else 0)
          ≤ Real.exp (√L / 2) * pot y := by
      intro y
      split_ifs with h
      · rw [hpot, ← Real.exp_add]
        apply Real.one_le_exp
        have h1 : |gapR y| / (256 * √(n : ℝ)) ≤ √L / 2 := by
          rw [div_le_iff₀ (by positivity)]
          rw [hsL] at h
          linarith
        linarith
      · exact mul_nonneg (Real.exp_pos _).le (pot_pos y).le
    have hA : Real.exp (√L / 2) * (Real.exp (-(1 / 65536)) ^ T * pot x) ≤ 1 / n := by
      have hpow : Real.exp (-(1 / 65536 : ℝ)) ^ T = Real.exp (T * (-(1 / 65536))) :=
        (Real.exp_nat_mul _ T).symm
      rw [hpow]
      calc Real.exp (√L / 2) * (Real.exp (T * (-(1 / 65536))) * pot x)
          ≤ Real.exp (√L / 2) * (Real.exp (T * (-(1 / 65536))) * 1) := by
            gcongr
            exact pot_le_one x
        _ = Real.exp (√L / 2 + T * (-(1 / 65536))) := by rw [mul_one, ← Real.exp_add]
        _ ≤ Real.exp (-L) := Real.exp_le_exp.mpr (by linarith)
        _ = 1 / n := by rw [Real.exp_neg, hexpL, one_div]
    have hB : Real.exp (√L / 2) * (T * Real.exp (1 / 131072 - √(n : ℝ) / 512)) ≤ 1 / n := by
      have he1 : Real.exp (√L / 2) ≤ n := by
        rw [← hexpL]
        exact Real.exp_le_exp.mpr hsqL
      have he3 : Real.exp (1 / 131072 - √(n : ℝ) / 512) ≤ Real.exp (-(3 * L)) :=
        Real.exp_le_exp.mpr (by linarith)
      have he3' : Real.exp (-(3 * L)) = 1 / (n : ℝ) ^ 3 := by
        rw [Real.exp_neg, show (3 : ℝ) * L = ((3 : ℕ) : ℝ) * L by norm_num, Real.exp_nat_mul,
          hexpL, one_div]
      have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
      calc Real.exp (√L / 2) * (T * Real.exp (1 / 131072 - √(n : ℝ) / 512))
          ≤ n * (n * (1 / (n : ℝ) ^ 3)) := by
            rw [← he3']
            gcongr
        _ = 1 / n := by field_simp
    calc expList (Round n) T
          (fun l => if |gapR (run x l)| < 128 * √((n : ℝ) * L) then (1 : ℝ) else 0)
        ≤ expList (Round n) T (fun l => Real.exp (√L / 2) * pot (run x l)) :=
          expList_le_expList fun l => hind _
      _ = Real.exp (√L / 2) * expList (Round n) T (fun l => pot (run x l)) :=
          expList_const_mul _ _ _
      _ ≤ Real.exp (√L / 2) * (Real.exp (-(1 / 65536)) ^ T * pot x
            + T * Real.exp (1 / 131072 - √(n : ℝ) / 512)) :=
          mul_le_mul_of_nonneg_left hdrift (Real.exp_pos _).le
      _ = Real.exp (√L / 2) * (Real.exp (-(1 / 65536)) ^ T * pot x)
            + Real.exp (√L / 2) * (T * Real.exp (1 / 131072 - √(n : ℝ) / 512)) := mul_add _ _ _
      _ ≤ 1 / n + 1 / n := add_le_add hA hB
      _ = 2 / n := by ring
  /- ### Assembly -/
  intro hL x
  have hL0 : (0 : ℝ) ≤ Real.log n := by linarith
  -- both phases together fail with probability at most `130/n`
  have htwo : expList (Round n) (⌈131072 * Real.log n⌉₊ + ⌈128 * Real.log n⌉₊)
      (fun l => notConsensus (run x l)) ≤ 130 / n := by
    rw [expList_append]
    calc expList (Round n) ⌈131072 * Real.log n⌉₊ (fun l₁ => expList (Round n)
            ⌈128 * Real.log n⌉₊ (fun l₂ => notConsensus (run x (l₁ ++ l₂))))
        ≤ expList (Round n) ⌈131072 * Real.log n⌉₊ (fun l₁ => 128 / n
            + (if |gapR (run x l₁)| < 128 * √((n : ℝ) * Real.log n) then (1 : ℝ) else 0)) := by
          refine expList_le_expList fun l₁ => ?_
          simp_rw [run_append]
          exact finish_bound (by linarith) _
      _ = 128 / n + expList (Round n) ⌈131072 * Real.log n⌉₊ (fun l₁ =>
            if |gapR (run x l₁)| < 128 * √((n : ℝ) * Real.log n) then (1 : ℝ) else 0) := by
          rw [expList_add, expList_const]
      _ ≤ 128 / n + 2 / n := by
          have := escape_bound (by linarith) x
          linarith
      _ = 130 / n := by ring
  -- the two phases fit into `⌈2¹⁸ log n⌉` rounds
  have h1 : ((⌈131072 * Real.log n⌉₊ : ℕ) : ℝ) < 131072 * Real.log n + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have h2 : ((⌈128 * Real.log n⌉₊ : ℕ) : ℝ) < 128 * Real.log n + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have h3 : 262144 * Real.log n ≤ ((⌈262144 * Real.log n⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hle : ⌈131072 * Real.log n⌉₊ + ⌈128 * Real.log n⌉₊ ≤ ⌈262144 * Real.log n⌉₊ := by
    have h : ((⌈131072 * Real.log n⌉₊ + ⌈128 * Real.log n⌉₊ : ℕ) : ℝ)
        ≤ ((⌈262144 * Real.log n⌉₊ : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  rw [hd]
  -- more rounds never hurt
  refine (expList_run_anti x _ d).trans (htwo.trans ?_)
  exact div_le_div_of_nonneg_right (by norm_num) hn0.le

variable {n : ℕ} {α : Type*} [LinearOrder α]

/-- **Reduction to two values.** If every binary configuration fails to reach consensus within
`T` rounds with probability at most `ε`, then a configuration with `m` distinct values fails with
probability at most `(m - 1) ε`. -/
theorem consensus_of_binary [NeZero n] {T : ℕ} {ε : ℝ}
    (hbin : ∀ y : Config n Bool, expList (Round n) T (fun l => notConsensus (run y l)) ≤ ε)
    (x : Config n α) :
    expList (Round n) T (fun l => notConsensus (run x l)) ≤ (((univ.image x).card : ℝ) - 1) * ε := by
  classical
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  set S := univ.image x with hS
  have hSne : S.Nonempty := ⟨x ⟨0, hn⟩, Finset.mem_image_of_mem x (Finset.mem_univ _)⟩
  set m := S.min' hSne with hm
  have hcard1 : 1 ≤ S.card := Finset.card_pos.mpr hSne
  have hmem : m ∈ S := Finset.min'_mem S hSne
  -- pointwise, a failure of `x` is witnessed by a failed threshold configuration
  have hpt : ∀ l : List (Round n), notConsensus (run x l)
      ≤ ∑ b ∈ S.erase m, notConsensus (run (fun v => decide (b ≤ x v)) l) := by
    intro l
    rcases notConsensus_cases' (run x l) with h0 | h1
    · rw [h0]
      exact Finset.sum_nonneg fun b _ => notConsensus_nonneg' _
    · have hnc : ¬ Consensus (run x l) := by
        intro hc
        rw [notConsensus_cons' hc] at h1
        norm_num at h1
      obtain ⟨u, v, huv⟩ : ∃ u v : Fin n, run x l u ≠ run x l v := by
        by_contra hcon
        push Not at hcon
        exact hnc ⟨run x l ⟨0, hn⟩, fun w => hcon _ _⟩
      have key : ∀ u v : Fin n, run x l u < run x l v →
          1 ≤ ∑ b ∈ S.erase m, notConsensus (run (fun w => decide (b ≤ x w)) l) := by
        intro u v hlt
        have hbS : run x l v ∈ S := run_mem_image x l v
        have haS : run x l u ∈ S := run_mem_image x l u
        have hbm : run x l v ≠ m := by
          intro heq
          have hminle : m ≤ run x l u := Finset.min'_le S _ haS
          rw [heq] at hlt
          exact absurd hlt (not_lt.mpr hminle)
        have hmemE : run x l v ∈ S.erase m := Finset.mem_erase.mpr ⟨hbm, hbS⟩
        have hthr : run (fun w => decide (run x l v ≤ x w)) l
            = fun w => decide (run x l v ≤ run x l w) := (threshold_run _ x l).symm
        have hnc2 : ¬ Consensus (run (fun w => decide (run x l v ≤ x w)) l) := by
          rintro ⟨c, hc⟩
          have hu : decide (run x l v ≤ run x l u) = c := by
            have := hc u
            rw [hthr] at this
            exact this
          have hv : decide (run x l v ≤ run x l v) = c := by
            have := hc v
            rw [hthr] at this
            exact this
          rw [decide_eq_false (not_le.mpr hlt)] at hu
          rw [decide_eq_true (le_refl _)] at hv
          exact absurd hv (by rw [← hu]; simp)
        have hone : notConsensus (run (fun w => decide (run x l v ≤ x w)) l) = 1 :=
          notConsensus_noncons' hnc2
        have hsingle : notConsensus (run (fun w => decide (run x l v ≤ x w)) l)
            ≤ ∑ b ∈ S.erase m, notConsensus (run (fun w => decide (b ≤ x w)) l) :=
          Finset.single_le_sum (f := fun b => notConsensus (run (fun w => decide (b ≤ x w)) l))
            (fun b _ => notConsensus_nonneg' _) hmemE
        rwa [hone] at hsingle
      rcases lt_or_gt_of_ne huv with h | h
      · rw [h1]; exact key u v h
      · rw [h1]; exact key v u h
  calc expList (Round n) T (fun l => notConsensus (run x l))
      ≤ expList (Round n) T
          (fun l => ∑ b ∈ S.erase m, notConsensus (run (fun v => decide (b ≤ x v)) l)) :=
        expList_le_expList hpt
    _ = ∑ b ∈ S.erase m,
          expList (Round n) T (fun l => notConsensus (run (fun v => decide (b ≤ x v)) l)) :=
        expList_finset_sum T _ _
    _ ≤ ∑ b ∈ S.erase m, ε := Finset.sum_le_sum fun b _ => hbin _
    _ = ((S.erase m).card : ℝ) * ε := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((S.card : ℝ) - 1) * ε := by
        rw [Finset.card_erase_of_mem hmem, Nat.cast_sub hcard1, Nat.cast_one]

/-- **Consensus from any configuration** (the paper's Theorem 1, no adversary). From any
configuration with values in a linear order, all nodes agree after `⌈C log n⌉` rounds except
with probability at most `C/n`. -/
theorem median_consensus_any : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) [NeZero n], C ≤ Real.log n →
    ∀ x : Config n α,
      expList (Round n) ⌈C * Real.log n⌉₊ (fun l => notConsensus (run x l)) ≤ C / n := by
  obtain ⟨C₀, hC₀pos, hbin⟩ := binary_any_start
  refine ⟨3 * C₀ + 3, by positivity, ?_⟩
  intro n _ hC x
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hL1 : (1 : ℝ) ≤ Real.log n := le_trans (by linarith) hC
  have hC₀L : C₀ ≤ Real.log n := by
    have hle : C₀ ≤ 3 * C₀ + 3 := by nlinarith
    exact hle.trans hC
  have hne : Nonempty (Round n) := ⟨fun _ => ((0 : Fin n), (0 : Fin n))⟩
  -- the binary bound of `binary_any_start`, amplified over three blocks
  have hbin3 : ∀ y : Config n Bool, expList (Round n) (3 * ⌈C₀ * Real.log n⌉₊)
      (fun l => notConsensus (run y l)) ≤ (C₀ / (n : ℝ)) ^ 3 :=
    fun y => expList_amplify (hbin n hC₀L) 3 y
  -- the reduction to two values, with at most `n` distinct values
  have hred := consensus_of_binary (T := 3 * ⌈C₀ * Real.log n⌉₊)
    (ε := (C₀ / (n : ℝ)) ^ 3) hbin3 x
  have hcard : (((univ.image x).card : ℝ) - 1) ≤ (n : ℝ) := by
    have hcardn : (univ.image x).card ≤ n := by
      simpa using Finset.card_image_le (f := x) (s := (univ : Finset (Fin n)))
    have h1 : (1 : ℕ) ≤ (univ.image x).card :=
      Finset.card_pos.mpr ⟨x ⟨0, hn⟩, Finset.mem_image_of_mem x (Finset.mem_univ _)⟩
    have hcast : (((univ.image x).card : ℝ) - 1) = (((univ.image x).card - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub h1, Nat.cast_one]
    rw [hcast]
    exact_mod_cast (Nat.sub_le (univ.image x).card 1).trans hcardn
  -- the constant `C₀` is small enough that `C₀³ ≤ n`
  have hcube : C₀ ^ 3 ≤ (n : ℝ) := by
    by_cases h1 : C₀ ≤ 1
    · have h13 : C₀ ^ 3 ≤ 1 := pow_le_one₀ hC₀pos.le h1
      exact h13.trans (by exact_mod_cast hn)
    · have h1' : 1 < C₀ := not_le.mp h1
      have hle : 3 * Real.log C₀ ≤ 3 * C₀ + 3 := by
        have hl : Real.log C₀ ≤ C₀ := Real.log_le_self hC₀pos.le
        nlinarith
      have hle2 : 3 * Real.log C₀ ≤ Real.log n := hle.trans hC
      have hex : Real.exp (3 * Real.log C₀) = C₀ ^ 3 := by
        rw [show (3 : ℝ) * Real.log C₀ = ((3 : ℕ) : ℝ) * Real.log C₀ by norm_num,
          Real.exp_nat_mul, Real.exp_log hC₀pos]
      have hexpn : Real.exp (3 * Real.log C₀) ≤ Real.exp (Real.log n) :=
        Real.exp_le_exp.mpr hle2
      rwa [hex, Real.exp_log hnR] at hexpn
  -- failure within `3 ⌈C₀ log n⌉₊` rounds is at most `1/n`
  have hpow : (0 : ℝ) ≤ C₀ / (n : ℝ) := div_nonneg hC₀pos.le hnR.le
  have h3T : expList (Round n) (3 * ⌈C₀ * Real.log n⌉₊)
      (fun l => notConsensus (run x l)) ≤ 1 / (n : ℝ) := by
    have h2 : (((univ.image x).card : ℝ) - 1) * (C₀ / (n : ℝ)) ^ 3
        ≤ (n : ℝ) * (C₀ / (n : ℝ)) ^ 3 :=
      mul_le_mul_of_nonneg_right hcard (pow_nonneg hpow 3)
    have hval : (n : ℝ) * (C₀ / (n : ℝ)) ^ 3 = C₀ ^ 3 / (n : ℝ) ^ 2 := by
      field_simp
    have h3 : (n : ℝ) * (C₀ / (n : ℝ)) ^ 3 ≤ 1 / (n : ℝ) := by
      rw [hval, div_le_div_iff₀ (pow_pos hnR 2) hnR]
      nlinarith [hcube, hnR]
    exact hred.trans (h2.trans h3)
  -- the round counts fit: `3 ⌈C₀ log n⌉₊ < (3C₀ + 3) log n ≤ ⌈(3C₀ + 3) log n⌉₊`
  have hTn : ((⌈C₀ * Real.log n⌉₊ : ℕ) : ℝ) < C₀ * Real.log n + 1 :=
    Nat.ceil_lt_add_one (mul_nonneg hC₀pos.le (by linarith))
  have h3Tlt : ((3 * ⌈C₀ * Real.log n⌉₊ : ℕ) : ℝ) < 3 * C₀ * Real.log n + 3 := by
    have h1 : ((3 * ⌈C₀ * Real.log n⌉₊ : ℕ) : ℝ) = 3 * ((⌈C₀ * Real.log n⌉₊ : ℕ) : ℝ) := by
      push_cast
      ring
    rw [h1]
    nlinarith [hTn]
  have hmid : 3 * C₀ * Real.log n + 3 ≤ (3 * C₀ + 3) * Real.log n := by
    have hexp : (3 : ℝ) ≤ 3 * Real.log n := by linarith
    nlinarith [hexp]
  have hceil : 3 * ⌈C₀ * Real.log n⌉₊ ≤ ⌈(3 * C₀ + 3) * Real.log n⌉₊ := by
    have hlt : ((3 * ⌈C₀ * Real.log n⌉₊ : ℕ) : ℝ) < (3 * C₀ + 3) * Real.log n :=
      lt_of_lt_of_le h3Tlt hmid
    have hle : (3 * C₀ + 3) * Real.log n
        ≤ ((⌈(3 * C₀ + 3) * Real.log n⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have hlt' : ((3 * ⌈C₀ * Real.log n⌉₊ : ℕ) : ℝ) < ((⌈(3 * C₀ + 3) * Real.log n⌉₊ : ℕ) : ℝ) :=
      lt_of_lt_of_le hlt hle
    exact_mod_cast hlt'.le
  -- pad up to `⌈C log n⌉₊` rounds using that consensus absorbs
  obtain ⟨d, hd⟩ : ∃ d : ℕ, ⌈(3 * C₀ + 3) * Real.log n⌉₊ = 3 * ⌈C₀ * Real.log n⌉₊ + d :=
    ⟨⌈(3 * C₀ + 3) * Real.log n⌉₊ - 3 * ⌈C₀ * Real.log n⌉₊, by omega⟩
  rw [hd]
  refine le_trans (expList_run_anti x (3 * ⌈C₀ * Real.log n⌉₊) d) ?_
  have hlast : 1 / (n : ℝ) ≤ (3 * C₀ + 3) / (n : ℝ) := by
    rw [div_le_div_iff₀ hnR hnR]
    nlinarith
  exact h3T.trans hlast

end Median
