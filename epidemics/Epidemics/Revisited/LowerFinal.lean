import Epidemics.Revisited.LowerRound
import Epidemics.Revisited.LowerGeneric

/-! # Final-phase lower bounds (EPI-8, Theorems 38 and 48 for the three protocols)

Round-by-round lower envelopes of the number of uninformed nodes. Pull and push–pull use the
double exponential targets `g (i+1) = g i ^ 2 / (2 n)` and `g (i+1) = g i ^ 2 / (2 e n)`,
started at `n / 2`. Push uses `g i = y i - 20 (y i)^{3/4}` with `y i = u e^{-i}`.
-/

namespace Epidemics.Revisited
open Finset Dynamics RumorProcess Real

variable {n : ℕ}

/-! ### Real comparisons used by every final phase -/

lemma half_le_log_two : (1 / 2 : ℝ) ≤ log 2 := by
  have hsq : exp (1 / 2) ^ 2 = exp 1 := by
    rw [pow_two, ← exp_add]
    norm_num
  have he : exp 1 < 4 := lt_trans exp_one_lt_d9 (by norm_num)
  have hlt : exp (1 / 2) < 2 := by
    have hcmp : exp (1 / 2) ^ 2 < (2 : ℝ) ^ 2 := by
      calc exp (1 / 2) ^ 2 = exp 1 := hsq
        _ < 4 := he
        _ = (2 : ℝ) ^ 2 := by norm_num
    have habs := (sq_lt_sq).mp hcmp
    simpa [abs_of_pos (exp_pos _), abs_of_pos (by norm_num : (0 : ℝ) < 2)] using habs
  have hlog : log (exp (1 / 2)) < log 2 := log_lt_log (exp_pos _) hlt
  rw [log_exp] at hlog
  exact hlog.le

/-- `log₂ x ≤ 2 x` for `x > 0`, from `ln x ≤ x` and `ln 2 ≥ 1/2`. -/
lemma logb_two_le_two_mul {x : ℝ} (hx : 0 < x) : logb 2 x ≤ 2 * x := by
  rw [logb]
  have hlog : log x ≤ x := by linarith [log_le_sub_one_of_pos hx]
  have hden : (1 / 2 : ℝ) ≤ log 2 := half_le_log_two
  have hpos : 0 < log 2 := by linarith
  by_cases hle : 0 < log x
  · have hdiv : log x / log 2 ≤ log x / (1 / 2) :=
      div_le_div_of_nonneg_left hle.le (by norm_num) hden
    have hsimp : log x / (1 / 2) = 2 * log x := by ring
    linarith [hdiv, hlog]
  · have hle' : log x ≤ 0 := by linarith
    have hquot : log x / log 2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hle' hpos.le
    have h2x : 0 ≤ 2 * x := by linarith
    linarith

lemma log_le_eight_rpow {n : ℕ} (hn : (0 : ℝ) < n) :
    log (n : ℝ) ≤ 8 * (n : ℝ) ^ (1 / 8 : ℝ) := by
  have h := log_le_rpow_div (x := (n : ℝ)) (ε := (1 / 8 : ℝ)) hn.le (by norm_num)
  have hrew : (n : ℝ) ^ (1 / 8 : ℝ) / (1 / 8) = 8 * (n : ℝ) ^ (1 / 8 : ℝ) := by ring
  linarith

lemma t_le_sixteen_rpow {n t : ℕ} (hn : (0 : ℝ) < n) (hlog : 0 < log (n : ℝ))
    (ht : (t : ℝ) ≤ logb 2 (log (n : ℝ))) :
    (t : ℝ) ≤ 16 * (n : ℝ) ^ (1 / 8 : ℝ) := by
  have h1 : logb 2 (log (n : ℝ)) ≤ 2 * log (n : ℝ) := logb_two_le_two_mul hlog
  have h2 : log (n : ℝ) ≤ 8 * (n : ℝ) ^ (1 / 8 : ℝ) := log_le_eight_rpow hn
  linarith

lemma log_four_le_three : log (4 : ℝ) ≤ 3 := by
  have h := log_le_sub_one_of_pos (x := (4 : ℝ)) (by norm_num)
  linarith

lemma log_four_nonneg : 0 ≤ log (4 : ℝ) := log_nonneg (by norm_num)

/-- `(1/4)^{2^i} ≥ n^{-1/8}` once `2^i ≤ ln n / 32`. -/
lemma quarter_pow_ge {n i : ℕ} (hn : (0 : ℝ) < n) (hlog : 0 ≤ log (n : ℝ))
    (hi : (2 : ℝ) ^ i ≤ log (n : ℝ) / 32) :
    (n : ℝ) ^ (-(1 / 8 : ℝ)) ≤ (1 / 4 : ℝ) ^ (2 ^ i) := by
  have hcoeff : (2 : ℝ) ^ i * log 4 ≤ log (n : ℝ) / 8 := by
    calc (2 : ℝ) ^ i * log 4
        ≤ (log (n : ℝ) / 32) * log 4 := mul_le_mul_of_nonneg_right hi log_four_nonneg
      _ ≤ (log (n : ℝ) / 32) * 3 :=
          mul_le_mul_of_nonneg_left log_four_le_three (by positivity)
      _ ≤ log (n : ℝ) / 8 := by
          have h38 : (3 : ℝ) / 32 ≤ 1 / 8 := by norm_num
          have hrew : (log (n : ℝ) / 32) * 3 = log (n : ℝ) * (3 / 32) := by ring
          have hrew' : log (n : ℝ) / 8 = log (n : ℝ) * (1 / 8) := by ring
          rw [hrew, hrew']
          exact mul_le_mul_of_nonneg_left h38 hlog
  have hrepr : (1 / 4 : ℝ) ^ (2 ^ i) =
      exp (log (1 / 4) * ((2 ^ i : ℕ) : ℝ)) := by
    rw [← rpow_natCast, rpow_def_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
  have hlogq : log ((1 : ℝ) / 4) = -log 4 := by
    rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num, log_inv]
  have hcast : ((2 ^ i : ℕ) : ℝ) = (2 : ℝ) ^ i := by norm_cast
  have hneg : -log 4 * (2 : ℝ) ^ i ≥ -(log (n : ℝ) / 8) := by linarith
  have hexp : exp (-(log (n : ℝ) / 8)) ≤ exp (log (1 / 4) * ((2 ^ i : ℕ) : ℝ)) := by
    apply exp_le_exp.mpr
    rw [hlogq, hcast]
    linarith
  have hrpow : (n : ℝ) ^ (-(1 / 8 : ℝ)) = exp (log (n : ℝ) * (-(1 / 8 : ℝ))) :=
    rpow_def_of_pos hn _
  have hmul : log (n : ℝ) * (-(1 / 8 : ℝ)) = -(log (n : ℝ) / 8) := by ring
  calc (n : ℝ) ^ (-(1 / 8 : ℝ))
      = exp (-(log (n : ℝ) / 8)) := by rw [hrpow, hmul]
    _ ≤ (1 / 4 : ℝ) ^ (2 ^ i) := by rw [hrepr]; exact hexp

lemma inv_four_exp_pow_ge {n i : ℕ} (hn : (0 : ℝ) < n) (hlog : 0 ≤ log (n : ℝ))
    (hi : (2 : ℝ) ^ i ≤ log (n : ℝ) / 32) :
    (n : ℝ) ^ (-(1 / 8 : ℝ)) ≤ (1 / (4 * exp 1) : ℝ) ^ (2 ^ i) := by
  have hlogle : log (4 * exp 1) ≤ 4 := by
    rw [log_mul (by norm_num) (exp_pos _).ne', log_exp]
    linarith [log_four_le_three]
  have hlog0 : 0 ≤ log (4 * exp 1) := by
    have : (1 : ℝ) ≤ 4 * exp 1 := by
      have : (1 : ℝ) ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
      nlinarith [exp_pos 1]
    exact log_nonneg this
  have hcoeff : (2 : ℝ) ^ i * log (4 * exp 1) ≤ log (n : ℝ) / 8 := by
    calc (2 : ℝ) ^ i * log (4 * exp 1)
        ≤ (log (n : ℝ) / 32) * log (4 * exp 1) := mul_le_mul_of_nonneg_right hi hlog0
      _ ≤ (log (n : ℝ) / 32) * 4 :=
          mul_le_mul_of_nonneg_left hlogle (div_nonneg hlog (by norm_num))
      _ = log (n : ℝ) / 8 := by ring
  have hbase : (0 : ℝ) < 1 / (4 * exp 1) := by positivity
  have hrepr : (1 / (4 * exp 1) : ℝ) ^ (2 ^ i) =
      exp (log (1 / (4 * exp 1)) * ((2 ^ i : ℕ) : ℝ)) := by
    rw [← rpow_natCast, rpow_def_of_pos hbase]
  have hlogq : log (1 / (4 * exp 1) : ℝ) = -log (4 * exp 1) := by
    rw [show (1 / (4 * exp 1) : ℝ) = (4 * exp 1)⁻¹ by ring, log_inv]
  have hcast : ((2 ^ i : ℕ) : ℝ) = (2 : ℝ) ^ i := by norm_cast
  have hexp : exp (-(log (n : ℝ) / 8)) ≤
      exp (log (1 / (4 * exp 1)) * ((2 ^ i : ℕ) : ℝ)) := by
    apply exp_le_exp.mpr
    rw [hlogq, hcast]
    linarith [hcoeff]
  have hrpow : (n : ℝ) ^ (-(1 / 8 : ℝ)) = exp (log (n : ℝ) * (-(1 / 8 : ℝ))) :=
    rpow_def_of_pos hn _
  have hmul : log (n : ℝ) * (-(1 / 8 : ℝ)) = -(log (n : ℝ) / 8) := by ring
  calc (n : ℝ) ^ (-(1 / 8 : ℝ))
      = exp (-(log (n : ℝ) / 8)) := by rw [hrpow, hmul]
    _ ≤ (1 / (4 * exp 1) : ℝ) ^ (2 ^ i) := by rw [hrepr]; exact hexp

/-- `2^i ≤ ln n / 32` for every `i ≤ t`, once `t + 5 ≤ log₂ ln n`. -/
lemma two_pow_le_log_div {n t i : ℕ} (hlog : 0 < log (n : ℝ))
    (ht : (t : ℝ) + 5 ≤ logb 2 (log (n : ℝ))) (hi : i ≤ t) :
    (2 : ℝ) ^ i ≤ log (n : ℝ) / 32 := by
  have hpow := pow_le_of_logb (ρ := 2) (x := log (n : ℝ)) (j := t + 5) (by norm_num) hlog
    (by
      have : ((t + 5 : ℕ) : ℝ) = (t : ℝ) + 5 := by norm_cast
      linarith)
  have h32 : (2 : ℝ) ^ (t + 5) = (2 : ℝ) ^ t * 32 := by
    rw [pow_add]
    norm_num
  have ht' : (2 : ℝ) ^ t ≤ log (n : ℝ) / 32 := by
    rw [le_div_iff₀ (by norm_num), ← h32]
    exact hpow
  exact le_trans (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hi) ht'

lemma n_sq_div_cube_le {n : ℕ} {u : ℝ} (hn : (0 : ℝ) < n)
    (hu : (n : ℝ) ^ (7 / 8 : ℝ) ≤ u) :
    (n : ℝ) ^ 2 / u ^ 3 ≤ (n : ℝ) ^ (-(5 / 8 : ℝ)) := by
  have hpow3 : ((n : ℝ) ^ (7 / 8 : ℝ)) ^ 3 = (n : ℝ) ^ (21 / 8 : ℝ) := by
    rw [← rpow_natCast, ← rpow_mul (le_of_lt hn)]
    norm_num
  have hu3 : (n : ℝ) ^ (21 / 8 : ℝ) ≤ u ^ 3 := by
    rw [← hpow3]
    exact pow_le_pow_left₀ (rpow_nonneg (le_of_lt hn) _) hu 3
  have hpos : 0 < (n : ℝ) ^ (21 / 8 : ℝ) := rpow_pos_of_pos hn _
  have hfrac : (n : ℝ) ^ 2 / u ^ 3 ≤ (n : ℝ) ^ 2 / (n : ℝ) ^ (21 / 8 : ℝ) :=
    div_le_div_of_nonneg_left (by positivity) hpos hu3
  have hid : (n : ℝ) ^ 2 / (n : ℝ) ^ (21 / 8 : ℝ) = (n : ℝ) ^ (-(5 / 8 : ℝ)) := by
    have hnat : (n : ℝ) ^ 2 = (n : ℝ) ^ (2 : ℝ) := (rpow_natCast _ _).symm
    rw [hnat, ← rpow_sub hn]
    congr 1
    norm_num
  exact le_trans hfrac (le_of_eq hid)

lemma one_sub_below_le_deficit {g : ℝ} (hg : 0 < g) (T : Finset (Fin n)) :
    1 - below (n : ℝ) T ≤ (if (n : ℝ) - (T.card : ℝ) < g then 1 else 0) := by
  classical
  by_cases hT : (T.card : ℝ) < (n : ℝ)
  · rw [below, if_pos hT, sub_self]
    split <;> norm_num
  · have hle : (T.card : ℝ) ≤ n := card_le_n T
    have hge : (n : ℝ) ≤ T.card := not_lt.mp hT
    have hdef : (n : ℝ) - (T.card : ℝ) = 0 := by linarith
    rw [below, if_neg hT, sub_zero, hdef, if_pos hg]

/-- All-informed is contained in `V < g t` whenever `g t > 0`, so the reach probability is at
most the envelope sum. -/
lemma reach_le_envelope (P : RumorProcess n) (g δ : ℕ → ℝ) (hδ : ∀ i, 0 ≤ δ i)
    (hstep : ∀ i a, g i ≤ (n : ℝ) - (a.card : ℝ) →
      (P.K a).prob (fun b => (n : ℝ) - (b.card : ℝ) < g (i + 1)) ≤ δ i)
    (t : ℕ) (S : Finset (Fin n)) (hstart : g 0 ≤ (n : ℝ) - (S.card : ℝ)) (hgt : 0 < g t) :
    1 - P.notYet n t S ≤ ∑ i ∈ range t, δ i := by
  classical
  have hind : ∀ T, 1 - below (n : ℝ) T ≤
      (if (n : ℝ) - (T.card : ℝ) < g t then 1 else 0) :=
    fun T => one_sub_below_le_deficit hgt T
  have hev := Kernel.event_eq_iterate P.K (fun T => (n : ℝ) - (T.card : ℝ) < g t) t S
  calc 1 - P.notYet n t S
      = P.K.iterate t (fun T => 1 - below (n : ℝ) T) S := one_sub_notYet_eq _ _ _ _
    _ ≤ P.K.iterate t (fun T => if (n : ℝ) - (T.card : ℝ) < g t then 1 else 0) S :=
        P.K.iterate_mono t hind S
    _ = P.K.event (fun T => (n : ℝ) - (T.card : ℝ) < g t) t S := by rw [← hev]
    _ ≤ ∑ i ∈ range t, δ i :=
        envelope_seq_le P.K (fun T => (n : ℝ) - (T.card : ℝ)) g δ hδ hstep t S hstart

/-! ### Pull: `g i = 2 n (1/4)^{2^i}` -/

noncomputable def pullTarget (n i : ℕ) : ℝ :=
  2 * (n : ℝ) * (1 / 4 : ℝ) ^ (2 ^ i)

lemma pullTarget_zero (n : ℕ) : pullTarget n 0 = (n : ℝ) / 2 := by
  unfold pullTarget
  simp [pow_zero, pow_one]
  ring

lemma pullTarget_pos {n : ℕ} (hn : 0 < n) (i : ℕ) : 0 < pullTarget n i := by
  unfold pullTarget
  positivity

lemma pullTarget_succ {n : ℕ} (hn : n ≠ 0) (i : ℕ) :
    pullTarget n (i + 1) = pullTarget n i ^ 2 / (2 * (n : ℝ)) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  unfold pullTarget
  rw [pow_succ, pow_mul]
  field_simp [hn0]

lemma pullTarget_ge_rpow {n i : ℕ} (hn : (0 : ℝ) < n) (hlog : 0 ≤ log (n : ℝ))
    (hi : (2 : ℝ) ^ i ≤ log (n : ℝ) / 32) :
    (n : ℝ) ^ (7 / 8 : ℝ) ≤ pullTarget n i := by
  have hq := quarter_pow_ge hn hlog hi
  have hadd : (n : ℝ) ^ (7 / 8 : ℝ) = (n : ℝ) * (n : ℝ) ^ (-(1 / 8 : ℝ)) := by
    rw [show (7 / 8 : ℝ) = 1 + (-(1 / 8 : ℝ)) by norm_num, rpow_add hn, rpow_one]
  have hnn : 0 ≤ (n : ℝ) * (n : ℝ) ^ (-(1 / 8 : ℝ)) :=
    mul_nonneg (le_of_lt hn) (rpow_nonneg (le_of_lt hn) _)
  calc (n : ℝ) ^ (7 / 8 : ℝ)
      = (n : ℝ) * (n : ℝ) ^ (-(1 / 8 : ℝ)) := hadd
    _ ≤ 2 * ((n : ℝ) * (n : ℝ) ^ (-(1 / 8 : ℝ))) := by linarith
    _ ≤ 2 * ((n : ℝ) * (1 / 4 : ℝ) ^ (2 ^ i)) := by
        gcongr
    _ = pullTarget n i := by unfold pullTarget; ring

noncomputable def pullFail (n i : ℕ) : ℝ :=
  if (n : ℝ) ^ (7 / 8 : ℝ) ≤ pullTarget n i then 4 * (n : ℝ) ^ (-(5 / 8 : ℝ)) else 1

lemma pullFail_nonneg (n i : ℕ) : 0 ≤ pullFail n i := by
  unfold pullFail
  split
  · positivity
  · norm_num

lemma pull_step {n : ℕ} (hn : 0 < n) (i : ℕ) (a : Finset (Fin n))
    (ha : pullTarget n i ≤ (n : ℝ) - (a.card : ℝ)) :
    ((pull n).K a).prob (fun b => (n : ℝ) - (b.card : ℝ) < pullTarget n (i + 1)) ≤
      pullFail n i := by
  by_cases hbig : (n : ℝ) ^ (7 / 8 : ℝ) ≤ pullTarget n i
  · have hu : (n : ℝ) ^ (7 / 8 : ℝ) ≤ (n : ℝ) - (a.card : ℝ) := le_trans hbig ha
    have hrec := pullTarget_succ (by omega : n ≠ 0) i
    have hden : 0 < 2 * (n : ℝ) := by positivity
    have hsq : pullTarget n i ^ 2 ≤ ((n : ℝ) - (a.card : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (pullTarget_pos hn i).le ha 2
    have hle : pullTarget n (i + 1) ≤
        ((n : ℝ) - (a.card : ℝ)) ^ 2 / (2 * (n : ℝ)) := by
      rw [hrec, div_le_div_iff_of_pos_right hden]
      exact hsq
    have hmono :
        ((pull n).K a).prob (fun b => (n : ℝ) - (b.card : ℝ) < pullTarget n (i + 1)) ≤
          ((pull n).K a).prob (fun b => (n : ℝ) - (b.card : ℝ) <
            ((n : ℝ) - (a.card : ℝ)) ^ 2 / (2 * (n : ℝ))) :=
      prob_mono _ fun _ hb => lt_of_lt_of_le hb hle
    have hround := pull_round_lower_proof a
    have hfrac : 4 * (n : ℝ) ^ 2 / ((n : ℝ) - (a.card : ℝ)) ^ 3 ≤
        4 * (n : ℝ) ^ (-(5 / 8 : ℝ)) := by
      have hmul := n_sq_div_cube_le (by exact_mod_cast hn) hu
      have hc : (0 : ℝ) ≤ 4 := by norm_num
      simpa [mul_div_assoc] using mul_le_mul_of_nonneg_left hmul hc
    unfold pullFail
    rw [if_pos hbig]
    exact le_trans (le_trans hmono hround) hfrac
  · unfold pullFail
    rw [if_neg hbig]
    exact ((pull n).K a).prob_le_one _

lemma pull_final_lower_proof :
    ∃ C : ℝ, ∃ r₀ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ S : Finset (Fin n), 2 * S.card ≤ n →
      ∀ t : ℕ, (t : ℝ) + r₀ ≤ logb 2 (log n) →
        1 - (pull n).notYet n t S ≤ C * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  refine ⟨128, 5, 3, ?_⟩
  intro n hn S hS t ht
  have hn0 : 0 < n := by omega
  have hn0r : (0 : ℝ) < n := by exact_mod_cast hn0
  have hlog1 : 1 < log (n : ℝ) := by
    have he : exp 1 < 3 := lt_trans exp_one_lt_d9 (by norm_num)
    have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hlt : exp 1 < (n : ℝ) := lt_of_lt_of_le he hn3
    rw [← log_exp 1]
    exact log_lt_log (exp_pos _) hlt
  have hlog0 : 0 < log (n : ℝ) := lt_trans (by norm_num) hlog1
  have hlognn : 0 ≤ log (n : ℝ) := hlog0.le
  have hstart : pullTarget n 0 ≤ (n : ℝ) - (S.card : ℝ) := by
    rw [pullTarget_zero]
    have hcast : (2 : ℝ) * S.card ≤ n := by exact_mod_cast hS
    linarith
  have hδ : ∀ i, 0 ≤ pullFail n i := fun i => pullFail_nonneg n i
  have hstep : ∀ i a, pullTarget n i ≤ (n : ℝ) - (a.card : ℝ) →
      ((pull n).K a).prob (fun b => (n : ℝ) - (b.card : ℝ) < pullTarget n (i + 1)) ≤
        pullFail n i :=
    fun i a ha => pull_step hn0 i a ha
  have hge : ∀ i, i ≤ t → (n : ℝ) ^ (7 / 8 : ℝ) ≤ pullTarget n i := by
    intro i hi
    exact pullTarget_ge_rpow hn0r hlognn (two_pow_le_log_div hlog0 ht hi)
  have hgt : 0 < pullTarget n t := pullTarget_pos hn0 t
  have henv := reach_le_envelope (pull n) (pullTarget n) (pullFail n) hδ hstep t S hstart hgt
  have hsum : ∑ i ∈ range t, pullFail n i ≤
      (t : ℝ) * (4 * (n : ℝ) ^ (-(5 / 8 : ℝ))) := by
    have heq : ∀ i ∈ range t, pullFail n i = 4 * (n : ℝ) ^ (-(5 / 8 : ℝ)) := by
      intro i hi
      have hi' : i ≤ t := le_of_lt (mem_range.mp hi)
      unfold pullFail
      rw [if_pos (hge i hi')]
    rw [sum_congr rfl heq, sum_const, card_range, nsmul_eq_mul]
  have ht16 : (t : ℝ) ≤ 16 * (n : ℝ) ^ (1 / 8 : ℝ) := by
    have : (t : ℝ) ≤ logb 2 (log (n : ℝ)) := by linarith
    exact t_le_sixteen_rpow hn0r hlog0 this
  have hmul : (t : ℝ) * (4 * (n : ℝ) ^ (-(5 / 8 : ℝ))) ≤
      64 * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have hc : 0 ≤ 4 * (n : ℝ) ^ (-(5 / 8 : ℝ)) := by positivity
    have hleft := mul_le_mul_of_nonneg_right ht16 hc
    have hrew : 16 * (n : ℝ) ^ (1 / 8 : ℝ) * (4 * (n : ℝ) ^ (-(5 / 8 : ℝ))) =
        64 * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
      have hadd : (n : ℝ) ^ (1 / 8 : ℝ) * (n : ℝ) ^ (-(5 / 8 : ℝ)) =
          (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [← rpow_add hn0r]
        norm_num
      calc 16 * (n : ℝ) ^ (1 / 8 : ℝ) * (4 * (n : ℝ) ^ (-(5 / 8 : ℝ)))
          = 64 * ((n : ℝ) ^ (1 / 8 : ℝ) * (n : ℝ) ^ (-(5 / 8 : ℝ))) := by ring
        _ = 64 * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by rw [hadd]
    linarith
  have h128 : 64 * (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 128 * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have hnn : 0 ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := rpow_nonneg (le_of_lt hn0r) _
    linarith
  exact le_trans henv (le_trans hsum (le_trans hmul h128))

/-! ### Push–pull: `g i = 2 e n (1/(4e))^{2^i}` -/

noncomputable def pushPullTarget (n i : ℕ) : ℝ :=
  2 * exp 1 * (n : ℝ) * (1 / (4 * exp 1) : ℝ) ^ (2 ^ i)

lemma pushPullTarget_zero (n : ℕ) : pushPullTarget n 0 = (n : ℝ) / 2 := by
  unfold pushPullTarget
  simp [pow_zero, pow_one]
  field_simp
  ring

lemma pushPullTarget_pos {n : ℕ} (hn : 0 < n) (i : ℕ) : 0 < pushPullTarget n i := by
  unfold pushPullTarget
  positivity

lemma pushPullTarget_succ {n : ℕ} (hn : n ≠ 0) (i : ℕ) :
    pushPullTarget n (i + 1) = pushPullTarget n i ^ 2 / (2 * exp 1 * (n : ℝ)) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  unfold pushPullTarget
  rw [pow_succ, pow_mul]
  field_simp [hn0]

lemma pushPullTarget_ge_rpow {n i : ℕ} (hn : (0 : ℝ) < n) (hlog : 0 ≤ log (n : ℝ))
    (hi : (2 : ℝ) ^ i ≤ log (n : ℝ) / 32) :
    (n : ℝ) ^ (7 / 8 : ℝ) ≤ pushPullTarget n i := by
  have hq := inv_four_exp_pow_ge hn hlog hi
  have hadd : (n : ℝ) ^ (7 / 8 : ℝ) = (n : ℝ) * (n : ℝ) ^ (-(1 / 8 : ℝ)) := by
    rw [show (7 / 8 : ℝ) = 1 + (-(1 / 8 : ℝ)) by norm_num, rpow_add hn, rpow_one]
  have hbase0 : 0 ≤ (1 / (4 * exp 1) : ℝ) ^ (2 ^ i) := by positivity
  have he : (1 : ℝ) ≤ 2 * exp 1 := by
    have : (1 : ℝ) ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
    nlinarith
  have hmul : (n : ℝ) * (1 / (4 * exp 1) : ℝ) ^ (2 ^ i) ≤
      2 * exp 1 * ((n : ℝ) * (1 / (4 * exp 1) : ℝ) ^ (2 ^ i)) := by
    simpa [one_mul] using
      mul_le_mul_of_nonneg_right he (mul_nonneg (le_of_lt hn) hbase0)
  calc (n : ℝ) ^ (7 / 8 : ℝ)
      = (n : ℝ) * (n : ℝ) ^ (-(1 / 8 : ℝ)) := hadd
    _ ≤ (n : ℝ) * (1 / (4 * exp 1) : ℝ) ^ (2 ^ i) :=
        mul_le_mul_of_nonneg_left hq (le_of_lt hn)
    _ ≤ 2 * exp 1 * ((n : ℝ) * (1 / (4 * exp 1) : ℝ) ^ (2 ^ i)) := hmul
    _ = pushPullTarget n i := by unfold pushPullTarget; ring

noncomputable def pushPullFail (n i : ℕ) : ℝ :=
  if (n : ℝ) ^ (7 / 8 : ℝ) ≤ pushPullTarget n i then
    4 * exp 1 ^ 2 * (n : ℝ) ^ (-(5 / 8 : ℝ))
  else 1

lemma pushPullFail_nonneg (n i : ℕ) : 0 ≤ pushPullFail n i := by
  unfold pushPullFail
  split
  · positivity
  · norm_num

lemma pushPull_step {n : ℕ} (hn : 0 < n) (i : ℕ) (a : Finset (Fin n))
    (ha : pushPullTarget n i ≤ (n : ℝ) - (a.card : ℝ)) :
    ((pushPull n).K a).prob (fun b => (n : ℝ) - (b.card : ℝ) < pushPullTarget n (i + 1)) ≤
      pushPullFail n i := by
  by_cases hbig : (n : ℝ) ^ (7 / 8 : ℝ) ≤ pushPullTarget n i
  · have hu : (n : ℝ) ^ (7 / 8 : ℝ) ≤ (n : ℝ) - (a.card : ℝ) := le_trans hbig ha
    have hrec := pushPullTarget_succ (by omega : n ≠ 0) i
    have hden : 0 < 2 * exp 1 * (n : ℝ) := by positivity
    have hsq : pushPullTarget n i ^ 2 ≤ ((n : ℝ) - (a.card : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (pushPullTarget_pos hn i).le ha 2
    have hle : pushPullTarget n (i + 1) ≤
        ((n : ℝ) - (a.card : ℝ)) ^ 2 / (2 * exp 1 * (n : ℝ)) := by
      rw [hrec, div_le_div_iff_of_pos_right hden]
      exact hsq
    have hmono :
        ((pushPull n).K a).prob
            (fun b => (n : ℝ) - (b.card : ℝ) < pushPullTarget n (i + 1)) ≤
          ((pushPull n).K a).prob (fun b => (n : ℝ) - (b.card : ℝ) <
            ((n : ℝ) - (a.card : ℝ)) ^ 2 / (2 * exp 1 * (n : ℝ))) :=
      prob_mono _ fun _ hb => lt_of_lt_of_le hb hle
    have hround := pushPull_round_lower_proof a
    have hfrac : 4 * exp 1 ^ 2 * (n : ℝ) ^ 2 / ((n : ℝ) - (a.card : ℝ)) ^ 3 ≤
        4 * exp 1 ^ 2 * (n : ℝ) ^ (-(5 / 8 : ℝ)) := by
      have hmul := n_sq_div_cube_le (by exact_mod_cast hn) hu
      have hc : (0 : ℝ) ≤ 4 * exp 1 ^ 2 := by positivity
      calc 4 * exp 1 ^ 2 * (n : ℝ) ^ 2 / ((n : ℝ) - (a.card : ℝ)) ^ 3
          = (4 * exp 1 ^ 2) * ((n : ℝ) ^ 2 / ((n : ℝ) - (a.card : ℝ)) ^ 3) := by ring
        _ ≤ (4 * exp 1 ^ 2) * (n : ℝ) ^ (-(5 / 8 : ℝ)) :=
            mul_le_mul_of_nonneg_left hmul hc
        _ = 4 * exp 1 ^ 2 * (n : ℝ) ^ (-(5 / 8 : ℝ)) := by ring
    unfold pushPullFail
    rw [if_pos hbig]
    exact le_trans (le_trans hmono hround) hfrac
  · unfold pushPullFail
    rw [if_neg hbig]
    exact ((pushPull n).K a).prob_le_one _

lemma pushPull_final_lower_proof :
    ∃ C : ℝ, ∃ r₀ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ S : Finset (Fin n), 2 * S.card ≤ n →
      ∀ t : ℕ, (t : ℝ) + r₀ ≤ logb 2 (log n) →
        1 - (pushPull n).notYet n t S ≤ C * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  refine ⟨128 * exp 1 ^ 2, 5, 3, ?_⟩
  intro n hn S hS t ht
  have hn0 : 0 < n := by omega
  have hn0r : (0 : ℝ) < n := by exact_mod_cast hn0
  have hlog1 : 1 < log (n : ℝ) := by
    have he : exp 1 < 3 := lt_trans exp_one_lt_d9 (by norm_num)
    have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hlt : exp 1 < (n : ℝ) := lt_of_lt_of_le he hn3
    rw [← log_exp 1]
    exact log_lt_log (exp_pos _) hlt
  have hlog0 : 0 < log (n : ℝ) := lt_trans (by norm_num) hlog1
  have hlognn : 0 ≤ log (n : ℝ) := hlog0.le
  have hstart : pushPullTarget n 0 ≤ (n : ℝ) - (S.card : ℝ) := by
    rw [pushPullTarget_zero]
    have hcast : (2 : ℝ) * S.card ≤ n := by exact_mod_cast hS
    linarith
  have hδ : ∀ i, 0 ≤ pushPullFail n i := fun i => pushPullFail_nonneg n i
  have hstep : ∀ i a, pushPullTarget n i ≤ (n : ℝ) - (a.card : ℝ) →
      ((pushPull n).K a).prob
        (fun b => (n : ℝ) - (b.card : ℝ) < pushPullTarget n (i + 1)) ≤
        pushPullFail n i :=
    fun i a ha => pushPull_step hn0 i a ha
  have hge : ∀ i, i ≤ t → (n : ℝ) ^ (7 / 8 : ℝ) ≤ pushPullTarget n i := by
    intro i hi
    exact pushPullTarget_ge_rpow hn0r hlognn (two_pow_le_log_div hlog0 ht hi)
  have hgt : 0 < pushPullTarget n t := pushPullTarget_pos hn0 t
  have henv := reach_le_envelope (pushPull n) (pushPullTarget n) (pushPullFail n)
    hδ hstep t S hstart hgt
  have hsum : ∑ i ∈ range t, pushPullFail n i ≤
      (t : ℝ) * (4 * exp 1 ^ 2 * (n : ℝ) ^ (-(5 / 8 : ℝ))) := by
    have heq : ∀ i ∈ range t, pushPullFail n i =
        4 * exp 1 ^ 2 * (n : ℝ) ^ (-(5 / 8 : ℝ)) := by
      intro i hi
      have hi' : i ≤ t := le_of_lt (mem_range.mp hi)
      unfold pushPullFail
      rw [if_pos (hge i hi')]
    rw [sum_congr rfl heq, sum_const, card_range, nsmul_eq_mul]
  have ht16 : (t : ℝ) ≤ 16 * (n : ℝ) ^ (1 / 8 : ℝ) := by
    have : (t : ℝ) ≤ logb 2 (log (n : ℝ)) := by linarith
    exact t_le_sixteen_rpow hn0r hlog0 this
  have hmul : (t : ℝ) * (4 * exp 1 ^ 2 * (n : ℝ) ^ (-(5 / 8 : ℝ))) ≤
      64 * exp 1 ^ 2 * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have hc : 0 ≤ 4 * exp 1 ^ 2 * (n : ℝ) ^ (-(5 / 8 : ℝ)) := by positivity
    have hleft := mul_le_mul_of_nonneg_right ht16 hc
    have hrew : 16 * (n : ℝ) ^ (1 / 8 : ℝ) * (4 * exp 1 ^ 2 * (n : ℝ) ^ (-(5 / 8 : ℝ))) =
        64 * exp 1 ^ 2 * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
      have hadd : (n : ℝ) ^ (1 / 8 : ℝ) * (n : ℝ) ^ (-(5 / 8 : ℝ)) =
          (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [← rpow_add hn0r]
        norm_num
      calc 16 * (n : ℝ) ^ (1 / 8 : ℝ) * (4 * exp 1 ^ 2 * (n : ℝ) ^ (-(5 / 8 : ℝ)))
          = 64 * exp 1 ^ 2 * ((n : ℝ) ^ (1 / 8 : ℝ) * (n : ℝ) ^ (-(5 / 8 : ℝ))) := by ring
        _ = 64 * exp 1 ^ 2 * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by rw [hadd]
    linarith
  have h128 : 64 * exp 1 ^ 2 * (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      128 * exp 1 ^ 2 * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have hnn : 0 ≤ exp 1 ^ 2 * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
    linarith
  exact le_trans henv (le_trans hsum (le_trans hmul h128))

end Epidemics.Revisited
