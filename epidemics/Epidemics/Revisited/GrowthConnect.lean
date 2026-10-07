import Epidemics.Revisited.GrowthAux

/-! # Crossing a flat middle range (Lemma 19)

If every uninformed node is informed with probability at least `p` while the number of
informed nodes lies in `[ℓ, m)`, the tail `P[T(ℓ, m) > r]` is at most the Markov bound on the
expected number of uninformed nodes. The potential is `gap m`, equal to `n - |S|` below `m`
and to `0` at and above `m`. Monotonicity keeps the chain inside `{|S| ≥ ℓ}`, so there is no
dummy process.
-/

namespace Epidemics.Revisited
open Finset Dynamics

variable {α : Type*} [Fintype α]

/-- `Kernel.event` agrees with iteration of any indicator of the event. -/
lemma event_of_indicator (K : Kernel α) (s : α → Prop) (ind : α → ℝ)
    (h0 : ∀ a, ¬ s a → ind a = 0) (h1 : ∀ a, s a → ind a = 1) (t : ℕ) (a : α) :
    K.event s t a = K.iterate t ind a := by
  classical
  simp only [Kernel.event]
  congr 1
  funext b
  by_cases hb : s b
  · rw [if_pos hb, h1 b hb]
  · rw [if_neg hb, h0 b hb]

variable {n : ℕ}

/-- Uninformed mass while fewer than `m` nodes are informed, and `0` afterwards. -/
noncomputable def gap (m : ℝ) (T : Finset (Fin n)) : ℝ := by
  classical
  exact if (T.card : ℝ) < m then (n : ℝ) - T.card else 0

lemma gap_of_lt {m : ℝ} {T : Finset (Fin n)} (h : (T.card : ℝ) < m) :
    gap m T = (n : ℝ) - T.card := by
  classical
  simp [gap, h]

lemma gap_of_not_lt {m : ℝ} {T : Finset (Fin n)} (h : ¬ (T.card : ℝ) < m) :
    gap m T = 0 := by
  classical
  simp [gap, h]

lemma gap_nonneg (m : ℝ) (T : Finset (Fin n)) : 0 ≤ gap m T := by
  classical
  unfold gap
  split
  · have hle : T.card ≤ n := by
      simpa [Fintype.card_fin] using card_le_univ (s := T)
    exact sub_nonneg.mpr (Nat.cast_le.mpr hle)
  · norm_num

lemma gap_le_deficit (m : ℝ) (T : Finset (Fin n)) :
    gap m T ≤ (n : ℝ) - T.card := by
  classical
  by_cases h : (T.card : ℝ) < m
  · rw [gap_of_lt h]
  · rw [gap_of_not_lt h]
    have hle : T.card ≤ n := by
      simpa [Fintype.card_fin] using card_le_univ (s := T)
    exact sub_nonneg.mpr (Nat.cast_le.mpr hle)

lemma gap_le_slack {m : ℝ} {ℓ : ℕ} {T : Finset (Fin n)} (hℓ : ℓ ≤ T.card) :
    gap m T ≤ (n : ℝ) - ℓ := by
  by_cases h : (T.card : ℝ) < m
  · rw [gap_of_lt h]
    have hcast : (ℓ : ℝ) ≤ T.card := Nat.cast_le.mpr hℓ
    linarith only [hcast]
  · rw [gap_of_not_lt h]
    have hℓn : ℓ ≤ n := le_trans hℓ (by simpa [Fintype.card_fin] using card_le_univ (s := T))
    have hcast : (ℓ : ℝ) ≤ n := Nat.cast_le.mpr hℓn
    linarith only [hcast]

lemma notYet_indicator_le {m : ℝ} (hmn : m < n) (T : Finset (Fin n)) :
    (if (T.card : ℝ) < m then (1 : ℝ) else 0) ≤ gap m T / ((n : ℝ) - m) := by
  classical
  have hden : 0 < (n : ℝ) - m := sub_pos.mpr hmn
  by_cases h : (T.card : ℝ) < m
  · rw [if_pos h, gap_of_lt h, le_div_iff₀ hden]
    have hle : (T.card : ℝ) ≤ m := le_of_lt h
    have hone : (1 : ℝ) * ((n : ℝ) - m) ≤ (n : ℝ) - T.card := by linarith only [hle]
    simpa [one_mul] using hone
  · rw [if_neg h, gap_of_not_lt h, zero_div]

lemma expect_card_eq (P : RumorProcess n) (S : Finset (Fin n)) :
    (P.K S).expect (fun T => (T.card : ℝ)) =
      (S.card : ℝ) + ∑ x ∈ (univ : Finset (Fin n)) \ S, P.informProb S x := by
  classical
  have hagree : ∀ T, S ⊆ T → (T.card : ℝ) =
      (S.card : ℝ) + ∑ x ∈ (univ : Finset (Fin n)) \ S, (if x ∈ T then (1 : ℝ) else 0) := by
    intro T hT
    exact card_eq_add_indicators hT
  have h := expect_eq_of_agree_on_superset P S hagree
  rw [h, Distribution.expect_add, Distribution.expect_const]
  congr 1
  rw [expect_finset_sum]
  refine sum_congr rfl ?_
  intro x _
  exact (prob_indicator_eq (P.K S) (fun T => x ∈ T) _
    (fun T hT => by simp [hT]) (fun T hT => by simp [hT])).symm.trans rfl

lemma expect_deficit (P : RumorProcess n) (S : Finset (Fin n)) :
    (P.K S).expect (fun T => (n : ℝ) - (T.card : ℝ)) =
      ∑ x ∈ (univ : Finset (Fin n)) \ S, (1 - P.informProb S x) := by
  rw [Distribution.expect_sub, Distribution.expect_const, expect_card_eq]
  have hsum1 : ∑ x ∈ (univ : Finset (Fin n)) \ S, (1 : ℝ) = (n : ℝ) - S.card := by
    rw [sum_const, nsmul_one, card_compl_cast]
  rw [sum_sub_distrib, hsum1]
  ring

lemma apply_gap_le (P : RumorProcess n) {ℓ : ℕ} {m p : ℝ} (hp1 : p ≤ 1)
    (hp : ∀ S : Finset (Fin n), ℓ ≤ S.card → (S.card : ℝ) < m → ∀ x ∉ S, p ≤ P.informProb S x)
    (S : Finset (Fin n)) (hS : ℓ ≤ S.card) :
    P.K.apply (gap m) S ≤ (1 - p) * gap m S := by
  classical
  by_cases hlt : (S.card : ℝ) < m
  · rw [Kernel.apply, gap_of_lt hlt]
    have hpt : ∀ T, S ⊆ T → gap m T ≤ (n : ℝ) - T.card := fun T _ => gap_le_deficit m T
    have hE := expect_le_of_weight P S hpt
    rw [expect_deficit] at hE
    have hterm : ∀ x ∈ (univ : Finset (Fin n)) \ S, 1 - P.informProb S x ≤ 1 - p := by
      intro x hx
      have hxS : x ∉ S := (mem_sdiff.mp hx).2
      have hp' : p ≤ P.informProb S x := hp S hS hlt x hxS
      linarith only [hp']
    have hsum := sum_le_sum hterm
    have hconst : ∑ x ∈ (univ : Finset (Fin n)) \ S, (1 - p) =
        (1 - p) * ((n : ℝ) - S.card) := by
      rw [sum_const, nsmul_eq_mul, card_compl_cast]
      ring
    linarith only [hE, hsum, hconst]
  · have hzero : ∀ T, S ⊆ T → gap m T = 0 := by
      intro T hT
      have hcard : (S.card : ℝ) ≤ T.card := Nat.cast_le.mpr (card_le_card hT)
      have hge : ¬ (T.card : ℝ) < m := by
        intro hTlt
        exact hlt (lt_of_le_of_lt hcard hTlt)
      exact gap_of_not_lt hge
    have heq := expect_eq_of_agree_on_superset P S (f := gap m) (g := fun _ => 0) hzero
    rw [gap_of_not_lt hlt, Kernel.apply, heq, Distribution.expect_const]
    have hnonneg : 0 ≤ 1 - p := sub_nonneg.mpr hp1
    linarith only [hnonneg]

lemma iterate_gap_le (P : RumorProcess n) {ℓ : ℕ} {m p : ℝ} (hp1 : p ≤ 1)
    (hp : ∀ S : Finset (Fin n), ℓ ≤ S.card → (S.card : ℝ) < m → ∀ x ∉ S, p ≤ P.informProb S x)
    (r : ℕ) (S : Finset (Fin n)) (hS : ℓ ≤ S.card) :
    P.K.iterate r (gap m) S ≤ (1 - p) ^ r * gap m S := by
  induction r generalizing S with
  | zero => simp
  | succ r ih =>
    rw [Kernel.iterate_succ]
    have hpt : ∀ T, S ⊆ T →
        P.K.iterate r (gap m) T ≤ (1 - p) ^ r * gap m T := by
      intro T hT
      exact ih T (le_trans hS (card_le_card hT))
    have hE := expect_le_of_weight P S hpt
    rw [Distribution.expect_mul] at hE
    have hstep := apply_gap_le P hp1 hp S hS
    have hpow : 0 ≤ (1 - p) ^ r := pow_nonneg (sub_nonneg.mpr hp1) r
    calc P.K.apply (P.K.iterate r (gap m)) S
        ≤ (1 - p) ^ r * P.K.apply (gap m) S := hE
      _ ≤ (1 - p) ^ r * ((1 - p) * gap m S) :=
          mul_le_mul_of_nonneg_left hstep hpow
      _ = (1 - p) ^ (r + 1) * gap m S := by ring

lemma iterate_notYet_le (P : RumorProcess n) {ℓ : ℕ} {m p : ℝ}
    (hmn : m < n) (hp1 : p ≤ 1)
    (hp : ∀ S : Finset (Fin n), ℓ ≤ S.card → (S.card : ℝ) < m → ∀ x ∉ S, p ≤ P.informProb S x)
    (S : Finset (Fin n)) (hS : ℓ ≤ S.card) (r : ℕ) :
    P.K.iterate r (fun T => if (T.card : ℝ) < m then (1 : ℝ) else 0) S ≤
      ((n : ℝ) - ℓ) / ((n : ℝ) - m) * (1 - p) ^ r := by
  have hden : 0 < (n : ℝ) - m := sub_pos.mpr hmn
  have hpt : ∀ T, (if (T.card : ℝ) < m then (1 : ℝ) else 0) ≤ gap m T / ((n : ℝ) - m) :=
    fun T => notYet_indicator_le hmn T
  have hmono := P.K.iterate_mono r hpt S
  have hfun : (fun T : Finset (Fin n) => gap m T / ((n : ℝ) - m)) =
      fun T : Finset (Fin n) => ((n : ℝ) - m)⁻¹ * gap m T := by
    funext T
    rw [div_eq_mul_inv, mul_comm]
  have hscale : P.K.iterate r (fun T => gap m T / ((n : ℝ) - m)) S =
      ((n : ℝ) - m)⁻¹ * P.K.iterate r (gap m) S := by
    rw [hfun, P.K.iterate_mul]
  have hgap := iterate_gap_le P hp1 hp r S hS
  have hslack := gap_le_slack (m := m) hS
  have hpow : 0 ≤ (1 - p) ^ r := pow_nonneg (sub_nonneg.mpr hp1) r
  have hinv : 0 ≤ ((n : ℝ) - m)⁻¹ := inv_nonneg.mpr hden.le
  calc P.K.iterate r (fun T => if (T.card : ℝ) < m then (1 : ℝ) else 0) S
      ≤ P.K.iterate r (fun T => gap m T / ((n : ℝ) - m)) S := hmono
    _ = ((n : ℝ) - m)⁻¹ * P.K.iterate r (gap m) S := hscale
    _ ≤ ((n : ℝ) - m)⁻¹ * ((1 - p) ^ r * gap m S) :=
        mul_le_mul_of_nonneg_left hgap hinv
    _ ≤ ((n : ℝ) - m)⁻¹ * ((1 - p) ^ r * ((n : ℝ) - ℓ)) := by
        have hmul : (1 - p) ^ r * gap m S ≤ (1 - p) ^ r * ((n : ℝ) - ℓ) :=
          mul_le_mul_of_nonneg_left hslack hpow
        exact mul_le_mul_of_nonneg_left hmul hinv
    _ = ((n : ℝ) - ℓ) / ((n : ℝ) - m) * (1 - p) ^ r := by
        rw [div_eq_mul_inv]
        ring

/-- States that already have at least `m` informed nodes stay there, so the tail is zero. -/
lemma notYet_eq_zero_of_ge (P : RumorProcess n) {m : ℝ} {S : Finset (Fin n)}
    (hS : m ≤ (S.card : ℝ)) (t : ℕ) : P.notYet m t S = 0 := by
  classical
  have hzero : ∀ t' : ℕ, ∀ T : Finset (Fin n), m ≤ (T.card : ℝ) →
      P.K.iterate t' (fun U => if (U.card : ℝ) < m then (1 : ℝ) else 0) T = 0 := by
    intro t'
    induction t' with
    | zero =>
      intro T hT
      simp [not_lt.mpr hT]
    | succ t' ih =>
      intro T hT
      rw [Kernel.iterate_succ]
      have hpt : ∀ U, T ⊆ U →
          P.K.iterate t' (fun V => if (V.card : ℝ) < m then (1 : ℝ) else 0) U = 0 := by
        intro U hU
        have hcard : (T.card : ℝ) ≤ U.card := Nat.cast_le.mpr (card_le_card hU)
        exact ih U (le_trans hT hcard)
      have heq := expect_eq_of_agree_on_superset P T hpt
      simpa [Kernel.apply, Distribution.expect_const] using heq
  have hnot : ¬ (S.card : ℝ) < m := not_lt.mpr hS
  rw [RumorProcess.notYet, event_of_indicator P.K (fun U => (U.card : ℝ) < m)
      (fun U => if (U.card : ℝ) < m then (1 : ℝ) else 0)
      (fun U h => by simp [h]) (fun U h => by simp [h])]
  exact hzero t S hS

theorem connect_tail_proof (P : RumorProcess n) {ℓ : ℕ} {m p : ℝ} (hℓm : (ℓ : ℝ) < m)
    (hmn : m < n) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp : ∀ S : Finset (Fin n), ℓ ≤ S.card → (S.card : ℝ) < m → ∀ x ∉ S, p ≤ P.informProb S x)
    (S : Finset (Fin n)) (hS : ℓ ≤ S.card) (r : ℕ) :
    P.notYet m r S ≤ ((n : ℝ) - ℓ) / ((n : ℝ) - m) * (1 - p) ^ r := by
  classical
  by_cases horder : (ℓ : ℝ) < m
  · rw [RumorProcess.notYet, event_of_indicator P.K (fun U => (U.card : ℝ) < m)
        (fun U => if (U.card : ℝ) < m then (1 : ℝ) else 0)
        (fun U h => by simp [h]) (fun U h => by simp [h])]
    by_cases hsign : 0 ≤ p
    · exact iterate_notYet_le P hmn hp1 hp S hS r
    · exact absurd hp0 hsign
  · exact absurd hℓm horder

theorem connect_expect_proof (P : RumorProcess n) {ℓ : ℕ} {m p : ℝ} (hℓm : (ℓ : ℝ) < m)
    (hmn : m < n) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hp : ∀ S : Finset (Fin n), ℓ ≤ S.card → (S.card : ℝ) < m → ∀ x ∉ S, p ≤ P.informProb S x)
    (S : Finset (Fin n)) (hS : ℓ ≤ S.card) (R : ℕ) :
    ∑ t ∈ range R, P.notYet m t S ≤ ((n : ℝ) - ℓ) / ((n : ℝ) - m) * (1 / p) := by
  have hq0 : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hq1 : 1 - p < 1 := by linarith only [hp0]
  have hratio : 0 ≤ ((n : ℝ) - ℓ) / ((n : ℝ) - m) := by
    have hnum : 0 ≤ (n : ℝ) - ℓ := by
      have hℓn : ℓ ≤ n := le_trans hS (by simpa [Fintype.card_fin] using card_le_univ (s := S))
      exact sub_nonneg.mpr (Nat.cast_le.mpr hℓn)
    have hden : 0 ≤ (n : ℝ) - m := (sub_pos.mpr hmn).le
    exact div_nonneg hnum hden
  have hterm : ∀ t ∈ range R, P.notYet m t S ≤
      ((n : ℝ) - ℓ) / ((n : ℝ) - m) * (1 - p) ^ t := by
    intro t _
    exact connect_tail_proof P hℓm hmn hp0.le hp1 hp S hS t
  have hsum := sum_le_sum hterm
  rw [← mul_sum] at hsum
  have hgeom := geom_partial_le hq0 hq1 R
  calc ∑ t ∈ range R, P.notYet m t S
      ≤ ((n : ℝ) - ℓ) / ((n : ℝ) - m) * ∑ t ∈ range R, (1 - p) ^ t := hsum
    _ ≤ ((n : ℝ) - ℓ) / ((n : ℝ) - m) * (1 - (1 - p))⁻¹ :=
        mul_le_mul_of_nonneg_left hgeom hratio
    _ = ((n : ℝ) - ℓ) / ((n : ℝ) - m) * (1 / p) := by
        have hpinv : (1 - (1 - p))⁻¹ = (1 : ℝ) / p := by
          rw [sub_sub_self, inv_eq_one_div]
        rw [hpinv]

end Epidemics.Revisited
