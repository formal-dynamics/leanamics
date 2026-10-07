import Undecided.SequentialCorners
import Undecided.SequentialGap

/-! # Assembly: convergence within `O(n log n)` interactions

The path sums of the six weights are linear combinations of the counters
`S_vb, S_xy, S_c, S_b, S_x, S_y` (numbers of interactions of each type, and of interactions taking
place in each region). Off the five events `{∑_path φ ≥ L}` of P1, PC, PB, PX, PY:

* `S_ch = S_vb + S_xy < 60nL + 11n` (`sch_lt`, using `S_xy ≤ S_vb + n`, [AAE08, §4.4]);
* the number of non-consensus interactions is `< 256L + 34576nL + 6336n` (`cons_of_small`).

Since consensus is absorbing, a run that is not in consensus after `T` interactions had `T`
non-consensus interactions, so `T` at least that bound forces consensus. Markov's inequality for
each supermartingale gives `prob_notCons_le` (cf. [AAE08, Theorem 1]) and, with PM,
`prob_notAllX_le` (cf. [AAE08, Theorem 2]).
-/

namespace Undecided.Sequential
open Dynamics Real

variable {n : ℕ}

/-- A per-interaction observable given by the states of the initiator and the responder. -/
def onPair (f : Op → Op → ℝ) (s : Config n) (p : Interaction n) : ℝ := f (s p.1.1) (s p.1.2)

/-- The indicator of a property of the current configuration, as a per-interaction
observable. -/
noncomputable def onState (P : Config n → Prop) [DecidablePred P] (s : Config n)
    (_p : Interaction n) : ℝ :=
  if P s then 1 else 0

/-! ### Path sums of the weights -/

section PathSums
variable (s : Config n) (l : List (Interaction n))

/-- Number of `xb`/`yb` interactions along the path. -/
noncomputable abbrev Svb : ℝ := pathSum step (onPair vbI) s l
/-- Number of `xy`/`yx` interactions along the path. -/
noncomputable abbrev Sxy : ℝ := pathSum step (onPair xyI) s l

lemma ps_wSC : pathSum step (fun s p => wSC n (s p.1.1) (s p.1.2)) s l =
    (Svb s l / 5 - Sxy s l / 6) / n := by
  induction l generalizing s with
  | nil => simp
  | cons p l ih =>
    rw [pathSum_cons, ih]
    simp only [Svb, Sxy, pathSum_cons, wSC, onPair]
    ring

lemma ps_wC : pathSum step (fun s p => wC s (s p.1.1) (s p.1.2)) s l =
    (pathSum step (onState CentralR) s l - 256 * (Svb s l + Sxy s l)) / 256 := by
  induction l generalizing s with
  | nil => simp
  | cons p l ih =>
    rw [pathSum_cons, ih]
    simp only [Svb, Sxy, pathSum_cons, wC, onPair, onState]
    ring

lemma ps_wB : pathSum step (fun s p => wB n s (s p.1.1) (s p.1.2)) s l =
    5 / (16 * n) * (pathSum step (onState BlankR) s l - 64 * Sxy s l) := by
  induction l generalizing s with
  | nil => simp
  | cons p l ih =>
    rw [pathSum_cons, ih]
    simp only [Sxy, pathSum_cons, wB, onPair, onState]
    ring

lemma ps_wX : pathSum step (fun s p => wX n s (s p.1.1) (s p.1.2)) s l =
    5 / (32 * n) * (pathSum step (onState XR) s l - 128 * (Svb s l + Sxy s l)) := by
  induction l generalizing s with
  | nil => simp
  | cons p l ih =>
    rw [pathSum_cons, ih]
    simp only [Svb, Sxy, pathSum_cons, wX, onPair, onState]
    ring

lemma ps_wY : pathSum step (fun s p => wY n s (s p.1.1) (s p.1.2)) s l =
    5 / (32 * n) * (pathSum step (onState YR) s l - 128 * (Svb s l + Sxy s l)) := by
  induction l generalizing s with
  | nil => simp
  | cons p l ih =>
    rw [pathSum_cons, ih]
    simp only [Svb, Sxy, pathSum_cons, wY, onPair, onState]
    ring

lemma ps_wM (t : ℝ) : pathSum step (fun s p => wM t (s p.1.1) (s p.1.2)) s l =
    -(t ^ 2 / 2) * (Svb s l + Sxy s l) := by
  induction l generalizing s with
  | nil => simp
  | cons p l ih =>
    rw [pathSum_cons, ih]
    simp only [Svb, Sxy, pathSum_cons, wM, onPair]
    ring

lemma Svb_nonneg : 0 ≤ Svb s l := pathSum_nonneg (fun _ _ => vbI_nonneg _ _) s l
lemma Sxy_nonneg : 0 ≤ Sxy s l := pathSum_nonneg (fun _ _ => xyI_nonneg _ _) s l

lemma ps_onState_nonneg (P : Config n → Prop) [DecidablePred P] :
    0 ≤ pathSum step (onState P) s l :=
  pathSum_nonneg (fun s _ => by unfold onState; split <;> norm_num) s l

/-- The blank count moves by `S_xy - S_vb` ([AAE08, §4.4]). -/
lemma count_run_u : (count (run s l) .u : ℝ) = count s .u + Sxy s l - Svb s l := by
  induction l generalizing s with
  | nil => simp [run]
  | cons p l ih =>
    rw [run_cons, ih, count_step_u]
    simp only [Svb, Sxy, pathSum_cons, onPair]
    ring

/-- Every blank consumed was created or initially present: `S_xy ≤ S_vb + n`. -/
lemma Sxy_le : Sxy s l ≤ Svb s l + n := by
  have h := count_run_u s l
  have h1 : (count (run s l) .u : ℝ) ≤ n := by exact_mod_cast count_le _ .u
  have h2 : (0 : ℝ) ≤ count s .u := Nat.cast_nonneg _
  linarith

/-- A run that ends outside consensus never visited a consensus configuration. -/
lemma ps_notCons (h : ¬ Cons (run s l)) :
    pathSum step (onState fun s => ¬ Cons s) s l = l.length := by
  induction l generalizing s with
  | nil => simp
  | cons p l ih =>
    rw [run_cons] at h
    have hs : ¬ Cons s := fun hc => h (cons_run (cons_of_step_cons (p := p) hc) l)
    rw [pathSum_cons, ih _ h]
    simp [onState, hs, add_comm]

end PathSums

/-- Every non-consensus configuration lies in one of the four regions. -/
lemma notCons_le_regions (s : Config n) :
    (if ¬ Cons s then (1 : ℝ) else 0) ≤ (if CentralR s then 1 else 0) +
      (if BlankR s then 1 else 0) + (if XR s then 1 else 0) + (if YR s then 1 else 0) := by
  have h0 : ∀ P : Prop, [Decidable P] → (0 : ℝ) ≤ if P then 1 else 0 := fun P _ => by
    split <;> norm_num
  by_cases hc : Cons s
  · simp only [hc, not_true_eq_false, if_false]
    linarith [h0 (CentralR s), h0 (BlankR s), h0 (XR s), h0 (YR s)]
  · simp only [hc, not_false_eq_true, if_true]
    unfold Cons at hc
    obtain ⟨hca, hcb⟩ := not_or.mp hc
    have ha := count_le s .a
    have hb := count_le s .b
    have hs := count_add_nat s
    by_cases hB : BlankR s
    · simp only [hB, if_true]; linarith [h0 (CentralR s), h0 (XR s), h0 (YR s)]
    by_cases hX : XR s
    · simp only [hX, if_true]; linarith [h0 (CentralR s), h0 (BlankR s), h0 (YR s)]
    by_cases hY : YR s
    · simp only [hY, if_true]; linarith [h0 (CentralR s), h0 (BlankR s), h0 (XR s)]
    have hC : CentralR s := by
      unfold BlankR at hB; unfold XR at hX; unfold YR at hY; unfold CentralR
      refine ⟨by omega, ?_, ?_⟩
      · by_contra h; exact hX ⟨by omega, by omega⟩
      · by_contra h; exact hY ⟨by omega, by omega⟩
    simp only [hC, if_true]; linarith [h0 (BlankR s), h0 (XR s), h0 (YR s)]

/-! ### The deterministic core -/

section Core
variable (s : Config n) (l : List (Interaction n))

/-- Off the event of P1, few interactions change the state. -/
lemma sch_lt (hn : 0 < n) {L : ℝ}
    (h1 : pathSum step (fun s p => wSC n (s p.1.1) (s p.1.2)) s l < L) :
    Svb s l + Sxy s l < 60 * n * L + 11 * n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [ps_wSC, div_lt_iff₀ hn0] at h1
  have := Sxy_le s l
  have := Svb_nonneg s l
  nlinarith

/-- **Deterministic core.** Off the five events, a long enough run ends in consensus. -/
lemma cons_of_small (hn : 0 < n) {L : ℝ}
    (hT : 256 * L + 34576 * n * L + 6336 * n ≤ l.length)
    (h1 : pathSum step (fun s p => wSC n (s p.1.1) (s p.1.2)) s l < L)
    (hC : pathSum step (fun s p => wC s (s p.1.1) (s p.1.2)) s l < L)
    (hB : pathSum step (fun s p => wB n s (s p.1.1) (s p.1.2)) s l < L)
    (hX : pathSum step (fun s p => wX n s (s p.1.1) (s p.1.2)) s l < L)
    (hY : pathSum step (fun s p => wY n s (s p.1.1) (s p.1.2)) s l < L) :
    Cons (run s l) := by
  by_contra hnc
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hch := sch_lt s l hn h1
  have hxy0 := Sxy_nonneg s l
  have hvb0 := Svb_nonneg s l
  rw [ps_wC] at hC
  rw [ps_wB, ← lt_div_iff₀' (by positivity)] at hB
  rw [ps_wX, ← lt_div_iff₀' (by positivity)] at hX
  rw [ps_wY, ← lt_div_iff₀' (by positivity)] at hY
  have eB : L / (5 / (16 * (n : ℝ))) = 16 * n * L / 5 := by field_simp
  have eX : L / (5 / (32 * (n : ℝ))) = 32 * n * L / 5 := by field_simp
  rw [eB] at hB
  rw [eX] at hX hY
  -- the number of non-consensus interactions is the length of the run
  have hN := ps_notCons s l hnc
  have hle : pathSum step (onState fun s => ¬ Cons s) s l ≤
      pathSum step (onState CentralR) s l + pathSum step (onState BlankR) s l +
        pathSum step (onState XR) s l + pathSum step (onState YR) s l := by
    rw [← pathSum_add, ← pathSum_add, ← pathSum_add]
    exact pathSum_mono (fun s _ => notCons_le_regions s) s l
  have hnl : 0 ≤ (n : ℝ) * L := by
    rcases le_or_gt 0 L with hL | hL
    · positivity
    · nlinarith [ps_onState_nonneg s l CentralR]
  nlinarith

end Core

/-! ### Probabilities -/

lemma ind_le_of_imp {P Q : Prop} [Decidable P] [Decidable Q] (h : P → Q) :
    (if P then (1 : ℝ) else 0) ≤ if Q then 1 else 0 := by
  by_cases hp : P
  · simp [hp, h hp]
  · simp only [hp, if_false]; split <;> norm_num

lemma ind_nonneg (P : Prop) [Decidable P] : (0 : ℝ) ≤ if P then 1 else 0 := by
  split <;> norm_num

/-- Markov bound for one of the five events, in the form used below. -/
lemma event_le {φ : Config n → Interaction n → ℝ} {F : Config n → ℝ} (hF : ∀ s, 0 ≤ F s)
    (h : ∀ s, avg (fun p => exp (φ s p) * F (step s p)) ≤ F s) (T : ℕ) (s : Config n) (L : ℝ)
    {m A : ℝ} (hm : 0 < m) (hFm : ∀ l, m ≤ F (run s l)) (hA : F s ≤ A) :
    expList (Interaction n) T (fun l => if L ≤ pathSum step φ s l then 1 else 0) ≤
      A / m * exp (-L) := by
  have hb := expList_ind_le_of_weight hF h T s (fun l => L ≤ pathSum step φ s l)
    (m := exp L * m) (by positivity) (fun l hl => by
      have h1 : exp L ≤ exp (pathSum step φ s l) := exp_le_exp.mpr hl
      exact mul_le_mul h1 (hFm l) hm.le (exp_pos _).le)
  calc _ ≤ F s / (exp L * m) := hb
    _ ≤ A / (exp L * m) := by gcongr
    _ = A / m * exp (-L) := by rw [exp_neg]; field_simp

lemma five_events (hn : 16 ≤ n) (s : Config n) (hs : 1 ≤ count s .a + count s .b) (T : ℕ)
    (L : ℝ) :
    expList (Interaction n) T (fun l => if L ≤ pathSum step (fun s p => wSC n (s p.1.1) (s p.1.2))
        s l then 1 else 0) +
      expList (Interaction n) T (fun l => if L ≤ pathSum step (fun s p => wC s (s p.1.1) (s p.1.2))
        s l then 1 else 0) +
      expList (Interaction n) T (fun l => if L ≤ pathSum step (fun s p => wB n s (s p.1.1)
        (s p.1.2)) s l then 1 else 0) +
      expList (Interaction n) T (fun l => if L ≤ pathSum step (fun s p => wX n s (s p.1.1)
        (s p.1.2)) s l then 1 else 0) +
      expList (Interaction n) T (fun l => if L ≤ pathSum step (fun s p => wY n s (s p.1.1)
        (s p.1.2)) s l then 1 else 0) ≤ 9 * n * exp (-L) := by
  have hm : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hn2 : 2 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by linarith
  have hcnt : ∀ s : Config n, (count s .a : ℝ) ≤ n ∧ (count s .b : ℝ) ≤ n ∧
      (count s .u : ℝ) ≤ n := fun s =>
    ⟨by exact_mod_cast count_le s .a, by exact_mod_cast count_le s .b,
      by exact_mod_cast count_le s .u⟩
  -- P1: `F = 1 / (u² + 4n) ∈ [1 / (n² + 4n), 1 / (4n)]`
  have e1 := event_le (φ := fun s p => wSC n (s p.1.1) (s p.1.2)) (F := cpot (fSC n))
    (fun s => by unfold cpot fSC; positivity) (stepSC hn2) T s L
    (m := 1 / ((n : ℝ) ^ 2 + 4 * n)) (A := 1 / (4 * n)) (by positivity)
    (fun l => by
      unfold cpot fSC
      obtain ⟨ha, hb, -⟩ := hcnt (run s l)
      have h0a : (0 : ℝ) ≤ count (run s l) .a := Nat.cast_nonneg _
      have h0b : (0 : ℝ) ≤ count (run s l) .b := Nat.cast_nonneg _
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith)
    (by unfold cpot fSC; apply one_div_le_one_div_of_le (by positivity); nlinarith)
  -- PC: `F = 1`
  have eC := event_le (φ := fun s p => wC s (s p.1.1) (s p.1.2)) (F := cpot fun _ _ _ => 1)
    (fun s => by unfold cpot; norm_num) (stepC hn2) T s L (m := 1) (A := 1) one_pos
    (fun l => by unfold cpot; norm_num) (by unfold cpot; norm_num)
  -- PB: `F = 1 / v ∈ [1/n, 1]` on non-blank configurations
  have eB := event_le (φ := fun s p => wB n s (s p.1.1) (s p.1.2)) (F := cpot fB)
    (fun s => by unfold cpot fB; positivity) (stepB hn) T s L (m := 1 / n) (A := 1)
    (by positivity)
    (fun l => by
      unfold cpot fB
      have hv : (1 : ℝ) ≤ count (run s l) .a + count (run s l) .b := by
        exact_mod_cast nonblank_run hs l
      have hs' := count_add (run s l)
      have : (0 : ℝ) ≤ count (run s l) .u := Nat.cast_nonneg _
      apply one_div_le_one_div_of_le (by linarith)
      linarith)
    (by
      unfold cpot fB
      have hv : (1 : ℝ) ≤ count s .a + count s .b := by exact_mod_cast hs
      rw [div_le_one (by linarith)]
      exact hv)
  -- PX, PY: `F = 3y + b + 1 ∈ [1, 3n + 1]`
  have eX := event_le (φ := fun s p => wX n s (s p.1.1) (s p.1.2)) (F := cpot fX)
    (fun s => by unfold cpot fX; positivity) (stepX hn) T s L (m := 1) (A := 3 * n + 1) one_pos
    (fun l => by
      unfold cpot fX
      have := (Nat.cast_nonneg (count (run s l) .b) : (0 : ℝ) ≤ _)
      have := (Nat.cast_nonneg (count (run s l) .u) : (0 : ℝ) ≤ _)
      linarith)
    (by unfold cpot fX; have := count_add s; have := (hcnt s).2.1; nlinarith [hcnt s])
  have eY := event_le (φ := fun s p => wY n s (s p.1.1) (s p.1.2)) (F := cpot fY)
    (fun s => by unfold cpot fY; positivity) (stepY hn) T s L (m := 1) (A := 3 * n + 1) one_pos
    (fun l => by
      unfold cpot fY
      have := (Nat.cast_nonneg (count (run s l) .a) : (0 : ℝ) ≤ _)
      have := (Nat.cast_nonneg (count (run s l) .u) : (0 : ℝ) ≤ _)
      linarith)
    (by unfold cpot fY; have := count_add s; have := (hcnt s).1; nlinarith [hcnt s])
  have hexp : 0 < exp (-L) := exp_pos _
  have k1 : 1 / (4 * (n : ℝ)) / (1 / ((n : ℝ) ^ 2 + 4 * n)) = (n + 4) / 4 := by field_simp
  have k2 : (1 : ℝ) / (1 / (n : ℝ)) = n := by field_simp
  rw [k1] at e1
  rw [k2] at eB
  simp only [div_one] at eC eX eY
  nlinarith

/-- Off the five events, a run of length at least `256L + 34576nL + 6336n` ends in consensus. -/
lemma notCons_le_events (hn : 0 < n) (s : Config n) (L : ℝ) (l : List (Interaction n))
    (hT : 256 * L + 34576 * n * L + 6336 * n ≤ l.length) :
    (if Cons (run s l) then (0 : ℝ) else 1) ≤
      (if L ≤ pathSum step (fun s p => wSC n (s p.1.1) (s p.1.2)) s l then 1 else 0) +
      (if L ≤ pathSum step (fun s p => wC s (s p.1.1) (s p.1.2)) s l then 1 else 0) +
      (if L ≤ pathSum step (fun s p => wB n s (s p.1.1) (s p.1.2)) s l then 1 else 0) +
      (if L ≤ pathSum step (fun s p => wX n s (s p.1.1) (s p.1.2)) s l then 1 else 0) +
      (if L ≤ pathSum step (fun s p => wY n s (s p.1.1) (s p.1.2)) s l then 1 else 0) := by
  have h0 := ind_nonneg (L ≤ pathSum step (fun s p => wSC n (s p.1.1) (s p.1.2)) s l)
  have h1 := ind_nonneg (L ≤ pathSum step (fun s p => wC s (s p.1.1) (s p.1.2)) s l)
  have h2 := ind_nonneg (L ≤ pathSum step (fun s p => wB n s (s p.1.1) (s p.1.2)) s l)
  have h3 := ind_nonneg (L ≤ pathSum step (fun s p => wX n s (s p.1.1) (s p.1.2)) s l)
  have h4 := ind_nonneg (L ≤ pathSum step (fun s p => wY n s (s p.1.1) (s p.1.2)) s l)
  by_cases hc : Cons (run s l)
  · simp only [hc, if_true]; linarith
  simp only [hc, if_false]
  by_cases e1 : L ≤ pathSum step (fun s p => wSC n (s p.1.1) (s p.1.2)) s l
  · simp only [e1, if_true]; linarith
  by_cases eC : L ≤ pathSum step (fun s p => wC s (s p.1.1) (s p.1.2)) s l
  · simp only [eC, if_true]; linarith
  by_cases eB : L ≤ pathSum step (fun s p => wB n s (s p.1.1) (s p.1.2)) s l
  · simp only [eB, if_true]; linarith
  by_cases eX : L ≤ pathSum step (fun s p => wX n s (s p.1.1) (s p.1.2)) s l
  · simp only [eX, if_true]; linarith
  by_cases eY : L ≤ pathSum step (fun s p => wY n s (s p.1.1) (s p.1.2)) s l
  · simp only [eY, if_true]; linarith
  exact absurd (cons_of_small s l hn hT (not_le.mp e1) (not_le.mp eC) (not_le.mp eB)
    (not_le.mp eX) (not_le.mp eY)) hc

/-- **Convergence** (cf. [AAE08, Theorem 1]): from a non-blank configuration of `n ≥ 16` agents,
after `T ≥ 256L + 34576nL + 6336n` interactions the protocol is in consensus except with
probability at most `9 n e^{-L}`. -/
theorem prob_notCons_le (hn : 16 ≤ n) (s : Config n) (hs : 1 ≤ count s .a + count s .b) (L : ℝ)
    (T : ℕ) (hT : 256 * L + 34576 * n * L + 6336 * n ≤ T) :
    expList (Interaction n) T (fun l => if Cons (run s l) then 0 else 1) ≤ 9 * n * exp (-L) := by
  refine le_trans (expList_le_expList_of_length fun l hl =>
    notCons_le_events (by omega) s L l (by rw [hl]; exact hT)) ?_
  rw [expList_add, expList_add, expList_add, expList_add]
  exact five_events hn s hs T L

/-- The event of PM: the gap is not positive at the end although few interactions changed the
state. Its probability is at most `exp (-u₀² / (2N))`, by PM with `t = u₀ / N`. -/
lemma gap_event_le (hn : 2 ≤ n) (s : Config n) (T : ℕ) {N : ℝ} (hN : 0 < N)
    (hu : 0 ≤ (count s .a : ℝ) - count s .b) :
    expList (Interaction n) T (fun l => if count (run s l) .a ≤ count (run s l) .b ∧
        Svb s l + Sxy s l ≤ N then 1 else 0) ≤
      exp (-(((count s .a : ℝ) - count s .b) ^ 2 / (2 * N))) := by
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = ((count s .a : ℝ) - count s .b) / N := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by rw [ht]; exact div_nonneg hu hN.le
  have hF : ∀ s : Config n, 0 ≤ cpot (fM t) s := fun s => (exp_pos _).le
  have hb := expList_ind_le_of_weight (step := step) (φ := fun s p => wM t (s p.1.1) (s p.1.2))
    (F := cpot (fM t)) hF (stepM hn ht0) T s
    (fun l => count (run s l) .a ≤ count (run s l) .b ∧ Svb s l + Sxy s l ≤ N)
    (m := exp (-(t ^ 2 / 2 * N))) (exp_pos _) (fun l hl => by
      have hrun : l.foldl step s = run s l := rfl
      rw [ps_wM, hrun]
      have hxy : (count (run s l) .a : ℝ) ≤ count (run s l) .b := by exact_mod_cast hl.1
      have hF1 : cpot (fM t) (run s l) = 1 := by
        unfold cpot fM
        rw [max_eq_right (by linarith), mul_zero, neg_zero, exp_zero]
      rw [hF1, mul_one]
      apply exp_le_exp.mpr
      have h2 := hl.2
      have h3 : 0 ≤ t ^ 2 / 2 := by positivity
      nlinarith)
  have hF0 : cpot (fM t) s = exp (-(t * ((count s .a : ℝ) - count s .b))) := by
    unfold cpot fM
    rw [max_eq_left hu]
  rw [hF0, ← exp_sub] at hb
  refine le_trans hb (le_of_eq ?_)
  congr 1
  rw [ht]
  field_simp
  ring

/-- **Correctness** (cf. [AAE08, Theorem 2]): if `x > y` initially, after
`T ≥ 256L + 34576nL + 6336n` interactions all agents hold `x`, except with probability at most
`9 n e^{-L} + exp (-u₀² / (2N))`, where `u₀ = x - y` and `N = 60nL + 11n`. -/
theorem prob_notAllX_le (hn : 16 ≤ n) (s : Config n) (hu : count s .b < count s .a) {L : ℝ}
    (hL : 0 ≤ L) (T : ℕ) (hT : 256 * L + 34576 * n * L + 6336 * n ≤ T) :
    expList (Interaction n) T (fun l => if count (run s l) .a = n then 0 else 1) ≤
      9 * n * exp (-L) +
        exp (-(((count s .a : ℝ) - count s .b) ^ 2 / (2 * (60 * n * L + 11 * n)))) := by
  have hm : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : 0 < 60 * (n : ℝ) * L + 11 * n := by positivity
  have hs : 1 ≤ count s .a + count s .b := by omega
  have hu' : 0 ≤ (count s .a : ℝ) - count s .b := by
    have : (count s .b : ℝ) ≤ count s .a := by exact_mod_cast hu.le
    linarith
  have hpt : ∀ l : List (Interaction n), l.length = T →
      (if count (run s l) .a = n then (0 : ℝ) else 1) ≤
        ((if L ≤ pathSum step (fun s p => wSC n (s p.1.1) (s p.1.2)) s l then 1 else 0) +
        (if L ≤ pathSum step (fun s p => wC s (s p.1.1) (s p.1.2)) s l then 1 else 0) +
        (if L ≤ pathSum step (fun s p => wB n s (s p.1.1) (s p.1.2)) s l then 1 else 0) +
        (if L ≤ pathSum step (fun s p => wX n s (s p.1.1) (s p.1.2)) s l then 1 else 0) +
        (if L ≤ pathSum step (fun s p => wY n s (s p.1.1) (s p.1.2)) s l then 1 else 0)) +
        (if count (run s l) .a ≤ count (run s l) .b ∧
          Svb s l + Sxy s l ≤ 60 * n * L + 11 * n then 1 else 0) := by
    intro l hl
    have hev := notCons_le_events (by omega) s L l (by rw [hl]; exact hT)
    have hM := ind_nonneg (count (run s l) .a ≤ count (run s l) .b ∧
      Svb s l + Sxy s l ≤ 60 * n * L + 11 * n)
    have h1 := ind_nonneg (L ≤ pathSum step (fun s p => wSC n (s p.1.1) (s p.1.2)) s l)
    have h2 := ind_nonneg (L ≤ pathSum step (fun s p => wC s (s p.1.1) (s p.1.2)) s l)
    have h3 := ind_nonneg (L ≤ pathSum step (fun s p => wB n s (s p.1.1) (s p.1.2)) s l)
    have h4 := ind_nonneg (L ≤ pathSum step (fun s p => wX n s (s p.1.1) (s p.1.2)) s l)
    have h5 := ind_nonneg (L ≤ pathSum step (fun s p => wY n s (s p.1.1) (s p.1.2)) s l)
    by_cases ha : count (run s l) .a = n
    · rw [if_pos ha]
      linarith
    rw [if_neg ha]
    by_cases hc : Cons (run s l)
    · -- consensus on `y`: the gap is not positive
      have hb : count (run s l) .b = n := hc.resolve_left ha
      have hxy : count (run s l) .a ≤ count (run s l) .b := by rw [hb]; exact count_le _ _
      by_cases hS : Svb s l + Sxy s l ≤ 60 * n * L + 11 * n
      · rw [if_pos (show count (run s l) .a ≤ count (run s l) .b ∧
          Svb s l + Sxy s l ≤ 60 * n * L + 11 * n from ⟨hxy, hS⟩)]
        linarith
      · have e1 : L ≤ pathSum step (fun s p => wSC n (s p.1.1) (s p.1.2)) s l := by
          by_contra h
          exact hS (sch_lt s l (by omega) (not_le.mp h)).le
        rw [if_pos e1]
        linarith
    · rw [if_neg hc] at hev
      linarith
  refine le_trans (expList_le_expList_of_length hpt) ?_
  rw [expList_add, expList_add, expList_add, expList_add, expList_add]
  have h5 := five_events hn s hs T L
  have hg := gap_event_le (by omega) s T hN hu'
  linarith

end Undecided.Sequential
