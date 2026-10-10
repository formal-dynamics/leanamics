import Median.ExpanderGeneralDefs

/-! # Phase I: from one round to the hitting time

The induction over the rounds in the proof of the paper's Lemma 2 (Cooper, Elsässer and Radzik,
ICALP 2014, arXiv:1404.7479): if, in every round started with a minority above `c n`, the
imbalance grows by the factor `5/4` (while `120 α ≤ ν ≤ 1/2`) and `1 − ν` shrinks by the
factor `3/4` (while `ν ≥ 1/2`), except with probability `q`, then within `phaseIRounds ν₀ c`
rounds the minority drops to at most `c n`, except with probability `phaseIRounds ν₀ c · q`.
-/

namespace Median.ExpanderGeneral
open Finset Dynamics Real

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- `expList` is monotone in the functional, compared on the lists of length `T` only. -/
private theorem expList_le_expList_of_length {β : Type*} [Fintype β] {T : ℕ}
    {F₁ F₂ : List β → ℝ} (h : ∀ l : List β, l.length = T → F₁ l ≤ F₂ l) :
    expList β T F₁ ≤ expList β T F₂ := by
  induction T generalizing F₁ F₂ with
  | zero => exact h [] rfl
  | succ T ih => exact avg_le_avg fun b => ih fun l hl => h (b :: l) (by simp [hl])

/-- A lower bound `1 − F₁ ≤ F₂` on the lists of length `T` passes to the expectations. -/
private theorem one_sub_expList_le {β : Type*} [Fintype β] [Nonempty β] {T : ℕ}
    {F₁ F₂ : List β → ℝ} (h : ∀ l : List β, l.length = T → 1 - F₁ l ≤ F₂ l) :
    1 - expList β T F₁ ≤ expList β T F₂ := by
  have h1 : expList β T (fun l => 1 - F₁ l) + expList β T F₁ = 1 := by
    rw [← expList_add]
    simp only [sub_add_cancel]
    exact expList_const T 1
  have h2 := expList_le_expList_of_length h
  linarith

/-- An indicator of failure below the complement of an event of probability at least `1 − q`
has average at most `q`. -/
private theorem avg_le_of_le_one_sub {β : Type*} [Fintype β] [Nonempty β] {f g : β → ℝ} {q : ℝ}
    (hg : 1 - q ≤ avg g) (h : ∀ r, f r ≤ 1 - g r) : avg f ≤ q := by
  have := avg_le_avg h
  rw [avg_sub, avg_const] at this
  linarith

/-- `⌈log_{5/4} (1/(2ν₀))⌉` rounds of growth by the factor `5/4` bring `ν₀` to `1/2`. -/
private theorem half_le_pow_mul {ν₀ : ℝ} (hν₀ : 0 < ν₀) {t : ℕ}
    (ht : log (1 / (2 * ν₀)) / log (5 / 4) ≤ t) : 1 / 2 ≤ (5 / 4) ^ t * ν₀ := by
  rw [div_le_iff₀ (Real.log_pos (by norm_num)), ← Real.log_pow] at ht
  have h := (Real.log_le_log_iff (by positivity) (by positivity)).1 ht
  rw [div_le_iff₀ (by positivity)] at h
  linarith

/-- `⌈log_{4/3} (1/(4c))⌉` rounds of shrinking by the factor `3/4` bring `1/2` to `2c`. -/
private theorem pow_div_two_le {c : ℝ} (hc : 0 < c) {t : ℕ}
    (ht : log (1 / (4 * c)) / log (4 / 3) ≤ t) : (3 / 4) ^ t / 2 ≤ 2 * c := by
  rw [div_le_iff₀ (Real.log_pos (by norm_num)), ← Real.log_pow] at ht
  have h := (Real.log_le_log_iff (by positivity) (by positivity)).1 ht
  rw [one_div] at h
  have h' := inv_le_of_inv_le₀ (by positivity) h
  rw [← inv_pow, show (4 / 3 : ℝ)⁻¹ = 3 / 4 by norm_num] at h'
  linarith

/-- The deterministic envelope of the imbalance in Phase I: `(5/4)^t ν₀`, capped at `1/2`, for
`t ≤ t₁`, then `1 − (3/4)^{t − t₁}/2`. -/
private noncomputable def envelope (ν₀ : ℝ) (t₁ t : ℕ) : ℝ :=
  if t ≤ t₁ then min ((5 / 4) ^ t * ν₀) (1 / 2) else 1 - (3 / 4) ^ (t - t₁) / 2

/-- The envelope starts below `ν₀`. -/
private theorem envelope_zero_le (ν₀ : ℝ) (t₁ : ℕ) : envelope ν₀ t₁ 0 ≤ ν₀ := by
  unfold envelope
  rw [if_pos (Nat.zero_le _), pow_zero, one_mul]
  exact min_le_left _ _

/-- The envelope is nonnegative. -/
private theorem envelope_nonneg {ν₀ : ℝ} (hν₀ : 0 ≤ ν₀) (t₁ t : ℕ) : 0 ≤ envelope ν₀ t₁ t := by
  unfold envelope
  split_ifs
  · exact le_min (by positivity) (by norm_num)
  · have : (3 / 4 : ℝ) ^ (t - t₁) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith

/-- After `t₁ + t₂` rounds the envelope is at least `1 − (3/4)^{t₂}/2`. -/
private theorem envelope_final {ν₀ : ℝ} {t₁ : ℕ} (h1 : 1 / 2 ≤ (5 / 4) ^ t₁ * ν₀) (t₂ : ℕ) :
    1 - (3 / 4) ^ t₂ / 2 ≤ envelope ν₀ t₁ (t₁ + t₂) := by
  unfold envelope
  split_ifs with h
  · rw [show t₂ = 0 by omega, pow_zero, add_zero, min_eq_right h1]
    norm_num
  · rw [Nat.add_sub_cancel_left]

/-- One round keeps the imbalance above the envelope, whenever the growth event of the round
holds. -/
private theorem envelope_step {ν₀ α ν ν' : ℝ} {t₁ t : ℕ} (h0 : 120 * α ≤ ν₀) (hν₀ : 0 ≤ ν₀)
    (h1 : 1 / 2 ≤ (5 / 4) ^ t₁ * ν₀) (hg : envelope ν₀ t₁ t ≤ ν)
    (hE : (120 * α ≤ ν → ν ≤ 1 / 2 → 5 / 4 * ν ≤ ν') ∧
      (1 / 2 ≤ ν → 1 - ν' ≤ 3 / 4 * (1 - ν))) :
    envelope ν₀ t₁ (t + 1) ≤ ν' := by
  unfold envelope at hg ⊢
  rcases lt_or_ge ν (1 / 2) with hlt | hge
  · -- below `1/2` the envelope is `(5/4)^t ν₀`, in the first stage
    have ht : t < t₁ := by
      by_contra hcon
      rcases (not_lt.1 hcon).lt_or_eq with htt | htt
      · rw [if_neg (by omega)] at hg
        have : (3 / 4 : ℝ) ^ (t - t₁) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        linarith
      · subst htt
        rw [if_pos le_rfl, min_eq_right h1] at hg
        linarith
    rw [if_pos ht.le] at hg
    rw [if_pos (by omega : t + 1 ≤ t₁)]
    have hpow : (5 / 4 : ℝ) ^ t * ν₀ ≤ ν := by
      rcases min_le_iff.1 hg with h | h
      · exact h
      · linarith
    have h5 : ν₀ ≤ (5 / 4 : ℝ) ^ t * ν₀ := le_mul_of_one_le_left hν₀ (one_le_pow₀ (by norm_num))
    have := hE.1 (by linarith) hlt.le
    calc min ((5 / 4 : ℝ) ^ (t + 1) * ν₀) (1 / 2) ≤ (5 / 4) ^ (t + 1) * ν₀ := min_le_left _ _
      _ = 5 / 4 * ((5 / 4) ^ t * ν₀) := by ring
      _ ≤ ν' := by linarith
  · have h' := hE.2 hge
    by_cases ht : t < t₁
    · rw [if_pos (by omega : t + 1 ≤ t₁)]
      exact (min_le_right _ _).trans (by linarith)
    · rw [if_neg (by omega : ¬t + 1 ≤ t₁), show t + 1 - t₁ = t - t₁ + 1 by omega, pow_succ]
      have hν : 1 - ν ≤ (3 / 4) ^ (t - t₁) / 2 := by
        by_cases htt : t ≤ t₁
        · rw [show t - t₁ = 0 by omega, pow_zero]
          linarith
        · rw [if_neg htt] at hg
          linarith
      linarith

omit [DecidableEq V] in
/-- An imbalance at least `1 − 2c` means a minority at most `c n`. -/
private theorem minority_le_of_imbalance {a : Bool} {z : V → Bool} {c : ℝ}
    (h : 1 - 2 * c ≤ imbalance a z) : (minority a z : ℝ) ≤ c * Fintype.card V := by
  have hsum : (majority a z : ℝ) + minority a z = Fintype.card V := by
    exact_mod_cast majority_add_minority a z
  rcases (Nat.cast_nonneg (Fintype.card V) : (0 : ℝ) ≤ _).eq_or_lt with h0 | hn
  · have : (minority a z : ℝ) = 0 := by
      linarith [Nat.cast_nonneg (α := ℝ) (majority a z), Nat.cast_nonneg (α := ℝ) (minority a z)]
    rw [this, ← h0, mul_zero]
  · unfold imbalance at h
    rw [le_div_iff₀ hn] at h
    linarith

/-- One round of two-sample voting, frozen once the minority is at most `c n`. -/
private noncomputable def frozenStep (a : Bool) (c : ℝ) (y : V → Bool) (r : GraphRound G) :
    V → Bool :=
  if (minority a y : ℝ) ≤ c * Fintype.card V then y else graphStep G y r

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- If the frozen run ends with a minority at most `c n`, then so does a prefix of the run. -/
private theorem exists_take_of_frozen (a : Bool) (c : ℝ) :
    ∀ (l : List (GraphRound G)) (y : V → Bool),
      (minority a (l.foldl (frozenStep a c) y) : ℝ) ≤ c * Fintype.card V →
        ∃ t ≤ l.length, (minority a (graphRun G y (l.take t)) : ℝ) ≤ c * Fintype.card V
  | [], _, h => ⟨0, le_rfl, h⟩
  | r :: l, y, h => by
    by_cases hy : (minority a y : ℝ) ≤ c * Fintype.card V
    · exact ⟨0, Nat.zero_le _, hy⟩
    · rw [List.foldl_cons, frozenStep, if_neg hy] at h
      obtain ⟨t, ht, h'⟩ := exists_take_of_frozen a c l (graphStep G y r) h
      exact ⟨t + 1, by simp [ht], h'⟩

/-- **Phase I from the one-round recursion.** -/
theorem phaseI_of_step {d : ℕ} (hd : 0 < d) (hreg : G.IsRegularOfDegree d) {c α q : ℝ}
    (hc0 : 0 < c) (hα0 : 0 < α) (hq : 0 ≤ q) (a : Bool)
    (hstep : ∀ y : V → Bool, c * Fintype.card V ≤ minority a y → minority a y ≤ majority a y →
      1 - q ≤ avg (fun r : GraphRound G =>
        if (120 * α ≤ imbalance a y → imbalance a y ≤ 1 / 2 →
              5 / 4 * imbalance a y ≤ imbalance a (graphStep G y r)) ∧
           (1 / 2 ≤ imbalance a y →
              1 - imbalance a (graphStep G y r) ≤ 3 / 4 * (1 - imbalance a y))
        then (1 : ℝ) else 0))
    (x : V → Bool) (hν : 120 * α ≤ imbalance a x) :
    1 - (phaseIRounds (imbalance a x) c : ℝ) * q
      ≤ expList (GraphRound G) (phaseIRounds (imbalance a x) c)
          (fun l => if ∃ t ≤ phaseIRounds (imbalance a x) c,
              (minority a (graphRun G x (l.take t)) : ℝ) ≤ c * Fintype.card V
            then (1 : ℝ) else 0) := by
  have hdeg : ∀ v, 0 < G.degree v := fun v => by rw [hreg v]; exact hd
  have := neighborRound_nonempty G hdeg
  have : Nonempty (GraphRound G) := inferInstance
  set ν₀ := imbalance a x
  have hν₀ : 0 < ν₀ := by linarith
  set t₁ := ⌈log (1 / (2 * ν₀)) / log (5 / 4)⌉₊
  set t₂ := ⌈log (1 / (4 * c)) / log (4 / 3)⌉₊
  have hT : phaseIRounds ν₀ c = t₁ + t₂ := rfl
  have h1 : 1 / 2 ≤ (5 / 4) ^ t₁ * ν₀ := half_le_pow_mul hν₀ (Nat.le_ceil _)
  have h2 : (3 / 4) ^ t₂ / 2 ≤ 2 * c := pow_div_two_le hc0 (Nat.le_ceil _)
  -- the targets: the minority is at most `c n`, or the imbalance is above the envelope
  let Gt : ℕ → Set (V → Bool) := fun t =>
    {y | (minority a y : ℝ) ≤ c * Fintype.card V ∨ envelope ν₀ t₁ t ≤ imbalance a y}
  have hfail := expList_escape (frozenStep a c) hq (phaseIRounds ν₀ c) Gt x
    (Or.inr (envelope_zero_le ν₀ t₁)) fun t _ y hy => by
      by_cases hB : (minority a y : ℝ) ≤ c * Fintype.card V
      · have hm : ∀ r : GraphRound G, frozenStep a c y r ∈ Gt (t + 1) := fun r => by
          rw [frozenStep, if_pos hB]
          exact Or.inl hB
        calc _ ≤ avg (fun _ : GraphRound G => (0 : ℝ)) := avg_le_avg fun r => by
              rw [if_pos (hm r)]
          _ = 0 := avg_const 0
          _ ≤ q := hq
      · have hy' : envelope ν₀ t₁ t ≤ imbalance a y := hy.resolve_left hB
        replace hB := not_le.1 hB
        have hBn : (minority a y : ℝ) ≤ Fintype.card V := by
          exact_mod_cast (majority_add_minority a y ▸ Nat.le_add_left _ _)
        have hn : 0 < (Fintype.card V : ℝ) := by
          by_contra hn
          have h0 : (Fintype.card V : ℝ) = 0 := le_antisymm (not_lt.1 hn) (Nat.cast_nonneg _)
          rw [h0, mul_zero] at hB
          linarith
        have hBA : minority a y ≤ majority a y := by
          have := (envelope_nonneg hν₀.le t₁ t).trans hy'
          unfold imbalance at this
          rw [le_div_iff₀ hn, zero_mul, sub_nonneg] at this
          exact_mod_cast this
        refine avg_le_of_le_one_sub (hstep y hB.le hBA) fun r => ?_
        split_ifs with hm hE hE
        · norm_num
        · norm_num
        · refine absurd ?_ hm
          show _ ∨ _
          rw [frozenStep, if_neg (not_le.2 hB)]
          exact Or.inr (envelope_step hν hν₀.le h1 hy' hE)
        · norm_num
  refine (sub_le_sub_left hfail 1).trans (one_sub_expList_le fun l hl => ?_)
  have hfin : l.foldl (frozenStep a c) x ∈ Gt (phaseIRounds ν₀ c) →
      (minority a (l.foldl (frozenStep a c) x) : ℝ) ≤ c * Fintype.card V := fun hm =>
    hm.elim id fun h => minority_le_of_imbalance <| by
      have := envelope_final h1 t₂
      rw [← hT] at this
      linarith
  split_ifs with hm hex
  · norm_num
  · obtain ⟨t, ht, h⟩ := exists_take_of_frozen a c l x (hfin hm)
    exact absurd ⟨t, hl ▸ ht, h⟩ hex
  · norm_num
  · norm_num

end Median.ExpanderGeneral
