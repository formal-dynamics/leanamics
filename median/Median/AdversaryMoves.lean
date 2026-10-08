import Median.AdversaryDefs
import Median.AdversaryPerturbed
import Median.AnyStartPhases

/-! # Adversary: one-round moves of 2-Choices under recolourings

The one-round estimates behind `binary_almost_stable` (`Median/Adversary.lean`). An adversary
that recolours at most `F` nodes changes the number of `true` nodes by at most `F`
(`abs_ones_sub_le`), hence the gap `g = #true - #false` by at most `2F` and the minority by at
most `F`. With `F ≤ √n/1024` this costs little in each of the moves of the adversary-free proof:

* `gapPot_le_of_hammingDist`: the potential `gapPot = exp (-|g|/(256 √n))` grows by at most a
  factor `e^{1/131072}`, so `avg_gapPot_perturbed` still contracts it by `e^{-1/131072}` per round;
* `growth_move_gap`: from `G ≤ g ≤ n/2` the next gap is at least `5G/4` except with probability
  `n⁻²` (the Hoeffding step of `growth_move_big`, without its alternative conclusion);
* `adv_growth_move`: with recolourings, the gap grows from `G` to `min (9G/8) (17n/32)`;
* `adv_sat_move`: with recolourings, the minority shrinks from `t` to `max (15t/16) K`, where
  `K = max (16 F) (1024 log n)` (`sat_move`, Bernstein).

The flip symmetry (`isAdvRun_flip`, `notAlmostStable_flip`) reduces a negative gap to a positive
one.
-/

namespace Median
open Finset Real Dynamics

variable {n : ℕ}

/-! ### Recolourings and the counts -/

/-- Recolouring changes the number of `true` nodes by at most the number of recoloured nodes. -/
lemma ones_le_add_hammingDist (z z' : Config n Bool) :
    (ones z : ℝ) ≤ ones z' + hammingDist z z' := by
  have h : (univ.filter fun v => z v = true)
      ⊆ (univ.filter fun v => z' v = true) ∪ (univ.filter fun v => z v ≠ z' v) := by
    intro v hv
    simp only [mem_filter, mem_univ, true_and, mem_union] at hv ⊢
    by_cases h' : z' v = true
    · exact Or.inl h'
    · exact Or.inr (by rw [hv]; exact fun e => h' e.symm)
  have hc := (card_le_card h).trans (card_union_le _ _)
  have : ones z ≤ ones z' + hammingDist z z' := hc
  exact_mod_cast this

/-- `|#true z - #true z'| ≤ hammingDist z z'`. -/
lemma abs_ones_sub_le (z z' : Config n Bool) :
    |(ones z : ℝ) - ones z'| ≤ hammingDist z z' := by
  have h1 := ones_le_add_hammingDist z z'
  have h2 := ones_le_add_hammingDist z' z
  rw [hammingDist_comm] at h2
  rw [abs_le]
  constructor <;> linarith

/-- Recolouring `F` nodes moves the gap by at most `2F`. -/
lemma abs_gapR_sub_le (z z' : Config n Bool) :
    |gapR z - gapR z'| ≤ 2 * hammingDist z z' := by
  have h := abs_ones_sub_le z z'
  rw [gapR_two, gapR_two, show 2 * (ones z : ℝ) - n - (2 * ones z' - n)
    = 2 * ((ones z : ℝ) - ones z') by ring, abs_mul, abs_two]
  linarith

/-- Recolouring `F` nodes raises the number of `false` nodes by at most `F`. -/
lemma falsesR_le_add (z z' : Config n Bool) : falsesR z ≤ falsesR z' + hammingDist z z' := by
  have h := ones_le_add_hammingDist z' z
  rw [hammingDist_comm] at h
  unfold falsesR
  linarith

/-- The number of nodes not holding `true` is the number of `false` nodes. -/
lemma card_ne_true (y : Config n Bool) :
    ((univ.filter fun v => y v ≠ true).card : ℝ) = falsesR y := by
  have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun v => y v = true)
  rw [card_univ, Fintype.card_fin] at h
  have h' : ((univ.filter fun v => y v = true).card : ℝ)
      + ((univ.filter fun v => ¬ y v = true).card : ℝ) = n := by exact_mod_cast h
  unfold falsesR ones
  linarith

/-- `notAlmostStable` is the failure indicator of almost stable consensus. -/
lemma notAlmostStable_eq {α : Type*} [LinearOrder α] (K : ℝ) (T₀ H : ℕ)
    (P : List (Round n) → Config n α) (l : List (Round n)) :
    notAlmostStable K T₀ H P l
      = failInd (∃ b : α, ∀ t, T₀ ≤ t → t ≤ T₀ + H → AlmostConsensus K b (P (l.take t))) :=
  rfl

/-! ### Flip symmetry -/

/-- Flipping both configurations keeps the Hamming distance. -/
lemma hammingDist_flip (a b : Config n Bool) :
    hammingDist (fun v => !a v) (fun v => !b v) = hammingDist a b := by
  unfold hammingDist
  congr 1
  ext v
  simp

/-- The flip of a perturbed run is a perturbed run of the flipped start. -/
lemma isAdvRun_flip {F : ℕ} {y : Config n Bool} {Q : List (Round n) → Config n Bool}
    (hQ : IsAdvRun F y Q) : IsAdvRun F (fun v => !y v) (fun l v => !Q l v) := by
  refine ⟨by funext v; simp [hQ.1], fun l r => ?_⟩
  rw [step_flip, hammingDist_flip]
  exact hQ.2 l r

/-- Almost consensus of the flip on `b` is almost consensus on `!b`. -/
lemma almostConsensus_flip {K : ℝ} {b : Bool} {y : Config n Bool} :
    AlmostConsensus K b (fun v => !y v) ↔ AlmostConsensus K (!b) y := by
  unfold AlmostConsensus
  have e : (univ.filter fun v => (!y v) ≠ b) = univ.filter fun v => y v ≠ !b := by
    ext v
    cases y v <;> cases b <;> simp
  rw [e]

/-- Almost stable consensus does not see the flip. -/
lemma notAlmostStable_flip (K : ℝ) (T₀ H : ℕ) (Q : List (Round n) → Config n Bool)
    (l : List (Round n)) :
    notAlmostStable K T₀ H (fun l v => !Q l v) l = notAlmostStable K T₀ H Q l := by
  have e : (∃ b : Bool, ∀ t, T₀ ≤ t → t ≤ T₀ + H →
        AlmostConsensus K b (fun v => !Q (l.take t) v))
      ↔ ∃ b : Bool, ∀ t, T₀ ≤ t → t ≤ T₀ + H → AlmostConsensus K b (Q (l.take t)) := by
    constructor
    · rintro ⟨b, hb⟩
      exact ⟨!b, fun t h1 h2 => almostConsensus_flip.mp (hb t h1 h2)⟩
    · rintro ⟨b, hb⟩
      refine ⟨!b, fun t h1 h2 => almostConsensus_flip.mpr ?_⟩
      rw [Bool.not_not]
      exact hb t h1 h2
  rw [notAlmostStable_eq, notAlmostStable_eq]
  exact congrArg failInd (propext e)

/-- A perturbed run is a `Perturbed` process of the median rule. -/
lemma IsAdvRun.perturbed {α : Type*} [LinearOrder α] {F : ℕ} {x : Config n α}
    {P : List (Round n) → Config n α} (hP : IsAdvRun F x P) :
    Perturbed step (fun z z' => hammingDist z' z ≤ F) x P := hP

variable [NeZero n]

/-! ### From kernel probabilities to failure indicators -/

/-- A one-round success probability `≥ 1 - ε` bounds the average failure indicator by `ε`. -/
lemma avg_failInd_step_le {x : Config n Bool} {P : Config n Bool → Prop} {ε : ℝ}
    (h : 1 - ε ≤ (Median.kernel n Bool x).prob P) :
    avg (fun r : Round n => failInd (P (step x r))) ≤ ε := by
  classical
  rw [Median.kernel, Kernel.prob_ofStep] at h
  have e : ∀ r : Round n, failInd (P (step x r))
      = 1 - (if P (step x r) then (1 : ℝ) else 0) := by
    intro r
    by_cases hp : P (step x r)
    · rw [failInd_of hp, if_pos hp]; norm_num
    · rw [failInd_of_not hp, if_neg hp]; norm_num
  simp_rw [e]
  rw [avg_sub, avg_const]
  convert (show 1 - avg (fun r : Round n => if P (step x r) then (1 : ℝ) else 0) ≤ ε by
    linarith) using 3

/-! ### The potential under recolourings -/

/-- Recolouring at most `F ≤ √n/1024` nodes multiplies `gapPot` by at most `e^{1/131072}`. -/
lemma gapPot_le_of_hammingDist {F : ℕ} (hF : 1024 * (F : ℝ) ≤ √(n : ℝ)) {z z' : Config n Bool}
    (h : hammingDist z' z ≤ F) : gapPot z' ≤ exp (1 / 131072) * gapPot z := by
  have hs := sqrt_cast_pos (n := n)
  have hd := abs_gapR_sub_le z' z
  have hF' : ((hammingDist z' z : ℕ) : ℝ) ≤ F := by exact_mod_cast h
  have habs : |gapR z| - 2 * F ≤ |gapR z'| := by
    have := abs_sub_abs_le_abs_sub (gapR z) (gapR z')
    rw [abs_sub_comm] at this
    linarith
  unfold gapPot
  rw [← exp_add, exp_le_exp]
  have h1 : (|gapR z| - 2 * F) / (256 * √(n : ℝ)) ≤ |gapR z'| / (256 * √(n : ℝ)) :=
    div_le_div_of_nonneg_right habs (by positivity)
  have h2 : 2 * (F : ℝ) / (256 * √(n : ℝ)) ≤ 1 / 131072 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have h3 : (|gapR z| - 2 * F) / (256 * √(n : ℝ))
      = |gapR z| / (256 * √(n : ℝ)) - 2 * F / (256 * √(n : ℝ)) := sub_div _ _ _
  linarith

/-- **Drift of the potential against the adversary.** For `n ≥ 10` and `F ≤ √n/1024`, one
round followed by at most `F` recolourings contracts the expected potential by `e^{-1/131072}`,
up to the additive error `e^{1/65536 - √n/512}`. -/
lemma avg_gapPot_perturbed (hn : (10 : ℝ) ≤ n) {F : ℕ} (hF : 1024 * (F : ℝ) ≤ √(n : ℝ))
    (y : Config n Bool) (g : Round n → Config n Bool)
    (hg : ∀ r, hammingDist (g r) (step y r) ≤ F) :
    avg (fun r => gapPot (g r))
      ≤ exp (-(1 / 131072)) * gapPot y + exp (1 / 65536 - √(n : ℝ) / 512) := by
  calc avg (fun r => gapPot (g r)) ≤ avg (fun r => exp (1 / 131072) * gapPot (step y r)) :=
        avg_le_avg fun r => gapPot_le_of_hammingDist hF (hg r)
    _ = exp (1 / 131072) * avg (fun r => gapPot (step y r)) := avg_const_mul _ _
    _ ≤ exp (1 / 131072)
          * (exp (-(1 / 65536)) * gapPot y + exp (1 / 131072 - √(n : ℝ) / 512)) :=
        mul_le_mul_of_nonneg_left (avg_gapPot_step hn y) (exp_pos _).le
    _ = exp (-(1 / 131072)) * gapPot y + exp (1 / 65536 - √(n : ℝ) / 512) := by
        rw [mul_add, ← mul_assoc, ← exp_add, ← exp_add,
          show (1 : ℝ) / 131072 + -(1 / 65536) = -(1 / 131072) by norm_num,
          show (1 : ℝ) / 131072 + (1 / 131072 - √(n : ℝ) / 512) = 1 / 65536 - √(n : ℝ) / 512 by
            ring]

/-! ### Growth and saturation moves -/

/-- **Growth of the gap.** From `G ≤ g ≤ n/2` with `G² ≥ 16384 n log n`, one round gives a gap
at least `5G/4` except with probability `n⁻²` (Hoeffding's lower tail for the `true` nodes; the
argument of `growth_move_big`). -/
lemma growth_move_gap (hL : (128 : ℝ) ≤ log n) {G : ℝ} (hG0 : 0 ≤ G)
    (hG2 : 16384 * (n : ℝ) * log n ≤ G ^ 2) {x : Config n Bool}
    (hg : G ≤ gapR x) (hgn : gapR x ≤ (n : ℝ) / 2) :
    avg (fun r : Round n => failInd (5 / 4 * G ≤ gapR (step x r))) ≤ 1 / (n : ℝ) ^ 2 := by
  have hn : 1 ≤ n := one_le_of_log_pos (lt_of_lt_of_le (by norm_num) hL)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hg0 : 0 ≤ gapR x := le_trans hG0 hg
  have hE : (n : ℝ) / 2 + 11 / 16 * gapR x ≤ ∑ v, avg (coord x v) := expones_ge x hg0 hgn
  have hlam : 0 ≤ G / 16 := by positivity
  have hbad : avg (fun r : Round n =>
      if (ones (step x r) : ℝ) + G / 16 ≤ ∑ v, avg (coord x v) then (1 : ℝ) else 0)
      ≤ exp (-(2 * (G / 16) ^ 2 / n)) := ones_tail_lower x hlam
  have hkey : 2 * log n ≤ 2 * (G / 16) ^ 2 / n := by
    rw [le_div_iff₀ hn0]
    nlinarith
  have hpt : ∀ r : Round n, failInd (5 / 4 * G ≤ gapR (step x r))
      ≤ if (ones (step x r) : ℝ) + G / 16 ≤ ∑ v, avg (coord x v) then (1 : ℝ) else 0 := by
    intro r
    by_cases h : 5 / 4 * G ≤ gapR (step x r)
    · rw [failInd_of h]
      split_ifs <;> norm_num
    · rw [failInd_of_not h, if_pos]
      have hones : (ones (step x r) : ℝ) = ((n : ℝ) + gapR (step x r)) / 2 := by
        have h1 := falses_plus_ones (step x r)
        have h2 := gapR_eq (step x r)
        linarith
      nlinarith
  calc avg (fun r : Round n => failInd (5 / 4 * G ≤ gapR (step x r)))
      ≤ avg (fun r : Round n =>
          if (ones (step x r) : ℝ) + G / 16 ≤ ∑ v, avg (coord x v) then (1 : ℝ) else 0) :=
        avg_le_avg hpt
    _ ≤ exp (-(2 * (G / 16) ^ 2 / n)) := hbad
    _ ≤ 1 / (n : ℝ) ^ 2 := exp_le_inv_sq hn hkey

/-- **Growth against the adversary.** For `F ≤ √n/1024` and `128 √(n log n) ≤ G ≤ 17n/32`,
from a gap at least `G`, one round followed by at most `F` recolourings gives a gap at least
`min (9G/8) (17n/32)` except with probability `n⁻²`. -/
lemma adv_growth_move (hL : (128 : ℝ) ≤ log n) {F : ℕ} (hF : 1024 * (F : ℝ) ≤ √(n : ℝ))
    {G : ℝ} (hG : 128 * √((n : ℝ) * log n) ≤ G) (hGn : G ≤ 17 * (n : ℝ) / 32)
    {y : Config n Bool} (hy : G ≤ gapR y) (g : Round n → Config n Bool)
    (hg : ∀ r, hammingDist (g r) (step y r) ≤ F) :
    avg (fun r => failInd (min (9 / 8 * G) (17 * (n : ℝ) / 32) ≤ gapR (g r)))
      ≤ 1 / (n : ℝ) ^ 2 := by
  have hn : 1 ≤ n := one_le_of_log_pos (lt_of_lt_of_le (by norm_num) hL)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hL0 : 0 ≤ log n := by linarith
  have hbig := big_log_le hL
  have hs := sqrt_cast_pos (n := n)
  -- `√n ≤ G/128` and `√n ≤ n/16`, so `2F ≤ G/8` and `2F ≤ n/32`
  have hsG : √(n : ℝ) ≤ G / 128 := by
    have : √(n : ℝ) ≤ √((n : ℝ) * log n) :=
      sqrt_le_sqrt (le_mul_of_one_le_right hn0.le (by linarith))
    linarith
  have hsn : √(n : ℝ) ≤ (n : ℝ) / 16 := by
    rw [sqrt_le_left (by positivity)]
    nlinarith
  have hF2G : 2 * (F : ℝ) ≤ G / 8 := by nlinarith
  have hF2n : 2 * (F : ℝ) ≤ (n : ℝ) / 32 := by nlinarith
  have hG0 : 0 ≤ G := le_trans (by positivity) hG
  have hG2 : 16384 * (n : ℝ) * log n ≤ G ^ 2 := by
    have h1 : (128 * √((n : ℝ) * log n)) ^ 2 = 16384 * ((n : ℝ) * log n) := by
      rw [mul_pow, sq_sqrt (by positivity)]
      norm_num
    nlinarith [pow_le_pow_left₀ (by positivity) hG 2]
  -- pointwise: the recolouring costs at most `2F` of the gap
  have hpt : ∀ r, failInd (min (9 / 8 * G) (17 * (n : ℝ) / 32) ≤ gapR (g r))
      ≤ failInd (min (5 / 4 * G) (9 * (n : ℝ) / 16) ≤ gapR (step y r)) := by
    intro r
    refine failInd_mono fun h => ?_
    have hd := abs_gapR_sub_le (g r) (step y r)
    have hF' : ((hammingDist (g r) (step y r) : ℕ) : ℝ) ≤ F := by exact_mod_cast hg r
    have hlow : gapR (step y r) - 2 * F ≤ gapR (g r) := by
      have := neg_abs_le (gapR (g r) - gapR (step y r))
      linarith
    rcases le_total (5 / 4 * G) (9 * (n : ℝ) / 16) with hm | hm
    · rw [min_eq_left hm] at h
      exact min_le_of_left_le (by linarith)
    · rw [min_eq_right hm] at h
      exact min_le_of_right_le (by linarith)
  refine le_trans (avg_le_avg hpt) ?_
  have hgap : ∀ z : Config n Bool, gapR z = (n : ℝ) - 2 * falsesR z := fun z => by
    have h1 := falses_plus_ones z
    have h2 := gapR_eq z
    linarith
  rcases le_or_gt (gapR y) ((n : ℝ) / 2) with hyn | hyn
  · -- below `n/2`: the gap grows by `5/4`
    refine le_trans (avg_le_avg fun r => failInd_mono fun h => min_le_of_left_le h) ?_
    exact growth_move_gap hL hG0 hG2 hy hyn
  · -- above `n/2`: the minority is below `n/4`, and `sat_move` brings it below `7n/32`
    have hm : falsesR y < (n : ℝ) / 4 := by rw [hgap] at hyn; linarith
    have hsat := avg_failInd_step_le (sat_move hL (by positivity) le_rfl hm)
    refine le_trans (avg_le_avg fun r => failInd_mono fun h => ?_) hsat
    have h' : falsesR (step y r) < max (7 / 8 * ((n : ℝ) / 4)) (512 * log n) := h
    have hmax : max (7 / 8 * ((n : ℝ) / 4)) (512 * log n) = 7 / 8 * ((n : ℝ) / 4) :=
      max_eq_left (by linarith)
    rw [hmax] at h'
    exact min_le_of_right_le (by rw [hgap]; linarith)

/-- **Saturation against the adversary.** Let `K = max (16 F) (1024 log n)`. For
`K ≤ t ≤ n/4`, from a minority below `t`, one round followed by at most `F` recolourings
leaves a minority below `max (15t/16) K` except with probability `n⁻²`. -/
lemma adv_sat_move (hL : (128 : ℝ) ≤ log n) {F : ℕ} {t : ℝ}
    (hKt : max (16 * (F : ℝ)) (1024 * log n) ≤ t) (htn : t ≤ (n : ℝ) / 4)
    {y : Config n Bool} (hy : falsesR y < t) (g : Round n → Config n Bool)
    (hg : ∀ r, hammingDist (g r) (step y r) ≤ F) :
    avg (fun r => failInd (falsesR (g r) < max (15 / 16 * t) (max (16 * (F : ℝ))
      (1024 * log n)))) ≤ 1 / (n : ℝ) ^ 2 := by
  have hL0 : 0 ≤ log n := by linarith
  have hK1 := le_trans (le_max_left _ _) hKt
  have hK2 := le_trans (le_max_right _ _) hKt
  have hsat := avg_failInd_step_le (sat_move hL (by linarith) htn hy)
  refine le_trans (avg_le_avg fun r => failInd_mono fun h => ?_) hsat
  have h' : falsesR (step y r) < max (7 / 8 * t) (512 * log n) := h
  have hd := falsesR_le_add (g r) (step y r)
  have hF' : ((hammingDist (g r) (step y r) : ℕ) : ℝ) ≤ F := by exact_mod_cast hg r
  rcases le_total (7 / 8 * t) (512 * log n) with hm | hm
  · rw [max_eq_right hm] at h'
    refine lt_of_lt_of_le ?_ (le_max_right _ _)
    have := le_max_left (16 * (F : ℝ)) (1024 * log n)
    have := le_max_right (16 * (F : ℝ)) (1024 * log n)
    linarith
  · rw [max_eq_left hm] at h'
    exact lt_of_lt_of_le (by linarith) (le_max_left _ _)

end Median
