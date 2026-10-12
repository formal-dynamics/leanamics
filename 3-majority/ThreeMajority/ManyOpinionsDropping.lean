import ThreeMajority.ManyOpinionsExpect
import ThreeMajority.ManyOpinionsTails
import Dynamics.Rounds

/-!
# The dropping stage (BCNPT16, Lemmas 3.4 and 3.5; roadmap MAJ-12 (a))

Becchetti, Clementi, Natale, Pasquale, Trevisan, *Stabilizing consensus with many opinions*,
SODA 2016, arXiv:1508.06782 (BCNPT16 below), Section 3. Once a colour `a` is below
`n/j − 16 √(j n log n)` agents in a configuration with at most `j` colours, Lemma 2.1 makes it
shrink geometrically: its gap to the average `n/j` grows by a factor `1 + 1/(4j)` per round, and
below `n/(2j)` the support itself shrinks by a factor `1 − 1/(2j)`.

* `dropping_stage1`: **Lemma 3.4**. Within `O(j log n)` rounds the support of `a` is
  `O(j² log n)`, with probability at least `1 − 1/n` (at every time `t` with
  `C j log n ≤ t ≤ n`).
* `dropping_stage2`: **Lemma 3.5**. From at most `n/(2j)` agents, colour `a` dies within
  `O(j log n)` rounds with probability at least `1/2`.

One-round estimates (Chernoff upper tails, `avg_colourCount_stepCol_ge`): below `n/(2j)` the
support shrinks by `1 − 1/(4j)` (`avg_colourCount_stepCol_ge_shrink`), between `n/(2j)` and `n/j`
the gap to `n/j` grows by `1 + 1/(4j)` (`avg_colourCount_stepCol_ge_gap`). Lemma 3.4 follows them
along one moving target `stage1Level` (`stage1_step`, `Dynamics.expList_escape`); Lemma 3.5
iterates the contraction of `min(c_a, n/(2j))` (`expList_min_colourCount_le`, BCNPT16,
Appendix B) and applies Markov's inequality.

Both assume `C j³ log n ≤ n`, implied by the paper's `j ≤ n^{1/3 − ε}` for large `n`. The proof of
Lemma 3.4 needs a minor correction: from the paper's threshold `n/j − √(j n log n)` the one-round
Chernoff bound (Appendix B, Equation (7)) only gives failure probability `n^{-1/12}`, still at least
`n^{-1/10}` during the first `j/10` rounds, so the iterated union bound exceeds `1` as soon as
`j ≥ 20 n^{1/10}`, and the same happens near the floor `j² log n`. With the threshold
`n/j − 16 √(j n log n)` and the floor `C j² log n` for a large `C` the failure is at most `n^{-5}`
per round.
-/

namespace ThreeMajority

open Finset Dynamics

section OneRound

variable {n : ℕ} [NeZero n]

/-- From at most `j` colours and `c_a ≤ b ≤ n/(2j)`, the expected new support of `a` is at most
`(1 − 1/(2j)) b` (Lemma 2.1). -/
lemma avg_colourCount_stepCol_le_half {y : Fin n → Fin n} {a : Fin n} {j : ℕ} (hj : 1 ≤ j)
    (hy : numColours y ≤ j) {b : ℝ} (hb0 : 0 ≤ b) (hb : b ≤ n / (2 * j))
    (hya : (colourCount y a : ℝ) ≤ b) :
    avg (fun r : Tgt3 n => (colourCount (stepCol y r) a : ℝ)) ≤ (1 - 1 / (2 * (j : ℝ))) * b := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  refine (avg_colourCount_stepCol_le_of_le y a hy hya).trans ?_
  have hbn : b / n ≤ 1 / (2 * j) := by
    rw [div_le_iff₀ hn]
    calc b ≤ n / (2 * j) := hb
      _ = 1 / (2 * j) * n := by ring
  have e : 1 / (j : ℝ) = 2 * (1 / (2 * j)) := by field_simp
  calc b * (1 + b / n - 1 / j) ≤ b * (1 - 1 / (2 * j)) :=
        mul_le_mul_of_nonneg_left (by linarith) hb0
    _ = _ := by ring

/-- **One round below `n/(2j)`** (Chernoff upper tail): from at most `j` colours and
`c_a ≤ b ≤ n/(2j)`, the new support of `a` reaches `b (1 − 1/(4j))` with probability at most
`exp(−b/(32 j²))`. -/
lemma avg_colourCount_stepCol_ge_shrink {y : Fin n → Fin n} {a : Fin n} {j : ℕ} (hj : 1 ≤ j)
    (hy : numColours y ≤ j) {b : ℝ} (hb0 : 0 < b) (hb : b ≤ n / (2 * j))
    (hya : (colourCount y a : ℝ) ≤ b) :
    avg (fun r : Tgt3 n =>
        if b * (1 - 1 / (4 * (j : ℝ))) ≤ (colourCount (stepCol y r) a : ℝ) then (1 : ℝ) else 0) ≤
      Real.exp (-(b / (32 * (j : ℝ) ^ 2))) := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hmean := avg_colourCount_stepCol_le_half hj hy hb0.le hb hya
  have h2j : 1 / (2 * (j : ℝ)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have h4j : 0 < 1 / (4 * (j : ℝ)) := by positivity
  have e1 : b * (1 - 1 / (4 * (j : ℝ))) - (1 - 1 / (2 * (j : ℝ))) * b = b / (4 * j) := by
    field_simp
    ring
  have hμ0 : 0 < (1 - 1 / (2 * (j : ℝ))) * b := mul_pos (by linarith) hb0
  have hμk : (1 - 1 / (2 * (j : ℝ))) * b < b * (1 - 1 / (4 * (j : ℝ))) := by
    have : 0 < b / (4 * j) := by positivity
    linarith
  refine (avg_colourCount_stepCol_ge y a hμ0 hμk hmean).trans
    (Real.exp_le_exp.mpr (neg_le_neg ?_))
  have hsum : b * (1 - 1 / (4 * (j : ℝ))) + (1 - 1 / (2 * (j : ℝ))) * b ≤ 2 * b := by
    have : 0 < 1 / (2 * (j : ℝ)) := by positivity
    nlinarith
  rw [e1, le_div_iff₀ (by linarith)]
  calc b / (32 * (j : ℝ) ^ 2) * (b * (1 - 1 / (4 * (j : ℝ))) + (1 - 1 / (2 * (j : ℝ))) * b)
      ≤ b / (32 * (j : ℝ) ^ 2) * (2 * b) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (b / (4 * j)) ^ 2 := by field_simp; ring

end OneRound

section Stage2

variable {n : ℕ} [NeZero n]

/-- The potential `ψ = min(c_a, n/(2j))` of Lemma 3.5 contracts by `1 − 1/(2j)` per round, up to
the event that `c_a` is above `n/(2j)`. -/
lemma avg_min_colourCount_stepCol_le {y : Fin n → Fin n} {a : Fin n} {j : ℕ} (hj : 1 ≤ j)
    (hy : numColours y ≤ j) :
    avg (fun r : Tgt3 n => min (colourCount (stepCol y r) a : ℝ) (n / (2 * j))) ≤
      (1 - 1 / (2 * (j : ℝ))) * min (colourCount y a : ℝ) (n / (2 * j)) +
        n / (4 * (j : ℝ) ^ 2) * (if (n : ℝ) / (2 * j) < colourCount y a then 1 else 0) := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  by_cases h : (colourCount y a : ℝ) ≤ n / (2 * j)
  · rw [min_eq_left h, if_neg (not_lt.mpr h), mul_zero, add_zero]
    calc _ ≤ avg (fun r : Tgt3 n => (colourCount (stepCol y r) a : ℝ)) :=
          avg_le_avg fun r => min_le_left _ _
      _ ≤ _ := avg_colourCount_stepCol_le_half hj hy (Nat.cast_nonneg _) h le_rfl
  · push Not at h
    rw [min_eq_right h.le, if_pos h, mul_one]
    calc _ ≤ avg (fun _ : Tgt3 n => (n : ℝ) / (2 * j)) := avg_le_avg fun r => min_le_right _ _
      _ = (n : ℝ) / (2 * j) := avg_const _
      _ = _ := by field_simp; ring

/-- Union bound over rounds: from `c_a ≤ n/(2j)` and at most `j` colours, if every round from
such a state takes `c_a` above `n/(2j)` with probability at most `ε`, then after `s` rounds
`c_a > n/(2j)` with probability at most `s ε`. -/
lemma expList_colourCount_gt_half_le {x : Fin n → Fin n} {a : Fin n} {j : ℕ}
    (hx : numColours x ≤ j) (hxa : (colourCount x a : ℝ) ≤ n / (2 * j)) {ε : ℝ} (hε : 0 ≤ ε)
    (hesc : ∀ y : Fin n → Fin n, numColours y ≤ j → (colourCount y a : ℝ) ≤ n / (2 * j) →
      avg (fun r : Tgt3 n =>
        if (n : ℝ) / (2 * j) < colourCount (stepCol y r) a then (1 : ℝ) else 0) ≤ ε)
    (s : ℕ) :
    expList (Tgt3 n) s
        (fun l => if (n : ℝ) / (2 * j) < colourCount (runCol x l) a then (1 : ℝ) else 0) ≤
      s * ε := by
  have key := Dynamics.expList_escape (stepCol (n := n) (σ := Fin n)) hε s
    (fun _ => {y | numColours y ≤ j ∧ (colourCount y a : ℝ) ≤ n / (2 * j)}) x ⟨hx, hxa⟩
    (fun t _ y hy => by
      refine le_trans (Dynamics.avg_le_avg fun r => ?_) (hesc y hy.1 hy.2)
      by_cases h2 : (n : ℝ) / (2 * j) < colourCount (stepCol y r) a
      · rw [if_pos h2]
        split_ifs <;> norm_num
      · rw [if_neg h2, if_pos (show stepCol y r ∈
            {y | numColours y ≤ j ∧ (colourCount y a : ℝ) ≤ n / (2 * j)} from
            ⟨(numColours_stepCol_le y r).trans hy.1, not_lt.mp h2⟩)])
  refine le_trans (expList_le_expList fun l => ?_) key
  rw [runCol_eq_foldl]
  split_ifs with h1 h2
  · exact absurd h2.2 (not_le.mpr h1)
  · norm_num
  · norm_num
  · norm_num

/-- The recursion of Lemma 3.5 (BCNPT16, Appendix B): `𝔼 ψ(x_s) ≤ (1 − 1/(2j))^s n/(2j) +
(n/(4j²)) ε s²`. -/
lemma expList_min_colourCount_le {x : Fin n → Fin n} {a : Fin n} {j : ℕ} (hj : 1 ≤ j)
    (hx : numColours x ≤ j) (hxa : (colourCount x a : ℝ) ≤ n / (2 * j)) {ε : ℝ} (hε : 0 ≤ ε)
    (hesc : ∀ y : Fin n → Fin n, numColours y ≤ j → (colourCount y a : ℝ) ≤ n / (2 * j) →
      avg (fun r : Tgt3 n =>
        if (n : ℝ) / (2 * j) < colourCount (stepCol y r) a then (1 : ℝ) else 0) ≤ ε)
    (s : ℕ) :
    expList (Tgt3 n) s (fun l => min (colourCount (runCol x l) a : ℝ) (n / (2 * j))) ≤
      (1 - 1 / (2 * (j : ℝ))) ^ s * (n / (2 * j)) + n / (4 * (j : ℝ) ^ 2) * ε * s ^ 2 := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hρ0 : 0 ≤ 1 - 1 / (2 * (j : ℝ)) := by
    have : 1 / (2 * (j : ℝ)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  have hρ1 : 1 - 1 / (2 * (j : ℝ)) ≤ 1 := by
    have : 0 ≤ 1 / (2 * (j : ℝ)) := by positivity
    linarith
  have hK0 : 0 ≤ (n : ℝ) / (4 * (j : ℝ) ^ 2) := by positivity
  induction s with
  | zero =>
    simp only [expList_zero, runCol_nil, pow_zero, one_mul, CharP.cast_eq_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero]
    exact min_le_right _ _
  | succ s ih =>
    rw [expList_append s 1]
    have hpt : ∀ l₁ : List (Tgt3 n), expList (Tgt3 n) 1
        (fun l₂ => min (colourCount (runCol x (l₁ ++ l₂)) a : ℝ) (n / (2 * j))) ≤
        (1 - 1 / (2 * (j : ℝ))) * min (colourCount (runCol x l₁) a : ℝ) (n / (2 * j)) +
          n / (4 * (j : ℝ) ^ 2) *
            (if (n : ℝ) / (2 * j) < colourCount (runCol x l₁) a then 1 else 0) := by
      intro l₁
      rw [expList_succ]
      simp only [expList_zero, runCol_append, runCol_cons, runCol_nil]
      exact avg_min_colourCount_stepCol_le hj ((numColours_runCol_le x l₁).trans hx)
    have hesc' := expList_colourCount_gt_half_le hx hxa hε hesc s
    have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
    calc _ ≤ expList (Tgt3 n) s (fun l₁ =>
          (1 - 1 / (2 * (j : ℝ))) * min (colourCount (runCol x l₁) a : ℝ) (n / (2 * j)) +
            n / (4 * (j : ℝ) ^ 2) *
              (if (n : ℝ) / (2 * j) < colourCount (runCol x l₁) a then 1 else 0)) :=
          expList_le_expList hpt
      _ = (1 - 1 / (2 * (j : ℝ))) * expList (Tgt3 n) s
            (fun l => min (colourCount (runCol x l) a : ℝ) (n / (2 * j))) +
          n / (4 * (j : ℝ) ^ 2) * expList (Tgt3 n) s
            (fun l => if (n : ℝ) / (2 * j) < colourCount (runCol x l) a then (1 : ℝ) else 0) := by
          rw [expList_add, expList_const_mul, expList_const_mul]
      _ ≤ (1 - 1 / (2 * (j : ℝ))) * ((1 - 1 / (2 * (j : ℝ))) ^ s * (n / (2 * j)) +
            n / (4 * (j : ℝ) ^ 2) * ε * s ^ 2) + n / (4 * (j : ℝ) ^ 2) * (s * ε) :=
          add_le_add (mul_le_mul_of_nonneg_left ih hρ0) (mul_le_mul_of_nonneg_left hesc' hK0)
      _ ≤ _ := by
          have hKε : 0 ≤ (n : ℝ) / (4 * (j : ℝ) ^ 2) * ε := mul_nonneg hK0 hε
          have h1 : (1 - 1 / (2 * (j : ℝ))) * ((n : ℝ) / (4 * (j : ℝ) ^ 2) * ε * s ^ 2) ≤
              (n : ℝ) / (4 * (j : ℝ) ^ 2) * ε * s ^ 2 := by
            have := mul_le_mul_of_nonneg_right hρ1 (mul_nonneg hKε (sq_nonneg (s : ℝ)))
            linarith
          have h2 : (n : ℝ) / (4 * (j : ℝ) ^ 2) * ε * s ^ 2 + n / (4 * (j : ℝ) ^ 2) * (s * ε) ≤
              (n : ℝ) / (4 * (j : ℝ) ^ 2) * ε * ((s + 1 : ℕ) : ℝ) ^ 2 := by
            push_cast
            nlinarith
          have e : (1 - 1 / (2 * (j : ℝ))) * ((1 - 1 / (2 * (j : ℝ))) ^ s * (n / (2 * j)) +
              n / (4 * (j : ℝ) ^ 2) * ε * s ^ 2) = (1 - 1 / (2 * (j : ℝ))) ^ (s + 1) *
                (n / (2 * j)) + (1 - 1 / (2 * (j : ℝ))) * (n / (4 * (j : ℝ) ^ 2) * ε * s ^ 2) := by
            ring
          linarith

end Stage2

section Stage1

variable {n : ℕ} [NeZero n]

/-- **One round between `n/(2j)` and `n/j`** (Chernoff upper tail): from at most `j` colours and
`c_a ≤ b` with `n/(2j) < b < n/j`, the gap `g = n/j − b` grows by a factor `1 + 1/(4j)`
except with probability at most `exp(−g²/(32 j n))`: the new support of `a` reaches
`b − g/(4j)` with at most that probability (the mean is at most `b − g/(2j)`). -/
lemma avg_colourCount_stepCol_ge_gap {y : Fin n → Fin n} {a : Fin n} {j : ℕ} (hj : 1 ≤ j)
    (hy : numColours y ≤ j) {b : ℝ} (hb : (n : ℝ) / (2 * j) < b) (hg : 0 < (n : ℝ) / j - b)
    (hya : (colourCount y a : ℝ) ≤ b) :
    avg (fun r : Tgt3 n => if b - ((n : ℝ) / j - b) / (4 * j) ≤
        (colourCount (stepCol y r) a : ℝ) then (1 : ℝ) else 0) ≤
      Real.exp (-(((n : ℝ) / j - b) ^ 2 / (32 * j * n))) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hnj : (n : ℝ) / j = 2 * (n / (2 * j)) := by field_simp
  obtain ⟨g, hgdef⟩ : ∃ g, g = (n : ℝ) / j - b := ⟨_, rfl⟩
  rw [← hgdef] at hg ⊢
  have hb0 : 0 < b := lt_of_le_of_lt (by positivity) hb
  have hmean : avg (fun r : Tgt3 n => (colourCount (stepCol y r) a : ℝ)) ≤ b - g / (2 * j) := by
    refine (avg_colourCount_stepCol_le_of_le y a hy hya).trans ?_
    have e : b * (1 + b / n - 1 / j) = b - b * g / n := by
      rw [hgdef]
      field_simp
      ring
    have h2 : g / (2 * j) ≤ b * g / n := by
      rw [div_le_div_iff₀ (by positivity) hn]
      have : (n : ℝ) ≤ b * (2 * j) := by
        rw [div_lt_iff₀ (by positivity)] at hb
        linarith
      nlinarith
    linarith
  have hgn : g < n / (2 * j) := by linarith
  have hμ0 : 0 < b - g / (2 * j) := by
    have : g / (2 * j) ≤ g := div_le_self hg.le (by linarith)
    linarith
  have hμk : b - g / (2 * j) < b - g / (4 * j) := by
    have : g / (4 * j) < g / (2 * j) := div_lt_div_of_pos_left hg (by positivity) (by linarith)
    linarith
  refine (avg_colourCount_stepCol_ge y a hμ0 hμk hmean).trans
    (Real.exp_le_exp.mpr (neg_le_neg ?_))
  have e1 : b - g / (4 * j) - (b - g / (2 * j)) = g / (4 * j) := by
    field_simp
    ring
  have hsum : b - g / (4 * j) + (b - g / (2 * j)) ≤ 2 * (n / j) := by
    have : 0 ≤ g / (4 * j) := by positivity
    have : 0 ≤ g / (2 * j) := by positivity
    linarith
  rw [e1, le_div_iff₀ (by linarith)]
  calc g ^ 2 / (32 * j * n) * (b - g / (4 * j) + (b - g / (2 * j)))
      ≤ g ^ 2 / (32 * j * n) * (2 * (n / j)) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (g / (4 * j)) ^ 2 := by field_simp; ring

/-- The target levels of the proof of Lemma 3.4 (BCNPT16, Appendix B, with the corrections of
`PROGRESS-MAJ-12.md`): `max(n/j − m (1 + 1/(4j))^s, (n/(2j)) (1 − 1/(4j))^(s − s_A), K)`. The
first term is the gap-growth block (until `c_a ≤ n/(2j)`), the second the geometric decrease
from `n/(2j)` (after round `s_A`), and `K` the floor. -/
noncomputable def stage1Level (n j : ℕ) (m K : ℝ) (sA s : ℕ) : ℝ :=
  max ((n : ℝ) / j - m * (1 + 1 / (4 * (j : ℝ))) ^ s)
    (max ((n : ℝ) / (2 * j) * (1 - 1 / (4 * (j : ℝ))) ^ (s - sA)) K)

/-- **One round along the schedule of Lemma 3.4**: from at most `j` colours and `c_a` below the
level of round `s`, the new support of `a` exceeds the level of round `s + 1` with probability at
most `1/n²` (`exp(−2 log n)`). Above `n/(2j)` the level is `n/j − m (1 + 1/(4j))^s` and the gap
grows (`avg_colourCount_stepCol_ge_gap`); below, it shrinks by `1 − 1/(4j)` down to the floor
`K ≥ 64 j² log n` (`avg_colourCount_stepCol_ge_shrink`). -/
lemma stage1_step {y : Fin n → Fin n} {a : Fin n} {j : ℕ} (hj : 1 ≤ j) (hy : numColours y ≤ j)
    {m K : ℝ} {sA : ℕ} (hm : 0 < m) (hmL : 64 * j * n * Real.log n ≤ m ^ 2)
    (hK : 64 * (j : ℝ) ^ 2 * Real.log n ≤ K) (hK0 : 0 < K) (hKn : K ≤ n / (2 * j))
    (hsA : ∀ s, sA ≤ s → (n : ℝ) / j ≤ m * (1 + 1 / (4 * (j : ℝ))) ^ s) (s : ℕ)
    (hya : (colourCount y a : ℝ) ≤ stage1Level n j m K sA s) :
    avg (fun r : Tgt3 n => if stage1Level n j m K sA (s + 1) < colourCount (stepCol y r) a
      then (1 : ℝ) else 0) ≤ Real.exp (-(2 * Real.log n)) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have h4j : 1 / (4 * (j : ℝ)) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have h4j0 : 0 ≤ 1 / (4 * (j : ℝ)) := by positivity
  have hq1 : 1 ≤ 1 + 1 / (4 * (j : ℝ)) := by linarith
  have hr0 : 0 ≤ 1 - 1 / (4 * (j : ℝ)) := by linarith
  have hr1 : 1 - 1 / (4 * (j : ℝ)) ≤ 1 := by linarith
  have htransfer : ∀ k : ℝ, k ≤ stage1Level n j m K sA (s + 1) →
      avg (fun r : Tgt3 n => if stage1Level n j m K sA (s + 1) < colourCount (stepCol y r) a
        then (1 : ℝ) else 0) ≤
      avg (fun r : Tgt3 n => if k ≤ (colourCount (stepCol y r) a : ℝ) then (1 : ℝ) else 0) := by
    intro k hk
    refine avg_le_avg fun r => ?_
    by_cases h1 : stage1Level n j m K sA (s + 1) < colourCount (stepCol y r) a
    · rw [if_pos h1, if_pos (by linarith)]
    · rw [if_neg h1]
      split_ifs <;> norm_num
  have hT2 : (n : ℝ) / (2 * j) * (1 - 1 / (4 * (j : ℝ))) ^ (s - sA) ≤ n / (2 * j) := by
    calc _ ≤ (n : ℝ) / (2 * j) * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ hr0 hr1) (by positivity)
      _ = _ := mul_one _
  have hmaxle : max ((n : ℝ) / (2 * j) * (1 - 1 / (4 * (j : ℝ))) ^ (s - sA)) K ≤ n / (2 * j) :=
    max_le hT2 hKn
  by_cases hcase : (n : ℝ) / (2 * j) < stage1Level n j m K sA s
  · -- gap growth
    have hT1 : stage1Level n j m K sA s = (n : ℝ) / j - m * (1 + 1 / (4 * (j : ℝ))) ^ s := by
      unfold stage1Level at hcase ⊢
      rcases le_total ((n : ℝ) / j - m * (1 + 1 / (4 * (j : ℝ))) ^ s)
        (max ((n : ℝ) / (2 * j) * (1 - 1 / (4 * (j : ℝ))) ^ (s - sA)) K) with h | h
      · rw [max_eq_right h] at hcase
        linarith
      · exact max_eq_left h
    rw [hT1] at hcase hya
    have hqs : 1 ≤ (1 + 1 / (4 * (j : ℝ))) ^ s := one_le_pow₀ hq1
    have hgpos : 0 < (n : ℝ) / j - ((n : ℝ) / j - m * (1 + 1 / (4 * (j : ℝ))) ^ s) := by
      have : 0 < m * (1 + 1 / (4 * (j : ℝ))) ^ s := mul_pos hm (by positivity)
      linarith
    have h := avg_colourCount_stepCol_ge_gap hj hy hcase hgpos hya
    rw [show (n : ℝ) / j - ((n : ℝ) / j - m * (1 + 1 / (4 * (j : ℝ))) ^ s) =
      m * (1 + 1 / (4 * (j : ℝ))) ^ s by ring] at h
    have hk : (n : ℝ) / j - m * (1 + 1 / (4 * (j : ℝ))) ^ s -
        m * (1 + 1 / (4 * (j : ℝ))) ^ s / (4 * j) ≤ stage1Level n j m K sA (s + 1) := by
      refine le_trans (le_of_eq ?_) (le_max_left _ _)
      rw [pow_succ]
      field_simp
      ring
    refine (htransfer _ hk).trans (h.trans (Real.exp_le_exp.mpr (neg_le_neg ?_)))
    rw [le_div_iff₀ (by positivity)]
    have hmg : m ≤ m * (1 + 1 / (4 * (j : ℝ))) ^ s := le_mul_of_one_le_right hm.le hqs
    have := pow_le_pow_left₀ hm.le hmg 2
    nlinarith
  · -- geometric decrease and floor
    push Not at hcase
    obtain ⟨b, hbdef⟩ : ∃ b, b = stage1Level n j m K sA s := ⟨_, rfl⟩
    rw [← hbdef] at hcase hya
    have hbK : K ≤ b := by
      rw [hbdef]
      unfold stage1Level
      exact le_max_of_le_right (le_max_right _ _)
    have hb0 : 0 < b := hK0.trans_le hbK
    have h := avg_colourCount_stepCol_ge_shrink hj hy hb0 hcase hya
    have hbmax : b ≤ max ((n : ℝ) / (2 * j) * (1 - 1 / (4 * (j : ℝ))) ^ (s - sA)) K := by
      have hT1b : (n : ℝ) / j - m * (1 + 1 / (4 * (j : ℝ))) ^ s ≤ b := by
        rw [hbdef]
        unfold stage1Level
        exact le_max_left _ _
      have hT1 : (n : ℝ) / j - m * (1 + 1 / (4 * (j : ℝ))) ^ s ≤
          max ((n : ℝ) / (2 * j) * (1 - 1 / (4 * (j : ℝ))) ^ (s - sA)) K := by
        by_cases hs : s < sA
        · have h0 : s - sA = 0 := by omega
          rw [h0, pow_zero, mul_one]
          exact le_max_of_le_left (hT1b.trans hcase)
        · push Not at hs
          have := hsA s hs
          exact le_max_of_le_right (by linarith)
      rw [hbdef]
      unfold stage1Level
      exact max_le hT1 le_rfl
    have hk : b * (1 - 1 / (4 * (j : ℝ))) ≤ stage1Level n j m K sA (s + 1) := by
      unfold stage1Level
      refine le_max_of_le_right ?_
      calc b * (1 - 1 / (4 * (j : ℝ)))
          ≤ max ((n : ℝ) / (2 * j) * (1 - 1 / (4 * (j : ℝ))) ^ (s - sA)) K *
              (1 - 1 / (4 * (j : ℝ))) := mul_le_mul_of_nonneg_right hbmax hr0
        _ = max ((n : ℝ) / (2 * j) * (1 - 1 / (4 * (j : ℝ))) ^ (s - sA) *
              (1 - 1 / (4 * (j : ℝ)))) (K * (1 - 1 / (4 * (j : ℝ)))) := max_mul_of_nonneg _ _ hr0
        _ ≤ _ := by
            refine max_le_max ?_ (mul_le_of_le_one_right hK0.le hr1)
            rw [mul_assoc, ← pow_succ]
            exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr0 hr1 (by omega))
              (by positivity)
    refine (htransfer _ hk).trans (h.trans (Real.exp_le_exp.mpr (neg_le_neg ?_)))
    rw [le_div_iff₀ (by positivity)]
    nlinarith

end Stage1

/-- **Lemma 3.4** (BCNPT16, dropping stage 1): there is `C` such that, for `j ≥ 2` with
`C j³ log n ≤ n`, from every configuration `x` with at most `j` colours and every colour `a` with
at most `n/j − 16 √(j n log n)` agents, at every time `t` with `C j log n ≤ t ≤ n` colour `a` has
more than `C j² log n` agents with probability at most `1/n`. -/
theorem dropping_stage1 :
    ∃ C : ℝ, ∀ (n j : ℕ) (x : Fin n → Fin n) (a : Fin n), 2 ≤ j →
      C * (j : ℝ) ^ 3 * Real.log n ≤ n → numColours x ≤ j →
      (colourCount x a : ℝ) ≤ n / j - 16 * √(j * n * Real.log n) →
      ∀ t : ℕ, C * j * Real.log n ≤ t → t ≤ n →
        expList (Tgt3 n) t
          (fun l => if C * j ^ 2 * Real.log n < colourCount (runCol x l) a then 1 else 0) ≤
            1 / n := by
  refine ⟨240, fun n j x a hj2 hC hx hxa t ht htn => ?_⟩
  have hn1 : 0 < n := a.pos
  haveI : NeZero n := ⟨by omega⟩
  have hjR : (2 : ℝ) ≤ j := by exact_mod_cast hj2
  have hj0 : (0 : ℝ) < j := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  -- a dead colour stays dead
  by_cases h0 : colourCount x a = 0
  · have : (fun l => if 240 * (j : ℝ) ^ 2 * Real.log n < colourCount (runCol x l) a then (1 : ℝ)
        else 0) = fun _ => 0 := funext fun l => by
      rw [colourCount_runCol_eq_zero h0 l, Nat.cast_zero, if_neg]
      push Not
      have := Real.log_natCast_nonneg n
      positivity
    rw [this, expList_const]
    positivity
  have hc1 : (1 : ℝ) ≤ colourCount x a := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
  have hm0' : 0 ≤ 16 * √(j * n * Real.log n) := by positivity
  have hnj : 1 ≤ (n : ℝ) / j := by linarith
  have hnR : (2 : ℝ) ≤ n := by
    rw [le_div_iff₀ hj0] at hnj
    linarith
  have hn2 : 2 ≤ n := by exact_mod_cast hnR
  have hL := log_ge_of_two_le hn2
  have hL0 : 0 < Real.log n := by linarith
  have hjL : 1 ≤ (j : ℝ) * Real.log n := by
    have := mul_le_mul hjR hL (by norm_num) hj0.le
    linarith
  have hj2L : 1 ≤ (j : ℝ) ^ 2 * Real.log n := by
    calc (1 : ℝ) ≤ j * Real.log n := hjL
      _ ≤ j * (j * Real.log n) := le_mul_of_one_le_left (by positivity) (by linarith)
      _ = (j : ℝ) ^ 2 * Real.log n := by ring
  -- the gap `m = 16 √(j n log n)`
  obtain ⟨m, hm⟩ : ∃ m, m = 16 * √(j * n * Real.log n) := ⟨_, rfl⟩
  rw [← hm] at hxa
  have hjnL : 1 ≤ (j : ℝ) * n * Real.log n := by
    calc (1 : ℝ) ≤ j * Real.log n := hjL
      _ ≤ n * (j * Real.log n) := le_mul_of_one_le_left (by positivity) (by linarith)
      _ = (j : ℝ) * n * Real.log n := by ring
  have hm16 : 16 ≤ m := by
    rw [hm]
    have := Real.one_le_sqrt.mpr hjnL
    linarith
  have hm0 : 0 < m := by linarith
  have hmsq : m ^ 2 = 256 * (j * n * Real.log n) := by
    rw [hm, mul_pow, Real.sq_sqrt (by positivity)]
    norm_num
  have hmL : 64 * j * n * Real.log n ≤ m ^ 2 := by
    rw [hmsq]
    have : 0 ≤ (j : ℝ) * n * Real.log n := by positivity
    calc 64 * (j : ℝ) * n * Real.log n = 64 * (j * n * Real.log n) := by ring
      _ ≤ 256 * (j * n * Real.log n) := by linarith
  -- the floor `K = min(240 j² log n, n/(2j))`
  obtain ⟨K, hKdef⟩ : ∃ K, K = min (240 * (j : ℝ) ^ 2 * Real.log n) ((n : ℝ) / (2 * j)) :=
    ⟨_, rfl⟩
  have hKn : K ≤ n / (2 * j) := hKdef ▸ min_le_right _ _
  have hKC : K ≤ 240 * (j : ℝ) ^ 2 * Real.log n := hKdef ▸ min_le_left _ _
  have hn2j : 120 * (j : ℝ) ^ 2 * Real.log n ≤ n / (2 * j) := by
    rw [le_div_iff₀ (by positivity)]
    calc 120 * (j : ℝ) ^ 2 * Real.log n * (2 * j) = 240 * (j : ℝ) ^ 3 * Real.log n := by ring
      _ ≤ (n : ℝ) := hC
  have hK64 : 64 * (j : ℝ) ^ 2 * Real.log n ≤ K := by
    have : 0 ≤ (j : ℝ) ^ 2 * Real.log n := by positivity
    rw [hKdef]
    exact le_min (by linarith) (by linarith)
  have hK1 : 1 ≤ K := by linarith
  have hK0 : 0 < K := by linarith
  -- the lengths of the blocks
  obtain ⟨sA, hsAdef⟩ : ∃ sA : ℕ, sA = ⌈5 * (j : ℝ) * Real.log n⌉₊ := ⟨_, rfl⟩
  obtain ⟨sB, hsBdef⟩ : ∃ sB : ℕ, sB = ⌈4 * (j : ℝ) * Real.log n⌉₊ := ⟨_, rfl⟩
  have hsA1 : 5 * (j : ℝ) * Real.log n ≤ sA := hsAdef ▸ Nat.le_ceil _
  have hsA2 : (sA : ℝ) < 5 * j * Real.log n + 1 := hsAdef ▸ Nat.ceil_lt_add_one (by positivity)
  have hsB1 : 4 * (j : ℝ) * Real.log n ≤ sB := hsBdef ▸ Nat.le_ceil _
  have hsB2 : (sB : ℝ) < 4 * j * Real.log n + 1 := hsBdef ▸ Nat.ceil_lt_add_one (by positivity)
  have h4j : 1 / (4 * (j : ℝ)) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have h4j0 : 0 < 1 / (4 * (j : ℝ)) := by positivity
  have hr0 : 0 ≤ 1 - 1 / (4 * (j : ℝ)) := by linarith
  have hr1 : 1 - 1 / (4 * (j : ℝ)) ≤ 1 := by linarith
  -- block A: `(1 + 1/(4j))^{s_A} ≥ n`
  have hq : (n : ℝ) ≤ (1 + 1 / (4 * (j : ℝ))) ^ sA := by
    have hq0 : 0 < 1 + 1 / (4 * (j : ℝ)) := by positivity
    have hlog : 1 / (4 * (j : ℝ) + 1) ≤ Real.log (1 + 1 / (4 * (j : ℝ))) := by
      have := Real.one_sub_inv_le_log_of_pos hq0
      have e : 1 - (1 + 1 / (4 * (j : ℝ)))⁻¹ = 1 / (4 * j + 1) := by
        field_simp
        ring
      linarith
    have hLs : Real.log n ≤ sA * Real.log (1 + 1 / (4 * (j : ℝ))) := by
      calc Real.log n ≤ sA * (1 / (4 * (j : ℝ) + 1)) := by
            rw [← div_eq_mul_one_div, le_div_iff₀ (by positivity)]
            have : Real.log n ≤ j * Real.log n := le_mul_of_one_le_left hL0.le (by linarith)
            calc Real.log n * (4 * j + 1) = 4 * (j * Real.log n) + Real.log n := by ring
              _ ≤ 5 * j * Real.log n := by linarith
              _ ≤ sA := hsA1
        _ ≤ _ := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)
    calc (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log hn0).symm
      _ ≤ Real.exp (sA * Real.log (1 + 1 / (4 * (j : ℝ)))) := Real.exp_le_exp.mpr hLs
      _ = Real.exp (Real.log (1 + 1 / (4 * (j : ℝ)))) ^ sA := Real.exp_nat_mul _ _
      _ = _ := by rw [Real.exp_log hq0]
  have hsA : ∀ s, sA ≤ s → (n : ℝ) / j ≤ m * (1 + 1 / (4 * (j : ℝ))) ^ s := by
    intro s hs
    have h1 : (1 + 1 / (4 * (j : ℝ))) ^ sA ≤ (1 + 1 / (4 * (j : ℝ))) ^ s :=
      pow_le_pow_right₀ (by linarith) hs
    have h2 : (n : ℝ) / j ≤ n := div_le_self hn0.le (by linarith)
    calc (n : ℝ) / j ≤ n := h2
      _ ≤ (1 + 1 / (4 * (j : ℝ))) ^ s := hq.trans h1
      _ ≤ m * (1 + 1 / (4 * (j : ℝ))) ^ s := le_mul_of_one_le_left (by positivity) (by linarith)
  -- block B: `(1 − 1/(4j))^{s_B} ≤ 1/n`
  have hr : (1 - 1 / (4 * (j : ℝ))) ^ sB ≤ 1 / n := by
    have h1 : 1 - 1 / (4 * (j : ℝ)) ≤ Real.exp (-(1 / (4 * j))) := by
      linarith [Real.add_one_le_exp (-(1 / (4 * (j : ℝ))))]
    have hlog : Real.log n ≤ (sB : ℝ) * (1 / (4 * j)) := by
      rw [← div_eq_mul_one_div, le_div_iff₀ (by positivity)]
      linarith
    calc _ ≤ Real.exp (-(1 / (4 * j))) ^ sB := pow_le_pow_left₀ hr0 h1 sB
      _ = Real.exp (sB * (-(1 / (4 * j)))) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (-((1 : ℕ) * Real.log n)) := by
          refine Real.exp_le_exp.mpr ?_
          push_cast
          linarith
      _ = 1 / (n : ℝ) ^ 1 := exp_neg_nat_mul_log hn1 1
      _ = 1 / n := by rw [pow_one]
  -- after `s_A + s_B ≤ t` rounds the level is the floor
  have hst : sA + sB ≤ t := by
    have : (sA : ℝ) + sB ≤ t := by linarith
    exact_mod_cast this
  have hlevel : stage1Level n j m K sA t ≤ K := by
    unfold stage1Level
    refine max_le ?_ (max_le ?_ le_rfl)
    · have := hsA t (by omega)
      linarith
    · calc (n : ℝ) / (2 * j) * (1 - 1 / (4 * (j : ℝ))) ^ (t - sA)
          ≤ (n : ℝ) / (2 * j) * (1 - 1 / (4 * (j : ℝ))) ^ sB :=
            mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr0 hr1 (by omega)) (by positivity)
        _ ≤ (n : ℝ) / (2 * j) * (1 / n) := mul_le_mul_of_nonneg_left hr (by positivity)
        _ = 1 / (2 * (j : ℝ)) := by field_simp
        _ ≤ K := by
            have : 1 / (2 * (j : ℝ)) ≤ 1 / 4 := by
              rw [div_le_div_iff₀ (by positivity) (by norm_num)]
              linarith
            linarith
  -- the moving target, one round failing with probability at most `1/n²`
  have key := Dynamics.expList_escape (stepCol (n := n) (σ := Fin n))
    (p := Real.exp (-(2 * Real.log n))) (Real.exp_pos _).le t
    (fun s => {y | numColours y ≤ j ∧ (colourCount y a : ℝ) ≤ stage1Level n j m K sA s}) x
    ⟨hx, by
      unfold stage1Level
      rw [pow_zero, mul_one]
      exact hxa.trans (le_max_left _ _)⟩
    (fun s _ y hy => by
      refine le_trans (Dynamics.avg_le_avg fun r => ?_)
        (stage1_step (by omega) hy.1 hm0 hmL hK64 hK0 hKn hsA s hy.2)
      by_cases h2 : stage1Level n j m K sA (s + 1) < colourCount (stepCol y r) a
      · rw [if_pos h2]
        split_ifs <;> norm_num
      · rw [if_neg h2, if_pos (show stepCol y r ∈
            {y | numColours y ≤ j ∧ (colourCount y a : ℝ) ≤ stage1Level n j m K sA (s + 1)} from
            ⟨(numColours_stepCol_le y r).trans hy.1, not_lt.mp h2⟩)])
  refine le_trans (expList_le_expList fun l => ?_) (key.trans ?_)
  · rw [runCol_eq_foldl]
    by_cases h1 : 240 * (j : ℝ) ^ 2 * Real.log n < colourCount (l.foldl stepCol x) a
    · rw [if_pos h1, if_neg]
      intro hmem
      exact absurd hmem.2 (not_le.mpr (by linarith))
    · rw [if_neg h1]
      split_ifs <;> norm_num
  calc (t : ℝ) * Real.exp (-(2 * Real.log n)) = t * (1 / (n : ℝ) ^ 2) := by
        rw [show (2 : ℝ) * Real.log n = ((2 : ℕ) : ℝ) * Real.log n by norm_num,
          exp_neg_nat_mul_log hn1 2]
    _ ≤ n * (1 / (n : ℝ) ^ 2) := mul_le_mul_of_nonneg_right (by exact_mod_cast htn) (by positivity)
    _ = 1 / n := by field_simp

/-- **Lemma 3.5** (BCNPT16, dropping stage 2): there is `C` such that, for `j ≥ 2` with
`C j³ log n ≤ n`, from every configuration `x` with at most `j` colours and every colour `a` with
at most `n/(2j)` agents, colour `a` has died after any `t ≥ C j log n` rounds with probability at
least `1/2`. -/
theorem dropping_stage2 :
    ∃ C : ℝ, ∀ (n j : ℕ) (x : Fin n → Fin n) (a : Fin n), 2 ≤ j →
      C * (j : ℝ) ^ 3 * Real.log n ≤ n → numColours x ≤ j →
      (colourCount x a : ℝ) ≤ n / (2 * j) →
      ∀ t : ℕ, C * j * Real.log n ≤ t →
        1 / 2 ≤ expList (Tgt3 n) t
          (fun l => if colourCount (runCol x l) a = 0 then 1 else 0) := by
  refine ⟨1024, fun n j x a hj2 hC hx hxa t ht => ?_⟩
  have hn1 : 0 < n := a.pos
  haveI : NeZero n := ⟨by omega⟩
  -- a dead colour stays dead
  by_cases h0 : colourCount x a = 0
  · have : (fun l => if colourCount (runCol x l) a = 0 then (1 : ℝ) else 0) = fun _ => 1 :=
      funext fun l => if_pos (colourCount_runCol_eq_zero h0 l)
    rw [this, expList_const]
    norm_num
  have hjR : (2 : ℝ) ≤ j := by exact_mod_cast hj2
  have hj0 : (0 : ℝ) < j := by linarith
  have hc1 : (1 : ℝ) ≤ colourCount x a := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
  have hB1 : 1 ≤ (n : ℝ) / (2 * j) := hc1.trans hxa
  have hnR : 4 ≤ (n : ℝ) := by
    rw [le_div_iff₀ (by positivity)] at hB1
    linarith
  have hn2 : 2 ≤ n := by exact_mod_cast (show (2 : ℝ) ≤ n by linarith)
  have hL := log_ge_of_two_le hn2
  have hL0 : 0 < Real.log n := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hjL : 0 ≤ (j : ℝ) * Real.log n := by positivity
  have hj3 : (j : ℝ) ≤ (j : ℝ) ^ 3 := by
    calc (j : ℝ) = j * 1 := by ring
      _ ≤ j * (j : ℝ) ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hj0.le
      _ = (j : ℝ) ^ 3 := by ring
  have hj38 : (8 : ℝ) ≤ (j : ℝ) ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hjR 3
    norm_num at this
    linarith
  have hB : 512 * (j : ℝ) ^ 2 * Real.log n ≤ n / (2 * j) := by
    rw [le_div_iff₀ (by positivity)]
    calc 512 * (j : ℝ) ^ 2 * Real.log n * (2 * j) = 1024 * (j : ℝ) ^ 3 * Real.log n := by ring
      _ ≤ (n : ℝ) := hC
  -- one round above `n/(2j)`: probability at most `1/n⁴`
  have hesc : ∀ y : Fin n → Fin n, numColours y ≤ j → (colourCount y a : ℝ) ≤ n / (2 * j) →
      avg (fun r : Tgt3 n =>
        if (n : ℝ) / (2 * j) < colourCount (stepCol y r) a then (1 : ℝ) else 0) ≤
          1 / (n : ℝ) ^ 4 := by
    intro y hy hya
    have h := avg_colourCount_stepCol_ge_shrink (by omega) hy (b := n / (2 * j))
      (by positivity) le_rfl hya
    have hsh : (n : ℝ) / (2 * j) * (1 - 1 / (4 * (j : ℝ))) ≤ n / (2 * j) := by
      have : 0 ≤ (n : ℝ) / (2 * j) * (1 / (4 * (j : ℝ))) := by positivity
      nlinarith
    calc _ ≤ avg (fun r : Tgt3 n => if (n : ℝ) / (2 * j) * (1 - 1 / (4 * (j : ℝ))) ≤
          colourCount (stepCol y r) a then (1 : ℝ) else 0) :=
          avg_le_avg fun r => by
            by_cases h1 : (n : ℝ) / (2 * j) < colourCount (stepCol y r) a
            · rw [if_pos h1, if_pos (by linarith)]
            · rw [if_neg h1]
              split_ifs <;> norm_num
      _ ≤ _ := h
      _ ≤ Real.exp (-((4 : ℕ) * Real.log n)) := by
          refine Real.exp_le_exp.mpr (neg_le_neg ?_)
          rw [le_div_iff₀ (by positivity)]
          push_cast
          have : 0 ≤ (j : ℝ) ^ 2 * Real.log n := by positivity
          nlinarith
      _ = 1 / (n : ℝ) ^ 4 := exp_neg_nat_mul_log hn1 4
  have hε : (0 : ℝ) ≤ 1 / (n : ℝ) ^ 4 := by positivity
  -- Markov at `t₀ = ⌈2 j log n⌉`
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : ℕ, t₀ = ⌈2 * (j : ℝ) * Real.log n⌉₊ := ⟨_, rfl⟩
  have hE := expList_min_colourCount_le (by omega) hx hxa hε hesc t₀
  have ht₀ge : 2 * (j : ℝ) * Real.log n ≤ t₀ := ht₀ ▸ Nat.le_ceil _
  have ht₀le : (t₀ : ℝ) < 2 * j * Real.log n + 1 := ht₀ ▸ Nat.ceil_lt_add_one (by positivity)
  have ht₀n : (t₀ : ℝ) ≤ n := by
    have : 2 * (j : ℝ) * Real.log n ≤ 2 * (j : ℝ) ^ 3 * Real.log n := by nlinarith
    have : 1 ≤ 1000 * (j : ℝ) ^ 3 * Real.log n := by nlinarith
    linarith
  have hρ0 : 0 ≤ 1 - 1 / (2 * (j : ℝ)) := by
    have : 1 / (2 * (j : ℝ)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  have hρ : (1 - 1 / (2 * (j : ℝ))) ^ t₀ ≤ 1 / n := by
    have h1 : 1 - 1 / (2 * (j : ℝ)) ≤ Real.exp (-(1 / (2 * j))) := by
      linarith [Real.add_one_le_exp (-(1 / (2 * (j : ℝ))))]
    have hlog : Real.log n ≤ (t₀ : ℝ) * (1 / (2 * j)) := by
      rw [← div_eq_mul_one_div, le_div_iff₀ (by positivity)]
      linarith
    calc _ ≤ Real.exp (-(1 / (2 * j))) ^ t₀ := pow_le_pow_left₀ hρ0 h1 t₀
      _ = Real.exp (t₀ * (-(1 / (2 * j)))) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (-((1 : ℕ) * Real.log n)) := by
          refine Real.exp_le_exp.mpr ?_
          push_cast
          linarith
      _ = 1 / (n : ℝ) ^ 1 := exp_neg_nat_mul_log hn1 1
      _ = 1 / n := by rw [pow_one]
  have hE2 : expList (Tgt3 n) t₀
      (fun l => min (colourCount (runCol x l) a : ℝ) (n / (2 * j))) ≤ 1 / 2 := by
    have h1 : (1 - 1 / (2 * (j : ℝ))) ^ t₀ * (n / (2 * j)) ≤ 1 / 4 := by
      calc _ ≤ 1 / (n : ℝ) * ((n : ℝ) / (2 * j)) := mul_le_mul_of_nonneg_right hρ (by positivity)
        _ = 1 / (2 * (j : ℝ)) := by field_simp
        _ ≤ 1 / 4 := by
            rw [div_le_div_iff₀ (by positivity) (by norm_num)]
            linarith
    have h2 : (n : ℝ) / (4 * (j : ℝ) ^ 2) * (1 / (n : ℝ) ^ 4) * (t₀ : ℝ) ^ 2 ≤ 1 / 4 := by
      have ht0 : (0 : ℝ) ≤ t₀ := Nat.cast_nonneg t₀
      calc _ ≤ (n : ℝ) / (4 * (j : ℝ) ^ 2) * (1 / (n : ℝ) ^ 4) * (n : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht0 ht₀n 2) (by positivity)
        _ = 1 / (4 * (j : ℝ) ^ 2 * n) := by field_simp
        _ ≤ 1 / 4 := by
            rw [div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith
    linarith
  have hdead : 1 / 2 ≤ expList (Tgt3 n) t₀
      (fun l => if colourCount (runCol x l) a = 0 then (1 : ℝ) else 0) := by
    have hpt : ∀ l, (1 : ℝ) + (-1) * min (colourCount (runCol x l) a : ℝ) (n / (2 * j)) ≤
        (if colourCount (runCol x l) a = 0 then (1 : ℝ) else 0) := by
      intro l
      split_ifs with hd
      · rw [hd, Nat.cast_zero, min_eq_left (by positivity)]
        norm_num
      · have h1 : (1 : ℝ) ≤ colourCount (runCol x l) a := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd
        have : 1 ≤ min (colourCount (runCol x l) a : ℝ) (n / (2 * j)) := le_min h1 hB1
        linarith
    have := expList_le_expList (α := Tgt3 n) (T := t₀) hpt
    rw [expList_add, expList_const, expList_const_mul] at this
    linarith
  -- later times: a dead colour stays dead
  have ht₀t : t₀ ≤ t := by
    rw [ht₀]
    refine Nat.ceil_le.mpr ?_
    have : 2 * (j : ℝ) * Real.log n ≤ 1024 * j * Real.log n := by nlinarith
    linarith
  obtain ⟨d, rfl⟩ : ∃ d, t = t₀ + d := ⟨t - t₀, by omega⟩
  rw [expList_append]
  refine hdead.trans (expList_le_expList fun l₁ => ?_)
  by_cases hd : colourCount (runCol x l₁) a = 0
  · rw [if_pos hd]
    have : (fun l₂ => if colourCount (runCol x (l₁ ++ l₂)) a = 0 then (1 : ℝ) else 0) =
        fun _ => 1 :=
      funext fun l₂ => by rw [runCol_append, if_pos (colourCount_runCol_eq_zero hd l₂)]
    rw [this, expList_const]
  · rw [if_neg hd]
    exact expList_nonneg fun l₂ => by split_ifs <;> norm_num

end ThreeMajority
