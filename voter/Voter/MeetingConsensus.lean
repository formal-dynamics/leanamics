import Voter.MeetingTime

/-! # `O(n³ log n)` voter consensus on every connected graph (VOT-6)

Hassin–Peleg Theorem 2.5 and Survey Theorem 8, for the lazy synchronous voter dynamics: on
every connected graph with `n` vertices, from every initial colouring, the voter dynamics in
which every vertex keeps its colour with probability `1/2` and otherwise copies a uniformly
random neighbour reaches consensus within `O(n³ log n)` rounds with probability at least
`1 - 1/n`. The proof combines the meeting time `lazy_meeting_le_half` with the duality and
union bound `iterate_disagreement_le_of_meeting`.
-/

namespace Voter
open Dynamics

universe u v

/-- `(n − 1) 2^{-k} ≤ 1/n` as soon as `k + 1 > 5 log n`. -/
lemma card_sub_one_mul_half_pow_le {n : ℕ} (hn : 1 ≤ n) {k : ℕ}
    (hk : 5 * Real.log n < k + 1) : ((n : ℝ) - 1) * (1 / 2) ^ k ≤ 1 / n := by
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · have : n = 1 := by omega
    subst this
    norm_num
  · have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have hnpos : (0 : ℝ) < n := by linarith
    set L := Real.log n with hL_def
    have hl2 := Real.log_two_gt_d9
    have hL : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hnR
    have hlog : 2 * L ≤ k * Real.log 2 := by
      have h1 : Real.log 2 ≤ L * (5 * Real.log 2 - 2) := by
        have h5 : (1 : ℝ) ≤ 5 * Real.log 2 - 2 := by linarith
        calc Real.log 2 = Real.log 2 * 1 := (mul_one _).symm
          _ ≤ L * (5 * Real.log 2 - 2) :=
              mul_le_mul hL h5 zero_le_one (by linarith)
      have h2 : (5 * L - 1) * Real.log 2 < k * Real.log 2 :=
        mul_lt_mul_of_pos_right (by linarith) (by linarith)
      nlinarith
    have hpow : (n : ℝ) ^ 2 ≤ 2 ^ k := by
      rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_pow, Real.log_pow]
      push_cast
      linarith
    have hk2 : (0 : ℝ) < 2 ^ k := by positivity
    rw [one_div_pow, mul_one_div, div_le_div_iff₀ hk2 hnpos]
    nlinarith

/-- **Consensus within `O(n³ log n)` rounds with probability at least `1 - 1/n`** (Hassin–Peleg
Theorem 2.5; Survey Theorem 8), for the lazy voter dynamics. There is a constant `A > 0` such
that on every connected graph with `n` vertices (all degrees positive), for every finite
palette and every initial colouring `s`, after `T ≥ A n³ log n` rounds the lazy voter dynamics
has not reached consensus with probability at most `1/n`. -/
theorem lazy_voter_consensus_whp :
    ∃ A : ℝ, 0 < A ∧ ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj], G.Connected →
      ∀ (hd : ∀ i, 0 < G.degree i) (C : Type v) [Fintype C] (s : Config V C) (T : ℕ),
        A * (Fintype.card V : ℝ) ^ 3 * Real.log (Fintype.card V) ≤ T →
          (transition (lazyNeighbor G hd)).iterate T disagreement s ≤
            1 / (Fintype.card V : ℝ) := by
  refine ⟨255, by norm_num, ?_⟩
  intro V _ _ G _ hc hd C _ s T hT
  haveI : Nonempty V := hc.nonempty
  obtain ⟨u₀⟩ := ‹Nonempty V›
  have hcard : 1 ≤ Fintype.card V := Fintype.card_pos
  have hn1 : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hcard
  have hc51 : (0 : ℝ) < 51 * (Fintype.card V : ℝ) ^ 3 := by positivity
  -- the number of halvings of the probability of being apart
  set k : ℕ := ⌊(T : ℝ) / (51 * (Fintype.card V : ℝ) ^ 3)⌋₊ with hk_def
  have hkT : k * 51 * (Fintype.card V : ℝ) ^ 3 ≤ T := by
    have := Nat.floor_le (div_nonneg (Nat.cast_nonneg T) hc51.le)
    rw [← hk_def, le_div_iff₀ hc51] at this
    linarith
  have hk : 5 * Real.log (Fintype.card V) < k + 1 := by
    have hlt := Nat.lt_floor_add_one ((T : ℝ) / (51 * (Fintype.card V : ℝ) ^ 3))
    rw [← hk_def] at hlt
    have : 5 * Real.log (Fintype.card V) ≤ (T : ℝ) / (51 * (Fintype.card V : ℝ) ^ 3) := by
      rw [le_div_iff₀ hc51]
      linarith
    linarith
  calc (transition (lazyNeighbor G hd)).iterate T disagreement s
      ≤ ∑ v ∈ Finset.univ.erase u₀,
          (pairWalk (lazyNeighbor G hd)).event (fun p => p.1 ≠ p.2) T (v, u₀) :=
        iterate_disagreement_le_pairWalk _ s T u₀
    _ ≤ ∑ v ∈ Finset.univ.erase u₀, ((1 : ℝ) / 2) ^ k := by
        refine Finset.sum_le_sum fun v _ => ?_
        rw [event_pairWalk]
        exact lazy_apart_le_pow hd hc v u₀ k T hkT
    _ = ((Fintype.card V : ℝ) - 1) * (1 / 2) ^ k := by
        rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ u₀), Finset.card_univ,
          nsmul_eq_mul, Nat.cast_sub hcard, Nat.cast_one]
    _ ≤ 1 / (Fintype.card V : ℝ) := card_sub_one_mul_half_pow_le hcard hk

end Voter
