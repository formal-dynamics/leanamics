import Voter.Meeting

/-! # Meeting of two lazy walks from a two-coordinate potential (VOT-6 helpers)

Following Kanade, Mallmann-Trenn, Sauerwald (*On coalescence time in graphs*, SODA 2019,
Proposition B.9), the synchronous two-token walk `pairWalk H` is compared with *sequential*
walks, in which the first token moves and then the second, meeting being checked after each
move. Here `H` is any sampling kernel and laziness means `1/2 ≤ (H y).weight y`.

* `seqSurvival H T p` is the probability that the sequential walks started at `p` have not met
  during `T` full steps.
* If `F ≥ 0` decreases by `1` in expectation whenever one coordinate makes an `H`-step away
  from the other (the potential of Coppersmith, Tetali, Winkler), then
  `T * seqSurvival H T p ≤ F p` (`seqSurvival_mul_le`).
* Since a lazy token stays put with probability at least `1/2`, a crossing of the synchronous
  tokens is a meeting with probability at least `1/2`, whence
  `P(apart at T + 1) ≤ (apart + seqSurvival H T) / 2` (`iterate_outside_succ_le`).
* Hence the tokens are apart after `T + 1 ≥ 2 sup F + 1` steps with probability at most `3/4`
  (`iterate_outside_le_three_quarters`).
-/

namespace Voter
open Dynamics Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Survival of the sequential walks for `T` full steps: in each step the first token makes an
`H`-step, then (if they have not met) the second token makes an `H`-step. -/
noncomputable def seqSurvival (H : Kernel V) : ℕ → V × V → ℝ
  | 0 => Kernel.outside (Set.diagonal V)
  | T + 1 => fun p => Kernel.outside (Set.diagonal V) p *
      (H p.1).expect fun a => Kernel.outside (Set.diagonal V) (a, p.2) *
        (H p.2).expect fun b => seqSurvival H T (a, b)

omit [DecidableEq V] in
lemma seqSurvival_nonneg (H : Kernel V) (T : ℕ) (p : V × V) : 0 ≤ seqSurvival H T p := by
  induction T generalizing p with
  | zero => exact Kernel.outside_nonneg _ _
  | succ T ih =>
    exact mul_nonneg (Kernel.outside_nonneg _ _) <| Distribution.expect_nonneg _ fun a =>
      mul_nonneg (Kernel.outside_nonneg _ _) (Distribution.expect_nonneg _ fun b => ih _)

omit [DecidableEq V] in
lemma seqSurvival_le_one (H : Kernel V) (T : ℕ) (p : V × V) : seqSurvival H T p ≤ 1 := by
  induction T generalizing p with
  | zero => exact Kernel.outside_le_one _ _
  | succ T ih =>
    have hin : (H p.1).expect (fun a => Kernel.outside (Set.diagonal V) (a, p.2) *
        (H p.2).expect fun b => seqSurvival H T (a, b)) ≤ 1 := by
      calc _ ≤ (H p.1).expect (fun _ => (1 : ℝ)) := by
            refine Distribution.expect_mono _ fun a => ?_
            refine mul_le_one₀ (Kernel.outside_le_one _ _)
              (Distribution.expect_nonneg _ fun b => seqSurvival_nonneg H T _) ?_
            calc _ ≤ (H p.2).expect (fun _ => (1 : ℝ)) := Distribution.expect_mono _ fun b => ih _
              _ = 1 := Distribution.expect_const _ 1
        _ = 1 := Distribution.expect_const _ 1
    exact mul_le_one₀ (Kernel.outside_le_one _ _)
      (Distribution.expect_nonneg _ fun a => mul_nonneg (Kernel.outside_nonneg _ _)
        (Distribution.expect_nonneg _ fun b => seqSurvival_nonneg H T _)) hin

lemma seqSurvival_diag (H : Kernel V) (T : ℕ) (z : V) : seqSurvival H T (z, z) = 0 := by
  cases T with
  | zero => simp [seqSurvival, outside_diagonal_apply]
  | succ T => simp [seqSurvival, outside_diagonal_apply]

/-- **Sequential meeting time from a potential** (Coppersmith–Tetali–Winkler). -/
lemma seqSurvival_mul_le (H : Kernel V) (F : V × V → ℝ) (hF : ∀ p, 0 ≤ F p)
    (hx : ∀ x y, x ≠ y → (H x).expect (fun a => F (a, y)) ≤ F (x, y) - 1)
    (hy : ∀ x y, x ≠ y → (H y).expect (fun b => F (x, b)) ≤ F (x, y) - 1)
    (T : ℕ) (p : V × V) : (T : ℝ) * seqSurvival H T p ≤ F p := by
  induction T generalizing p with
  | zero => simpa using hF p
  | succ T ih =>
    obtain ⟨x, y⟩ := p
    by_cases hxy : x = y
    · subst hxy
      rw [seqSurvival_diag, mul_zero]
      exact hF _
    · have hle1 := seqSurvival_le_one H (T + 1) (x, y)
      have key : (T : ℝ) * seqSurvival H (T + 1) (x, y) ≤ F (x, y) - 1 := by
        simp only [seqSurvival, outside_diagonal_apply, if_neg hxy, one_mul]
        rw [← Distribution.expect_mul]
        calc (H x).expect (fun a => (T : ℝ) * ((if a = y then (0 : ℝ) else 1) *
              (H y).expect fun b => seqSurvival H T (a, b)))
            ≤ (H x).expect (fun a => F (a, y)) := by
              refine Distribution.expect_mono _ fun a => ?_
              by_cases hay : a = y
              · simp only [if_pos hay, zero_mul, mul_zero]
                exact hF _
              · simp only [if_neg hay, one_mul]
                rw [← Distribution.expect_mul]
                calc _ ≤ (H y).expect (fun b => F (a, b)) :=
                      Distribution.expect_mono _ fun b => ih (a, b)
                  _ ≤ F (a, y) - 1 := hy a y hay
                  _ ≤ F (a, y) := by linarith
          _ ≤ F (x, y) - 1 := hx x y hxy
      push_cast
      linarith

/-- Expected off-diagonal indicator after one move of the second token from the diagonal. -/
lemma expect_outside_self (H : Kernel V) (y : V) :
    (H y).expect (fun b => Kernel.outside (Set.diagonal V) (y, b)) = 1 - (H y).weight y := by
  have hfun : (fun b => Kernel.outside (Set.diagonal V) (y, b)) =
      fun b => 1 - (if y = b then (1 : ℝ) else 0) := by
    funext b
    rw [outside_diagonal_apply]
    split <;> norm_num
  rw [hfun, Distribution.expect_sub, Distribution.expect_const]
  simp [Distribution.expect]

/-- **Synchronous versus sequential walks** (Kanade–Mallmann-Trenn–Sauerwald, Prop. B.9). For a
lazy kernel, a crossing of the synchronous tokens is a meeting with probability at least
`1/2`, so `P(apart at T + 1) ≤ (apart + seqSurvival H T) / 2`. -/
lemma iterate_outside_succ_le (H : Kernel V) (hlazy : ∀ y, 1 / 2 ≤ (H y).weight y) (T : ℕ)
    (p : V × V) :
    (pairWalk H).iterate (T + 1) (Kernel.outside (Set.diagonal V)) p ≤
      (Kernel.outside (Set.diagonal V) p + seqSurvival H T p) / 2 := by
  induction T generalizing p with
  | zero =>
    have := pairWalk_iterate_outside_le_outside H 1 p
    simp only [seqSurvival]
    linarith
  | succ T ih =>
    obtain ⟨x, y⟩ := p
    by_cases hxy : x = y
    · subst hxy
      rw [pairWalk_iterate_outside_diag, seqSurvival_diag, outside_diagonal_apply, if_pos rfl]
      norm_num
    · rw [Kernel.iterate_succ, pairWalk_apply_of_ne _ _ hxy]
      have hinner (a : V) :
          (H y).expect (fun b =>
              (pairWalk H).iterate (T + 1) (Kernel.outside (Set.diagonal V)) (a, b)) ≤
            1 / 2 + 1 / 2 * (Kernel.outside (Set.diagonal V) (a, y) *
              (H y).expect fun b => seqSurvival H T (a, b)) := by
        by_cases hay : a = y
        · subst hay
          rw [outside_diagonal_apply, if_pos rfl, zero_mul, mul_zero, add_zero]
          calc _ ≤ (H a).expect (fun b => Kernel.outside (Set.diagonal V) (a, b)) :=
                Distribution.expect_mono _ fun b =>
                  pairWalk_iterate_outside_le_outside H (T + 1) (a, b)
            _ = 1 - (H a).weight a := expect_outside_self H a
            _ ≤ 1 / 2 := by linarith [hlazy a]
        · rw [outside_diagonal_apply, if_neg hay, one_mul]
          calc _ ≤ (H y).expect (fun b => 1 / 2 + 1 / 2 * seqSurvival H T (a, b)) := by
                refine Distribution.expect_mono _ fun b => (ih (a, b)).trans ?_
                linarith [Kernel.outside_le_one (Set.diagonal V) (a, b)]
            _ = 1 / 2 + 1 / 2 * (H y).expect (fun b => seqSurvival H T (a, b)) := by
                rw [Distribution.expect_add, Distribution.expect_const,
                  Distribution.expect_mul]
      calc _ ≤ (H x).expect (fun a => 1 / 2 + 1 / 2 * (Kernel.outside (Set.diagonal V) (a, y) *
              (H y).expect fun b => seqSurvival H T (a, b))) :=
            Distribution.expect_mono _ hinner
        _ = (Kernel.outside (Set.diagonal V) (x, y) + seqSurvival H (T + 1) (x, y)) / 2 := by
            rw [Distribution.expect_add, Distribution.expect_const, Distribution.expect_mul]
            simp only [seqSurvival, outside_diagonal_apply, if_neg hxy, one_mul]
            ring

/-- **Meeting with probability at least `1/4`.** For a lazy kernel and a potential `F` as in
`seqSurvival_mul_le` bounded by `B`, the tokens are apart after `T + 1` steps with
probability at most `3/4` once `T ≥ 2 B` and `T ≥ 1`. -/
lemma iterate_outside_le_three_quarters (H : Kernel V) (hlazy : ∀ y, 1 / 2 ≤ (H y).weight y)
    (F : V × V → ℝ) (hF : ∀ p, 0 ≤ F p)
    (hx : ∀ x y, x ≠ y → (H x).expect (fun a => F (a, y)) ≤ F (x, y) - 1)
    (hy : ∀ x y, x ≠ y → (H y).expect (fun b => F (x, b)) ≤ F (x, y) - 1)
    {B : ℝ} (hFB : ∀ p, F p ≤ B) {T : ℕ} (hT : 2 * B ≤ T) (hT1 : 1 ≤ T) (p : V × V) :
    (pairWalk H).iterate (T + 1) (Kernel.outside (Set.diagonal V)) p ≤ 3 / 4 := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT1
  have hs : seqSurvival H T p ≤ 1 / 2 := by
    have h1 := seqSurvival_mul_le H F hF hx hy T p
    have h2 := hFB p
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have := iterate_outside_succ_le H hlazy T p
  linarith [Kernel.outside_le_one (Set.diagonal V) p]

end Voter
