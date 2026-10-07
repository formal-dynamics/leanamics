import Voter.Coalescence
import Voter.MeetingRounds
import Voter.Colors
import Dynamics.Phases

/-! # Coalescing random walks for an arbitrary sampling kernel (VOT-6)

Hassin–Peleg §2.4 (Theorem 2.4) and Survey Theorems 6 and 8, for the synchronous voter
dynamics `Voter.transition H` with an arbitrary sampling kernel `H`.

*Two tokens.* `pairWalk H` moves two tokens with the rounds of the voter dynamics: in each
round a vector `r` of sampled neighbours is drawn from `Distribution.independent H` and the
token at `x` moves to `r x`. Tokens at distinct vertices make independent `H`-steps; once they
meet they move together. Hence the probability that they are apart after `T` steps is the
probability that two independent `H`-walks have not met within `T` steps.

*Duality.* By `runRounds_eq_comp` the voter colours at time `T` are read through the backward
map of the rounds, whose point images are coalescing `H`-walks (the rounds are i.i.d., so
reading them backwards does not change their law). A union bound over the walks that must meet
the walk of a fixed vertex bounds nonconsensus (`iterate_disagreement_le_pairWalk`).

*Time.* If two tokens meet within `T₀` steps with probability at least `1/2` from every pair of
start vertices, then they are apart after `k T₀` steps with probability at most `2^{-k}`, and
consensus fails after `k T₀` rounds with probability at most `(n - 1) 2^{-k}`
(`iterate_disagreement_le_of_meeting`, the tail form of Hassin–Peleg Theorem 2.4).
-/

namespace Voter
open Dynamics Finset

variable {V C : Type*} [Fintype V] [DecidableEq V]

/-- Two tokens driven by the common rounds of the voter dynamics with sampling kernel `H`
(Survey Definition 5 with two tokens): the token at `x` moves to `r x`, where the round `r`
is drawn from `Distribution.independent H`. The diagonal is absorbing, and off the diagonal
the two tokens make independent `H`-steps. -/
noncomputable def pairWalk (H : Kernel V) : Kernel (V × V) :=
  fun p => (Distribution.independent H).map fun r => (r p.1, r p.2)

/-! ### The two-token walk: diagonal, independence, projection -/

omit [Fintype V] in
/-- Being apart is the indicator of lying off the diagonal. -/
lemma outside_diagonal_apply (a b : V) :
    Kernel.outside (Set.diagonal V) (a, b) = if a = b then 0 else 1 := by
  by_cases h : a = b
  · rw [if_pos h, Kernel.outside_of_mem (Set.mem_diagonal_iff.mpr h)]
  · rw [if_neg h, Kernel.outside_of_not_mem (fun hm => h (Set.mem_diagonal_iff.mp hm))]

/-- The probability of being apart is the iterated off-diagonal indicator. -/
lemma event_pairWalk (H : Kernel V) (T : ℕ) (p : V × V) :
    (pairWalk H).event (fun q => q.1 ≠ q.2) T p =
      (pairWalk H).iterate T (Kernel.outside (Set.diagonal V)) p := by
  classical
  unfold Kernel.event
  congr 1
  funext q
  obtain ⟨a, b⟩ := q
  rw [outside_diagonal_apply]
  by_cases h : a = b <;> simp [h]

/-- Two tokens on the same vertex move together. -/
lemma pairWalk_apply_diag (H : Kernel V) (f : V × V → ℝ) (z : V) :
    (pairWalk H).apply f (z, z) = (H z).expect fun a => f (a, a) := by
  simp only [Kernel.apply, pairWalk, Distribution.map_expect]
  exact Distribution.independent_expect_eval H z (fun a => f (a, a))

/-- Two tokens on distinct vertices make independent `H`-steps. -/
lemma pairWalk_apply_of_ne (H : Kernel V) (f : V × V → ℝ) {x y : V} (hxy : x ≠ y) :
    (pairWalk H).apply f (x, y) = (H x).expect fun a => (H y).expect fun b => f (a, b) := by
  simp only [Kernel.apply, pairWalk, Distribution.map_expect]
  exact independent_expect_pair H hxy (fun a b => f (a, b))

/-- Observables vanishing on the diagonal keep vanishing there: the diagonal is absorbing. -/
lemma pairWalk_iterate_diag (H : Kernel V) {f : V × V → ℝ} (hf : ∀ z, f (z, z) = 0)
    (T : ℕ) (z : V) : (pairWalk H).iterate T f (z, z) = 0 := by
  induction T generalizing z with
  | zero => exact hf z
  | succ T ih =>
    rw [Kernel.iterate_succ, pairWalk_apply_diag]
    simp only [ih, Distribution.expect_const]

/-- The tokens started on the diagonal are never apart. -/
lemma pairWalk_iterate_outside_diag (H : Kernel V) (T : ℕ) (z : V) :
    (pairWalk H).iterate T (Kernel.outside (Set.diagonal V)) (z, z) = 0 :=
  pairWalk_iterate_diag H (fun z => by rw [outside_diagonal_apply, if_pos rfl]) T z

lemma pairWalk_iterate_outside_nonneg (H : Kernel V) (T : ℕ) (p : V × V) :
    0 ≤ (pairWalk H).iterate T (Kernel.outside (Set.diagonal V)) p :=
  (pairWalk H).iterate_nonneg T (Kernel.outside_nonneg _) p

lemma pairWalk_iterate_outside_le_one (H : Kernel V) (T : ℕ) (p : V × V) :
    (pairWalk H).iterate T (Kernel.outside (Set.diagonal V)) p ≤ 1 :=
  (pairWalk H).iterate_le_one T (Kernel.outside_le_one _) p

/-- Being apart after `T` steps is at most the indicator of starting apart. -/
lemma pairWalk_iterate_outside_le_outside (H : Kernel V) (T : ℕ) (p : V × V) :
    (pairWalk H).iterate T (Kernel.outside (Set.diagonal V)) p ≤
      Kernel.outside (Set.diagonal V) p := by
  obtain ⟨x, y⟩ := p
  by_cases h : x = y
  · subst h
    rw [pairWalk_iterate_outside_diag, outside_diagonal_apply, if_pos rfl]
  · rw [outside_diagonal_apply, if_neg h]
    exact pairWalk_iterate_outside_le_one H T (x, y)

/-- The probability of being apart does not increase with time. -/
lemma pairWalk_iterate_outside_antitone (H : Kernel V) (p : V × V) :
    Antitone fun T => (pairWalk H).iterate T (Kernel.outside (Set.diagonal V)) p := by
  refine antitone_nat_of_succ_le fun T => ?_
  rw [Kernel.iterate_add_time (pairWalk H) T 1]
  exact (pairWalk H).iterate_mono T (pairWalk_iterate_outside_le_outside H 1) p

/-- **Submultiplicativity.** If from every pair the tokens are apart after `T₀` steps with
probability at most `q`, then they are apart after `k T₀` steps with probability at most
`q^k`. -/
lemma pairWalk_iterate_outside_mul_le (H : Kernel V) {T₀ : ℕ} {q : ℝ} (hq : 0 ≤ q)
    (h : ∀ x y : V, (pairWalk H).iterate T₀ (Kernel.outside (Set.diagonal V)) (x, y) ≤ q)
    (k : ℕ) (p : V × V) :
    (pairWalk H).iterate (k * T₀) (Kernel.outside (Set.diagonal V)) p ≤
      q ^ k * Kernel.outside (Set.diagonal V) p := by
  have hstep (p : V × V) : (pairWalk H).iterate T₀ (Kernel.outside (Set.diagonal V)) p ≤
      q * Kernel.outside (Set.diagonal V) p := by
    obtain ⟨x, y⟩ := p
    by_cases hxy : x = y
    · subst hxy
      rw [pairWalk_iterate_outside_diag, outside_diagonal_apply, if_pos rfl, mul_zero]
    · rw [outside_diagonal_apply, if_neg hxy, mul_one]
      exact h x y
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Kernel.iterate_add_time]
    calc (pairWalk H).iterate (k * T₀)
          ((pairWalk H).iterate T₀ (Kernel.outside (Set.diagonal V))) p
        ≤ (pairWalk H).iterate (k * T₀)
            (fun p => q * Kernel.outside (Set.diagonal V) p) p :=
          (pairWalk H).iterate_mono _ hstep p
      _ = q * (pairWalk H).iterate (k * T₀) (Kernel.outside (Set.diagonal V)) p := by
          rw [Kernel.iterate_mul]
      _ ≤ q * (q ^ k * Kernel.outside (Set.diagonal V) p) :=
          mul_le_mul_of_nonneg_left (ih p) hq
      _ = q ^ (k + 1) * Kernel.outside (Set.diagonal V) p := by ring

/-- Rounds composed on the left, read at two vertices, are the two-token walk. -/
lemma iterate_leftRounds_pair (H : Kernel V) (v w : V) (g : V × V → ℝ) (T : ℕ) (W : V → V) :
    (leftRounds H).iterate T (fun W => g (W v, W w)) W = (pairWalk H).iterate T g (W v, W w) := by
  induction T generalizing W with
  | zero => rfl
  | succ T ih =>
    rw [Kernel.iterate_succ, Kernel.iterate_succ]
    have hfun : (leftRounds H).iterate T (fun W => g (W v, W w)) =
        fun W => (pairWalk H).iterate T g (W v, W w) := funext ih
    rw [hfun]
    simp only [Kernel.apply, leftRounds, pairWalk, Distribution.map_expect]
    rfl

/-- **Duality and union bound** (Survey Theorem 6; Hassin–Peleg §2.4). For every sampling
kernel `H`, every colouring `s`, every time `T` and every vertex `u₀`, the probability that the
voter dynamics has not reached consensus after `T` rounds is at most the sum over `v ≠ u₀` of
the probability that the tokens started at `v` and `u₀` are still apart after `T` steps. -/
theorem iterate_disagreement_le_pairWalk [Fintype C] (H : Kernel V) (s : Config V C) (T : ℕ)
    (u₀ : V) :
    (transition H).iterate T disagreement s ≤
      ∑ v ∈ univ.erase u₀, (pairWalk H).event (fun p => p.1 ≠ p.2) T (v, u₀) := by
  -- read the colours through the voter dynamics on maps started from the identity
  rw [show (transition H).iterate T disagreement s =
      (transition H).iterate T (fun B : V → V => disagreement (s ∘ B)) id from
    iterate_project H s disagreement T id]
  calc (transition H).iterate T (fun B : V → V => disagreement (s ∘ B)) id
      ≤ (transition H).iterate T
          (fun B : V → V => ∑ v ∈ univ.erase u₀, if B v = B u₀ then (0 : ℝ) else 1) id :=
        (transition H).iterate_mono T (fun B => disagreement_runRounds_le s [B] u₀) id
    _ = ∑ v ∈ univ.erase u₀,
          (transition H).iterate T (fun B : V → V => if B v = B u₀ then (0 : ℝ) else 1) id :=
        kernel_iterate_finset_sum _ _ _ _ _
    _ = ∑ v ∈ univ.erase u₀, (pairWalk H).event (fun p => p.1 ≠ p.2) T (v, u₀) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [iterate_transition_eq_leftRounds, event_pairWalk]
        have hfun : (fun W : V → V => if (id ∘ W) v = (id ∘ W) u₀ then (0 : ℝ) else 1) =
            fun W => Kernel.outside (Set.diagonal V) (W v, W u₀) := by
          funext W
          rw [outside_diagonal_apply]
          rfl
        rw [hfun, iterate_leftRounds_pair]
        rfl

/-- **Consensus time from meeting time** (Hassin–Peleg Theorem 2.4, tail form). If from every
pair of start vertices two tokens are apart after `T₀` steps with probability at most `1/2`,
then after `k T₀` rounds the voter dynamics has not reached consensus with probability at most
`(n - 1) 2^{-k}`, from every initial colouring. -/
theorem iterate_disagreement_le_of_meeting [Nonempty V] [Fintype C] (H : Kernel V) {T₀ : ℕ}
    (hmeet : ∀ x y : V, (pairWalk H).event (fun p => p.1 ≠ p.2) T₀ (x, y) ≤ 1 / 2)
    (s : Config V C) (k : ℕ) :
    (transition H).iterate (k * T₀) disagreement s ≤
      ((Fintype.card V : ℝ) - 1) * (1 / 2) ^ k := by
  obtain ⟨u₀⟩ := ‹Nonempty V›
  have hsub := pairWalk_iterate_outside_mul_le H (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (fun x y => by rw [← event_pairWalk]; exact hmeet x y) k
  calc (transition H).iterate (k * T₀) disagreement s
      ≤ ∑ v ∈ univ.erase u₀, (pairWalk H).event (fun p => p.1 ≠ p.2) (k * T₀) (v, u₀) :=
        iterate_disagreement_le_pairWalk H s (k * T₀) u₀
    _ ≤ ∑ v ∈ univ.erase u₀, ((1 : ℝ) / 2) ^ k := by
        refine Finset.sum_le_sum fun v _ => ?_
        rw [event_pairWalk]
        have hone := Kernel.outside_le_one (Set.diagonal V) (v, u₀)
        have hpow : (0 : ℝ) ≤ (1 / 2) ^ k := by positivity
        calc (pairWalk H).iterate (k * T₀) (Kernel.outside (Set.diagonal V)) (v, u₀)
            ≤ (1 / 2) ^ k * Kernel.outside (Set.diagonal V) (v, u₀) := hsub (v, u₀)
          _ ≤ (1 / 2) ^ k * 1 := mul_le_mul_of_nonneg_left hone hpow
          _ = (1 / 2) ^ k := mul_one _
    _ = ((Fintype.card V : ℝ) - 1) * (1 / 2) ^ k := by
        rw [Finset.sum_const, Finset.card_erase_of_mem (mem_univ u₀), Finset.card_univ,
          nsmul_eq_mul, Nat.cast_sub (Nat.succ_le_of_lt (Fintype.card_pos (α := V))),
          Nat.cast_one]

end Voter
