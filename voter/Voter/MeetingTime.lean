import Voter.MeetingDrift
import Voter.MeetingHitting

/-! # Meeting time of two lazy random walks on a connected graph (VOT-6)

Hassin–Peleg §2.4 (Fact 2.3 and Lemma 2.4, uniform case), for lazy walks: on a connected graph
with `n` vertices, two synchronous lazy random walks have met within `O(n³)` steps with
probability at least `1/2`, from every pair of start vertices; hence they are apart after
`k · O(n³)` steps with probability at most `2^{-k}`.

The walks are lazy (stay with probability `1/2`, otherwise move to a uniformly random
neighbour): Hassin–Peleg's polling with self-loop weight `1/2`. This makes every connected
graph aperiodic, as Survey Theorem 8 requires, and it is the setting of Cooper, Elsässer, Ono,
Radzik (SIAM J. Discrete Math. 2013) and of Kanade, Mallmann-Trenn, Sauerwald (SODA 2019),
whose Proposition B.9 gives `t_meet ≤ 4 t_hit`.

Proof (`lazy_meeting_core`): the lazy hitting times of `Voter/MeetingHitting.lean` satisfy
`h_y x + h_x y ≤ 4 vol (n − 1) ≤ 4 n³`; the potential `meetingPotential` built from them drops by
one under a lazy step of either token; `Voter/MeetingDrift.lean` turns it into a meeting
probability of at least `1/4` within `16 n³ + 1` steps, and three such blocks give `1/2`
within `3 (16 n³ + 1) ≤ 51 n³` steps.
-/

namespace Voter
open Dynamics Finset

universe u

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Lazy uniform neighbour sampling: a vertex samples itself with probability `1/2` and
otherwise a uniformly random neighbour (the lazy version of `uniformNeighbor`). In the voter
dynamics `transition (lazyNeighbor G hd)` every vertex keeps its colour with probability `1/2`
and otherwise copies the colour of a uniformly random neighbour. -/
noncomputable def lazyNeighbor (G : SimpleGraph V) [DecidableRel G.Adj]
    (hd : ∀ i, 0 < G.degree i) : Kernel V := fun i => {
  weight := fun j => (if j = i then 1 / 2 else 0) + (uniformNeighbor G hd i).weight j / 2
  nonneg := fun j => add_nonneg (by split <;> norm_num)
    (div_nonneg ((uniformNeighbor G hd i).nonneg j) (by norm_num))
  sum_one := by
    rw [sum_add_distrib, Fintype.sum_ite_eq', ← sum_div, (uniformNeighbor G hd i).sum_one]
    norm_num }

/-! ### The lazy kernel and the meeting potential -/

section Lazy
variable {G : SimpleGraph V} [DecidableRel G.Adj] (hd : ∀ i, 0 < G.degree i)

/-- The lazy walk stays put with probability `1/2`. -/
lemma lazyNeighbor_weight_self (y : V) : (lazyNeighbor G hd y).weight y = 1 / 2 := by
  simp [lazyNeighbor, uniformNeighbor]

/-- Expectation under the lazy kernel: half the current value plus half the neighbour
average. -/
lemma lazyNeighbor_expect (x : V) (f : V → ℝ) :
    (lazyNeighbor G hd x).expect f =
      f x / 2 + (∑ w ∈ G.neighborFinset x, f w) / (2 * G.degree x) := by
  have hsplit (w : V) : (lazyNeighbor G hd x).weight w * f w =
      (if w = x then f x / 2 else 0) + (if G.Adj x w then f w / (2 * G.degree x) else 0) := by
    simp only [lazyNeighbor, uniformNeighbor]
    by_cases hw : w = x
    · subst hw
      simp only [if_true, SimpleGraph.irrefl, if_false]
      ring
    · by_cases ha : G.Adj x w
      · simp only [if_neg hw, if_pos ha]
        ring
      · simp only [if_neg hw, if_neg ha]
        ring
  simp only [Distribution.expect, hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [← Finset.sum_filter, Finset.sum_div]
  congr 1
  exact Finset.sum_congr (by ext w; simp) fun _ _ => rfl

/-- Hitting times drop by one in expectation under a lazy step away from the target. -/
lemma lazyNeighbor_expect_hitting (hc : G.Connected) {x y : V} (hxy : x ≠ y) :
    (lazyNeighbor G hd x).expect (hitting G hc y) = hitting G hc y x - 1 := by
  have hlap := hitting_lapMatrix_of_ne hc hxy
  rw [SimpleGraph.lapMatrix_mulVec_apply] at hlap
  have hS : ∑ w ∈ G.neighborFinset x, hitting G hc y w =
      G.degree x * hitting G hc y x - 2 * G.degree x := by linarith
  have hdx : (G.degree x : ℝ) ≠ 0 := by exact_mod_cast (hd x).ne'
  rw [lazyNeighbor_expect, hS]
  field_simp
  ring

/-- The Coppersmith–Tetali–Winkler potential `Z_{x,y} − E_π T_y + B₀` of two lazy walks at
`(x, y)`; by `hitting_symm` it is also `Z_{y,x} − E_π T_x + B₀`. -/
noncomputable def meetingPotential (hc : G.Connected) (B₀ : ℝ) (p : V × V) : ℝ :=
  hitting G hc p.2 p.1 - (∑ z, (G.degree z : ℝ) * hitting G hc p.2 z) / volume G + B₀

omit hd in
lemma meetingPotential_swap [Nonempty V] (hd : ∀ i, 0 < G.degree i) (hc : G.Connected)
    (B₀ : ℝ) (x y : V) :
    meetingPotential hc B₀ (x, y) =
      hitting G hc x y - (∑ z, (G.degree z : ℝ) * hitting G hc x z) / volume G + B₀ := by
  have hvol := volume_pos G hd
  have hs := hitting_symm hc x y
  simp only [meetingPotential]
  have hv : volume G ≠ 0 := hvol.ne'
  have e (a S : ℝ) : S / volume G = (S - volume G * a) / volume G + a := by
    field_simp
    ring
  rw [e (hitting G hc y x), e (hitting G hc x y) (∑ z, (G.degree z : ℝ) * hitting G hc x z), hs]
  ring

variable (hc : G.Connected) {B₀ : ℝ} (hB : ∀ x y, hitting G hc y x ≤ B₀)
include hd hB

lemma meetingPotential_nonneg [Nonempty V] (p : V × V) : 0 ≤ meetingPotential hc B₀ p := by
  have hvol := volume_pos G hd
  have hsum : (∑ z, (G.degree z : ℝ) * hitting G hc p.2 z) / volume G ≤ B₀ := by
    rw [div_le_iff₀ hvol, volume, Finset.mul_sum]
    exact Finset.sum_le_sum fun z _ => by
      rw [mul_comm B₀]
      exact mul_le_mul_of_nonneg_left (hB z p.2) (by positivity)
  have := hitting_nonneg hc hd p.2 p.1
  simp only [meetingPotential]
  linarith

lemma meetingPotential_le [Nonempty V] (p : V × V) : meetingPotential hc B₀ p ≤ 2 * B₀ := by
  have hvol := volume_pos G hd
  have hsum : 0 ≤ (∑ z, (G.degree z : ℝ) * hitting G hc p.2 z) / volume G :=
    div_nonneg (Finset.sum_nonneg fun z _ =>
      mul_nonneg (by positivity) (hitting_nonneg hc hd p.2 z)) hvol.le
  have := hB p.1 p.2
  simp only [meetingPotential]
  linarith

omit hB in
/-- The potential drops by one in expectation when the first token makes a lazy step. -/
lemma meetingPotential_expect_fst {x y : V} (hxy : x ≠ y) :
    (lazyNeighbor G hd x).expect (fun a => meetingPotential hc B₀ (a, y)) =
      meetingPotential hc B₀ (x, y) - 1 := by
  simp only [meetingPotential]
  rw [Distribution.expect_add, Distribution.expect_sub, Distribution.expect_const,
    Distribution.expect_const, lazyNeighbor_expect_hitting hd hc hxy]
  ring

omit hB in
/-- The potential drops by one in expectation when the second token makes a lazy step. -/
lemma meetingPotential_expect_snd [Nonempty V] {x y : V} (hxy : x ≠ y) :
    (lazyNeighbor G hd y).expect (fun b => meetingPotential hc B₀ (x, b)) =
      meetingPotential hc B₀ (x, y) - 1 := by
  simp only [meetingPotential_swap hd hc]
  rw [Distribution.expect_add, Distribution.expect_sub, Distribution.expect_const,
    Distribution.expect_const, lazyNeighbor_expect_hitting hd hc (Ne.symm hxy)]
  ring

end Lazy

/-- `3 (16 n³ + 1) ≤ 51 n³` for `n ≥ 1`. -/
lemma meetingTime_le {n : ℕ} (hn : 1 ≤ n) :
    ((3 * (16 * n ^ 3 + 1) : ℕ) : ℝ) ≤ 51 * (n : ℝ) ^ 3 := by
  have h1 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := by exact_mod_cast Nat.one_le_pow _ _ hn
  push_cast
  linarith

/-- **Meeting time with explicit constant.** On a connected graph with `n` vertices, two lazy
walks are apart after `3 (16 n³ + 1)` steps with probability at most `1/2`, from every pair of
start vertices. -/
lemma lazy_meeting_core {G : SimpleGraph V} [DecidableRel G.Adj] (hd : ∀ i, 0 < G.degree i)
    (hc : G.Connected) (p : V × V) :
    (pairWalk (lazyNeighbor G hd)).iterate (3 * (16 * Fintype.card V ^ 3 + 1))
      (Kernel.outside (Set.diagonal V)) p ≤ 1 / 2 := by
  haveI : Nonempty V := hc.nonempty
  set n : ℝ := (Fintype.card V : ℝ) with hn_def
  have hcard : 1 ≤ Fintype.card V := Fintype.card_pos
  have hn1 : (1 : ℝ) ≤ n := by rw [hn_def]; exact_mod_cast hcard
  -- the volume is at most `n (n - 1)`
  have hvol : volume G ≤ n * (n - 1) := by
    calc volume G = ∑ i, (G.degree i : ℝ) := rfl
      _ ≤ ∑ _i : V, (n - 1) := Finset.sum_le_sum fun i _ => by
          have := G.degree_lt_card_verts i
          have : (G.degree i : ℝ) + 1 ≤ n := by rw [hn_def]; exact_mod_cast this
          linarith
      _ = n * (n - 1) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hvol0 : 0 ≤ volume G := (volume_pos G hd).le
  -- hitting times are at most `4 n³`
  have hB : ∀ x y, hitting G hc y x ≤ 4 * n ^ 3 := by
    intro x y
    have h1 := hitting_add_hitting_le hc hd x y
    have h2 := hitting_nonneg hc hd x y
    have h3 : 4 * volume G * (n - 1) ≤ 4 * (n * (n - 1)) * (n - 1) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    nlinarith
  have h34 (q : V × V) :
      (pairWalk (lazyNeighbor G hd)).iterate (16 * Fintype.card V ^ 3 + 1)
        (Kernel.outside (Set.diagonal V)) q ≤ 3 / 4 := by
    refine iterate_outside_le_three_quarters (lazyNeighbor G hd)
      (fun y => (lazyNeighbor_weight_self hd y).ge) (meetingPotential hc (4 * n ^ 3))
      (meetingPotential_nonneg hd hc hB) (fun x y hxy => (meetingPotential_expect_fst hd hc hxy).le)
      (fun x y hxy => (meetingPotential_expect_snd hd hc hxy).le)
      (meetingPotential_le hd hc hB) ?_ ?_ q
    · push_cast
      linarith
    · have := Nat.one_le_pow 3 _ hcard
      omega
  have hsub := pairWalk_iterate_outside_mul_le (lazyNeighbor G hd) (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (fun x y => h34 (x, y)) 3 p
  have hone := Kernel.outside_le_one (Set.diagonal V) p
  have hzero := Kernel.outside_nonneg (Set.diagonal V) p
  calc _ ≤ (3 / 4) ^ 3 * Kernel.outside (Set.diagonal V) p := by
        simpa [mul_comm] using hsub
    _ ≤ 1 / 2 := by nlinarith

/-- **Iterated meeting time with explicit constant.** On a connected graph with `n` vertices,
two lazy walks are apart after `T ≥ 51 k n³` steps with probability at most `2^{-k}`. -/
lemma lazy_apart_le_pow {G : SimpleGraph V} [DecidableRel G.Adj] (hd : ∀ i, 0 < G.degree i)
    (hc : G.Connected) (x y : V) (k T : ℕ) (hT : k * 51 * (Fintype.card V : ℝ) ^ 3 ≤ T) :
    (pairWalk (lazyNeighbor G hd)).iterate T (Kernel.outside (Set.diagonal V)) (x, y) ≤
      (1 / 2) ^ k := by
  haveI : Nonempty V := hc.nonempty
  have hT₀ : k * (3 * (16 * Fintype.card V ^ 3 + 1)) ≤ T := by
    have h51 := meetingTime_le (Fintype.card_pos (α := V))
    have : ((k * (3 * (16 * Fintype.card V ^ 3 + 1)) : ℕ) : ℝ) ≤ T := by
      rw [Nat.cast_mul]
      calc (k : ℝ) * ((3 * (16 * Fintype.card V ^ 3 + 1) : ℕ) : ℝ)
          ≤ k * (51 * (Fintype.card V : ℝ) ^ 3) :=
            mul_le_mul_of_nonneg_left h51 (Nat.cast_nonneg k)
        _ = k * 51 * (Fintype.card V : ℝ) ^ 3 := by ring
        _ ≤ T := hT
    exact_mod_cast this
  have hone := Kernel.outside_le_one (Set.diagonal V) (x, y)
  have hpow : (0 : ℝ) ≤ (1 / 2) ^ k := by positivity
  calc _ ≤ (pairWalk (lazyNeighbor G hd)).iterate (k * (3 * (16 * Fintype.card V ^ 3 + 1)))
        (Kernel.outside (Set.diagonal V)) (x, y) :=
        pairWalk_iterate_outside_antitone _ (x, y) hT₀
    _ ≤ (1 / 2) ^ k * Kernel.outside (Set.diagonal V) (x, y) :=
        pairWalk_iterate_outside_mul_le _ (by norm_num)
          (fun a b => lazy_meeting_core hd hc (a, b)) k (x, y)
    _ ≤ (1 / 2) ^ k := by nlinarith

/-- **Meeting time** (Hassin–Peleg Fact 2.3 and Lemma 2.4, uniform case, for lazy walks). There
is a constant `A > 0` such that on every connected graph with `n` vertices (all degrees
positive), from every pair of start vertices `x, y`, two synchronous lazy random walks have not
met after `T ≥ A n³` steps with probability at most `1/2`. -/
theorem lazy_meeting_le_half :
    ∃ A : ℝ, 0 < A ∧ ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj], G.Connected →
      ∀ (hd : ∀ i, 0 < G.degree i) (x y : V) (T : ℕ), A * (Fintype.card V : ℝ) ^ 3 ≤ T →
        (pairWalk (lazyNeighbor G hd)).event (fun p => p.1 ≠ p.2) T (x, y) ≤ 1 / 2 := by
  refine ⟨51, by norm_num, ?_⟩
  intro V _ _ G _ hc hd x y T hT
  haveI : Nonempty V := hc.nonempty
  rw [event_pairWalk]
  have hT₀ : 3 * (16 * Fintype.card V ^ 3 + 1) ≤ T := by
    have := (meetingTime_le (Fintype.card_pos (α := V))).trans hT
    exact_mod_cast this
  exact (pairWalk_iterate_outside_antitone _ (x, y) hT₀).trans (lazy_meeting_core hd hc (x, y))

/-- **Iterated meeting time** (Hassin–Peleg §2.4, for lazy walks). There is a constant `A > 0`
such that on every connected graph with `n` vertices (all degrees positive), from every pair of
start vertices, two synchronous lazy random walks have not met after `T ≥ k A n³` steps with
probability at most `2^{-k}`. -/
theorem lazy_meeting_le_pow :
    ∃ A : ℝ, 0 < A ∧ ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj], G.Connected →
      ∀ (hd : ∀ i, 0 < G.degree i) (x y : V) (k T : ℕ),
        k * A * (Fintype.card V : ℝ) ^ 3 ≤ T →
          (pairWalk (lazyNeighbor G hd)).event (fun p => p.1 ≠ p.2) T (x, y) ≤ (1 / 2) ^ k := by
  refine ⟨51, by norm_num, ?_⟩
  intro V _ _ G _ hc hd x y k T hT
  rw [event_pairWalk]
  exact lazy_apart_le_pow hd hc x y k T hT

end Voter
