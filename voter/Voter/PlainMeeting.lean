import Voter.PlainCover

/-! # Meeting time of two plain random walks on a connected nonbipartite graph (VOT-6)

Hassin–Peleg Lemma 2.4 and Fact 2.3 (uniform case), for the plain walk: on a connected
nonbipartite graph with `n` vertices, two synchronous (simultaneous) uniform-neighbour random
walks are apart after `T` steps with probability at most `8 n³ / T`, from every pair of start
vertices; hence they meet within `16 n³` steps with probability at least `1/2`. This is the
hypothesis `hmeet` of `iterate_disagreement_le_of_meeting`.

*Why the lazy argument does not apply.* For the plain walk two adjacent tokens can swap
without meeting, so the Coppersmith–Tetali–Winkler potential of `Voter/MeetingTime.lean` read
on `G` has no drift at adjacent pairs, and the synchronous-versus-sequential comparison of
`Voter/MeetingDrift.lean` needs laziness.

*Route (Hassin–Peleg's reduction to the double cover `G̃`, following Tetali and Winkler).* A
simultaneous step of the two tokens at `(x, y)` is, on `G̃ = doubleCover G`, a step of the
first token from `(x, 0)` to `(x', 1)` followed by a step of the second token from `(y, 0)` to
`(y', 1)`. Between the two moves the tokens lie in different layers of `G̃`, hence are never
equal there. So the Coppersmith–Tetali–Winkler potential `Φ` of `G̃` (`meetingPotential`)
drops by `2` at each of the two moves whenever `x ≠ y`, by the hitting-time equations of `G̃`
(connected by `doubleCover_connected`), and the layer symmetry `hitting_doubleCover_flip`
brings the tokens back to layer `0`. The potential `plainPotential (x, y) = Φ((x, 0), (y, 0))`
thus drops by exactly `4` per synchronous step off the diagonal (`plainPotential_drift`), and
the commute bound `hitting_add_hitting_le` on `G̃` (`2n` vertices, volume `2 vol G ≤ 2 n²`)
bounds it by `32 n³`. The additive drift lemma `pairWalk_apart_mul_le` gives
`4 T · P(apart at T) ≤ 32 n³`.
-/

namespace Voter
open Dynamics Finset

universe u

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Additive drift for the two-token walk.** If a nonnegative potential `F` drops by at least
`c` in expectation under one step of the two-token walk from every pair of distinct vertices,
then `c T · P(apart after T steps) ≤ F p`. -/
lemma pairWalk_apart_mul_le (H : Kernel V) (F : V × V → ℝ) (hF : ∀ p, 0 ≤ F p) {c : ℝ}
    (hdrift : ∀ x y, x ≠ y → (pairWalk H).apply F (x, y) ≤ F (x, y) - c) (T : ℕ)
    (p : V × V) :
    c * T * (pairWalk H).iterate T (Kernel.outside (Set.diagonal V)) p ≤ F p := by
  by_cases hc : 0 ≤ c
  · -- truncate the potential on the diagonal, where the walk has already met
    let F' : V × V → ℝ := fun q => if q.1 = q.2 then 0 else F q
    have hF'0 : ∀ q, 0 ≤ F' q := by
      intro q
      by_cases h : q.1 = q.2 <;> simp [F', h, hF]
    have hF'le : ∀ q, F' q ≤ F q := by
      intro q
      by_cases h : q.1 = q.2 <;> simp [F', h, hF]
    let g : ℕ → V × V → ℝ := fun t q =>
      (pairWalk H).iterate t (Kernel.outside (Set.diagonal V)) q
    have hstep (q : V × V) :
        (pairWalk H).apply F' q ≤ F' q - c * Kernel.outside (Set.diagonal V) q := by
      obtain ⟨x, y⟩ := q
      by_cases hxy : x = y
      · subst y
        rw [pairWalk_apply_diag, outside_diagonal_apply, if_pos rfl]
        have : (fun a => F' (a, a)) = fun _ => (0 : ℝ) := by
          funext a
          simp [F']
        rw [this, Distribution.expect_const]
        simp [F']
      · have happ : (pairWalk H).apply F' (x, y) ≤ (pairWalk H).apply F (x, y) := by
          simp only [Kernel.apply]
          exact ((pairWalk H) (x, y)).expect_mono hF'le
        rw [outside_diagonal_apply, if_neg hxy, mul_one,
          show F' (x, y) = F (x, y) by simp [F', hxy]]
        exact happ.trans (hdrift x y hxy)
    have hind : ∀ n q, (pairWalk H).iterate n F' q +
        c * ∑ t ∈ Finset.range n, g t q ≤ F' q := by
      intro n
      induction n with
      | zero =>
        intro q
        simp
      | succ n ih =>
        intro q
        have hineq : (pairWalk H).iterate (n + 1) F' q ≤
            (pairWalk H).iterate n F' q + (-c) * g n q := by
          rw [Kernel.iterate_add_time (pairWalk H) n 1]
          have hfun : (fun r => F' r - c * Kernel.outside (Set.diagonal V) r) =
              fun r => F' r + (-c) * Kernel.outside (Set.diagonal V) r := by
            funext r
            ring
          calc (pairWalk H).iterate n ((pairWalk H).apply F') q
              ≤ (pairWalk H).iterate n
                  (fun r => F' r - c * Kernel.outside (Set.diagonal V) r) q :=
                (pairWalk H).iterate_mono n hstep q
            _ = (pairWalk H).iterate n F' q + (-c) * g n q := by
                rw [hfun, Kernel.iterate_add, Kernel.iterate_mul]
        have hsum : ∑ t ∈ Finset.range (n + 1), g t q =
            ∑ t ∈ Finset.range n, g t q + g n q := Finset.sum_range_succ _ _
        calc (pairWalk H).iterate (n + 1) F' q + c * ∑ t ∈ Finset.range (n + 1), g t q
            = (pairWalk H).iterate (n + 1) F' q +
                c * (∑ t ∈ Finset.range n, g t q + g n q) := by rw [hsum]
          _ ≤ ((pairWalk H).iterate n F' q + (-c) * g n q) +
                c * (∑ t ∈ Finset.range n, g t q + g n q) :=
              by linarith [hineq]
          _ = (pairWalk H).iterate n F' q + c * ∑ t ∈ Finset.range n, g t q := by ring
          _ ≤ F' q := ih q
    have hnn := (pairWalk H).iterate_nonneg T hF'0 p
    have hsumle : c * ∑ t ∈ Finset.range T, g t p ≤ F' p := by
      have := hind T p
      linarith
    have hTg : (T : ℝ) * g T p ≤ ∑ t ∈ Finset.range T, g t p := by
      calc (T : ℝ) * g T p = ∑ _t ∈ Finset.range T, g T p := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ ≤ ∑ t ∈ Finset.range T, g t p :=
            Finset.sum_le_sum fun t ht =>
              pairWalk_iterate_outside_antitone H p (Finset.mem_range.mp ht).le
    calc c * (T : ℝ) * g T p ≤ c * ∑ t ∈ Finset.range T, g t p := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left hTg hc
      _ ≤ F' p := hsumle
      _ ≤ F p := hF'le p
  · replace hc := not_le.mp hc
    have hg := pairWalk_iterate_outside_nonneg H T p
    have hnonpos : c * (T : ℝ) * (pairWalk H).iterate T
        (Kernel.outside (Set.diagonal V)) p ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hc.le (Nat.cast_nonneg T)) hg
    exact hnonpos.trans (hF p)

section Plain
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The meeting potential of two plain walks at `(x, y)`: the Coppersmith–Tetali–Winkler
potential `Φ` of the double cover `G̃` (`meetingPotential`, built from the hitting times of
`G̃`) at `((x, 0), (y, 0))`. -/
noncomputable def plainPotential (hc' : (doubleCover G).Connected) (B₀ : ℝ) (p : V × V) : ℝ :=
  meetingPotential hc' B₀ ((p.1, false), (p.2, false))

/-- **Hitting times of the double cover** (Hassin–Peleg Fact 2.3 on `G̃`, via the commute
bound): every hitting time of `G̃` is at most `16 n³`, where `n = |V|`. -/
lemma doubleCover_hitting_le (hd : ∀ i, 0 < G.degree i) (hc' : (doubleCover G).Connected)
    (u v : V × Bool) :
    hitting (doubleCover G) hc' v u ≤ 16 * (Fintype.card V : ℝ) ^ 3 := by
  haveI : Nonempty (V × Bool) := hc'.nonempty
  haveI : Nonempty V := ⟨hc'.nonempty.some.1⟩
  set n : ℝ := (Fintype.card V : ℝ) with hn
  have hn1 : (1 : ℝ) ≤ n := by
    rw [hn]
    exact_mod_cast Fintype.card_pos
  have hvol : volume G ≤ n * (n - 1) := by
    calc volume G = ∑ i, (G.degree i : ℝ) := rfl
      _ ≤ ∑ _i : V, (n - 1) := Finset.sum_le_sum fun i _ => by
          have := G.degree_lt_card_verts i
          have : (G.degree i : ℝ) + 1 ≤ n := by rw [hn]; exact_mod_cast this
          linarith
      _ = n * (n - 1) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hn]
  have hpair := hitting_add_hitting_le hc' (doubleCover_degree_pos hd) u v
  rw [volume_doubleCover] at hpair
  have hsub : ((Fintype.card (V × Bool) : ℝ) - 1) = 2 * n - 1 := by
    rw [Fintype.card_prod, Fintype.card_bool, hn]
    push_cast
    ring
  rw [hsub] at hpair
  have hnn := hitting_nonneg hc' (doubleCover_degree_pos hd) u v
  have hfac : 8 * volume G * (2 * n - 1) ≤ 8 * (n * (n - 1)) * (2 * n - 1) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  nlinarith [hpair, hfac, hnn]

/-- The plain meeting potential is nonnegative. -/
lemma plainPotential_nonneg (hd : ∀ i, 0 < G.degree i) (hc' : (doubleCover G).Connected)
    (p : V × V) : 0 ≤ plainPotential hc' (16 * (Fintype.card V : ℝ) ^ 3) p := by
  haveI : Nonempty (V × Bool) := hc'.nonempty
  simpa [plainPotential] using meetingPotential_nonneg (doubleCover_degree_pos hd) hc'
    (doubleCover_hitting_le hd hc') ((p.1, false), (p.2, false))

/-- The plain meeting potential is at most `32 n³`. -/
lemma plainPotential_le (hd : ∀ i, 0 < G.degree i) (hc' : (doubleCover G).Connected)
    (p : V × V) :
    plainPotential hc' (16 * (Fintype.card V : ℝ) ^ 3) p ≤ 32 * (Fintype.card V : ℝ) ^ 3 := by
  haveI : Nonempty (V × Bool) := hc'.nonempty
  have h := meetingPotential_le (doubleCover_degree_pos hd) hc'
    (doubleCover_hitting_le hd hc') ((p.1, false), (p.2, false))
  simp only [plainPotential] at h ⊢
  linarith

/-- The weighted hitting sum `Σ_z d_z h̃_{(b, j)} z` of the double cover does not depend on the
layer `j` of the target. -/
lemma doubleCover_hitting_sum_flip (hc' : (doubleCover G).Connected) (b : V) (j : Bool) :
    ∑ z, ((doubleCover G).degree z : ℝ) * hitting (doubleCover G) hc' (b, !j) z =
      ∑ z, ((doubleCover G).degree z : ℝ) * hitting (doubleCover G) hc' (b, j) z := by
  let e : V × Bool ≃ V × Bool :=
    { toFun := fun p => (p.1, !p.2)
      invFun := fun p => (p.1, !p.2)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun z _ => ?_
  obtain ⟨a, i⟩ := z
  show ((doubleCover G).degree (a, !i) : ℝ) * hitting (doubleCover G) hc' (b, !j) (a, !i) = _
  rw [doubleCover_degree, doubleCover_degree, hitting_doubleCover_flip]

/-- The Coppersmith–Tetali–Winkler potential of the double cover is invariant under swapping
the layers of both tokens. -/
lemma meetingPotential_doubleCover_flip (hc' : (doubleCover G).Connected) (B₀ : ℝ) (a b : V)
    (i j : Bool) :
    meetingPotential hc' B₀ ((a, !i), (b, !j)) = meetingPotential hc' B₀ ((a, i), (b, j)) := by
  simp only [meetingPotential]
  rw [hitting_doubleCover_flip hc', doubleCover_hitting_sum_flip hc']

/-- A plain step of the first token of the double cover, away from the second token, lowers the
potential by `2`. -/
lemma expect_meetingPotential_fst (hd : ∀ i, 0 < G.degree i) (hc' : (doubleCover G).Connected)
    (B₀ : ℝ) {x : V} {i : Bool} {q : V × Bool} (hne : (x, i) ≠ q) :
    (uniformNeighbor G hd x).expect (fun a => meetingPotential hc' B₀ ((a, !i), q)) =
      meetingPotential hc' B₀ ((x, i), q) - 2 := by
  have hexp := uniformNeighbor_doubleCover_expect hd (doubleCover_degree_pos hd) x i
    (hitting (doubleCover G) hc' q)
  simp only [meetingPotential]
  rw [Distribution.expect_add, Distribution.expect_sub, Distribution.expect_const,
    Distribution.expect_const, ← hexp,
    uniformNeighbor_expect_hitting (doubleCover_degree_pos hd) hc' hne]
  ring

/-- A plain step of the second token of the double cover, away from the first token, lowers
the potential by `2` (by the symmetry `meetingPotential_swap`). -/
lemma expect_meetingPotential_snd (hd : ∀ i, 0 < G.degree i) (hc' : (doubleCover G).Connected)
    (B₀ : ℝ) {y : V} {j : Bool} {q : V × Bool} (hne : (y, j) ≠ q) :
    (uniformNeighbor G hd y).expect (fun b => meetingPotential hc' B₀ (q, (b, !j))) =
      meetingPotential hc' B₀ (q, (y, j)) - 2 := by
  haveI : Nonempty (V × Bool) := hc'.nonempty
  have hsymm (p : V × Bool) : meetingPotential hc' B₀ (q, p) = meetingPotential hc' B₀ (p, q) :=
    meetingPotential_swap (doubleCover_degree_pos hd) hc' B₀ q p
  simp only [hsymm]
  exact expect_meetingPotential_fst hd hc' B₀ hne

/-- **Drift of the plain meeting potential** (the Tetali–Winkler reduction in Hassin–Peleg's
proof of Lemma 2.4). Off the diagonal, one synchronous step of two plain uniform-neighbour
walks lowers the potential by exactly `4` in expectation (`2` per token, in the
lazy-normalised units of `hitting`). -/
lemma plainPotential_drift (hd : ∀ i, 0 < G.degree i) (hc' : (doubleCover G).Connected)
    (B₀ : ℝ) {x y : V} (hxy : x ≠ y) :
    (pairWalk (uniformNeighbor G hd)).apply (plainPotential hc' B₀) (x, y) =
      plainPotential hc' B₀ (x, y) - 4 := by
  haveI : Nonempty (V × Bool) := hc'.nonempty
  rw [pairWalk_apply_of_ne _ _ hxy]
  -- second token: read the pair in layer `1`, where the step of `y` leaves `(y, 0)`
  have hinner (a : V) :
      (uniformNeighbor G hd y).expect (fun b => plainPotential hc' B₀ (a, b)) =
        meetingPotential hc' B₀ ((a, !false), (y, false)) - 2 := by
    have hfun : (fun b => plainPotential hc' B₀ (a, b)) =
        fun b => meetingPotential hc' B₀ ((a, true), (b, !false)) :=
      funext fun b => meetingPotential_doubleCover_flip hc' B₀ a b true true
    rw [hfun]
    exact expect_meetingPotential_snd hd hc' B₀
      (fun h => Bool.false_ne_true (congrArg Prod.snd h))
  -- first token: the pair `((x, 0), (y, 0))` of distinct vertices of `G̃`
  rw [funext hinner, Distribution.expect_sub, Distribution.expect_const,
    expect_meetingPotential_fst hd hc' B₀ (fun h => hxy (congrArg Prod.fst h))]
  simp only [plainPotential]
  ring

/-- **Meeting tail, Markov form.** On a connected nonbipartite graph with `n` vertices, two
synchronous plain random walks started at `p` are apart after `T` steps with probability `P`
satisfying `T · P ≤ 8 n³`. -/
theorem plain_apart_mul_le (hc : G.Connected) (hnb : ¬ G.Colorable 2)
    (hd : ∀ i, 0 < G.degree i) (T : ℕ) (p : V × V) :
    (T : ℝ) * (pairWalk (uniformNeighbor G hd)).iterate T (Kernel.outside (Set.diagonal V)) p ≤
      8 * (Fintype.card V : ℝ) ^ 3 := by
  have hc' := doubleCover_connected hc hnb
  have h := pairWalk_apart_mul_le (uniformNeighbor G hd)
    (plainPotential hc' (16 * (Fintype.card V : ℝ) ^ 3))
    (plainPotential_nonneg hd hc')
    (fun x y hxy => (plainPotential_drift hd hc' _ hxy).le) T p
  have hle := plainPotential_le hd hc' p
  linarith [h.trans hle]

/-- **Meeting time with explicit constant** (Hassin–Peleg Lemma 2.4, uniform case:
`M = O(n · 2m) = O(n³)`, tail form). On a connected nonbipartite graph with `n` vertices, two
synchronous plain random walks are apart after `16 n³` steps with probability at most `1/2`,
from every pair of start vertices. -/
theorem plain_meeting_core (hc : G.Connected) (hnb : ¬ G.Colorable 2)
    (hd : ∀ i, 0 < G.degree i) (p : V × V) :
    (pairWalk (uniformNeighbor G hd)).iterate (16 * Fintype.card V ^ 3)
      (Kernel.outside (Set.diagonal V)) p ≤ 1 / 2 := by
  haveI : Nonempty V := hc.nonempty
  have h := plain_apart_mul_le hc hnb hd (16 * Fintype.card V ^ 3) p
  have hcoe : ((16 * Fintype.card V ^ 3 : ℕ) : ℝ) = 16 * (Fintype.card V : ℝ) ^ 3 := by
    push_cast
    rfl
  rw [hcoe] at h
  have hpos : (0 : ℝ) < 16 * (Fintype.card V : ℝ) ^ 3 := by positivity
  apply le_of_mul_le_mul_left (a := 16 * (Fintype.card V : ℝ) ^ 3) _ hpos
  calc 16 * (Fintype.card V : ℝ) ^ 3 *
        (pairWalk (uniformNeighbor G hd)).iterate (16 * Fintype.card V ^ 3)
          (Kernel.outside (Set.diagonal V)) p
      ≤ 8 * (Fintype.card V : ℝ) ^ 3 := h
    _ = 16 * (Fintype.card V : ℝ) ^ 3 * (1 / 2) := by ring

/-- **Iterated meeting time with explicit constant.** On a connected nonbipartite graph with
`n` vertices, two synchronous plain random walks are apart after `T ≥ 16 k n³` steps with
probability at most `2^{-k}`. -/
theorem plain_apart_le_pow (hc : G.Connected) (hnb : ¬ G.Colorable 2)
    (hd : ∀ i, 0 < G.degree i) (x y : V) (k T : ℕ)
    (hT : k * 16 * (Fintype.card V : ℝ) ^ 3 ≤ T) :
    (pairWalk (uniformNeighbor G hd)).iterate T (Kernel.outside (Set.diagonal V)) (x, y) ≤
      (1 / 2) ^ k := by
  haveI : Nonempty V := hc.nonempty
  have hT₀ : k * (16 * Fintype.card V ^ 3) ≤ T := by
    have : ((k * (16 * Fintype.card V ^ 3) : ℕ) : ℝ) ≤ T := by
      rw [Nat.cast_mul]
      calc (k : ℝ) * ((16 * Fintype.card V ^ 3 : ℕ) : ℝ)
          = k * 16 * (Fintype.card V : ℝ) ^ 3 := by push_cast; ring
        _ ≤ T := hT
    exact_mod_cast this
  have hone := Kernel.outside_le_one (Set.diagonal V) (x, y)
  have hpow : (0 : ℝ) ≤ (1 / 2) ^ k := by positivity
  calc (pairWalk (uniformNeighbor G hd)).iterate T (Kernel.outside (Set.diagonal V)) (x, y)
      ≤ (pairWalk (uniformNeighbor G hd)).iterate (k * (16 * Fintype.card V ^ 3))
          (Kernel.outside (Set.diagonal V)) (x, y) :=
        pairWalk_iterate_outside_antitone _ (x, y) hT₀
    _ ≤ (1 / 2) ^ k * Kernel.outside (Set.diagonal V) (x, y) :=
        pairWalk_iterate_outside_mul_le _ (by norm_num)
          (fun a b => plain_meeting_core hc hnb hd (a, b)) k (x, y)
    _ ≤ (1 / 2) ^ k := by nlinarith

end Plain

/-- **Meeting time of two plain walks** (Hassin–Peleg Lemma 2.4 with Fact 2.3, uniform case;
Tetali–Winkler). There is a constant `A > 0` such that on every connected nonbipartite graph
with `n` vertices (all degrees positive), from every pair of start vertices `x, y`, two
synchronous plain uniform-neighbour random walks have not met after `T ≥ A n³` steps with
probability at most `1/2`. This is exactly the hypothesis of
`iterate_disagreement_le_of_meeting` for `H = uniformNeighbor G hd`. -/
theorem plain_meeting_le_half :
    ∃ A : ℝ, 0 < A ∧ ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj], G.Connected → ¬ G.Colorable 2 →
      ∀ (hd : ∀ i, 0 < G.degree i) (x y : V) (T : ℕ), A * (Fintype.card V : ℝ) ^ 3 ≤ T →
        (pairWalk (uniformNeighbor G hd)).event (fun p => p.1 ≠ p.2) T (x, y) ≤ 1 / 2 := by
  refine ⟨16, by norm_num, ?_⟩
  intro V _ _ G _ hc hnb hd x y T hT
  rw [event_pairWalk]
  have hT₀ : 16 * Fintype.card V ^ 3 ≤ T := by exact_mod_cast hT
  exact (pairWalk_iterate_outside_antitone _ (x, y) hT₀).trans
    (plain_meeting_core hc hnb hd (x, y))

end Voter
