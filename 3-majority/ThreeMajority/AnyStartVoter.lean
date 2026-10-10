import ThreeMajority.AnyStartModel
import Dynamics.Reverse
import Dynamics.Absorption

/-!
# Voter reduces the number of colours fast (BCEKMN17, Lemma 3)

The Voter process is dual to coalescing random walks (Lemma 4). On the complete graph with
self-loops, one step of the coalescing walks moves the set `Z` of occupied nodes to its image
`walkStep Z y = y '' Z` under one uniform round `y : Fin n → Fin n`, and two walks coalesce when
they move to the same node. This duality is restated here rather than imported, since this
package does not depend on the `voter` package.

* `numColours_voterRun_le`: Lemma 4 (the inequality `T^k_V ≤ T^k_C` used by the paper),
  pathwise: the colours of Voter after the rounds `y₀, …, y_{T-1}` are images of the walks
  started on all nodes and moved by the rounds in reverse order.
* `voter_dual`: the probabilistic form, Equation (6) as the inequality used: Voter has more than
  `k` colours at time `T` with at most the probability that more than `k` coalescing walks
  remain.
* `walk_drift`: the expected drop of the number of walks, `E[X_{t+1} | X_t = x] ≤
  x − x(x−1)/(3n)` for every `x` (an exact occupancy computation); `walk_drift_paper` is the
  paper's Equation (7), `≤ x − x²/(10n)` for `x ≥ 2`.
* `walk_expect_le`: `E[X_t] ≤ 1 + 3n/t`, from any initial set of walks; it replaces the
  expected coalescence time bound `E[T^k_C] ≤ 20 n/k` (Equations (18), (19)).
* `voter_reduce_whp`: Lemma 3, at most `k` colours remain after `24 (n/k) log n` rounds with
  probability at least `1 − 1/n`.
-/

namespace ThreeMajority

open Finset Dynamics

variable {n : ℕ}

/-- One step of coalescing random walks on the complete graph with self-loops: the walks at the
nodes of `Z` move along the round `y`, and walks on the same node coalesce. -/
def walkStep (Z : Finset (Fin n)) (y : Fin n → Fin n) : Finset (Fin n) :=
  Z.image y

/-- The colours of Voter after the rounds `l` are colours of the nodes still occupied by the
walks started on all nodes and moved by the rounds in reverse order. -/
lemma image_voterRun_subset {σ : Type*} [DecidableEq σ] (c : Fin n → σ)
    (l : List (Fin n → Fin n)) :
    univ.image (voterRun c l) ⊆ (l.foldr (fun y Z => walkStep Z y) univ).image c := by
  induction l generalizing c with
  | nil => exact subset_rfl
  | cons y l ih =>
    rw [voterRun_cons, List.foldr_cons, walkStep, image_image]
    exact ih _

/-- **Lemma 4** (BCEKMN17), the inequality `T^k_V ≤ T^k_C`, pathwise: the number of colours of
Voter after the rounds `l` is at most the number of coalescing walks, started on all nodes, after
the same rounds applied in reverse order (`List.foldr` applies the last round first). -/
theorem numColours_voterRun_le {σ : Type*} [DecidableEq σ] (c : Fin n → σ)
    (l : List (Fin n → Fin n)) :
    numColours (voterRun c l) ≤ (l.foldr (fun y Z => walkStep Z y) univ).card :=
  (card_le_card (image_voterRun_subset c l)).trans card_image_le

/-- **Equation (6)** (BCEKMN17), as the inequality used: after `T` rounds, Voter has more than
`k` colours with at most the probability that more than `k` of the `n` coalescing walks remain. -/
theorem voter_dual [NeZero n] {σ : Type*} [DecidableEq σ] (c : Fin n → σ) (k T : ℕ) :
    expList (Fin n → Fin n) T (fun l => if k < numColours (voterRun c l) then 1 else 0) ≤
      (Kernel.ofStep (walkStep (n := n))).event (fun Z => k < Z.card) T univ := by
  rw [Kernel.event_eq_iterate, Kernel.iterate_ofStep_foldr]
  refine expList_le_expList fun l => ?_
  have h := numColours_voterRun_le c l
  split_ifs <;> first | omega | norm_num

/-- The degree-three Bonferroni inequality `(1 - q)^x ≥ 1 - xq + C(x,2) q² - C(x,3) q³`. -/
lemma bonferroni_le_one_sub_pow {q : ℝ} (hq1 : q ≤ 1) (x : ℕ) :
    1 - x * q + x * (x - 1) / 2 * q ^ 2 - x * (x - 1) * (x - 2) / 6 * q ^ 3 ≤ (1 - q) ^ x := by
  induction x with
  | zero => simp
  | succ x ih =>
    have hx : 0 ≤ (x : ℝ) * (x - 1) * (x - 2) := by
      rcases x with _ | _ | _ | x
      · simp
      · simp
      · norm_num
      · push_cast
        ring_nf
        positivity
    -- `(1 - q) f(x) - f(x + 1) = q⁴ x(x-1)(x-2)/6` for the left side `f`
    have key : (1 - q) * (1 - x * q + x * (x - 1) / 2 * q ^ 2 - x * (x - 1) * (x - 2) / 6 * q ^ 3) =
        1 - (x + 1 : ℕ) * q + (x + 1 : ℕ) * ((x + 1 : ℕ) - 1) / 2 * q ^ 2 -
          (x + 1 : ℕ) * ((x + 1 : ℕ) - 1) * ((x + 1 : ℕ) - 2) / 6 * q ^ 3 +
          q ^ 4 * ((x : ℝ) * (x - 1) * (x - 2)) / 6 := by
      push_cast
      ring
    have h4 : 0 ≤ q ^ 4 * ((x : ℝ) * (x - 1) * (x - 2)) / 6 := by positivity
    have hstep := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hq1)
    rw [pow_succ' (1 - q) x]
    linarith

/-- The number of walks after a step, as a sum over nodes of occupation indicators. -/
lemma card_walkStep_eq_sum (Z : Finset (Fin n)) (y : Fin n → Fin n) :
    ((walkStep Z y).card : ℝ) = ∑ u, (1 - ∏ z ∈ Z, if y z ≠ u then (1 : ℝ) else 0) := by
  have h : ((walkStep Z y).card : ℝ) = ∑ u, if u ∈ walkStep Z y then (1 : ℝ) else 0 := by
    rw [sum_boole, filter_univ_mem]
  rw [h]
  refine sum_congr rfl fun u _ => ?_
  rw [prod_boole]
  by_cases hu : ∀ z ∈ Z, y z ≠ u
  · have : u ∉ walkStep Z y := by
      simp only [walkStep, mem_image, not_exists, not_and]
      exact hu
    rw [if_pos hu, if_neg this, sub_self]
  · have : u ∈ walkStep Z y := by
      simp only [walkStep, mem_image]
      simpa using hu
    rw [if_neg hu, if_pos this, sub_zero]

/-- A fixed node is missed by `x` independent uniform walkers with probability
`(1 - 1/n)^x`. -/
lemma avg_prod_ne [NeZero n] (Z : Finset (Fin n)) (u : Fin n) :
    avg (fun y : Fin n → Fin n => ∏ z ∈ Z, if y z ≠ u then (1 : ℝ) else 0) =
      (1 - 1 / n) ^ Z.card := by
  have hg : avg (fun w : Fin n => if w ≠ u then (1 : ℝ) else 0) = 1 - 1 / n := by
    rw [avg_indicator, filter_ne', card_erase_of_mem (mem_univ u), card_univ,
      Fintype.card_fin, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))]
    have : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
    field_simp
    simp
  have h := avg_prod_pi n (fun i w => if i ∈ Z then (if w ≠ u then (1 : ℝ) else 0) else 1)
  simp_rw [prod_ite_mem, univ_inter] at h
  have h' (i : Fin n) : avg (fun w : Fin n => if i ∈ Z then (if w ≠ u then (1 : ℝ) else 0) else 1)
      = if i ∈ Z then 1 - 1 / (n : ℝ) else 1 := by
    split_ifs
    · exact hg
    · exact avg_const 1
  rw [h, prod_congr rfl (fun i _ => h' i), prod_ite_mem, univ_inter, prod_const]

/-- The expected number of occupied nodes after one step from `x` walks is
`n (1 - (1 - 1/n)^x)`. -/
lemma avg_card_walkStep [NeZero n] (Z : Finset (Fin n)) :
    avg (fun y : Fin n → Fin n => ((walkStep Z y).card : ℝ)) = n * (1 - (1 - 1 / n) ^ Z.card) := by
  simp_rw [card_walkStep_eq_sum, avg_sum, avg_sub, avg_const, avg_prod_ne]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The expected number of coalescing walks after one step, from `x = |Z|` walks, is at most
`x − x(x−1)/(3n)` (exactly `n(1 − (1 − 1/n)^x)`, the expected number of occupied nodes). This
is the drift of Equation (7) of BCEKMN17, in a form valid for every `x`. -/
theorem walk_drift (Z : Finset (Fin n)) :
    avg (fun y : Fin n → Fin n => ((walkStep Z y).card : ℝ)) ≤
      Z.card - Z.card * (Z.card - 1 : ℝ) / (3 * n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain rfl : Z = ∅ := eq_empty_of_isEmpty Z
    simp [walkStep, Dynamics.avg]
  haveI : NeZero n := ⟨hn.ne'⟩
  rw [avg_card_walkStep]
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : (Z.card : ℝ) ≤ n := by
    exact_mod_cast (card_le_univ Z).trans_eq (Fintype.card_fin n)
  have hxx : 0 ≤ (Z.card : ℝ) * (Z.card - 1) := by
    rcases Nat.eq_zero_or_pos Z.card with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ Z.card := by exact_mod_cast h
      exact mul_nonneg (by linarith) (by linarith)
  have hB := bonferroni_le_one_sub_pow (q := 1 / n) (div_le_one_of_le₀ hN (by linarith)) Z.card
  obtain ⟨x, hx'⟩ : ∃ x : ℝ, x = Z.card := ⟨_, rfl⟩
  rw [← hx'] at hB hx hxx ⊢
  have e : (n : ℝ) * (1 - (1 - 1 / n) ^ Z.card) ≤
      x - x * (x - 1) / (2 * n) + x * (x - 1) * (x - 2) / (6 * n ^ 2) := by
    have e2 : (n : ℝ) * (x * (1 / n) - x * (x - 1) / 2 * (1 / n) ^ 2 +
        x * (x - 1) * (x - 2) / 6 * (1 / n) ^ 3) =
        x - x * (x - 1) / (2 * n) + x * (x - 1) * (x - 2) / (6 * n ^ 2) := by
      field_simp
    rw [← e2]
    exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have key : x - x * (x - 1) / (3 * n) -
      (x - x * (x - 1) / (2 * n) + x * (x - 1) * (x - 2) / (6 * n ^ 2)) =
        x * (x - 1) * (n - x + 2) / (6 * n ^ 2) := by
    field_simp
    ring
  have hk : 0 ≤ x * (x - 1) * (n - x + 2) / (6 * n ^ 2) :=
    div_nonneg (mul_nonneg hxx (by linarith)) (by positivity)
  linarith

/-- **Equation (7)** (BCEKMN17): `E[X_{t+1} | X_t = x] ≤ x − x²/(10n)` for `x ≥ 2`. -/
theorem walk_drift_paper (Z : Finset (Fin n)) (hZ : 2 ≤ Z.card) :
    avg (fun y : Fin n → Fin n => ((walkStep Z y).card : ℝ)) ≤
      Z.card - (Z.card : ℝ) ^ 2 / (10 * n) := by
  refine (walk_drift Z).trans ?_
  have hn : 2 ≤ n := hZ.trans (Z.card_le_univ.trans_eq (Fintype.card_fin n))
  have hx : (2 : ℝ) ≤ Z.card := by exact_mod_cast hZ
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  rw [sub_le_sub_iff_left, div_le_div_iff₀ (by positivity) (by positivity)]
  have h7 : (0 : ℝ) ≤ 7 * Z.card - 10 := by linarith
  nlinarith [mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ n)
    (by positivity : (0 : ℝ) ≤ Z.card)) h7]

/-- The concave drift bound `x − x(x−1)/(3N)` lies below its tangent line at `m`. -/
lemma walk_drift_le_tangent {N : ℝ} (hN : 0 ≤ N) (m x : ℝ) :
    x - x * (x - 1) / (3 * N) ≤
      m - m * (m - 1) / (3 * N) + (1 - (2 * m - 1) / (3 * N)) * (x - m) := by
  have e : m - m * (m - 1) / (3 * N) + (1 - (2 * m - 1) / (3 * N)) * (x - m) -
      (x - x * (x - 1) / (3 * N)) = (x - m) ^ 2 / (3 * N) := by ring
  have : 0 ≤ (x - m) ^ 2 / (3 * N) := by positivity
  linarith

/-- The drift bound `x − x(x−1)/(3N)` is nondecreasing on `[0, N + 1]`. -/
lemma walk_drift_mono {N x y : ℝ} (hN : 1 ≤ N) (hxy : x ≤ y) (hy : y ≤ N + 1) :
    x - x * (x - 1) / (3 * N) ≤ y - y * (y - 1) / (3 * N) := by
  have e : y - y * (y - 1) / (3 * N) - (x - x * (x - 1) / (3 * N)) =
      (y - x) * (3 * N - x - y + 1) / (3 * N) := by
    field_simp
    ring
  have : 0 ≤ (y - x) * (3 * N - x - y + 1) / (3 * N) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
  linarith

/-- One more step of the walks: `E[X_{t+1}] ≤ m − m(m−1)/(3n)` for `m = E[X_t]`, by
`walk_drift` and the concavity of the bound. -/
lemma walk_iterate_succ_le [NeZero n] (Z : Finset (Fin n)) (t : ℕ) {m : ℝ}
    (hm : (Kernel.ofStep (walkStep (n := n))).iterate t (fun W => (W.card : ℝ)) Z = m) :
    (Kernel.ofStep (walkStep (n := n))).iterate (t + 1) (fun W => (W.card : ℝ)) Z ≤
      m - m * (m - 1) / (3 * n) := by
  obtain ⟨K, hK⟩ : ∃ K, K = Kernel.ofStep (walkStep (n := n)) := ⟨_, rfl⟩
  rw [← hK] at hm ⊢
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 1 - (2 * m - 1) / (3 * n) := ⟨_, rfl⟩
  have hpt (W : Finset (Fin n)) :
      K.apply (fun W => (W.card : ℝ)) W ≤ (m - m * (m - 1) / (3 * n) - a * m) + a * W.card := by
    rw [hK, Kernel.apply_ofStep]
    have := walk_drift_le_tangent n.cast_nonneg m W.card
    rw [← ha] at this
    linarith [walk_drift W]
  rw [Kernel.iterate_add_time]
  calc K.iterate t (K.apply fun W => (W.card : ℝ)) Z
      ≤ K.iterate t (fun W => (m - m * (m - 1) / (3 * n) - a * m) + a * W.card) Z :=
        K.iterate_mono t hpt Z
    _ = m - m * (m - 1) / (3 * n) := by
        rw [K.iterate_add t (fun _ => _) (fun W => a * (W.card : ℝ)), K.iterate_const,
          K.iterate_mul]
        beta_reduce
        rw [hm]
        ring

/-- The expected number of coalescing walks after `t ≥ 1` steps, from any initial set, is at
most `1 + 3n/t`. This replaces the bound `E[T^k_C] ≤ 20 n/k` of BCEKMN17 (Equations (18),
(19), from the variable drift theorem, Theorem 7) in the proof of Lemma 3. -/
theorem walk_expect_le [NeZero n] (Z : Finset (Fin n)) {t : ℕ} (ht : 1 ≤ t) :
    (Kernel.ofStep (walkStep (n := n))).iterate t (fun W => (W.card : ℝ)) Z ≤ 1 + 3 * n / t := by
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have hle (s : ℕ) :
      (Kernel.ofStep (walkStep (n := n))).iterate s (fun W => (W.card : ℝ)) Z ≤ n := by
    calc _ ≤ (Kernel.ofStep (walkStep (n := n))).iterate s (fun _ => (n : ℝ)) Z :=
          Kernel.iterate_mono _ s (fun W => by
            exact_mod_cast (card_le_univ W).trans_eq (Fintype.card_fin n)) Z
      _ = n := by rw [Kernel.iterate_const]
  have h0 (s : ℕ) :
      0 ≤ (Kernel.ofStep (walkStep (n := n))).iterate s (fun W => (W.card : ℝ)) Z :=
    Kernel.iterate_nonneg _ s (fun W => W.card.cast_nonneg) Z
  induction t, ht using Nat.le_induction with
  | base =>
    have := hle 1
    push_cast
    linarith
  | succ t ht ih =>
    rcases le_or_gt t 2 with h2 | h3
    · have h1 := hle (t + 1)
      have ht' : ((t + 1 : ℕ) : ℝ) ≤ 3 := by exact_mod_cast Nat.succ_le_succ h2
      have : (n : ℝ) ≤ 3 * n / ((t + 1 : ℕ) : ℝ) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith
      linarith
    · obtain ⟨m, hm⟩ : ∃ m, (Kernel.ofStep (walkStep (n := n))).iterate t
          (fun W => (W.card : ℝ)) Z = m := ⟨_, rfl⟩
      have hstep := walk_iterate_succ_le Z t hm
      have hm0 := h0 t
      rw [hm] at ih hm0
      have ht3 : (3 : ℝ) ≤ t := by exact_mod_cast h3
      have hb : 1 + 3 * n / t ≤ (n : ℝ) + 1 := by
        rw [add_comm, add_le_add_iff_right, div_le_iff₀ (by positivity)]
        nlinarith
      have hmono := walk_drift_mono hN ih hb
      obtain ⟨b, hb'⟩ : ∃ b : ℝ, b = 1 + 3 * n / t := ⟨_, rfl⟩
      rw [← hb'] at hmono
      have e : b - b * (b - 1) / (3 * n) = (t + 3 * n) * (t - 1) / t ^ 2 := by
        rw [hb']
        field_simp
        ring
      have hfin : (t + 3 * n) * (t - 1) / t ^ 2 ≤ 1 + 3 * n / ((t : ℝ) + 1) := by
        rw [show 1 + 3 * n / ((t : ℝ) + 1) = (t + 1 + 3 * n) / (t + 1) by field_simp,
          div_le_div_iff₀ (by positivity) (by positivity)]
        have : (t + 1 + 3 * n) * (t : ℝ) ^ 2 - (t + 3 * n) * (t - 1) * (t + 1) =
            t ^ 2 + t + 3 * n := by ring
        nlinarith
      push_cast
      linarith

/-- Expectations along the walks compare on a set of configurations that the walks cannot
leave. -/
lemma walk_iterate_mono_of_closed [NeZero n] {P : Finset (Fin n) → Prop}
    (hP : ∀ W y, P W → P (walkStep W y)) {f g : Finset (Fin n) → ℝ}
    (hfg : ∀ W, P W → f W ≤ g W) (t : ℕ) {W : Finset (Fin n)} (hW : P W) :
    (Kernel.ofStep (walkStep (n := n))).iterate t f W ≤
      (Kernel.ofStep (walkStep (n := n))).iterate t g W := by
  induction t generalizing W with
  | zero => exact hfg W hW
  | succ t ih =>
    rw [Kernel.iterate_succ, Kernel.iterate_succ, Kernel.apply_ofStep, Kernel.apply_ofStep]
    exact Dynamics.avg_le_avg fun y => ih (hP W y hW)

/-- **Lemma 3** (BCEKMN17): from any configuration, Voter has at most `k` colours after any
`T ≥ 24 (n/k) log n` rounds, with probability at least `1 − 1/n`. -/
theorem voter_reduce_whp {σ : Type*} [DecidableEq σ] (hn : 2 ≤ n) (c : Fin n → σ) {k : ℕ}
    (hk : 1 ≤ k) {T : ℕ} (hT : 24 * ((n : ℝ) / k) * Real.log n ≤ T) :
    expList (Fin n → Fin n) T (fun l => if k < numColours (voterRun c l) then 1 else 0) ≤
      1 / n := by
  haveI : NeZero n := ⟨by omega⟩
  have hn0 : (0 : ℝ) < n := by positivity
  rcases le_or_gt n k with hnk | hkn
  · -- at most `n` colours: the event is empty
    calc _ = expList (Fin n → Fin n) T (fun _ => (0 : ℝ)) := by
          congr 1
          funext l
          have : numColours (voterRun c l) ≤ n :=
            card_image_le.trans_eq (by rw [card_univ, Fintype.card_fin])
          rw [if_neg (by omega)]
      _ = 0 := expList_const T 0
      _ ≤ 1 / n := by positivity
  obtain ⟨K, hK⟩ : ∃ K, K = Kernel.ofStep (walkStep (n := n)) := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : Finset (Fin n) → ℝ, g = fun W => if k < W.card then 1 else 0 :=
    ⟨_, rfl⟩
  refine (voter_dual c k T).trans ?_
  rw [Kernel.event_eq_iterate, ← hK, ← hg]
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn.le
  -- the block length `τ = ⌈6n/k⌉`
  obtain ⟨τ, hτ⟩ : ∃ τ : ℕ, τ = ⌈6 * (n : ℝ) / k⌉₊ := ⟨_, rfl⟩
  have hτ1 : 6 * (n : ℝ) / k ≤ τ := hτ ▸ Nat.le_ceil _
  have hτ2 : (τ : ℝ) ≤ 7 * (n / k) := by
    have h := hτ ▸ Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 6 * n / k)
    have : (1 : ℝ) ≤ n / k := (one_le_div hk0).mpr hkn'
    rw [mul_div_assoc] at h
    linarith
  have hτ0 : 0 < τ := by
    have : (0 : ℝ) < τ := lt_of_lt_of_le (by positivity) hτ1
    exact_mod_cast this
  -- the survival observable `g` contracts by `1/2` over a block of `τ` rounds
  have hblock (W : Finset (Fin n)) : K.iterate τ g W ≤ 1 / 2 * g W := by
    by_cases hW : k < W.card
    · have hle := walk_iterate_mono_of_closed (P := fun V => V.Nonempty)
        (fun V y hV => hV.image y) (f := g)
        (g := fun V => 1 / k * (V.card : ℝ) + -(1 / k)) (fun V hV => by
          have h1 : (1 : ℝ) ≤ V.card := by exact_mod_cast hV.card_pos
          rw [hg, show 1 / (k : ℝ) * V.card + -(1 / k) = (V.card - 1) / k by ring]
          dsimp only
          split_ifs with h
          · have h2 : (k : ℝ) + 1 ≤ V.card := by exact_mod_cast h
            rw [le_div_iff₀ hk0]
            linarith
          · exact div_nonneg (by linarith) hk0.le) τ
        (card_pos.mp (by omega : 0 < W.card))
      rw [← hK, K.iterate_add τ (fun V => 1 / k * (V.card : ℝ)) (fun _ => -(1 / k)),
        K.iterate_mul, K.iterate_const] at hle
      beta_reduce at hle
      have hm := walk_expect_le W (Nat.one_le_iff_ne_zero.mpr hτ0.ne')
      rw [← hK] at hm
      have h3 : 3 * (n : ℝ) / τ ≤ k / 2 := by
        rw [div_le_div_iff₀ (by exact_mod_cast hτ0) two_pos]
        rw [div_le_iff₀ hk0] at hτ1
        linarith
      have hgW : g W = 1 := by rw [hg]; exact if_pos hW
      rw [hgW]
      refine hle.trans ?_
      rw [show 1 / (k : ℝ) * K.iterate τ (fun V => (V.card : ℝ)) W + -(1 / k) =
          (K.iterate τ (fun V => (V.card : ℝ)) W - 1) / k by ring, div_le_iff₀ hk0]
      linarith
    · have hle := walk_iterate_mono_of_closed (P := fun V => V.card ≤ k)
        (fun V y hV => card_image_le.trans hV) (f := g) (g := fun _ => 0)
        (fun V hV => by rw [hg]; dsimp only; rw [if_neg (by omega)]) τ (not_lt.mp hW)
      rw [← hK, K.iterate_const] at hle
      have hgW : g W = 0 := by rw [hg]; exact if_neg hW
      rw [hgW, mul_zero]
      exact hle
  -- `g` does not increase along a step, since the number of walks does not
  have hstep (W : Finset (Fin n)) : K.apply g W ≤ g W := by
    rw [hK, Kernel.apply_ofStep]
    refine (Dynamics.avg_le_avg fun y => ?_).trans_eq (Dynamics.avg_const (g W))
    have := card_image_le (s := W) (f := y)
    rw [hg]
    dsimp only [walkStep] at this ⊢
    split_ifs <;> first | omega | norm_num
  obtain ⟨j, hj⟩ : ∃ j, j = T / τ := ⟨_, rfl⟩
  have hgeo := Kernel.geometric_blocks K g (1 / 2) (by norm_num) τ hblock j univ
  have hanti := Kernel.iterate_antitone K g hstep univ (hj ▸ Nat.div_mul_le_self T τ)
  have hg1 : g univ ≤ 1 := by
    rw [hg]
    dsimp only
    split_ifs <;> norm_num
  -- `j = ⌊T/τ⌋ ≥ (24/7) log n - 1`, so `2^j ≥ n`
  have hjT : (T : ℝ) < (j + 1) * τ := by
    have h := Nat.lt_mul_div_succ T hτ0
    rw [← hj] at h
    have h' : (T : ℝ) < τ * (j + 1) := by exact_mod_cast h
    linarith
  have hr : (0 : ℝ) < n / k := by positivity
  have hL : Real.log 2 ≤ Real.log n := Real.log_le_log two_pos (by exact_mod_cast hn)
  have h24 : 24 * Real.log n < 7 * (j + 1) := by
    refine lt_of_mul_lt_mul_left ?_ hr.le
    calc (n : ℝ) / k * (24 * Real.log n) = 24 * (n / k) * Real.log n := by ring
      _ ≤ T := hT
      _ < (j + 1) * τ := hjT
      _ ≤ (j + 1) * (7 * (n / k)) := mul_le_mul_of_nonneg_left hτ2 (by positivity)
      _ = n / k * (7 * (j + 1)) := by ring
  have ha := Real.log_two_gt_d9
  have hjlog : Real.log n ≤ j * Real.log 2 := by
    nlinarith [mul_pos (sub_pos.mpr h24) (by linarith : (0 : ℝ) < Real.log 2),
      mul_nonneg (sub_nonneg.mpr hL) (by linarith : (0 : ℝ) ≤ 24 * Real.log 2 - 7),
      mul_nonneg (by linarith : (0 : ℝ) ≤ Real.log 2)
        (by linarith : (0 : ℝ) ≤ 24 * Real.log 2 - 14)]
  have h2j : (n : ℝ) ≤ 2 ^ j := by
    rw [← Real.log_le_log_iff hn0 (by positivity), Real.log_pow]
    exact hjlog
  calc K.iterate T g univ ≤ K.iterate (j * τ) g univ := hanti
    _ ≤ (1 / 2) ^ j * g univ := hgeo
    _ ≤ (1 / 2) ^ j := mul_le_of_le_one_right (by positivity) hg1
    _ = 1 / 2 ^ j := by rw [one_div_pow]
    _ ≤ 1 / n := one_div_le_one_div_of_le hn0 h2j

end ThreeMajority
