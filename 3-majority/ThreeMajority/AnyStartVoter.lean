import ThreeMajority.AnyStartModel
import Dynamics.Reverse

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

/-- **Lemma 4** (BCEKMN17), the inequality `T^k_V ≤ T^k_C`, pathwise: the number of colours of
Voter after the rounds `l` is at most the number of coalescing walks, started on all nodes, after
the same rounds applied in reverse order (`List.foldr` applies the last round first). -/
theorem numColours_voterRun_le {σ : Type*} [DecidableEq σ] (c : Fin n → σ)
    (l : List (Fin n → Fin n)) :
    numColours (voterRun c l) ≤ (l.foldr (fun y Z => walkStep Z y) univ).card := by
  sorry

/-- **Equation (6)** (BCEKMN17), as the inequality used: after `T` rounds, Voter has more than
`k` colours with at most the probability that more than `k` of the `n` coalescing walks remain. -/
theorem voter_dual [NeZero n] {σ : Type*} [DecidableEq σ] (c : Fin n → σ) (k T : ℕ) :
    expList (Fin n → Fin n) T (fun l => if k < numColours (voterRun c l) then 1 else 0) ≤
      (Kernel.ofStep (walkStep (n := n))).event (fun Z => k < Z.card) T univ := by
  sorry

/-- The expected number of coalescing walks after one step, from `x = |Z|` walks, is at most
`x − x(x−1)/(3n)` (exactly `n(1 − (1 − 1/n)^x)`, the expected number of occupied nodes). This
is the drift of Equation (7) of BCEKMN17, in a form valid for every `x`. -/
theorem walk_drift (Z : Finset (Fin n)) :
    avg (fun y : Fin n → Fin n => ((walkStep Z y).card : ℝ)) ≤
      Z.card - Z.card * (Z.card - 1 : ℝ) / (3 * n) := by
  sorry

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

/-- The expected number of coalescing walks after `t ≥ 1` steps, from any initial set, is at
most `1 + 3n/t`. This replaces the bound `E[T^k_C] ≤ 20 n/k` of BCEKMN17 (Equations (18),
(19), from the variable drift theorem, Theorem 7) in the proof of Lemma 3. -/
theorem walk_expect_le [NeZero n] (Z : Finset (Fin n)) {t : ℕ} (ht : 1 ≤ t) :
    (Kernel.ofStep (walkStep (n := n))).iterate t (fun W => (W.card : ℝ)) Z ≤ 1 + 3 * n / t := by
  sorry

/-- **Lemma 3** (BCEKMN17): from any configuration, Voter has at most `k` colours after any
`T ≥ 24 (n/k) log n` rounds, with probability at least `1 − 1/n`. -/
theorem voter_reduce_whp {σ : Type*} [DecidableEq σ] (hn : 2 ≤ n) (c : Fin n → σ) {k : ℕ}
    (hk : 1 ≤ k) {T : ℕ} (hT : 24 * ((n : ℝ) / k) * Real.log n ≤ T) :
    expList (Fin n → Fin n) T (fun l => if k < numColours (voterRun c l) then 1 else 0) ≤
      1 / n := by
  sorry

end ThreeMajority
