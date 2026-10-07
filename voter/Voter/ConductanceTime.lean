import Voter.ConductanceDrift
import Voter.ConductanceLevels
import Dynamics.Drift

/-! # Consensus time of the lazy voter via conductance, two opinions (BGKM16, Lemma 2.2)

Berenbrink, Giakkoupis, Kermarrec, Mallmann-Trenn, *Bounds on the voter model in dynamic
networks*, ICALP 2016, arXiv:1603.01895 (BGKM16). By Lemma 2.1 (`potential_drift_conductance`)
the potential `Ψ = √vol(minority side)` drops in expectation by `d_min φ / (32 Ψ)` per round, and
`Ψ` vanishes exactly at consensus. The drift lemma `Dynamics.Kernel.drift_absorption` (FND-5,
BGKM16 Lemma 2.2) turns this into consensus with probability at least `1/2` once
`d_min φ T / 32 ≥ 4 Ψ(s₀)² = 4 vol(s₀)`, i.e. after `128 vol(s₀) / (d_min φ) ≤ 128 m / (d_min φ)`
rounds. The statements bound the probability `(transition H).iterate T disagreement s` that the
opinions still disagree at time `T`; since consensus is absorbing, this is the probability that
the consensus time exceeds `T`.

* `lazy_consensus_of_minority`: Lemma 2.2 on a static graph, from the minority volume;
* `lazy_consensus_conductance`: Theorem 1.1 (i) on a static graph, two opinions;
* `lazy_expected_consensus_time`: the expected consensus time is at most twice that bound
  (restarting);
* `dynamic_consensus_conductance`: Lemma 2.2 on a dynamic graph with fixed degrees.
-/

namespace Voter
open Dynamics Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

section Static
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The probability of disagreement at time `T` is one minus the probability that the potential
vanishes. -/
lemma iterate_disagreement_eq (hd : ∀ v, 0 < G.degree v) (K : Kernel (Config V Bool)) (T : ℕ)
    (s : Config V Bool) :
    K.iterate T disagreement s = 1 - K.event (fun x => potential G x = 0) T s := by
  have h : (disagreement : Config V Bool → ℝ) =
      fun x => 1 - if potential G x = 0 then 1 else 0 :=
    funext (disagreement_eq_potential G hd)
  rw [h, Kernel.event_eq_iterateSeq, ← Kernel.iterateSeq_one_sub, Kernel.iterateSeq_const]

/-- **Lemma 2.2 of BGKM16, static graph.** Two opinions, the lazy voter on `G`, started in `s`
with minority side `s_0`. For every `T` with `128 vol(s_0) ≤ d_min φ T`, the opinions still
disagree at time `T` with probability at most `1/2`: the consensus time is at most
`128 vol(s_0) / (d_min φ)` with probability at least `1/2`. -/
theorem lazy_consensus_of_minority (hd : ∀ v, 0 < G.degree v) (s : Config V Bool) (T : ℕ)
    (hT : 128 * (vol G (minority G s) : ℝ) ≤ G.minDegree * conductance G * T) :
    (transition (lazyNeighbor G hd)).iterate T disagreement s ≤ 1 / 2 := by
  set K : Kernel (Config V Bool) := transition (lazyNeighbor G hd)
  have hc : 0 ≤ (G.minDegree : ℝ) * conductance G / 32 :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (conductance_nonneg G)) (by norm_num)
  have hdrift : ∀ x, 0 < potential G x →
      K.apply (potential G) x ≤ potential G x - G.minDegree * conductance G / 32 / potential G x :=
    fun x hx => by
      rw [div_div]
      exact potential_drift_conductance G hd x ((potential_pos_iff G hd x).mp hx)
  have habs : ∀ x, potential G x = 0 → K.apply (potential G) x = 0 := fun x hx => by
    obtain ⟨c, rfl⟩ := (potential_eq_zero_iff G hd x).mp hx
    rw [transition_constant]
    exact hx
  have hT' : 4 * potential G s ^ 2 ≤ G.minDegree * conductance G / 32 * T := by
    rw [potential_sq]
    linarith
  have h := Kernel.drift_absorption K (potential G) hc (potential_nonneg G) hdrift habs s hT'
  rw [iterate_disagreement_eq G hd]
  linarith

/-- **Theorem 1.1 (i) of BGKM16, static graph, two opinions.** On a graph with `m` edges,
minimum degree `d_min` and conductance `φ`, from every two-opinion configuration the lazy voter
reaches consensus within `128 m / (d_min φ)` rounds with probability at least `1/2`: for every `T`
with `128 m ≤ d_min φ T`, the opinions still disagree at time `T` with probability at most `1/2`.
-/
theorem lazy_consensus_conductance (hd : ∀ v, 0 < G.degree v) (s : Config V Bool) (T : ℕ)
    (hT : 128 * (G.edgeFinset.card : ℝ) ≤ G.minDegree * conductance G * T) :
    (transition (lazyNeighbor G hd)).iterate T disagreement s ≤ 1 / 2 := by
  refine lazy_consensus_of_minority G hd s T (le_trans ?_ hT)
  have := vol_minority_le_edges G s
  have : (vol G (minority G s) : ℝ) ≤ G.edgeFinset.card := by exact_mod_cast this
  linarith

/-- **Expected consensus time by restarting** (BGKM16, after Theorem 1.1; roadmap VOT-5). If
`128 m ≤ d_min φ T₀`, then for every horizon `N`,
`𝔼[min(T_cons, N)] = ∑_{t < N} P(T_cons > t) ≤ 2 T₀`, where `T_cons` is the consensus time of the
lazy voter with two opinions; letting `N → ∞`, `𝔼[T_cons] ≤ 2 T₀`. -/
theorem lazy_expected_consensus_time (hd : ∀ v, 0 < G.degree v) (s : Config V Bool) (T₀ : ℕ)
    (hT₀ : 128 * (G.edgeFinset.card : ℝ) ≤ G.minDegree * conductance G * T₀) (N : ℕ) :
    ∑ t ∈ range N, (transition (lazyNeighbor G hd)).iterate t disagreement s ≤ 2 * T₀ := by
  have h := sum_iterate_le_of_block (transition (lazyNeighbor G hd)) disagreement disagreement T₀
    (by norm_num : (0 : ℝ) < 1 / 2)
    (fun x => by rcases disagreement_zero_or_one x with h | h <;> simp [h])
    (fun x => by rcases disagreement_zero_or_one x with h | h <;> simp [h])
    disagreement_zero_or_one (fun _ => le_rfl)
    (transition_disagreement_le (lazyNeighbor G hd))
    (fun x _ => by
      have := lazy_consensus_conductance G hd x T₀ hT₀
      linarith) N s
  have h1 : disagreement s ≤ 1 := by
    rcases disagreement_zero_or_one s with h | h <;> simp [h]
  calc ∑ t ∈ range N, (transition (lazyNeighbor G hd)).iterate t disagreement s
      ≤ T₀ / (1 / 2) * disagreement s := h
    _ ≤ T₀ / (1 / 2) * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 2 * T₀ := by ring

end Static

/-- **Lemma 2.2 of BGKM16, dynamic graph.** Two opinions, started in `s`. The round from time
`t` to `t + 1` runs the lazy voter on a graph `G t x` chosen by an adversary that sees the current
configuration `x`; every vertex keeps the same degree in all graphs, and `φ t` is a lower bound on
the conductance of every graph the adversary may use at time `t`. Let `s_0` be the minority side
of `s` and `d_min` the minimum degree (both computed in `G 0 s`). If
`128 vol(s_0) ≤ d_min ∑_{t < T} φ t`, the opinions still disagree at time `T` with probability at
most `1/2`. -/
theorem dynamic_consensus_conductance (G : ℕ → Config V Bool → SimpleGraph V)
    [∀ t x, DecidableRel (G t x).Adj] (hd : ∀ t x v, 0 < (G t x).degree v) (s : Config V Bool)
    (hdeg : ∀ t x v, (G t x).degree v = (G 0 s).degree v)
    (φ : ℕ → ℝ) (hφ : ∀ t x, φ t ≤ conductance (G t x)) (T : ℕ)
    (hT : 128 * (vol (G 0 s) (minority (G 0 s) s) : ℝ) ≤
      (G 0 s).minDegree * ∑ t ∈ range T, φ t) :
    Kernel.iterateSeq (dynamicLazy G hd) T disagreement s ≤ 1 / 2 := by
  set Ψ := potential (G 0 s)
  set dmin : ℝ := ((G 0 s).minDegree : ℝ)
  have hΨ : ∀ t x, potential (G t x) = Ψ := fun t x => potential_congr (G 0 s) (hdeg t x)
  have hmin : ∀ t x, ((G t x).minDegree : ℝ) = dmin := fun t x => by
    rw [minDegree_congr (G 0 s) (hdeg t x)]
  have hc : ∀ t < T, 0 ≤ dmin * max (φ t) 0 / 32 := fun t _ =>
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)) (by norm_num)
  have hdrift : ∀ t < T, ∀ x, 0 < Ψ x →
      (dynamicLazy G hd t).apply Ψ x ≤ Ψ x - dmin * max (φ t) 0 / 32 / Ψ x := by
    intro t _ x hx
    have hx' : 0 < potential (G t x) x := by rw [hΨ t x]; exact hx
    have h := potential_drift_conductance (G t x) (hd t x) x
      ((potential_pos_iff (G t x) (hd t x) x).mp hx')
    rw [hΨ t x, hmin t x] at h
    have hφ' : max (φ t) 0 ≤ conductance (G t x) := max_le (hφ t x) (conductance_nonneg _)
    have hdm : 0 ≤ dmin := Nat.cast_nonneg _
    have hle : dmin * max (φ t) 0 / 32 / Ψ x ≤ dmin * conductance (G t x) / (32 * Ψ x) := by
      rw [div_div]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hφ' hdm) (by positivity)
    exact h.trans (by linarith)
  have habs : ∀ t < T, ∀ x, Ψ x = 0 → (dynamicLazy G hd t).apply Ψ x = 0 := by
    intro t _ x hx
    obtain ⟨c, rfl⟩ := (potential_eq_zero_iff (G 0 s) (hd 0 s) x).mp hx
    exact (transition_constant _ c Ψ).trans hx
  have hT' : 4 * Ψ s ^ 2 ≤ ∑ t ∈ range T, dmin * max (φ t) 0 / 32 := by
    rw [potential_sq, ← sum_div, ← mul_sum]
    have hsum : ∑ t ∈ range T, φ t ≤ ∑ t ∈ range T, max (φ t) 0 :=
      sum_le_sum fun t _ => le_max_left _ _
    have hdm : 0 ≤ dmin := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left hsum hdm
    linarith
  have h := Kernel.drift_absorption_seq (dynamicLazy G hd) Ψ (fun t => dmin * max (φ t) 0 / 32)
    T (potential_nonneg _) hc hdrift habs s hT'
  have hdis : (disagreement : Config V Bool → ℝ) = fun x => 1 - if Ψ x = 0 then 1 else 0 :=
    funext (disagreement_eq_potential (G 0 s) (hd 0 s))
  rw [hdis, Kernel.iterateSeq_one_sub]
  linarith

end Voter
