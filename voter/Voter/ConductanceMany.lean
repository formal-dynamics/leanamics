import Voter.ConductanceManyTime

/-! # Consensus time of the lazy voter via conductance, many opinions (BGKM16, Theorem 1.1 (i))

Berenbrink, Giakkoupis, Kermarrec, Mallmann-Trenn, *Bounds on the voter model in dynamic
networks*, ICALP 2016, arXiv:1603.01895 (BGKM16). With any number of opinions (any finite colour
type `C`), the lazy voter on a static graph with `m` edges, minimum degree `d_min` and conductance
`φ` reaches consensus in expected time `O(m / (d_min φ))`, and hence within `O(m / (d_min φ))`
rounds with probability at least `1/2`, uniformly in the number of opinions.

The proof in BGKM16 (Part 1 of Theorem 1.1 and Lemma 2.3) projects each opinion `i` onto the
two-opinion process "`i` against the rest", in which `i` is resolved (vanishes or prevails) in
`O(vol(i) / (d_min φ))` rounds with probability `1/2` (Lemma 2.2), and runs a phase argument: out
of `ℓ` remaining opinions at least `2ℓ/3` have volume at most `3 vol(V) / ℓ`, so within
`O(vol(V) / (ℓ d_min φ))` rounds the number of opinions drops to `5ℓ/6` with constant probability.
The phase lengths sum to `O(vol(V) / (d_min φ))`.
-/

namespace Voter
open Dynamics Finset

universe u v

/-- **Expected consensus time, many opinions** (BGKM16, Theorem 1.1 (i) on a static graph, via
Lemma 2.3). There is a constant `b` such that on every graph without isolated vertices, with `m`
edges, minimum degree `d_min` and conductance `φ`, from every configuration with any number of
opinions: if `b m ≤ d_min φ T₀`, then for every horizon `N`,
`𝔼[min(T_cons, N)] = ∑_{t < N} P(T_cons > t) ≤ T₀`, where `T_cons` is the consensus time of the
lazy voter. -/
theorem lazy_expected_consensus_time_many :
    ∃ b : ℝ, ∀ (V : Type u) (C : Type v) [Fintype V] [DecidableEq V] [Nonempty V] [Fintype C]
      (G : SimpleGraph V) [DecidableRel G.Adj] (hd : ∀ w, 0 < G.degree w) (s : Config V C)
      (T₀ : ℕ), b * (G.edgeFinset.card : ℝ) ≤ G.minDegree * conductance G * T₀ →
      ∀ N : ℕ, ∑ t ∈ range N, (transition (lazyNeighbor G hd)).iterate t disagreement s ≤ T₀ := by
  refine ⟨7000, fun V C _ _ _ _ G _ hd s T₀ hT N => ?_⟩
  exact expected_time_many_bound G hd s T₀ hT N

/-- **Theorem 1.1 (i) of BGKM16, static graph, many opinions.** There is a constant `b` such
that on every graph without isolated vertices, with `m` edges, minimum degree `d_min` and
conductance `φ`, from every configuration with any number of opinions, the lazy voter reaches
consensus within `b m / (d_min φ)` rounds with probability at least `1/2`: for every `T` with
`b m ≤ d_min φ T`, the opinions still disagree at time `T` with probability at most `1/2`. -/
theorem lazy_consensus_conductance_many :
    ∃ b : ℝ, ∀ (V : Type u) (C : Type v) [Fintype V] [DecidableEq V] [Nonempty V] [Fintype C]
      (G : SimpleGraph V) [DecidableRel G.Adj] (hd : ∀ w, 0 < G.degree w) (s : Config V C)
      (T : ℕ), b * (G.edgeFinset.card : ℝ) ≤ G.minDegree * conductance G * T →
      (transition (lazyNeighbor G hd)).iterate T disagreement s ≤ 1 / 2 := by
  refine ⟨14000, fun V C _ _ _ _ G _ hd s T hT => ?_⟩
  set K : Kernel (Config V C) := transition (lazyNeighbor G hd)
  set D : ℝ := G.minDegree * conductance G
  have hD : 0 ≤ D := mul_nonneg (Nat.cast_nonneg _) (conductance_nonneg G)
  -- run the expectation bound with `T₀ = ⌊(T + 1)/2⌋`
  set T₀ := (T + 1) / 2
  have h2T₀ : (T : ℝ) ≤ 2 * T₀ := by
    have : T ≤ 2 * T₀ := by omega
    exact_mod_cast this
  have h2T₀' : 2 * (T₀ : ℝ) ≤ T + 1 := by
    have : 2 * T₀ ≤ T + 1 := by omega
    exact_mod_cast this
  have hT₀ : 7000 * (G.edgeFinset.card : ℝ) ≤ D * T₀ := by
    have : D * T ≤ D * (2 * T₀) := mul_le_mul_of_nonneg_left h2T₀ hD
    change 14000 * (G.edgeFinset.card : ℝ) ≤ D * T at hT
    linarith
  have hsum := expected_time_many_bound G hd s T₀ hT₀ (T + 1)
  -- the disagreement probability is nonincreasing in time
  have hanti := Kernel.iterate_antitone K disagreement
    (transition_disagreement_le (lazyNeighbor G hd)) s
  have hlow : ((T + 1 : ℕ) : ℝ) * K.iterate T disagreement s ≤
      ∑ t ∈ range (T + 1), K.iterate t disagreement s := by
    have h := card_nsmul_le_sum (range (T + 1)) (fun t => K.iterate t disagreement s)
      (K.iterate T disagreement s) fun t ht => hanti (Nat.lt_succ_iff.mp (mem_range.mp ht))
    rwa [card_range, nsmul_eq_mul] at h
  push_cast at hlow
  have hpos : (0 : ℝ) < T + 1 := by positivity
  nlinarith

end Voter
