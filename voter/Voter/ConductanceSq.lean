import Voter.ConductanceMany

/-! # Consensus time `O(n log n / φ²)` of the lazy voter (BGKM16, Theorem 1.1 (ii))

Berenbrink, Giakkoupis, Kermarrec, Mallmann-Trenn, *Bounds on the voter model in dynamic
networks*, ICALP 2016, arXiv:1603.01895 (BGKM16), Part 2 of Theorem 1.1 and Lemma 2.4.
For two opinions, the drop `∑_{u ∈ s_t} λ_u d_u / (32 Ψ³)` of Lemma 2.1 is at least
`Ψ φ² / (32 n)`: `λ_u d_u ≥ λ_u²`, Cauchy–Schwarz over the at most `n` vertices of the
minority side, and `∑_{u ∈ s_t} λ_u ≥ φ vol(s_t) = φ Ψ²`. So the potential drifts
multiplicatively, `𝔼[Ψ_{t+1} | S_t = s_t] ≤ (1 - φ²/(32n)) Ψ(s_t)` (`potential_drift_mul`),
and the multiplicative drift lemma `Dynamics.Kernel.multiplicative_drift_seq` (FND-5) gives
`P(T_cons > T) ≤ 𝔼[Ψ_T] ≤ Ψ(s_0) exp(-∑_{t<T} φ_t² / (32 n)) ≤ 1/n²` as soon as
`∑_{t<T} φ_t² ≥ 96 n ln n`, since `Ψ ≥ 1` before consensus and `Ψ(s_0) ≤ √m ≤ n`. With any
number of opinions, a union bound over the two-opinion projections "`i` against the rest" gives
`1/n`.

* `potential_drift_mul`: the multiplicative drift (proof of Lemma 2.4);
* `lazy_consensus_conductance_sq`, `dynamic_consensus_conductance_sq`: Lemma 2.4, two opinions,
  static and dynamic graphs;
* `lazy_consensus_conductance_sq_many`, `dynamic_consensus_conductance_sq_many`: Part 2 of
  Theorem 1.1, any number of opinions;
* `lazy_expected_consensus_time_sq`: the expected consensus time by restarting;
* `lazy_consensus_conductance_min`, `dynamic_consensus_conductance_min`: Theorem 1.1 with both
  parts, `T_cons ≤ min{τ, τ'}` with probability at least `1/2`.
-/

namespace Voter
open Dynamics Finset

universe u v

variable {V : Type*} [Fintype V] [DecidableEq V]

section Static
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **The multiplicative drift of the potential** (BGKM16, proof of Lemma 2.4, static graph).
Two opinions, one round of the lazy voter on a graph with `n` vertices and conductance `φ`:
`𝔼[Ψ(S_{t+1}) | S_t = s_t] ≤ (1 - φ² / (32 n)) Ψ(s_t)` from every configuration (at consensus
both sides vanish). -/
theorem potential_drift_mul (hd : ∀ v, 0 < G.degree v) (s : Config V Bool) :
    (transition (lazyNeighbor G hd)).apply (potential G) s ≤
      (1 - conductance G ^ 2 / (32 * Fintype.card V)) * potential G s := by
  sorry

/-- **Lemma 2.4 of BGKM16, static graph.** Two opinions, the lazy voter on a graph with `n`
vertices and conductance `φ`. For every `T` with `96 n ln n ≤ φ² T`, the opinions still disagree
at time `T` with probability at most `1/n²`: the consensus time is at most `96 n ln n / φ²` with
probability at least `1 - 1/n²`. -/
theorem lazy_consensus_conductance_sq (hd : ∀ v, 0 < G.degree v) (s : Config V Bool) (T : ℕ)
    (hT : 96 * (Fintype.card V : ℝ) * Real.log (Fintype.card V) ≤ conductance G ^ 2 * T) :
    (transition (lazyNeighbor G hd)).iterate T disagreement s ≤
      1 / (Fintype.card V : ℝ) ^ 2 := by
  sorry

/-- **Part 2 of Theorem 1.1 of BGKM16, static graph, any number of opinions.** The lazy voter on
a graph with `n` vertices and conductance `φ`, from a configuration with any number of opinions:
for every `T` with `96 n ln n ≤ φ² T`, the opinions still disagree at time `T` with probability
at most `1/n`. -/
theorem lazy_consensus_conductance_sq_many [Nonempty V] {C : Type*} [Fintype C]
    (hd : ∀ v, 0 < G.degree v) (s : Config V C) (T : ℕ)
    (hT : 96 * (Fintype.card V : ℝ) * Real.log (Fintype.card V) ≤ conductance G ^ 2 * T) :
    (transition (lazyNeighbor G hd)).iterate T disagreement s ≤ 1 / (Fintype.card V : ℝ) := by
  sorry

/-- **Expected consensus time by restarting** (BGKM16, Theorem 1.1 (ii), static graph, any
number of opinions). If `96 n ln n ≤ φ² T₀`, then for every horizon `N`,
`𝔼[min(T_cons, N)] = ∑_{t < N} P(T_cons > t) ≤ 2 T₀`; letting `N → ∞`, `𝔼[T_cons] ≤ 2 T₀`. -/
theorem lazy_expected_consensus_time_sq [Nonempty V] {C : Type*} [Fintype C]
    (hd : ∀ v, 0 < G.degree v) (s : Config V C) (T₀ : ℕ)
    (hT₀ : 96 * (Fintype.card V : ℝ) * Real.log (Fintype.card V) ≤ conductance G ^ 2 * T₀)
    (N : ℕ) :
    ∑ t ∈ range N, (transition (lazyNeighbor G hd)).iterate t disagreement s ≤ 2 * T₀ := by
  sorry

end Static

/-- **Lemma 2.4 of BGKM16, dynamic graph.** Two opinions, started in `s`. The round from time
`t` to `t + 1` runs the lazy voter on a graph `G t x` chosen by an adversary that sees the current
configuration `x`; every vertex keeps the same degree in all graphs, and `φ t ≥ 0` is a lower
bound on the conductance of every graph the adversary may use at time `t`. If
`96 n ln n ≤ ∑_{t < T} φ_t²`, the opinions still disagree at time `T` with probability at most
`1/n²`. -/
theorem dynamic_consensus_conductance_sq (G : ℕ → Config V Bool → SimpleGraph V)
    [∀ t x, DecidableRel (G t x).Adj] (hd : ∀ t x v, 0 < (G t x).degree v) (s : Config V Bool)
    (hdeg : ∀ t x v, (G t x).degree v = (G 0 s).degree v)
    (φ : ℕ → ℝ) (hφ0 : ∀ t, 0 ≤ φ t) (hφ : ∀ t x, φ t ≤ conductance (G t x)) (T : ℕ)
    (hT : 96 * (Fintype.card V : ℝ) * Real.log (Fintype.card V) ≤ ∑ t ∈ range T, φ t ^ 2) :
    Kernel.iterateSeq (dynamicLazy G hd) T disagreement s ≤ 1 / (Fintype.card V : ℝ) ^ 2 := by
  sorry

/-- **Part 2 of Theorem 1.1 of BGKM16, dynamic graph, any number of opinions.** The lazy voter
on a dynamic graph as in `dynamic_consensus_conductance_sq`, from a configuration `s` with any
number of opinions. If `96 n ln n ≤ ∑_{t < T} φ_t²`, the opinions still disagree at time `T`
with probability at most `1/n`. -/
theorem dynamic_consensus_conductance_sq_many [Nonempty V] {C : Type*} [Fintype C]
    (G : ℕ → Config V C → SimpleGraph V)
    [∀ t x, DecidableRel (G t x).Adj] (hd : ∀ t x v, 0 < (G t x).degree v) (s : Config V C)
    (hdeg : ∀ t x v, (G t x).degree v = (G 0 s).degree v)
    (φ : ℕ → ℝ) (hφ0 : ∀ t, 0 ≤ φ t) (hφ : ∀ t x, φ t ≤ conductance (G t x)) (T : ℕ)
    (hT : 96 * (Fintype.card V : ℝ) * Real.log (Fintype.card V) ≤ ∑ t ∈ range T, φ t ^ 2) :
    Kernel.iterateSeq (dynamicLazy G hd) T disagreement s ≤ 1 / (Fintype.card V : ℝ) := by
  sorry

/-- **Theorem 1.1 of BGKM16, dynamic graph, two opinions.** With the dynamic graph of
`dynamic_consensus_conductance_sq`, the consensus time is at most `min{τ, τ'}` with probability
at least `1/2`, where `τ` is the first time with `d_min ∑_{t < τ} φ_t ≥ 128 vol(s_0)`
(`vol(s_0) ≤ m`) and `τ'` the first time with `∑_{t < τ'} φ_t² ≥ 96 n ln n`: if `T` satisfies
either inequality, the opinions still disagree at time `T` with probability at most `1/2`. -/
theorem dynamic_consensus_conductance_min (G : ℕ → Config V Bool → SimpleGraph V)
    [∀ t x, DecidableRel (G t x).Adj] (hd : ∀ t x v, 0 < (G t x).degree v) (s : Config V Bool)
    (hdeg : ∀ t x v, (G t x).degree v = (G 0 s).degree v)
    (φ : ℕ → ℝ) (hφ0 : ∀ t, 0 ≤ φ t) (hφ : ∀ t x, φ t ≤ conductance (G t x)) (T : ℕ)
    (hT : 128 * (vol (G 0 s) (minority (G 0 s) s) : ℝ) ≤
        (G 0 s).minDegree * ∑ t ∈ range T, φ t ∨
      96 * (Fintype.card V : ℝ) * Real.log (Fintype.card V) ≤ ∑ t ∈ range T, φ t ^ 2) :
    Kernel.iterateSeq (dynamicLazy G hd) T disagreement s ≤ 1 / 2 := by
  sorry

/-- **Theorem 1.1 of BGKM16, static graph, any number of opinions.** There is a constant `b`
such that on every graph without isolated vertices, with `n` vertices, `m` edges, minimum degree
`d_min` and conductance `φ`, from every configuration with any number of opinions, the lazy voter
reaches consensus within `min{b m / (d_min φ), b n ln n / φ²}` rounds with probability at least
`1/2`: for every `T` with `b m ≤ d_min φ T` or `b n ln n ≤ φ² T`, the opinions still disagree at
time `T` with probability at most `1/2`. -/
theorem lazy_consensus_conductance_min :
    ∃ b : ℝ, ∀ (V : Type u) (C : Type v) [Fintype V] [DecidableEq V] [Nonempty V] [Fintype C]
      (G : SimpleGraph V) [DecidableRel G.Adj] (hd : ∀ w, 0 < G.degree w) (s : Config V C)
      (T : ℕ), (b * (G.edgeFinset.card : ℝ) ≤ G.minDegree * conductance G * T ∨
        b * (Fintype.card V : ℝ) * Real.log (Fintype.card V) ≤ conductance G ^ 2 * T) →
      (transition (lazyNeighbor G hd)).iterate T disagreement s ≤ 1 / 2 := by
  sorry

end Voter
