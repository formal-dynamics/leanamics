import Voter.ConductanceSqAux

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
  by_cases hs : (minority G s).Nonempty
  · have h := potential_drift G hd s hs
    have hΨ : 0 < potential G s := (potential_pos_iff G hd s).mpr hs
    obtain ⟨u₀, -⟩ := hs
    have hn : (0 : ℝ) < Fintype.card V := by
      exact_mod_cast Fintype.card_pos_iff.mpr ⟨u₀⟩
    have hkey := sq_conductance_mul_vol_le G s
    rw [← potential_sq] at hkey
    set L := ∑ u ∈ minority G s, (discordant G s u : ℝ) * G.degree u
    have hle : conductance G ^ 2 / (32 * Fintype.card V) * potential G s ≤
        L / (32 * potential G s ^ 3) := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hkey]
    nlinarith [h, hle]
  · rw [not_nonempty_iff_eq_empty] at hs
    obtain ⟨c, rfl⟩ := (minority_eq_empty_iff G hd s).mp hs
    rw [transition_constant, (potential_eq_zero_iff G hd _).mpr ⟨c, rfl⟩, mul_zero]

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
  set Ψ := potential (G 0 s)
  have hΨ : ∀ t x, potential (G t x) = Ψ := fun t x => potential_congr (G 0 s) (hdeg t x)
  rcases Nat.eq_zero_or_pos (Fintype.card V) with h0 | hpos
  · -- no vertices: every configuration is at consensus
    have hz : (disagreement : Config V Bool → ℝ) = fun _ => 0 :=
      funext (disagreement_eq_zero_of_card_le_one (by omega) false)
    rw [hz, Kernel.iterateSeq_const_fun]
    positivity
  have hn : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hpos
  have hφ1 : ∀ t, φ t ≤ 1 := fun t => (hφ t s).trans (conductance_le_one _)
  have hdrift : ∀ t < T, ∀ x, (dynamicLazy G hd t).apply Ψ x ≤
      (1 - φ t ^ 2 / (32 * Fintype.card V)) * Ψ x := by
    intro t _ x
    have h := potential_drift_mul (G t x) (hd t x) x
    rw [hΨ t x] at h
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (potential_nonneg _ x))
    have h2 : φ t ^ 2 ≤ conductance (G t x) ^ 2 := pow_le_pow_left₀ (hφ0 t) (hφ t x) 2
    have h3 : φ t ^ 2 / (32 * Fintype.card V) ≤ conductance (G t x) ^ 2 / (32 * Fintype.card V) :=
      div_le_div_of_nonneg_right h2 (by positivity)
    linarith
  have h := iterateSeq_pos_le_of_mul_drift (dynamicLazy G hd) Ψ (potential_nonneg _)
    (one_le_potential _) hn φ hφ0 hφ1 T hdrift hT s
  have hdis : (disagreement : Config V Bool → ℝ) = fun x => if 0 < Ψ x then 1 else 0 := by
    funext x
    rw [disagreement_eq_potential (G 0 s) (hd 0 s)]
    rcases (potential_nonneg (G 0 s) x).eq_or_lt with hx | hx
    · rw [if_pos hx.symm, if_neg (not_lt.mpr hx.symm.le)]
      norm_num
    · rw [if_neg hx.ne', if_pos hx]
      norm_num
  rw [hdis]
  calc Kernel.iterateSeq (dynamicLazy G hd) T (fun x => if 0 < Ψ x then 1 else 0) s
      ≤ Ψ s / (Fintype.card V : ℝ) ^ 3 := h
    _ ≤ (Fintype.card V : ℝ) / (Fintype.card V : ℝ) ^ 3 :=
        div_le_div_of_nonneg_right (potential_le_card _ s) (by positivity)
    _ = 1 / (Fintype.card V : ℝ) ^ 2 := by
        field_simp

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
  classical
  set Ψ := potential (G 0 s)
  set n : ℝ := (Fintype.card V : ℝ)
  have hΨ : ∀ t x, potential (G t x) = Ψ := fun t x => potential_congr (G 0 s) (hdeg t x)
  have hn : (1 : ℝ) ≤ n := by
    show (1 : ℝ) ≤ (Fintype.card V : ℝ)
    exact_mod_cast Fintype.card_pos
  have hφ1 : ∀ t, φ t ≤ 1 := fun t => (hφ t s).trans (conductance_le_one _)
  -- the potential of the projection "`i` against the rest"
  set f : C → Config V C → ℝ := fun i y => Ψ (colorIndicator i ∘ y)
  have hdrift : ∀ i, ∀ t < T, ∀ x, (dynamicLazy G hd t).apply (f i) x ≤
      (1 - φ t ^ 2 / (32 * n)) * f i x := by
    intro i t _ x
    have hproj : (dynamicLazy G hd t).apply (f i) x =
        (transition (lazyNeighbor (G t x) (hd t x))).apply Ψ (colorIndicator i ∘ x) :=
      (iterate_project (lazyNeighbor (G t x) (hd t x)) (colorIndicator i) Ψ 1 x).symm
    rw [hproj]
    have h := potential_drift_mul (G t x) (hd t x) (colorIndicator i ∘ x)
    rw [hΨ t x] at h
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (potential_nonneg _ _))
    have h2 : φ t ^ 2 ≤ conductance (G t x) ^ 2 := pow_le_pow_left₀ (hφ0 t) (hφ t x) 2
    have h3 : φ t ^ 2 / (32 * n) ≤ conductance (G t x) ^ 2 / (32 * n) :=
      div_le_div_of_nonneg_right h2 (by positivity)
    linarith
  have hbound : ∀ i, Kernel.iterateSeq (dynamicLazy G hd) T
      (fun x => if 0 < f i x then 1 else 0) s ≤ f i s / n ^ 3 := fun i =>
    iterateSeq_pos_le_of_mul_drift (dynamicLazy G hd) (f i) (fun _ => potential_nonneg _ _)
      (fun _ => one_le_potential _ _) hn φ hφ0 hφ1 T (hdrift i) hT s
  -- disagreement: some opinion is present but not everywhere
  have hpt : ∀ x, disagreement x ≤ ∑ i, if 0 < f i x then (1 : ℝ) else 0 := by
    intro x
    have hnn : ∀ i ∈ (univ : Finset C), (0 : ℝ) ≤ if 0 < f i x then 1 else 0 :=
      fun i _ => by split_ifs <;> norm_num
    unfold disagreement
    split_ifs with hc
    · exact sum_nonneg hnn
    · obtain ⟨v⟩ := ‹Nonempty V›
      have hpos : 0 < f (x v) x := by
        refine lt_of_le_of_ne (potential_nonneg _ _) (Ne.symm fun h0 => ?_)
        obtain ⟨b, hb⟩ := (potential_eq_zero_iff (G 0 s) (hd 0 s) _).mp h0
        apply hc
        refine ⟨x v, funext fun u => ?_⟩
        have hu := congrFun hb u
        have hv := congrFun hb v
        simp only [Function.comp, colorIndicator, decide_true] at hu hv
        subst hv
        simpa using hu
      calc (1 : ℝ) = if 0 < f (x v) x then 1 else 0 := by rw [if_pos hpos]
        _ ≤ ∑ i, if 0 < f i x then (1 : ℝ) else 0 :=
          single_le_sum hnn (mem_univ _)
  -- the opinions absent at time `0` contribute nothing, the others at most `n` each
  have hsum : ∑ i, f i s ≤ n ^ 2 := by
    have hzero : ∀ i ∈ (univ : Finset C), i ∉ univ.image s → f i s = 0 := by
      intro i _ hi
      refine (potential_eq_zero_iff (G 0 s) (hd 0 s) _).mpr ⟨false, funext fun u => ?_⟩
      have : s u ≠ i := fun h => hi (mem_image.mpr ⟨u, mem_univ _, h⟩)
      simp [colorIndicator, this]
    rw [← sum_subset (subset_univ _) hzero]
    calc ∑ i ∈ univ.image s, f i s ≤ ∑ _i ∈ univ.image s, n :=
          sum_le_sum fun i _ => potential_le_card _ _
      _ = (univ.image s).card * n := by rw [sum_const, nsmul_eq_mul]
      _ ≤ n * n := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          show ((univ.image s).card : ℝ) ≤ (Fintype.card V : ℝ)
          exact_mod_cast (card_image_le.trans (card_univ (α := V)).le)
      _ = n ^ 2 := by ring
  calc Kernel.iterateSeq (dynamicLazy G hd) T disagreement s
      ≤ Kernel.iterateSeq (dynamicLazy G hd) T
          (fun x => ∑ i, if 0 < f i x then (1 : ℝ) else 0) s :=
        Kernel.iterateSeq_mono _ T hpt s
    _ = ∑ i, Kernel.iterateSeq (dynamicLazy G hd) T (fun x => if 0 < f i x then 1 else 0) s :=
        iterateSeq_finset_sum _ T univ _ s
    _ ≤ ∑ i, f i s / n ^ 3 := sum_le_sum fun i _ => hbound i
    _ = (∑ i, f i s) / n ^ 3 := by rw [sum_div]
    _ ≤ n ^ 2 / n ^ 3 := div_le_div_of_nonneg_right hsum (by positivity)
    _ = 1 / n := by
        have : n ≠ 0 := by positivity
        field_simp

section StaticCorollaries
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Lemma 2.4 of BGKM16, static graph.** Two opinions, the lazy voter on a graph with `n`
vertices and conductance `φ`. For every `T` with `96 n ln n ≤ φ² T`, the opinions still disagree
at time `T` with probability at most `1/n²`: the consensus time is at most `96 n ln n / φ²` with
probability at least `1 - 1/n²`. -/
theorem lazy_consensus_conductance_sq (hd : ∀ v, 0 < G.degree v) (s : Config V Bool) (T : ℕ)
    (hT : 96 * (Fintype.card V : ℝ) * Real.log (Fintype.card V) ≤ conductance G ^ 2 * T) :
    (transition (lazyNeighbor G hd)).iterate T disagreement s ≤
      1 / (Fintype.card V : ℝ) ^ 2 := by
  have h := dynamic_consensus_conductance_sq (fun _ _ => G) (fun _ _ => hd) s (fun _ _ _ => rfl)
    (fun _ => conductance G) (fun _ => conductance_nonneg G) (fun _ _ => le_rfl) T (by
      rw [sum_const, card_range, nsmul_eq_mul]
      linarith)
  rwa [show dynamicLazy (fun _ _ => G) (fun _ _ => hd) =
    fun _ => transition (lazyNeighbor G hd) from rfl, Kernel.iterateSeq_const] at h

/-- **Part 2 of Theorem 1.1 of BGKM16, static graph, any number of opinions.** The lazy voter on
a graph with `n` vertices and conductance `φ`, from a configuration with any number of opinions:
for every `T` with `96 n ln n ≤ φ² T`, the opinions still disagree at time `T` with probability
at most `1/n`. -/
theorem lazy_consensus_conductance_sq_many [Nonempty V] {C : Type*} [Fintype C]
    (hd : ∀ v, 0 < G.degree v) (s : Config V C) (T : ℕ)
    (hT : 96 * (Fintype.card V : ℝ) * Real.log (Fintype.card V) ≤ conductance G ^ 2 * T) :
    (transition (lazyNeighbor G hd)).iterate T disagreement s ≤ 1 / (Fintype.card V : ℝ) := by
  have h := dynamic_consensus_conductance_sq_many (fun _ _ => G) (fun _ _ => hd) s
    (fun _ _ _ => rfl) (fun _ => conductance G) (fun _ => conductance_nonneg G) (fun _ _ => le_rfl)
    T (by
      rw [sum_const, card_range, nsmul_eq_mul]
      linarith)
  rwa [show dynamicLazy (C := C) (fun _ _ => G) (fun _ _ => hd) =
    fun _ => transition (lazyNeighbor G hd) from rfl, Kernel.iterateSeq_const] at h

/-- **Expected consensus time by restarting** (BGKM16, Theorem 1.1 (ii), static graph, any
number of opinions). If `96 n ln n ≤ φ² T₀`, then for every horizon `N`,
`𝔼[min(T_cons, N)] = ∑_{t < N} P(T_cons > t) ≤ 2 T₀`; letting `N → ∞`, `𝔼[T_cons] ≤ 2 T₀`. -/
theorem lazy_expected_consensus_time_sq [Nonempty V] {C : Type*} [Fintype C]
    (hd : ∀ v, 0 < G.degree v) (s : Config V C) (T₀ : ℕ)
    (hT₀ : 96 * (Fintype.card V : ℝ) * Real.log (Fintype.card V) ≤ conductance G ^ 2 * T₀)
    (N : ℕ) :
    ∑ t ∈ range N, (transition (lazyNeighbor G hd)).iterate t disagreement s ≤ 2 * T₀ := by
  set K : Kernel (Config V C) := transition (lazyNeighbor G hd)
  -- from every state, disagreement after `T₀` rounds has probability at most `1/2`
  have hhalf : ∀ x, K.iterate T₀ disagreement x ≤ 1 / 2 := by
    intro x
    rcases le_or_gt (Fintype.card V) 1 with h1 | h2
    · have hz : (disagreement : Config V C → ℝ) = fun _ => 0 :=
        funext (disagreement_eq_zero_of_card_le_one h1 (x (Classical.arbitrary V)))
      rw [hz, Kernel.iterate_const]
      norm_num
    · have h2' : (2 : ℝ) ≤ Fintype.card V := by
        have : 2 ≤ Fintype.card V := h2
        exact_mod_cast this
      exact (lazy_consensus_conductance_sq_many G hd x T₀ hT₀).trans
        (one_div_le_one_div_of_le (by norm_num) h2')
  have h := sum_iterate_le_of_block K disagreement disagreement T₀
    (by norm_num : (0 : ℝ) < 1 / 2)
    (fun x => by rcases disagreement_zero_or_one x with h | h <;> simp [h])
    (fun x => by rcases disagreement_zero_or_one x with h | h <;> simp [h])
    disagreement_zero_or_one (fun _ => le_rfl)
    (transition_disagreement_le (lazyNeighbor G hd))
    (fun x _ => by
      have := hhalf x
      linarith) N s
  have h1 : disagreement s ≤ 1 := by
    rcases disagreement_zero_or_one s with h | h <;> simp [h]
  calc ∑ t ∈ range N, K.iterate t disagreement s
      ≤ T₀ / (1 / 2) * disagreement s := h
    _ ≤ T₀ / (1 / 2) * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 2 * T₀ := by ring

end StaticCorollaries

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
  rcases hT with h1 | h2
  · exact dynamic_consensus_conductance G hd s hdeg φ hφ T h1
  · rcases le_or_gt (Fintype.card V) 1 with hV | hV
    · have hz : (disagreement : Config V Bool → ℝ) = fun _ => 0 :=
        funext (disagreement_eq_zero_of_card_le_one hV false)
      rw [hz, Kernel.iterateSeq_const_fun]
      norm_num
    · have hV' : (2 : ℝ) ≤ Fintype.card V := by
        have : 2 ≤ Fintype.card V := hV
        exact_mod_cast this
      refine (dynamic_consensus_conductance_sq G hd s hdeg φ hφ0 hφ T h2).trans ?_
      apply one_div_le_one_div_of_le (by norm_num)
      nlinarith

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
  obtain ⟨b₁, hb₁⟩ := lazy_consensus_conductance_many.{u, v}
  refine ⟨max b₁ 96, fun V C _ _ _ _ G _ hd s T hT => ?_⟩
  rcases hT with h1 | h2
  · apply hb₁ V C G hd s T
    have : b₁ * (G.edgeFinset.card : ℝ) ≤ max b₁ 96 * G.edgeFinset.card :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)
    linarith
  · rcases le_or_gt (Fintype.card V) 1 with hV | hV
    · have hz : (disagreement : Config V C → ℝ) = fun _ => 0 :=
        funext (disagreement_eq_zero_of_card_le_one hV (s (Classical.arbitrary V)))
      rw [hz, Kernel.iterate_const]
      norm_num
    · have hV' : (2 : ℝ) ≤ Fintype.card V := by
        have : 2 ≤ Fintype.card V := hV
        exact_mod_cast this
      have hlog : 0 ≤ (Fintype.card V : ℝ) * Real.log (Fintype.card V) :=
        mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith))
      have hb : 96 * (Fintype.card V : ℝ) * Real.log (Fintype.card V) ≤
          max b₁ 96 * (Fintype.card V : ℝ) * Real.log (Fintype.card V) := by
        rw [mul_assoc, mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) hlog
      exact (lazy_consensus_conductance_sq_many G hd s T (by linarith)).trans
        (one_div_le_one_div_of_le (by norm_num) hV')

end Voter
