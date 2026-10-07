import Voter.ConductanceManyAux
import Voter.ConductanceLevels

/-! # Expected consensus time with many opinions (BGKM16, Part 1 of Theorem 1.1)

Berenbrink, Giakkoupis, Kermarrec, Mallmann-Trenn, *Bounds on the voter model in dynamic
networks*, ICALP 2016 (BGKM16). Sort the configurations into levels by their number `ℓ` of
opinions: level `j` holds `θ_{j+1} < ℓ ≤ θ_j` with `θ_j = n (5/6)^j` (`levelInd`). By the phase
step (`phase_step`), from level `j` the chain leaves the levels `≤ j` within
`B_j = ⌈384 vol(V) / (θ_j d_min φ)⌉` rounds with probability at least `1/3`, so it spends at
most `3 B_j` rounds there in expectation (`level_time_le`, from `sum_iterate_le_of_block`).
Summing the geometric series `∑_j 1/θ_j ≤ 3` over the levels with `θ_j ≥ 2` gives an expected
consensus time of at most `6930 m / (d_min φ)` (`expected_time_many_bound`).
-/

namespace Voter
open Dynamics Finset

/-! ### The thresholds `θ_j = n (5/6)^j` -/

/-- The phase thresholds `θ_j = n (5/6)^j`. -/
noncomputable def phaseThreshold (n j : ℕ) : ℝ := n * (5 / 6 : ℝ) ^ j

lemma phaseThreshold_succ (n j : ℕ) :
    phaseThreshold n (j + 1) = phaseThreshold n j * (5 / 6) := by
  simp only [phaseThreshold, pow_succ, mul_assoc]

lemma phaseThreshold_zero (n : ℕ) : phaseThreshold n 0 = n := by simp [phaseThreshold]

lemma phaseThreshold_pos {n : ℕ} (hn : 0 < n) (j : ℕ) : 0 < phaseThreshold n j := by
  unfold phaseThreshold
  have : (0 : ℝ) < n := by exact_mod_cast hn
  positivity

lemma phaseThreshold_antitone (n : ℕ) : Antitone (phaseThreshold n) := by
  intro j k hjk
  unfold phaseThreshold
  exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) hjk)
    (Nat.cast_nonneg n)

lemma exists_phaseThreshold_lt_two (n : ℕ) : ∃ J, phaseThreshold n J < 2 := by
  obtain ⟨J, hJ⟩ := exists_pow_lt_of_lt_one (by positivity : (0 : ℝ) < 2 / (n + 1))
    (by norm_num : (5 / 6 : ℝ) < 1)
  refine ⟨J, ?_⟩
  unfold phaseThreshold
  have hn : (0 : ℝ) < n + 1 := by positivity
  rw [lt_div_iff₀ hn] at hJ
  have : (n : ℝ) * (5 / 6) ^ J ≤ (5 / 6) ^ J * (n + 1) := by
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 6) J]
  linarith

/-- If `θ_J ≥ 2`, then `(6/5)^J ≤ n/2`. -/
lemma six_fifths_pow_le {n J : ℕ} (hJ : 2 ≤ phaseThreshold n J) :
    (6 / 5 : ℝ) ^ J ≤ n / 2 := by
  unfold phaseThreshold at hJ
  have hprod : (6 / 5 : ℝ) ^ J * (5 / 6) ^ J = 1 := by
    rw [← mul_pow]
    norm_num
  have hpos : (0 : ℝ) < (6 / 5) ^ J := by positivity
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  nlinarith

/-- **The geometric series of the phases**: if `θ_J ≥ 2`, then `∑_{j ≤ J} 1/θ_j ≤ 3`. -/
lemma sum_inv_phaseThreshold_le {n J : ℕ} (hn : 0 < n) (hJ : 2 ≤ phaseThreshold n J) :
    ∑ j ∈ range (J + 1), 1 / phaseThreshold n j ≤ 3 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hterm (j : ℕ) : 1 / phaseThreshold n j = (6 / 5 : ℝ) ^ j / n := by
    unfold phaseThreshold
    rw [div_eq_div_iff (by positivity) hn'.ne', one_mul, mul_comm, mul_assoc, ← mul_pow]
    norm_num
  simp_rw [hterm]
  rw [← sum_div, geom_sum_eq (by norm_num : (6 / 5 : ℝ) ≠ 1), div_le_iff₀ hn']
  have h := six_fifths_pow_le hJ
  have he : ((6 / 5 : ℝ) ^ (J + 1) - 1) / (6 / 5 - 1) = 6 * (6 / 5) ^ J - 5 := by
    rw [pow_succ]
    ring
  rw [he]
  linarith

/-- If `θ_J ≥ 2`, then there are at most `3n` levels `j ≤ J`. -/
lemma levels_le {n J : ℕ} (hJ : 2 ≤ phaseThreshold n J) : ((J + 1 : ℕ) : ℝ) ≤ 3 * n := by
  have h := six_fifths_pow_le hJ
  have hb := one_add_mul_le_pow (by norm_num : (-2 : ℝ) ≤ 1 / 5) J
  push_cast
  have : (1 : ℝ) + 1 / 5 = 6 / 5 := by norm_num
  rw [this] at hb
  nlinarith

/-! ### Levels -/

variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

/-- Indicator of level `j`: at least two opinions, more than `θ_{j+1}` and at most `θ_j`. -/
noncomputable def levelInd (n j : ℕ) (y : Config V C) : ℝ :=
  if phaseThreshold n (j + 1) < (opinions y).card ∧
    ((opinions y).card : ℝ) ≤ phaseThreshold n j ∧ 2 ≤ (opinions y).card then 1 else 0

/-- Indicator of having more than `θ_{j+1}` opinions. -/
noncomputable def aboveInd (n j : ℕ) (y : Config V C) : ℝ :=
  if phaseThreshold n (j + 1) < (opinions y).card then 1 else 0

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Time spent in a level** (BGKM16, Lemma 2.3): at most `3 B` rounds in expectation, if
`384 vol(V) ≤ θ_j d_min φ B`. -/
lemma level_time_le [Nonempty V] (hd : ∀ v, 0 < G.degree v) (n j B : ℕ)
    (hB : 384 * (vol G univ : ℝ) ≤ phaseThreshold n j * (G.minDegree * conductance G * B))
    (N : ℕ) (x : Config V C) :
    ∑ t ∈ range N, (transition (lazyNeighbor G hd)).iterate t (levelInd n j) x ≤ 3 * B := by
  set K : Kernel (Config V C) := transition (lazyNeighbor G hd)
  have hf01 : ∀ y : Config V C, aboveInd n j y = 0 ∨ aboveInd n j y = 1 := fun y => by
    unfold aboveInd
    split_ifs <;> simp
  have hf0 : ∀ y : Config V C, 0 ≤ aboveInd n j y := fun y => by
    rcases hf01 y with h | h <;> simp [h]
  have hf1 : ∀ y : Config V C, aboveInd n j y ≤ 1 := fun y => by
    rcases hf01 y with h | h <;> simp [h]
  have hg : ∀ y : Config V C, levelInd n j y = 0 ∨ levelInd n j y = 1 := fun y => by
    unfold levelInd
    split_ifs <;> simp
  have hgf : ∀ y : Config V C, levelInd n j y ≤ aboveInd n j y := fun y => by
    unfold levelInd aboveInd
    split_ifs with h1 h2 <;> first | exact absurd h1.1 h2 | norm_num
  -- the number of opinions cannot grow
  have hK : ∀ y, K.apply (aboveInd n j) y ≤ aboveInd n j y := by
    intro y
    rcases hf01 y with h | h
    · have hle := iterate_le_of_closed K (fun z => opinions z ⊆ opinions y)
        (opinions_closed (lazyNeighbor G hd) (opinions y)) (F := aboveInd n j)
        (F' := fun _ => 0) (fun z hz => by
          have hy : ¬ phaseThreshold n (j + 1) < (opinions y).card := by
            intro hlt
            unfold aboveInd at h
            rw [if_pos hlt] at h
            norm_num at h
          have hc : ((opinions z).card : ℝ) ≤ (opinions y).card := by
            exact_mod_cast card_le_card hz
          unfold aboveInd
          rw [if_neg (not_lt.mpr (by linarith [not_lt.mp hy]))]) 1 y subset_rfl
      rw [K.iterate_const] at hle
      rw [h]
      exact hle
    · rw [h]
      calc K.apply (aboveInd n j) y ≤ (K y).expect (fun _ => 1) := (K y).expect_mono hf1
        _ = 1 := (K y).expect_const 1
  have hblock : ∀ y, levelInd n j y = 1 → K.iterate B (aboveInd n j) y ≤ 1 - 1 / 3 := by
    intro y hy
    unfold levelInd at hy
    split_ifs at hy with hlev
    · have h := phase_step G hd y B hlev.2.2 hlev.2.1 hB
      have he : aboveInd n j = fun z : Config V C =>
          if phaseThreshold n j * (5 / 6) < (opinions z).card then 1 else 0 := by
        funext z
        simp only [aboveInd, phaseThreshold_succ]
      rw [he]
      linarith
    · norm_num at hy
  have h := sum_iterate_le_of_block K (aboveInd n j) (levelInd n j) B
    (by norm_num : (0 : ℝ) < 1 / 3) hf0 hf1 hg hgf hK hblock N x
  calc ∑ t ∈ range N, K.iterate t (levelInd n j) x ≤ B / (1 / 3) * aboveInd n j x := h
    _ ≤ B / (1 / 3) * 1 := mul_le_mul_of_nonneg_left (hf1 x) (by positivity)
    _ = 3 * B := by ring

omit [Fintype C] [DecidableEq V] in
/-- **The levels cover the disagreement states**: with `θ_J ≥ 2` and `θ_{J+1} < 2`, every
configuration with at least two opinions lies in one of the levels `j ≤ J`. -/
lemma disagreement_le_sum_levelInd [Nonempty V] {J : ℕ}
    (hJ : phaseThreshold (Fintype.card V) (J + 1) < 2) (y : Config V C) :
    disagreement y ≤ ∑ j ∈ range (J + 1), levelInd (Fintype.card V) j y := by
  classical
  rw [disagreement_eq_opinions]
  have hnonneg : ∀ j ∈ range (J + 1), 0 ≤ levelInd (Fintype.card V) j y := fun j _ => by
    unfold levelInd
    split_ifs <;> norm_num
  split_ifs with h2
  · -- the level of `y`: the first `j` with `θ_{j+1} < ℓ`
    have hℓ2 : (2 : ℝ) ≤ (opinions y).card := by exact_mod_cast h2
    have hex : ∃ j, phaseThreshold (Fintype.card V) (j + 1) < (opinions y).card :=
      ⟨J, by linarith⟩
    set j := Nat.find hex
    have hj : phaseThreshold (Fintype.card V) (j + 1) < (opinions y).card := Nat.find_spec hex
    have hjJ : j ≤ J := Nat.find_min' hex (by linarith)
    have hjle : ((opinions y).card : ℝ) ≤ phaseThreshold (Fintype.card V) j := by
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · rw [h0, phaseThreshold_zero]
        have : (opinions y).card ≤ Fintype.card V := by
          unfold opinions
          exact (card_image_le).trans (by simp)
        exact_mod_cast this
      · obtain ⟨k, hk⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
        have hmin := Nat.find_min hex (show k < j by omega)
        rw [not_lt, ← hk] at hmin
        exact hmin
    have hlev : levelInd (Fintype.card V) j y = 1 := by
      unfold levelInd
      rw [if_pos ⟨hj, hjle, h2⟩]
    rw [← hlev]
    exact single_le_sum hnonneg (mem_range.mpr (by omega))
  · exact sum_nonneg hnonneg

/-! ### The expected consensus time -/

omit [DecidableEq C] in
/-- **Expected consensus time with many opinions** (BGKM16, Part 1 of Theorem 1.1, static
graph): if `7000 m ≤ d_min φ T₀`, then `∑_{t < N} P(T_cons > t) ≤ T₀` for every horizon `N`. -/
theorem expected_time_many_bound [Nonempty V] (hd : ∀ v, 0 < G.degree v) (s : Config V C)
    (T₀ : ℕ) (hT : 7000 * (G.edgeFinset.card : ℝ) ≤ G.minDegree * conductance G * T₀)
    (N : ℕ) :
    ∑ t ∈ range N, (transition (lazyNeighbor G hd)).iterate t disagreement s ≤ T₀ := by
  classical
  set K : Kernel (Config V C) := transition (lazyNeighbor G hd)
  set n := Fintype.card V
  set m : ℝ := (G.edgeFinset.card : ℝ)
  set D : ℝ := G.minDegree * conductance G
  have hn : 0 < n := Fintype.card_pos
  -- `vol(V) = 2m > 0`, `D > 0`, `n ≤ 2m / D`
  have hW : (vol G univ : ℝ) = 2 * m := by
    rw [vol_univ]
    push_cast
    rfl
  have hWpos : (0 : ℝ) < vol G univ := by
    obtain ⟨v⟩ := ‹Nonempty V›
    exact_mod_cast vol_pos hd (univ_nonempty_iff.mpr ⟨v⟩)
  have hm : 0 < m := by linarith
  have hD0 : 0 ≤ D := mul_nonneg (Nat.cast_nonneg _) (conductance_nonneg G)
  have hT0 : (0 : ℝ) ≤ T₀ := Nat.cast_nonneg _
  have hD : 0 < D := by
    by_contra hcon
    have : D = 0 := le_antisymm (not_lt.mp hcon) hD0
    rw [this, zero_mul] at hT
    linarith
  have hnD : (n : ℝ) * D ≤ 2 * m := by
    have h1 : (n : ℝ) * G.minDegree ≤ 2 * m := by
      have : ∑ v : V, (G.minDegree : ℝ) ≤ ∑ v : V, (G.degree v : ℝ) :=
        sum_le_sum fun v _ => by exact_mod_cast G.minDegree_le_degree v
      rw [sum_const, card_univ, nsmul_eq_mul] at this
      have h2 : ∑ v : V, (G.degree v : ℝ) = 2 * m := by
        rw [← hW]
        unfold vol
        push_cast
        rfl
      linarith
    have hφ := conductance_le_one G
    have : D ≤ G.minDegree := by
      have : (0 : ℝ) ≤ G.minDegree := Nat.cast_nonneg _
      calc D = G.minDegree * conductance G := rfl
        _ ≤ G.minDegree * 1 := mul_le_mul_of_nonneg_left hφ this
        _ = G.minDegree := mul_one _
    have : (n : ℝ) * D ≤ n * G.minDegree :=
      mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
    linarith
  -- the number of levels
  have hex := exists_phaseThreshold_lt_two n
  set J' := Nat.find hex
  have hJ'lt : phaseThreshold n J' < 2 := Nat.find_spec hex
  have hJ'pos : 0 < J' := by
    rcases Nat.eq_zero_or_pos J' with h0 | h0
    · -- then `n < 2`, so every configuration is a consensus and there is nothing to do
      exfalso
      rw [h0, phaseThreshold_zero] at hJ'lt
      have hn2 : n < 2 := by exact_mod_cast hJ'lt
      obtain ⟨v⟩ := ‹Nonempty V›
      obtain ⟨w, hw⟩ := (G.degree_pos_iff_exists_adj v).mp (hd v)
      have : 2 ≤ n := by
        have := Finset.card_le_univ ({v, w} : Finset V)
        rw [card_pair hw.ne] at this
        exact this
      omega
    · exact h0
  obtain ⟨J, hJ⟩ : ∃ J, J' = J + 1 := ⟨J' - 1, by omega⟩
  have hJ2 : 2 ≤ phaseThreshold n J := by
    have := Nat.find_min hex (show J < J' by omega)
    exact not_lt.mp this
  have hJlt : phaseThreshold n (J + 1) < 2 := by rw [← hJ]; exact hJ'lt
  -- the block lengths
  set B : ℕ → ℕ := fun j => ⌈384 * (vol G univ : ℝ) / (phaseThreshold n j * D)⌉₊
  have hB : ∀ j, 384 * (vol G univ : ℝ) ≤ phaseThreshold n j * (D * B j) := fun j => by
    have hθ := phaseThreshold_pos hn j
    have h := Nat.le_ceil (384 * (vol G univ : ℝ) / (phaseThreshold n j * D))
    rw [div_le_iff₀ (by positivity)] at h
    nlinarith
  have hBle : ∀ j, (B j : ℝ) ≤ 384 * (vol G univ : ℝ) / D * (1 / phaseThreshold n j) + 1 :=
    fun j => by
      have hθ := phaseThreshold_pos hn j
      have h := (Nat.ceil_lt_add_one (by positivity :
        0 ≤ 384 * (vol G univ : ℝ) / (phaseThreshold n j * D))).le
      calc (B j : ℝ) ≤ 384 * (vol G univ : ℝ) / (phaseThreshold n j * D) + 1 := h
        _ = 384 * (vol G univ : ℝ) / D * (1 / phaseThreshold n j) + 1 := by
          field_simp
  -- time with disagreement ≤ time in the levels ≤ `3 ∑ B_j`
  have hsum : ∑ t ∈ range N, K.iterate t disagreement s ≤
      ∑ j ∈ range (J + 1), 3 * (B j : ℝ) := by
    calc ∑ t ∈ range N, K.iterate t disagreement s
        ≤ ∑ t ∈ range N, ∑ j ∈ range (J + 1), K.iterate t (levelInd n j) s := by
          refine sum_le_sum fun t _ => ?_
          rw [← congrFun (iterate_finset_sum K t (range (J + 1)) (fun j => levelInd n j)) s]
          exact K.iterate_mono t (disagreement_le_sum_levelInd hJlt) s
      _ = ∑ j ∈ range (J + 1), ∑ t ∈ range N, K.iterate t (levelInd n j) s := sum_comm
      _ ≤ ∑ j ∈ range (J + 1), 3 * (B j : ℝ) :=
          sum_le_sum fun j _ => level_time_le G hd n j (B j) (hB j) N s
  -- the arithmetic
  have hgeo := sum_inv_phaseThreshold_le hn hJ2
  have hlev := levels_le hJ2
  have hBsum : ∑ j ∈ range (J + 1), (B j : ℝ) ≤
      384 * (vol G univ : ℝ) / D * 3 + (J + 1 : ℕ) := by
    calc ∑ j ∈ range (J + 1), (B j : ℝ)
        ≤ ∑ j ∈ range (J + 1), (384 * (vol G univ : ℝ) / D * (1 / phaseThreshold n j) + 1) :=
          sum_le_sum fun j _ => hBle j
      _ = 384 * (vol G univ : ℝ) / D * ∑ j ∈ range (J + 1), 1 / phaseThreshold n j +
            (J + 1 : ℕ) := by
          rw [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_one]
      _ ≤ 384 * (vol G univ : ℝ) / D * 3 + (J + 1 : ℕ) := by
          gcongr
  rw [← mul_sum] at hsum
  -- `3 ∑ B_j ≤ 3 (2304 m / D + 3n) ≤ 6930 m / D ≤ T₀`
  have hfin : 3 * (384 * (vol G univ : ℝ) / D * 3 + (J + 1 : ℕ)) ≤ T₀ := by
    rw [hW]
    have hTD : 7000 * m ≤ D * T₀ := hT
    have h1 : 3 * (384 * (2 * m) / D * 3) = 6912 * m / D := by ring
    have h2 : (3 : ℝ) * ((J + 1 : ℕ) : ℝ) ≤ 18 * m / D := by
      rw [le_div_iff₀ hD]
      nlinarith
    have h3 : 6930 * m / D ≤ T₀ := by
      rw [div_le_iff₀ hD]
      nlinarith
    have h4 : 6912 * m / D + 18 * m / D = 6930 * m / D := by ring
    nlinarith
  linarith

end Voter
