import Epidemics.CobraDuality

/-! # Spectral quantities for the COBRA cover time (EPI-4)

Cooper, Radzik, Rivera, *The coalescing-branching random walk on expanders and the dual epidemic
process*, PODC 2016 (arXiv:1602.05768), Section 1 and the proof of Lemma 1 (Section 3).

For a connected `r`-regular graph `G` the random walk has transition matrix `P = A(G) / r`, with
eigenvalues `1 = λ₁ ≥ λ₂ ≥ ⋯ ≥ λₙ ≥ -1`, and the paper's `λ = λ_max = max_{i ≥ 2} |λᵢ|`. Since
`λₙ ≤ λ₂`, this is `max {λ₂, |λₙ|}` (`lambdaG`).

*Duplication note.* `transitionMatrix`, `walkEigenvalues` and `lambdaG` are verbatim copies of
`Median.transitionMatrix`, `Median.walkEigenvalues` and `Median.lambdaG` (median package, two-sample
voting on expanders): the epidemics package does not depend on the median package. They should
move to `dynamics/` together with the spectral lemmas below.

The spectral core of Lemma 1 is `‖P 1_A‖² ≤ λ² |A| + (1 - λ²) |A|² / n`, where
`(P 1_A)(x) = d_A(x) / r` and `d_A(x) = |N(x) ∩ A|` (`sum_sq_neighbor_le`).
-/

namespace Epidemics
open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The transition matrix `P = A / d` of the random walk on a `d`-regular graph (copy of
`Median.transitionMatrix`). -/
noncomputable def transitionMatrix (d : ℕ) : Matrix V V ℝ := (d : ℝ)⁻¹ • G.adjMatrix ℝ

omit [Fintype V] [DecidableEq V] in
/-- `P = A / d` is real symmetric. -/
theorem transitionMatrix_isHermitian (d : ℕ) : (transitionMatrix G d).IsHermitian := by
  ext i j
  simp [transitionMatrix, Matrix.conjTranspose_apply, SimpleGraph.adjMatrix_apply, G.adj_comm]

/-- The eigenvalues `λ₁ ≥ λ₂ ≥ ⋯ ≥ λₙ` of the transition matrix, in non-increasing order
(copy of `Median.walkEigenvalues`). -/
noncomputable def walkEigenvalues (d : ℕ) : Fin (Fintype.card V) → ℝ :=
  (transitionMatrix_isHermitian G d).eigenvalues₀

/-- The paper's `λ = λ_max = max_{i ≥ 2} |λᵢ|` (Section 1), written `max {λ₂, |λₙ|}` (equal,
since `λₙ ≤ λ₂`), and set to `0` on graphs with fewer than two vertices (copy of
`Median.lambdaG`). -/
noncomputable def lambdaG (d : ℕ) : ℝ :=
  if h : 2 ≤ Fintype.card V then
    max (walkEigenvalues G d ⟨1, by omega⟩) |walkEigenvalues G d ⟨Fintype.card V - 1, by omega⟩|
  else 0

/-- `λ ≥ 0`. -/
lemma lambdaG_nonneg (d : ℕ) : 0 ≤ lambdaG G d := by
  unfold lambdaG
  split_ifs
  · exact (abs_nonneg _).trans (le_max_right _ _)
  · exact le_rfl

open Matrix

/-! ### Copies of the `Median` eigenbasis lemmas

`sum_eigvec_mul_eigvec`, `dotProduct_eq_sum_eigvec`, `eigvec_dotProduct_mulVec`,
`dotProduct_mulVec_eq_sum_eigvec`, `indVec`, `indVec_dotProduct_self`, `one_dotProduct_indVec`,
`transitionMatrix_mulVec_one` and `abs_eigenvalues_le_lambdaG` are copies of the declarations of
the same names in `Median/ExpanderMixing.lean` (median package). The epidemics package does not
depend on median, so they are restated here; together with `transitionMatrix` and `lambdaG` they
should move to `dynamics/`. -/

section Spectral
open Matrix

variable {A : Matrix V V ℝ} (hA : A.IsHermitian)

omit [DecidableEq V] in
private lemma sum_eigvec_mul_eigvec [DecidableEq V] (u v : V) :
    ∑ k, hA.eigenvectorBasis k u * hA.eigenvectorBasis k v = if u = v then 1 else 0 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2) u) v
  simpa [Matrix.mul_apply, one_apply] using h

lemma dotProduct_eq_sum_eigvec (y z : V → ℝ) :
    y ⬝ᵥ z = ∑ k, (⇑(hA.eigenvectorBasis k) ⬝ᵥ y) * (⇑(hA.eigenvectorBasis k) ⬝ᵥ z) := by
  calc y ⬝ᵥ z = ∑ u, ∑ v, y u * z v * (if u = v then 1 else 0) := by
        simp [dotProduct]
    _ = ∑ u, ∑ v, y u * z v *
          ∑ k, hA.eigenvectorBasis k u * hA.eigenvectorBasis k v := by
        simp_rw [sum_eigvec_mul_eigvec]
    _ = ∑ u, ∑ v, ∑ k, (hA.eigenvectorBasis k u * y u) *
          (hA.eigenvectorBasis k v * z v) := by
        refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
    _ = ∑ u, ∑ k, ∑ v, (hA.eigenvectorBasis k u * y u) *
          (hA.eigenvectorBasis k v * z v) :=
        Finset.sum_congr rfl fun u _ => Finset.sum_comm
    _ = ∑ k, ∑ u, ∑ v, (hA.eigenvectorBasis k u * y u) *
          (hA.eigenvectorBasis k v * z v) := Finset.sum_comm
    _ = _ := by
        simp only [dotProduct, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_comm

lemma eigvec_dotProduct_mulVec (k : V) (z : V → ℝ) :
    ⇑(hA.eigenvectorBasis k) ⬝ᵥ (A *ᵥ z) =
      hA.eigenvalues k * (⇑(hA.eigenvectorBasis k) ⬝ᵥ z) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, ← conjTranspose_eq_transpose_of_trivial, hA.eq,
    hA.mulVec_eigenvectorBasis, smul_dotProduct, smul_eq_mul]

lemma dotProduct_mulVec_eq_sum_eigvec (y z : V → ℝ) :
    y ⬝ᵥ (A *ᵥ z) = ∑ k, hA.eigenvalues k *
      ((⇑(hA.eigenvectorBasis k) ⬝ᵥ y) * (⇑(hA.eigenvectorBasis k) ⬝ᵥ z)) := by
  rw [dotProduct_eq_sum_eigvec hA]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [eigvec_dotProduct_mulVec hA]
  ring

end Spectral

/-- The indicator vector `1_S` (copy of `Median.indVec`). -/
def indVec (S : Finset V) : V → ℝ := fun v => if v ∈ S then 1 else 0

lemma indVec_dotProduct_self (S : Finset V) : indVec S ⬝ᵥ indVec S = S.card := by
  simp only [dotProduct, indVec, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_mem, univ_inter]
  simp

lemma one_dotProduct_indVec (S : Finset V) : (fun _ => (1 : ℝ)) ⬝ᵥ indVec S = S.card := by
  simp [dotProduct, indVec]

omit [DecidableEq V] in
/-- `P 1 = 1` on a `d`-regular graph, `d > 0` (copy of `Median.transitionMatrix_mulVec_one`). -/
lemma transitionMatrix_mulVec_one {d : ℕ} (hd : 0 < d) (hreg : G.IsRegularOfDegree d) :
    transitionMatrix G d *ᵥ (fun _ => (1 : ℝ)) = fun _ => 1 := by
  funext v
  rw [transitionMatrix, smul_mulVec, Pi.smul_apply, SimpleGraph.adjMatrix_mulVec_apply,
    Finset.sum_const, G.card_neighborFinset_eq_degree, hreg v, smul_eq_mul, nsmul_eq_mul,
    mul_one, inv_mul_cancel₀ (by exact_mod_cast hd.ne')]

/-- Every eigenvalue of `P` other than the top one has absolute value at most `λ`
(copy of `Median.abs_eigenvalues_le_lambdaG`). -/
lemma abs_eigenvalues_le_lambdaG (d : ℕ) (k : V)
    (hk : (Fintype.equivOfCardEq (Fintype.card_fin _)).symm k ≠
      ⟨0, Fintype.card_pos_iff.mpr ⟨k⟩⟩) :
    |(transitionMatrix_isHermitian G d).eigenvalues k| ≤ lambdaG G d := by
  set j := (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card V))).symm k
  have hj : 1 ≤ j.val := by
    rcases Nat.eq_zero_or_pos j.val with h | h
    · exact absurd (Fin.ext h) hk
    · exact h
  have hlt := j.isLt
  have h2 : 2 ≤ Fintype.card V := by omega
  have hμ : (transitionMatrix_isHermitian G d).eigenvalues k = walkEigenvalues G d j := rfl
  have anti : Antitone (walkEigenvalues G d) :=
    (transitionMatrix_isHermitian G d).eigenvalues₀_antitone
  have h1 : walkEigenvalues G d j ≤ walkEigenvalues G d ⟨1, by omega⟩ :=
    anti (Fin.mk_le_mk.mpr hj)
  have h3 : walkEigenvalues G d ⟨Fintype.card V - 1, by omega⟩ ≤ walkEigenvalues G d j :=
    anti (Fin.mk_le_mk.mpr (by omega))
  rw [hμ, lambdaG, dif_pos h2, abs_le]
  constructor
  · have := neg_abs_le (walkEigenvalues G d ⟨Fintype.card V - 1, by omega⟩)
    have := le_max_right (walkEigenvalues G d ⟨1, by omega⟩)
      |walkEigenvalues G d ⟨Fintype.card V - 1, by omega⟩|
    linarith
  · exact h1.trans (le_max_left _ _)

variable {G}

/-- A positive-degree regular simple graph has at least two vertices. -/
lemma two_le_card_of_pos_regular {r : ℕ} (hreg : G.IsRegularOfDegree r) (hr : 0 < r)
    [Nonempty V] : 2 ≤ Fintype.card V := by
  obtain ⟨v⟩ : Nonempty V := inferInstance
  have hsub : G.neighborFinset v ⊆ Finset.univ.erase v := by
    intro u hu
    exact Finset.mem_erase.2
      ⟨(G.ne_of_adj ((G.mem_neighborFinset v u).mp hu)).symm, Finset.mem_univ u⟩
  have hle : (G.neighborFinset v).card ≤ Fintype.card V - 1 := by
    calc (G.neighborFinset v).card
        ≤ (Finset.univ.erase v).card := Finset.card_le_card hsub
      _ = Fintype.card V - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]
  rw [G.card_neighborFinset_eq_degree, hreg v] at hle
  omega

/-- Double counting: `∑_x d_A(x) = r |A|` on an `r`-regular graph. -/
lemma sum_neighborCard_eq {r : ℕ} (hreg : G.IsRegularOfDegree r) (A : Finset V) :
    ∑ x, (G.neighborFinset x ∩ A).card = r * A.card := by
  classical
  have hcard (x : V) :
      (G.neighborFinset x ∩ A).card = ∑ w ∈ A, if G.Adj x w then 1 else 0 := by
    rw [Finset.card_eq_sum_ite
      (Finset.inter_subset_right (s₁ := G.neighborFinset x) (s₂ := A))]
    refine Finset.sum_congr rfl fun w hw => ?_
    simp [Finset.mem_inter, hw, G.mem_neighborFinset]
  calc ∑ x, (G.neighborFinset x ∩ A).card
      = ∑ x, ∑ w ∈ A, if G.Adj x w then 1 else 0 := by
        exact Finset.sum_congr rfl fun x _ => hcard x
    _ = ∑ w ∈ A, ∑ x, if G.Adj w x then 1 else 0 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun x _ => ?_
        simp [G.adj_comm]
    _ = ∑ w ∈ A, G.degree w := by
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [Finset.sum_boole, ← G.card_neighborFinset_eq_degree]
        apply congrArg Finset.card
        ext x
        simp [G.mem_neighborFinset]
    _ = ∑ _w ∈ A, r := by
        refine Finset.sum_congr rfl fun w _ => hreg w
    _ = r * A.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- `(P 1_A)(x) = d_A(x) / r`. -/
lemma transition_indVec_apply {r : ℕ} (A : Finset V) (x : V) :
    (transitionMatrix G r *ᵥ indVec A) x =
      ((G.neighborFinset x ∩ A).card : ℝ) / r := by
  rw [transitionMatrix, smul_mulVec, Pi.smul_apply, smul_eq_mul,
    SimpleGraph.adjMatrix_mulVec_apply, div_eq_inv_mul]
  congr 1
  classical
  simp only [indVec, Finset.sum_boole, Finset.filter_mem_eq_inter]

/-- `‖P 1_A‖² = ∑_x (d_A(x) / r)²`. -/
lemma sum_sq_neighbor_eq_dotProduct {r : ℕ} (A : Finset V) :
    ∑ x, (((G.neighborFinset x ∩ A).card : ℝ) / r) ^ 2 =
      (transitionMatrix G r *ᵥ indVec A) ⬝ᵥ (transitionMatrix G r *ᵥ indVec A) := by
  simp only [dotProduct, sq, transition_indVec_apply A]

/-- If `λ < 1`, expand `1_A` in the eigenbasis of `P`: the top eigenvalue is `1` with squared
coefficient `|A|² / n`, and every other eigenvalue has square at most `λ²`. -/
lemma norm_sq_indVec_le_of_lambda_lt {r : ℕ} (hreg : G.IsRegularOfDegree r) (hr : 0 < r)
    (hL : lambdaG G r < 1) (A : Finset V) :
    (transitionMatrix G r *ᵥ indVec A) ⬝ᵥ (transitionMatrix G r *ᵥ indVec A) ≤
      lambdaG G r ^ 2 * A.card +
        (1 - lambdaG G r ^ 2) * A.card ^ 2 / Fintype.card V := by
  rcases isEmpty_or_nonempty V with hV | hV
  · haveI := hV
    have hA : A = ∅ := Finset.eq_empty_of_isEmpty A
    simp [hA, dotProduct, lambdaG, Fintype.card_eq_zero]
  have hn2 : 2 ≤ Fintype.card V := two_le_card_of_pos_regular hreg hr
  have hn : 0 < Fintype.card V := by omega
  have hP := transitionMatrix_isHermitian G r
  set P := transitionMatrix G r
  set b : V → V → ℝ := fun k => ⇑(hP.eigenvectorBasis k)
  set μ : V → ℝ := hP.eigenvalues
  set one : V → ℝ := fun _ => 1
  set e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card V))
  set k₀ : V := e ⟨0, hn⟩ with hk₀
  have hsmall : ∀ k, k ≠ k₀ → |μ k| ≤ lambdaG G r := by
    intro k hk
    refine abs_eigenvalues_le_lambdaG G r k ?_
    intro h
    apply hk
    rw [hk₀, ← h, Equiv.apply_symm_apply]
  have hP1 : P *ᵥ one = one := transitionMatrix_mulVec_one G hr hreg
  have horth : ∀ k, k ≠ k₀ → b k ⬝ᵥ one = 0 := by
    intro k hk
    have h := eigvec_dotProduct_mulVec hP k one
    rw [hP1] at h
    have hμk : μ k < 1 := lt_of_le_of_lt ((le_abs_self _).trans (hsmall k hk)) hL
    have : (1 - μ k) * (b k ⬝ᵥ one) = 0 := by
      simp only [b, μ] at h ⊢
      linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · linarith
    · exact h0
  set c := b k₀ ⬝ᵥ one
  have hsum_single (f : V → ℝ) : ∑ k, (b k ⬝ᵥ one) * f k = c * f k₀ := by
    rw [Finset.sum_eq_single k₀ (fun k _ hk => by rw [horth k hk, zero_mul]) (by simp)]
  have hc2 : c * c = Fintype.card V := by
    have h := dotProduct_eq_sum_eigvec hP one one
    rw [hsum_single] at h
    rw [← h]
    simp [dotProduct, one]
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, mul_zero] at hc2
    exact (Nat.cast_pos.mpr hn).ne' hc2.symm
  have hcs (S : Finset V) : c * (b k₀ ⬝ᵥ indVec S) = S.card := by
    have h := dotProduct_eq_sum_eigvec hP one (indVec S)
    rw [hsum_single, one_dotProduct_indVec] at h
    exact h.symm
  have hμ0 : μ k₀ = 1 := by
    have h := eigvec_dotProduct_mulVec hP k₀ one
    rw [hP1] at h
    have : (μ k₀ - 1) * c = 0 := by
      simp only [b, μ, c] at h ⊢
      linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · linarith
    · exact absurd h0 hc0
  set s : V → ℝ := fun k => b k ⬝ᵥ indVec A
  have hS2 : ∑ k, s k ^ 2 = A.card := by
    have h := dotProduct_eq_sum_eigvec hP (indVec A) (indVec A)
    rw [indVec_dotProduct_self] at h
    rw [h]
    simp only [s, sq]
    rfl
  have hs0 : s k₀ ^ 2 = (A.card : ℝ) ^ 2 / Fintype.card V := by
    have hmul := hcs A
    have hs : s k₀ = A.card / c := by
      rw [eq_div_iff hc0]
      simpa [s, mul_comm] using hmul
    have hc2sq : c ^ 2 = (Fintype.card V : ℝ) := by rw [sq, hc2]
    rw [hs, div_pow, hc2sq]
  have hnorm : (P *ᵥ indVec A) ⬝ᵥ (P *ᵥ indVec A) = ∑ k, μ k ^ 2 * s k ^ 2 := by
    rw [dotProduct_eq_sum_eigvec hP]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [eigvec_dotProduct_mulVec hP]
    ring
  have hrest : ∑ k ∈ Finset.univ.erase k₀, μ k ^ 2 * s k ^ 2 ≤
      lambdaG G r ^ 2 * (A.card - s k₀ ^ 2) := by
    have hsum : ∑ k ∈ Finset.univ.erase k₀, s k ^ 2 = A.card - s k₀ ^ 2 := by
      have h := Finset.sum_erase_add Finset.univ (fun k => s k ^ 2) (Finset.mem_univ k₀)
      rw [hS2] at h
      linarith
    calc ∑ k ∈ Finset.univ.erase k₀, μ k ^ 2 * s k ^ 2
        ≤ ∑ k ∈ Finset.univ.erase k₀, lambdaG G r ^ 2 * s k ^ 2 := by
          refine Finset.sum_le_sum fun k hk => ?_
          exact mul_le_mul_of_nonneg_right (by
            have habs := hsmall k (Finset.ne_of_mem_erase hk)
            have : |μ k| ^ 2 ≤ lambdaG G r ^ 2 :=
              pow_le_pow_left₀ (abs_nonneg _) habs 2
            simpa [sq_abs] using this) (sq_nonneg _)
      _ = lambdaG G r ^ 2 * ∑ k ∈ Finset.univ.erase k₀, s k ^ 2 := by
          rw [Finset.mul_sum]
      _ = lambdaG G r ^ 2 * (A.card - s k₀ ^ 2) := by rw [hsum]
  have hsplit :=
    Finset.sum_erase_add Finset.univ (fun k => μ k ^ 2 * s k ^ 2) (Finset.mem_univ k₀)
  rw [hnorm, ← hsplit, hμ0]
  have htop : (1 : ℝ) ^ 2 * s k₀ ^ 2 = (A.card : ℝ) ^ 2 / Fintype.card V := by
    simp [hs0]
  calc ∑ k ∈ Finset.univ.erase k₀, μ k ^ 2 * s k ^ 2 + (1 : ℝ) ^ 2 * s k₀ ^ 2
      ≤ lambdaG G r ^ 2 * (A.card - s k₀ ^ 2) + (A.card : ℝ) ^ 2 / Fintype.card V := by
        linarith [hrest, htop]
    _ = lambdaG G r ^ 2 * A.card + (1 - lambdaG G r ^ 2) * A.card ^ 2 / Fintype.card V := by
        rw [hs0]
        field_simp
        ring

/-- **Spectral core of Lemma 1** (Section 3, inequality (7)): on an `r`-regular graph with
`r > 0`, for every set `A`,
`∑ₓ P(x, A)² = ‖P 1_A‖² ≤ λ² |A| + (1 - λ²) |A|² / n`, where `P(x, A) = d_A(x) / r`.
Proof idea: expand `1_A` in an orthonormal eigenbasis of `P`; the top eigenvector is the constant
vector `1/√n` (coefficient `|A| / √n`) and every other eigenvalue has square `≤ λ²`. If `λ ≥ 1`
the bound follows from `P(x, A) ≤ 1` and `∑ₓ P(x, A) = |A|`. -/
theorem sum_sq_neighbor_le {r : ℕ} (hreg : G.IsRegularOfDegree r) (hr : 0 < r)
    (A : Finset V) :
    ∑ x, (((G.neighborFinset x ∩ A).card : ℝ) / r) ^ 2 ≤
      lambdaG G r ^ 2 * A.card + (1 - lambdaG G r ^ 2) * A.card ^ 2 / Fintype.card V := by
  rw [sum_sq_neighbor_eq_dotProduct]
  by_cases hL : lambdaG G r < 1
  · exact norm_sq_indVec_le_of_lambda_lt hreg hr hL A
  · push Not at hL
    rcases isEmpty_or_nonempty V with hV | hV
    · haveI := hV
      have hA : A = ∅ := Finset.eq_empty_of_isEmpty A
      simp [hA, dotProduct, lambdaG, Fintype.card_eq_zero]
    · have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
      have hfrac (x : V) :
          0 ≤ ((G.neighborFinset x ∩ A).card : ℝ) / r ∧
            ((G.neighborFinset x ∩ A).card : ℝ) / r ≤ 1 := by
        have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
        have hle : (G.neighborFinset x ∩ A).card ≤ r := by
          rw [← hreg x, ← G.card_neighborFinset_eq_degree]
          exact Finset.card_le_card Finset.inter_subset_left
        constructor
        · positivity
        · rw [div_le_one hr0]
          exact_mod_cast hle
      have hsq : ∑ x, (((G.neighborFinset x ∩ A).card : ℝ) / r) ^ 2 ≤
          ∑ x, ((G.neighborFinset x ∩ A).card : ℝ) / r := by
        refine Finset.sum_le_sum fun x _ => ?_
        have h0 := (hfrac x).1
        have h1 := (hfrac x).2
        rw [sq]
        exact mul_le_of_le_one_left h0 h1
      have hsum : ∑ x, ((G.neighborFinset x ∩ A).card : ℝ) / r = A.card := by
        rw [← Finset.sum_div, ← Nat.cast_sum, sum_neighborCard_eq hreg, Nat.cast_mul,
          mul_div_cancel_left₀]
        exact_mod_cast hr.ne'
      have hcard : (A.card : ℝ) ≤ Fintype.card V := by exact_mod_cast Finset.card_le_univ A
      have hgap : 0 ≤ (A.card : ℝ) - A.card ^ 2 / Fintype.card V := by
        rw [sub_nonneg, div_le_iff₀ hn]
        nlinarith [sq_nonneg ((A.card : ℝ) - Fintype.card V)]
      have hlam2 : 1 ≤ lambdaG G r ^ 2 := by nlinarith [sq_nonneg (lambdaG G r)]
      have hRHS : (A.card : ℝ) ≤ lambdaG G r ^ 2 * A.card +
          (1 - lambdaG G r ^ 2) * A.card ^ 2 / Fintype.card V := by
        have hkey : lambdaG G r ^ 2 * (A.card : ℝ) +
            (1 - lambdaG G r ^ 2) * A.card ^ 2 / Fintype.card V - A.card =
            (lambdaG G r ^ 2 - 1) * (A.card - A.card ^ 2 / Fintype.card V) := by
          field_simp
          ring
        have hnn : 0 ≤ (lambdaG G r ^ 2 - 1) * (A.card - A.card ^ 2 / Fintype.card V) :=
          mul_nonneg (by linarith) hgap
        linarith
      calc (transitionMatrix G r *ᵥ indVec A) ⬝ᵥ (transitionMatrix G r *ᵥ indVec A)
          = ∑ x, (((G.neighborFinset x ∩ A).card : ℝ) / r) ^ 2 :=
            (sum_sq_neighbor_eq_dotProduct A).symm
        _ ≤ ∑ x, ((G.neighborFinset x ∩ A).card : ℝ) / r := hsq
        _ = A.card := hsum
        _ ≤ _ := hRHS

end Epidemics
