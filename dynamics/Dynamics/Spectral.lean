import Mathlib

/-!
# Spectral toolkit: real symmetric matrices and the random walk on a regular graph

**The eigenbasis on plain vectors.** For a real symmetric matrix `A` on a finite type `V`,
Mathlib's orthonormal eigenbasis `bₖ = hA.eigenvectorBasis k` (eigenvalues `μₖ = hA.eigenvalues k`)
lives in `EuclideanSpace ℝ V`. Here its vectors are read as plain functions `V → ℝ` with the dot
product `⬝ᵥ`:

* orthonormality `bₖ ⬝ bₗ = δₖₗ` (`eigenvectorBasis_dotProduct`), the expansion
  `y = ∑ₖ (bₖ ⬝ y) bₖ` (`sum_dotProduct_smul_eigenvectorBasis`) and Parseval
  `y ⬝ z = ∑ₖ (bₖ ⬝ y)(bₖ ⬝ z)` (`dotProduct_eq_sum_eigenvectorBasis`);
* the coefficients of `Aᵗ z`: `bₖ ⬝ (Aᵗ z) = μₖᵗ (bₖ ⬝ z)` (`eigenvectorBasis_dotProduct_mulVec`,
  `eigenvectorBasis_dotProduct_pow_mulVec`) and the spectral expansion of the bilinear form
  `y ⬝ A z = ∑ₖ μₖ (bₖ ⬝ y)(bₖ ⬝ z)` (`dotProduct_mulVec_eq_sum_eigenvectorBasis`);
* orthogonality to eigenvectors of other eigenvalues
  (`eigenvectorBasis_dotProduct_eq_zero_of_mulVec_eq_smul`) and the spectral bound for powers
  `‖Aᵗ y‖² ≤ λ²ᵗ ‖y‖²` when `y` has no component along eigenvectors with `|μ| > λ`
  (`pow_mulVec_dotProduct_self_le`).

**The random walk on a `d`-regular graph.** `transitionMatrix G d = A / d`, its eigenvalues
`λ₁ ≥ λ₂ ≥ ⋯ ≥ λₙ` in non-increasing order (`walkEigenvalues`, read off Mathlib's sorted
`Matrix.IsHermitian.eigenvalues₀`) and `λ_G = max {λ₂, |λₙ|}` (`lambdaG`). Every eigenvalue other
than the top one has `|μ| ≤ λ_G` (`abs_eigenvalues_le_lambdaG`), and when `λ_G < 1` the top
eigenvector is the constant vector `±1/√n` with eigenvalue `1` (`exists_top_eigenvectorBasis`).
The indicator vector `1_S` of a set of vertices is `indVec S`.
-/

namespace Dynamics
open Finset Matrix

/-! ### The eigenbasis of a real symmetric matrix, on plain vectors -/

section Eigenbasis

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An eigenvector of `M` is an eigenvector of every power `Mᵗ`. -/
lemma pow_mulVec_of_mulVec_eq_smul {M : Matrix V V ℝ} {u : V → ℝ} {c : ℝ}
    (hu : M *ᵥ u = c • u) (t : ℕ) : (M ^ t) *ᵥ u = c ^ t • u := by
  induction t with
  | zero => simp
  | succ t ih => rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, hu, smul_smul, pow_succ]

variable {A : Matrix V V ℝ} (hA : A.IsHermitian)

/-- Orthonormality of the eigenbasis: `bₖ ⬝ bₗ = δₖₗ`. -/
lemma eigenvectorBasis_dotProduct (k l : V) :
    ⇑(hA.eigenvectorBasis k) ⬝ᵥ ⇑(hA.eigenvectorBasis l) = if k = l then 1 else 0 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2) k) l
  simpa [Matrix.mul_apply, one_apply, dotProduct] using h

/-- Expansion of a vector in the orthonormal eigenbasis: `y = ∑ₖ (bₖ ⬝ y) bₖ`. -/
lemma sum_dotProduct_smul_eigenvectorBasis (y : V → ℝ) :
    ∑ k, (⇑(hA.eigenvectorBasis k) ⬝ᵥ y) • ⇑(hA.eigenvectorBasis k) = y := by
  have h := congrArg WithLp.ofLp (hA.eigenvectorBasis.sum_repr' (WithLp.toLp 2 y))
  simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using h

/-- Parseval: `y ⬝ z = ∑ₖ (bₖ ⬝ y)(bₖ ⬝ z)`. -/
lemma dotProduct_eq_sum_eigenvectorBasis (y z : V → ℝ) :
    y ⬝ᵥ z = ∑ k, (⇑(hA.eigenvectorBasis k) ⬝ᵥ y) * (⇑(hA.eigenvectorBasis k) ⬝ᵥ z) := by
  conv_lhs => rw [← sum_dotProduct_smul_eigenvectorBasis hA y]
  rw [sum_dotProduct]
  simp [smul_dotProduct]

/-- The coefficients of `A z`: `bₖ ⬝ (A z) = μₖ (bₖ ⬝ z)`. -/
lemma eigenvectorBasis_dotProduct_mulVec (k : V) (z : V → ℝ) :
    ⇑(hA.eigenvectorBasis k) ⬝ᵥ (A *ᵥ z) =
      hA.eigenvalues k * (⇑(hA.eigenvectorBasis k) ⬝ᵥ z) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, ← conjTranspose_eq_transpose_of_trivial, hA.eq,
    hA.mulVec_eigenvectorBasis, smul_dotProduct, smul_eq_mul]

/-- The eigenvectors of `A` are eigenvectors of `Aᵗ`: `Aᵗ bₖ = μₖᵗ bₖ`. -/
lemma pow_mulVec_eigenvectorBasis (t : ℕ) (k : V) :
    (A ^ t) *ᵥ ⇑(hA.eigenvectorBasis k) = hA.eigenvalues k ^ t • ⇑(hA.eigenvectorBasis k) :=
  pow_mulVec_of_mulVec_eq_smul (hA.mulVec_eigenvectorBasis k) t

/-- The coefficients of `Aᵗ z`: `bₖ ⬝ (Aᵗ z) = μₖᵗ (bₖ ⬝ z)`. -/
lemma eigenvectorBasis_dotProduct_pow_mulVec (t : ℕ) (k : V) (z : V → ℝ) :
    ⇑(hA.eigenvectorBasis k) ⬝ᵥ ((A ^ t) *ᵥ z) =
      hA.eigenvalues k ^ t * (⇑(hA.eigenvectorBasis k) ⬝ᵥ z) := by
  have hs : Aᵀ = A := IsSymm.eq hA
  have hT : (A ^ t)ᵀ = A ^ t := by rw [transpose_pow, hs]
  rw [dotProduct_mulVec, ← mulVec_transpose, hT, pow_mulVec_eigenvectorBasis, smul_dotProduct,
    smul_eq_mul]

/-- Spectral expansion of the bilinear form: `y ⬝ A z = ∑ₖ μₖ (bₖ ⬝ y)(bₖ ⬝ z)`. -/
lemma dotProduct_mulVec_eq_sum_eigenvectorBasis (y z : V → ℝ) :
    y ⬝ᵥ (A *ᵥ z) = ∑ k, hA.eigenvalues k *
      ((⇑(hA.eigenvectorBasis k) ⬝ᵥ y) * (⇑(hA.eigenvectorBasis k) ⬝ᵥ z)) := by
  rw [dotProduct_eq_sum_eigenvectorBasis hA]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [eigenvectorBasis_dotProduct_mulVec hA]
  ring

/-- Eigenvectors for distinct eigenvalues of a symmetric matrix are orthogonal: if `A u = c u`
and `μₖ ≠ c`, then `bₖ ⬝ u = 0`. -/
lemma eigenvectorBasis_dotProduct_eq_zero_of_mulVec_eq_smul {u : V → ℝ} {c : ℝ}
    (hu : A *ᵥ u = c • u) {k : V} (hk : hA.eigenvalues k ≠ c) :
    ⇑(hA.eigenvectorBasis k) ⬝ᵥ u = 0 := by
  have h := eigenvectorBasis_dotProduct_mulVec hA k u
  rw [hu, dotProduct_smul, smul_eq_mul] at h
  have h' : (c - hA.eigenvalues k) * (⇑(hA.eigenvectorBasis k) ⬝ᵥ u) = 0 := by linarith
  rcases mul_eq_zero.mp h' with h1 | h1
  · exact absurd (sub_eq_zero.mp h1).symm hk
  · exact h1

/-- **Spectral bound for powers.** If `y` has no component along the eigenvectors whose
eigenvalue exceeds `λ` in absolute value, then `‖Aᵗ y‖² ≤ λ²ᵗ ‖y‖²`. -/
lemma pow_mulVec_dotProduct_self_le {lam : ℝ} {y : V → ℝ}
    (hy : ∀ k, lam < |hA.eigenvalues k| → ⇑(hA.eigenvectorBasis k) ⬝ᵥ y = 0) (t : ℕ) :
    ((A ^ t) *ᵥ y) ⬝ᵥ ((A ^ t) *ᵥ y) ≤ (lam ^ t) ^ 2 * (y ⬝ᵥ y) := by
  rw [dotProduct_eq_sum_eigenvectorBasis hA, dotProduct_eq_sum_eigenvectorBasis hA y, mul_sum]
  refine sum_le_sum fun k _ => ?_
  rw [eigenvectorBasis_dotProduct_pow_mulVec]
  by_cases hk : lam < |hA.eigenvalues k|
  · simp [hy k hk]
  · have hle : |hA.eigenvalues k ^ t| ≤ lam ^ t := by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (not_lt.mp hk) t
    have hsq : (hA.eigenvalues k ^ t) ^ 2 ≤ (lam ^ t) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hle 2
    nlinarith [sq_nonneg (⇑(hA.eigenvectorBasis k) ⬝ᵥ y)]

end Eigenbasis

/-! ### The random walk on a regular graph -/

section RandomWalk

variable {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The transition matrix `P = A / d` of the random walk on a `d`-regular graph with adjacency
matrix `A`. -/
noncomputable def transitionMatrix (d : ℕ) : Matrix V V ℝ := (d : ℝ)⁻¹ • G.adjMatrix ℝ

/-- `P = A / d` is real symmetric. -/
theorem transitionMatrix_isHermitian (d : ℕ) : (transitionMatrix G d).IsHermitian :=
  (G.isHermitian_adjMatrix ℝ).smul (IsSelfAdjoint.all _)

variable [Fintype V] [DecidableEq V]

/-- The eigenvalues `λ₁ ≥ λ₂ ≥ ⋯ ≥ λₙ` of the transition matrix, in non-increasing order
(`Matrix.IsHermitian.eigenvalues₀_antitone`), indexed from `0`. -/
noncomputable def walkEigenvalues (d : ℕ) : Fin (Fintype.card V) → ℝ :=
  (transitionMatrix_isHermitian G d).eigenvalues₀

/-- `λ_G = max {λ₂, |λₙ|}` (set to `0` on graphs with fewer than two vertices). Since
`λₙ ≤ λ₂`, it is the largest absolute value `max_{i ≥ 2} |λᵢ|` of the eigenvalues other than
the top one. -/
noncomputable def lambdaG (d : ℕ) : ℝ :=
  if h : 2 ≤ Fintype.card V then
    max (walkEigenvalues G d ⟨1, by omega⟩) |walkEigenvalues G d ⟨Fintype.card V - 1, by omega⟩|
  else 0

/-- `λ_G ≥ 0`. -/
lemma lambdaG_nonneg (d : ℕ) : 0 ≤ lambdaG G d := by
  unfold lambdaG
  split_ifs
  · exact (abs_nonneg _).trans (le_max_right _ _)
  · exact le_rfl

omit [DecidableEq V] in
/-- `P 1 = 1` on a `d`-regular graph, `d > 0`: the transition matrix is stochastic. -/
lemma transitionMatrix_mulVec_one {d : ℕ} (hd : 0 < d) (hreg : G.IsRegularOfDegree d) :
    transitionMatrix G d *ᵥ 1 = 1 := by
  ext v
  rw [transitionMatrix, smul_mulVec, Pi.smul_apply, SimpleGraph.adjMatrix_mulVec_apply]
  simp only [Pi.one_apply, sum_const, G.card_neighborFinset_eq_degree, nsmul_eq_mul, mul_one,
    smul_eq_mul]
  rw [hreg v]
  exact inv_mul_cancel₀ (by exact_mod_cast hd.ne')

/-- Every eigenvalue of `P` other than the top one (index `0` in the sorted order) has absolute
value at most `λ_G`. -/
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

/-- **The top eigenvector.** On a `d`-regular graph with `d > 0` and `λ_G < 1`, the eigenvector
`b_{k₀}` at the top of the sorted spectrum of `P` has eigenvalue `1`, every other eigenvalue has
absolute value at most `λ_G`, and `b_{k₀} = ±1/√n` is constant, so that its coefficients satisfy
`(b_{k₀} ⬝ y)(b_{k₀} ⬝ z) = (∑ y)(∑ z) / n`. Proof: `P 1 = 1`, and every other eigenvector has an
eigenvalue `≤ λ_G < 1`, hence is orthogonal to `1`; Parseval does the rest. -/
lemma exists_top_eigenvectorBasis [Nonempty V] {d : ℕ} (hd : 0 < d)
    (hreg : G.IsRegularOfDegree d) (hL : lambdaG G d < 1) :
    ∃ k₀ : V, (transitionMatrix_isHermitian G d).eigenvalues k₀ = 1 ∧
      (∀ k, k ≠ k₀ → |(transitionMatrix_isHermitian G d).eigenvalues k| ≤ lambdaG G d) ∧
      ∀ y z : V → ℝ,
        (⇑((transitionMatrix_isHermitian G d).eigenvectorBasis k₀) ⬝ᵥ y) *
            (⇑((transitionMatrix_isHermitian G d).eigenvectorBasis k₀) ⬝ᵥ z) =
          (∑ v, y v) * (∑ v, z v) / Fintype.card V := by
  have hP := transitionMatrix_isHermitian G d
  have hn : 0 < Fintype.card V := Fintype.card_pos
  set k₀ : V := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card V)) ⟨0, hn⟩ with hk₀
  have hsmall : ∀ k, k ≠ k₀ → |hP.eigenvalues k| ≤ lambdaG G d := by
    intro k hk
    refine abs_eigenvalues_le_lambdaG G d k fun h => hk ?_
    rw [hk₀, ← h, Equiv.apply_symm_apply]
  have hP1 : transitionMatrix G d *ᵥ (1 : V → ℝ) = (1 : ℝ) • 1 := by
    rw [one_smul]
    exact transitionMatrix_mulVec_one G hd hreg
  -- the eigenvectors other than the top one are orthogonal to `1`
  have horth : ∀ k, k ≠ k₀ → ⇑(hP.eigenvectorBasis k) ⬝ᵥ 1 = 0 := by
    intro k hk
    refine eigenvectorBasis_dotProduct_eq_zero_of_mulVec_eq_smul hP hP1 fun h => ?_
    have := hsmall k hk
    rw [h, abs_one] at this
    linarith
  set c := ⇑(hP.eigenvectorBasis k₀) ⬝ᵥ 1 with hc
  -- `c (b_{k₀} ⬝ y) = ∑ y`
  have hcs (y : V → ℝ) : c * (⇑(hP.eigenvectorBasis k₀) ⬝ᵥ y) = ∑ v, y v := by
    rw [← one_dotProduct, dotProduct_eq_sum_eigenvectorBasis hP 1 y,
      Finset.sum_eq_single k₀ (fun k _ hk => by rw [horth k hk, zero_mul]) (by simp)]
  have hc2 : c * c = Fintype.card V := by
    have h := hcs 1
    simp only [Pi.one_apply, sum_const, card_univ, nsmul_eq_mul, mul_one] at h
    exact h
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, mul_zero] at hc2
    exact (Nat.cast_pos.mpr hn).ne' hc2.symm
  refine ⟨k₀, ?_, hsmall, fun y z => ?_⟩
  · have h := eigenvectorBasis_dotProduct_mulVec hP k₀ 1
    rw [transitionMatrix_mulVec_one G hd hreg, ← hc] at h
    have : (hP.eigenvalues k₀ - 1) * c = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · linarith
    · exact absurd h0 hc0
  · rw [← hcs y, ← hcs z, ← hc2]
    field_simp

/-! ### Indicator vectors -/

/-- The indicator vector `1_S` of a set of vertices. -/
def indVec (S : Finset V) : V → ℝ := fun v => if v ∈ S then 1 else 0

/-- `1_S ⬝ 1_S = |S|`. -/
lemma indVec_dotProduct_self (S : Finset V) : indVec S ⬝ᵥ indVec S = S.card := by
  simp only [dotProduct, indVec, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_mem, univ_inter]
  simp

/-- `∑ᵥ 1_S(v) = |S|`. -/
lemma sum_indVec (S : Finset V) : ∑ v, indVec S v = S.card := by
  simp [indVec]

end RandomWalk

end Dynamics
