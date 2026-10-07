import Averaging.RateBound

/-! # Unless `G` is bipartite, `λ < 1`

The sentence after Theorem 33 of the Survey, for a connected graph with a closed walk of odd
length. An eigenvector `x` of `N = D^{-1/2} A D^{-1/2}` with eigenvalue `μ` gives the vector
`y = D^{-1/2} x` with `x⁽ᵗ⁾ = μᵗ y` under the averaging dynamics. By the convergence theorem
`tendsto_degAvg` of `Averaging.Basic`, `μ = -1` forces `y = 0`, and `μ = 1` forces `y` constant,
that is `x ∥ √d`. Hence `-1` is not an eigenvalue, `1` is a simple eigenvalue, and every sorted
eigenvalue but the largest has absolute value `< 1`.
-/

namespace Averaging
open Finset Matrix Filter Topology

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- An eigenvector `x` of `N` with eigenvalue `μ` gives `P (D^{-1/2} x) = μ D^{-1/2} x`. -/
lemma walkMatrix_mulVec_of_eigen (hdeg : ∀ v, 0 < G.degree v) (x : V → ℝ) (μ : ℝ)
    (hx : normAdjMatrix G *ᵥ x = μ • x) :
    walkMatrix G *ᵥ (diagonal (fun v => (√(G.degree v : ℝ))⁻¹) *ᵥ x) =
      μ • (diagonal (fun v => (√(G.degree v : ℝ))⁻¹) *ᵥ x) := by
  rw [walkMatrix_eq_conj G hdeg, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_mulVec x,
    diagonal_sqrt_mul_inv G hdeg, one_mulVec, hx, mulVec_smul]

/-- Under the averaging dynamics, `D^{-1/2} x` evolves as `μᵗ D^{-1/2} x`. -/
lemma avgIter_of_eigen (hdeg : ∀ v, 0 < G.degree v) (x : V → ℝ) (μ : ℝ)
    (hx : normAdjMatrix G *ᵥ x = μ • x) (t : ℕ) :
    avgIter G t (diagonal (fun v => (√(G.degree v : ℝ))⁻¹) *ᵥ x) =
      μ ^ t • (diagonal (fun v => (√(G.degree v : ℝ))⁻¹) *ᵥ x) := by
  rw [avgIter_eq_walkMatrix_pow_mulVec']
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, walkMatrix_mulVec_of_eigen G hdeg x μ hx,
      smul_smul, pow_succ, mul_comm]

/-- A sequence `(-1)ᵗ c` converges only if `c = 0`. -/
lemma eq_zero_of_tendsto_neg_one_pow {c L : ℝ}
    (h : Tendsto (fun t : ℕ => (-1 : ℝ) ^ t * c) atTop (𝓝 L)) : c = 0 := by
  have h1 : Tendsto (fun t : ℕ => (-1 : ℝ) ^ (t + 1) * c) atTop (𝓝 L) :=
    h.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun t : ℕ => (-1 : ℝ) ^ (t + 1) * c) atTop (𝓝 (-L)) := by
    have := h.neg
    refine this.congr fun t => ?_
    rw [pow_succ]
    ring
  have hL : L = 0 := by
    have := tendsto_nhds_unique h1 h2
    linarith
  have habs : Tendsto (fun t : ℕ => |(-1 : ℝ) ^ t * c|) atTop (𝓝 |L|) := h.abs
  have hconst : (fun t : ℕ => |(-1 : ℝ) ^ t * c|) = fun _ => |c| := by
    funext t
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [hconst, hL, abs_zero] at habs
  exact abs_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds habs)

/-- On a connected non-bipartite graph, `-1` is not an eigenvalue of `N`. -/
lemma eq_zero_of_eigen_neg_one (hc : G.Connected)
    (hodd : ∃ (u : V) (p : G.Walk u u), Odd p.length) (x : V → ℝ)
    (hx : normAdjMatrix G *ᵥ x = (-1 : ℝ) • x) : x = 0 := by
  have hdeg := degree_pos_of_connected_odd G hc hodd
  funext v
  have hlim := tendsto_degAvg G hc hodd (diagonal (fun v => (√(G.degree v : ℝ))⁻¹) *ᵥ x) v
  simp_rw [avgIter_of_eigen G hdeg x (-1) hx, Pi.smul_apply, smul_eq_mul] at hlim
  have h0 := eq_zero_of_tendsto_neg_one_pow hlim
  rw [mulVec_diagonal] at h0
  have hv : (√(G.degree v : ℝ))⁻¹ ≠ 0 :=
    inv_ne_zero (Real.sqrt_ne_zero'.2 (by exact_mod_cast hdeg v))
  exact (mul_eq_zero.mp h0).resolve_left hv

/-- On a connected non-bipartite graph, every eigenvector of `N` for the eigenvalue `1` is a
multiple of `√d`. -/
lemma eq_smul_sqrt_of_eigen_one (hc : G.Connected)
    (hodd : ∃ (u : V) (p : G.Walk u u), Odd p.length) (x : V → ℝ)
    (hx : normAdjMatrix G *ᵥ x = (1 : ℝ) • x) :
    ∃ c : ℝ, ∀ v, x v = c * √(G.degree v : ℝ) := by
  have hdeg := degree_pos_of_connected_odd G hc hodd
  have hav (t : ℕ) : avgIter G t (diagonal (fun v => (√(G.degree v : ℝ))⁻¹) *ᵥ x) =
      diagonal (fun v => (√(G.degree v : ℝ))⁻¹) *ᵥ x := by
    rw [avgIter_of_eigen G hdeg x 1 hx, one_pow, one_smul]
  refine ⟨degAvg G (diagonal (fun v => (√(G.degree v : ℝ))⁻¹) *ᵥ x), fun v => ?_⟩
  have hlim := tendsto_degAvg G hc hodd (diagonal (fun v => (√(G.degree v : ℝ))⁻¹) *ᵥ x) v
  simp_rw [hav] at hlim
  have hyv := tendsto_nhds_unique tendsto_const_nhds hlim
  have hy : (diagonal (fun v => (√(G.degree v : ℝ))⁻¹) *ᵥ x) v =
      (√(G.degree v : ℝ))⁻¹ * x v := by rw [mulVec_diagonal]
  have hsv : √(G.degree v : ℝ) ≠ 0 := Real.sqrt_ne_zero'.2 (by exact_mod_cast hdeg v)
  rw [← hyv, hy]
  field_simp

omit [DecidableEq V] in
/-- Two orthonormal vectors cannot both be multiples of `√d`. -/
lemma not_orthonormal_sqrt (hdeg : ∀ v, 0 < G.degree v) [Nonempty V] (x z : V → ℝ)
    (hxx : x ⬝ᵥ x = 1) (hzz : z ⬝ᵥ z = 1) (hxz : x ⬝ᵥ z = 0) (c c' : ℝ)
    (hx : ∀ v, x v = c * √(G.degree v : ℝ)) (hz : ∀ v, z v = c' * √(G.degree v : ℝ)) :
    False := by
  have hsq (v : V) : √(G.degree v : ℝ) * √(G.degree v : ℝ) = G.degree v :=
    Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hS : (0 : ℝ) < ∑ v, (G.degree v : ℝ) := by
    obtain ⟨v⟩ := ‹Nonempty V›
    exact Finset.sum_pos' (fun w _ => Nat.cast_nonneg _) ⟨v, mem_univ v, by exact_mod_cast hdeg v⟩
  have hform (a b : ℝ) (f g : V → ℝ) (hf : ∀ v, f v = a * √(G.degree v : ℝ))
      (hg : ∀ v, g v = b * √(G.degree v : ℝ)) : f ⬝ᵥ g = a * b * ∑ v, (G.degree v : ℝ) := by
    simp only [dotProduct, hf, hg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [mul_mul_mul_comm, hsq v]
  rw [hform c c x x hx hx] at hxx
  rw [hform c' c' z z hz hz] at hzz
  rw [hform c c' x z hx hz] at hxz
  have hc : c ≠ 0 := by rintro rfl; simp at hxx
  have hc' : c' ≠ 0 := by rintro rfl; simp at hzz
  exact (mul_ne_zero (mul_ne_zero hc hc') hS.ne') hxz

/-- On a connected non-bipartite graph, every sorted eigenvalue of `N` but the largest has
absolute value `< 1`. -/
lemma abs_eigenvalues₀_lt_one (hc : G.Connected)
    (hodd : ∃ (u : V) (p : G.Walk u u), Odd p.length) (i : Fin (Fintype.card V))
    (hi : (0 : ℕ) < i.val) :
    |(normAdjMatrix_isHermitian G).eigenvalues₀ i| < 1 := by
  have hdeg := degree_pos_of_connected_odd G hc hodd
  haveI : Nonempty V := hc.nonempty
  have hN := normAdjMatrix_isHermitian G
  have hle1 := abs_eigenvalues_le_one hN (abs_dotProduct_normAdjMatrix_mulVec_le G hdeg)
  set e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card V))
  have heig (j : Fin (Fintype.card V)) : hN.eigenvalues (e j) = hN.eigenvalues₀ j := by
    simp [IsHermitian.eigenvalues, e]
  have hle (j : Fin (Fintype.card V)) : |hN.eigenvalues₀ j| ≤ 1 := by
    rw [← heig]
    exact hle1 _
  refine lt_of_le_of_ne (hle i) fun h1 => ?_
  have hvec (j : Fin (Fintype.card V)) :
      normAdjMatrix G *ᵥ ⇑(hN.eigenvectorBasis (e j)) =
        hN.eigenvalues₀ j • ⇑(hN.eigenvectorBasis (e j)) := by
    rw [hN.mulVec_eigenvectorBasis, heig]
  have hunit (j : Fin (Fintype.card V)) :
      ⇑(hN.eigenvectorBasis (e j)) ⬝ᵥ ⇑(hN.eigenvectorBasis (e j)) = 1 := by
    rw [eigenvectorBasis_dotProduct, if_pos rfl]
  rcases abs_eq (zero_le_one' ℝ) |>.mp h1 with hpos | hneg
  · -- `λᵢ = 1`: then the largest eigenvalue is `1` as well, and `1` is not simple
    set i0 : Fin (Fintype.card V) := ⟨0, by omega⟩
    have h0 : hN.eigenvalues₀ i0 = 1 := by
      have hge : hN.eigenvalues₀ i ≤ hN.eigenvalues₀ i0 :=
        hN.eigenvalues₀_antitone (Fin.le_iff_val_le_val.2 (Nat.zero_le _))
      have := (abs_le.mp (hle i0)).2
      linarith
    have hne : e i ≠ e i0 := fun h => by
      have h' : i.val = 0 := congrArg Fin.val (e.injective h)
      omega
    obtain ⟨c, hcx⟩ := eq_smul_sqrt_of_eigen_one G hc hodd _ (by rw [hvec, hpos])
    obtain ⟨c', hcz⟩ := eq_smul_sqrt_of_eigen_one G hc hodd _ (by rw [hvec, h0])
    have horth := eigenvectorBasis_dotProduct hN (e i) (e i0)
    rw [if_neg hne] at horth
    exact not_orthonormal_sqrt G hdeg _ _ (hunit i) (hunit i0) horth c c' hcx hcz
  · -- `λᵢ = -1` is impossible
    have h0 := eq_zero_of_eigen_neg_one G hc hodd _ (by rw [hvec, hneg])
    have := hunit i
    rw [h0, zero_dotProduct] at this
    exact zero_ne_one this

/-- Unless `G` is bipartite, `λ < 1` (Survey, after Theorem 33). -/
lemma walkLambda_lt_one' (hc : G.Connected)
    (hodd : ∃ (u : V) (p : G.Walk u u), Odd p.length) : walkLambda G < 1 := by
  have hdeg := degree_pos_of_connected_odd G hc hodd
  haveI : Nonempty V := hc.nonempty
  have h2 := two_le_card G hdeg
  rw [walkLambda, dif_pos h2]
  exact max_lt (abs_eigenvalues₀_lt_one G hc hodd _ (by show 0 < 1; omega))
    (abs_eigenvalues₀_lt_one G hc hodd _ (by show 0 < Fintype.card V - 1; omega))

end Averaging
