import Averaging.RateMatrix
import Averaging.RateSpectral

/-! # Theorem 33: the rate bound

Proof of Theorem 33 of the Survey (Lovász 1993, Theorem 5.1) for a graph without isolated nodes.
The vector `s = √π` is a unit eigenvector of `N = D^{-1/2} A D^{-1/2}` for the eigenvalue `1`;
the quadratic form of `N` is bounded by the squared norm (`|ab| ≤ (a² + b²)/2` on every edge),
so every eigenvalue has `|μ| ≤ 1`; by the sorting of `eigenvalues₀`, at most one eigenvalue (the
largest) has `|μ| > λ`. The spectral lemmas of `Averaging.RateSpectral` then give
`|Nᵗ(u, v) - s(u) s(v)| ≤ λᵗ`, and `Pᵗ = D^{-1/2} Nᵗ D^{1/2}` turns this into
`|Pᵗ(u, v) - π(v)| ≤ √(d(v)/d(u)) λᵗ`.
-/

namespace Averaging
open Finset Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The vector `s = √π`, a unit eigenvector of `N` for the eigenvalue `1`. -/
noncomputable def sqrtStationary (v : V) : ℝ := √(walkStationary G v)

omit [DecidableEq V] in
/-- A graph without isolated nodes on a nonempty vertex type has an edge. -/
lemma card_edgeFinset_pos (hdeg : ∀ v, 0 < G.degree v) [Nonempty V] : 0 < #G.edgeFinset := by
  obtain ⟨v⟩ := ‹Nonempty V›
  have h := G.sum_degrees_eq_twice_card_edges
  have : 0 < ∑ w, G.degree w := Finset.sum_pos' (fun w _ => Nat.zero_le _) ⟨v, mem_univ v, hdeg v⟩
  omega

omit [DecidableEq V] in
/-- A graph without isolated nodes on a nonempty vertex type has at least two nodes. -/
lemma two_le_card (hdeg : ∀ v, 0 < G.degree v) [Nonempty V] : 2 ≤ Fintype.card V := by
  obtain ⟨v⟩ := ‹Nonempty V›
  obtain ⟨w, hw⟩ := (G.degree_pos_iff_exists_adj v).mp (hdeg v)
  exact Fintype.one_lt_card_iff.2 ⟨v, w, hw.ne⟩

omit [DecidableEq V] in
/-- `π` is a probability vector. -/
lemma sum_walkStationary (hdeg : ∀ v, 0 < G.degree v) [Nonempty V] :
    ∑ v, walkStationary G v = 1 := by
  simp only [walkStationary, ← sum_div]
  rw [← Nat.cast_sum, G.sum_degrees_eq_twice_card_edges]
  have := card_edgeFinset_pos G hdeg
  push_cast
  exact div_self (by positivity)

omit [DecidableEq V] in
lemma walkStationary_nonneg (v : V) : 0 ≤ walkStationary G v := by
  unfold walkStationary
  positivity

omit [DecidableEq V] in
/-- `s = √π` is a unit vector. -/
lemma sqrtStationary_dotProduct_self (hdeg : ∀ v, 0 < G.degree v) [Nonempty V] :
    sqrtStationary G ⬝ᵥ sqrtStationary G = 1 := by
  simp only [dotProduct, sqrtStationary, Real.mul_self_sqrt (walkStationary_nonneg G _)]
  exact sum_walkStationary G hdeg

omit [DecidableEq V] in
lemma sqrtStationary_eq (v : V) :
    sqrtStationary G v = √(G.degree v : ℝ) / √(2 * (#G.edgeFinset : ℝ)) := by
  rw [sqrtStationary, walkStationary, Real.sqrt_div' _ (by positivity)]

/-- `N s = s`. -/
lemma normAdjMatrix_mulVec_sqrtStationary (hdeg : ∀ v, 0 < G.degree v) :
    normAdjMatrix G *ᵥ sqrtStationary G = sqrtStationary G := by
  funext u
  have hterm (v : V) : normAdjMatrix G u v * sqrtStationary G v =
      if G.Adj u v then (√(G.degree u : ℝ))⁻¹ * (√(2 * (#G.edgeFinset : ℝ)))⁻¹ else 0 := by
    rw [normAdjMatrix_apply, sqrtStationary_eq]
    split_ifs
    · have hv : √(G.degree v : ℝ) ≠ 0 := Real.sqrt_ne_zero'.2 (by exact_mod_cast hdeg v)
      field_simp
    · simp
  simp only [mulVec, dotProduct, hterm]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
    ← SimpleGraph.neighborFinset_eq_filter, SimpleGraph.card_neighborFinset_eq_degree,
    sqrtStationary_eq]
  have hu : (0 : ℝ) < G.degree u := by exact_mod_cast hdeg u
  have hsu : √(G.degree u : ℝ) ≠ 0 := Real.sqrt_ne_zero'.2 hu
  field_simp
  rw [Real.sq_sqrt hu.le]

/-- On one edge: `|w(u) w(v)| / √(d(u) d(v)) ≤ (w(u)²/d(u) + w(v)²/d(v)) / 2`. -/
lemma abs_mul_normAdj_le (hdeg : ∀ v, 0 < G.degree v) (w : V → ℝ) (u v : V) :
    |w u * normAdjMatrix G u v * w v| ≤
      if G.Adj u v then (w u ^ 2 / G.degree u + w v ^ 2 / G.degree v) / 2 else 0 := by
  rw [normAdjMatrix_apply]
  split_ifs
  · have hu : (0 : ℝ) < G.degree u := by exact_mod_cast hdeg u
    have hv : (0 : ℝ) < G.degree v := by exact_mod_cast hdeg v
    set a := w u * (√(G.degree u : ℝ))⁻¹
    set b := w v * (√(G.degree v : ℝ))⁻¹
    have ha : a ^ 2 = w u ^ 2 / G.degree u := by
      rw [mul_pow, inv_pow, Real.sq_sqrt hu.le, div_eq_mul_inv]
    have hb : b ^ 2 = w v ^ 2 / G.degree v := by
      rw [mul_pow, inv_pow, Real.sq_sqrt hv.le, div_eq_mul_inv]
    have hab : w u * ((√(G.degree u : ℝ))⁻¹ * (√(G.degree v : ℝ))⁻¹) * w v = a * b := by ring
    rw [hab, ← ha, ← hb]
    exact abs_le.2 ⟨by nlinarith [sq_nonneg (a + b)], by nlinarith [sq_nonneg (a - b)]⟩
  · simp

/-- The quadratic form of `N` is bounded by the squared norm: `|w ⬝ N w| ≤ w ⬝ w`. -/
lemma abs_dotProduct_normAdjMatrix_mulVec_le (hdeg : ∀ v, 0 < G.degree v) (w : V → ℝ) :
    |w ⬝ᵥ (normAdjMatrix G *ᵥ w)| ≤ w ⬝ᵥ w := by
  have hexp : w ⬝ᵥ (normAdjMatrix G *ᵥ w) = ∑ u, ∑ v, w u * normAdjMatrix G u v * w v := by
    simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  have hrow (u : V) : ∑ v, (if G.Adj u v then (1 : ℝ) else 0) = G.degree u := by
    rw [Finset.sum_boole, ← SimpleGraph.card_neighborFinset_eq_degree,
      SimpleGraph.neighborFinset_eq_filter]
  have hsplit (u v : V) :
      (if G.Adj u v then (w u ^ 2 / G.degree u + w v ^ 2 / G.degree v) / 2 else 0) =
        (w u ^ 2 / G.degree u / 2) * (if G.Adj u v then 1 else 0) +
          (w v ^ 2 / G.degree v / 2) * (if G.Adj v u then 1 else 0) := by
    simp only [G.adj_comm v u]
    split_ifs <;> ring
  have hfirst : ∑ u, ∑ v, (w u ^ 2 / G.degree u / 2) * (if G.Adj u v then (1 : ℝ) else 0) =
      (∑ u, w u ^ 2) / 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.mul_sum, hrow]
    have hu : (G.degree u : ℝ) ≠ 0 := by exact_mod_cast (hdeg u).ne'
    field_simp
  have hsecond : ∑ u, ∑ v, (w v ^ 2 / G.degree v / 2) * (if G.Adj v u then (1 : ℝ) else 0) =
      (∑ u, w u ^ 2) / 2 := by
    rw [Finset.sum_comm]
    exact hfirst
  rw [hexp]
  calc |∑ u, ∑ v, w u * normAdjMatrix G u v * w v|
      ≤ ∑ u, ∑ v, |w u * normAdjMatrix G u v * w v| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun u _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ u, ∑ v,
          (if G.Adj u v then (w u ^ 2 / G.degree u + w v ^ 2 / G.degree v) / 2 else 0) :=
        Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => abs_mul_normAdj_le G hdeg w u v
    _ = w ⬝ᵥ w := by
        simp_rw [hsplit, Finset.sum_add_distrib]
        rw [hfirst, hsecond]
        simp only [dotProduct, sq]
        ring

/-- `λ ≥ 0`. -/
lemma walkLambda_nonneg : 0 ≤ walkLambda G := by
  unfold walkLambda
  split_ifs
  · exact le_max_of_le_left (abs_nonneg _)
  · exact le_rfl

/-- Every sorted eigenvalue but the largest is at most `λ` in absolute value. -/
lemma abs_eigenvalues₀_le_walkLambda (h2 : 2 ≤ Fintype.card V) (i : Fin (Fintype.card V))
    (hi : i ≠ ⟨0, by omega⟩) :
    |(normAdjMatrix_isHermitian G).eigenvalues₀ i| ≤ walkLambda G := by
  have hanti := (normAdjMatrix_isHermitian G).eigenvalues₀_antitone
  have hi1 : 1 ≤ i.val := by
    rcases Nat.eq_zero_or_pos i.val with h | h
    · exact absurd (Fin.ext h) hi
    · exact h
  rw [walkLambda, dif_pos h2, max_comm]
  refine abs_le_max_abs_abs (hanti ?_) (hanti ?_)
  · rw [Fin.le_iff_val_le_val]
    show i.val ≤ Fintype.card V - 1
    omega
  · exact Fin.le_iff_val_le_val.2 hi1

/-- At most one eigenvalue of `N` exceeds `λ` in absolute value. -/
lemma eq_of_walkLambda_lt_abs (hdeg : ∀ v, 0 < G.degree v) [Nonempty V] (k l : V)
    (hk : walkLambda G < |(normAdjMatrix_isHermitian G).eigenvalues k|)
    (hl : walkLambda G < |(normAdjMatrix_isHermitian G).eigenvalues l|) : k = l := by
  have h2 := two_le_card G hdeg
  set e := (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card V))).symm
  have hzero (j : V) (hj : walkLambda G < |(normAdjMatrix_isHermitian G).eigenvalues j|) :
      e j = ⟨0, by omega⟩ := by
    by_contra h
    exact absurd (abs_eigenvalues₀_le_walkLambda G h2 (e j) h) (not_le.mpr hj)
  exact e.injective ((hzero k hk).trans (hzero l hl).symm)

omit [DecidableEq V] in
/-- `π(v)` through `s = √π`: `π(v) = d(u)^{-1/2} s(u) s(v) d(v)^{1/2}`. -/
lemma walkStationary_eq_sqrt (hdeg : ∀ v, 0 < G.degree v) (u v : V) :
    walkStationary G v =
      (√(G.degree u : ℝ))⁻¹ * (sqrtStationary G u * sqrtStationary G v) *
        √(G.degree v : ℝ) := by
  have hu : (0 : ℝ) < G.degree u := by exact_mod_cast hdeg u
  have hv : (0 : ℝ) < G.degree v := by exact_mod_cast hdeg v
  haveI : Nonempty V := ⟨u⟩
  have hm : (0 : ℝ) < 2 * (#G.edgeFinset : ℝ) := by
    have := card_edgeFinset_pos G hdeg
    positivity
  rw [sqrtStationary_eq, sqrtStationary_eq, walkStationary]
  have hsu : √(G.degree u : ℝ) ≠ 0 := Real.sqrt_ne_zero'.2 hu
  have hsm : √(2 * (#G.edgeFinset : ℝ)) ≠ 0 := Real.sqrt_ne_zero'.2 hm
  have hm' : (#G.edgeFinset : ℝ) ≠ 0 := by
    have := card_edgeFinset_pos G hdeg
    positivity
  field_simp
  rw [Real.sq_sqrt hv.le, Real.sq_sqrt hm.le]
  field_simp

/-- **Theorem 33** (Survey; Lovász 1993, Theorem 5.1), for a graph without isolated nodes. -/
lemma abs_walkMatrix_pow_sub_walkStationary_le' (hdeg : ∀ v, 0 < G.degree v) (u v : V)
    (t : ℕ) :
    |(walkMatrix G ^ t) u v - walkStationary G v| ≤
      √((G.degree v : ℝ) / G.degree u) * walkLambda G ^ t := by
  haveI : Nonempty V := ⟨u⟩
  have hN := normAdjMatrix_isHermitian G
  have hs := normAdjMatrix_mulVec_sqrtStationary G hdeg
  have hs1 := sqrtStationary_dotProduct_self G hdeg
  have hcore := abs_pow_apply_sub_le hN (sqrtStationary G) hs hs1 (walkLambda_nonneg G)
    (fun y hy => mulVec_dotProduct_mulVec_le hN (sqrtStationary G) hs hs1
      (abs_eigenvalues_le_one hN (abs_dotProduct_normAdjMatrix_mulVec_le G hdeg))
      (eq_of_walkLambda_lt_abs G hdeg) y hy) t u v
  have hu : (0 : ℝ) < G.degree u := by exact_mod_cast hdeg u
  have hsu : √(G.degree u : ℝ) ≠ 0 := Real.sqrt_ne_zero'.2 hu
  rw [walkMatrix_pow_apply_eq G hdeg, walkStationary_eq_sqrt G hdeg u v]
  have hfac : (√(G.degree u : ℝ))⁻¹ * (normAdjMatrix G ^ t) u v * √(G.degree v : ℝ) -
      (√(G.degree u : ℝ))⁻¹ * (sqrtStationary G u * sqrtStationary G v) * √(G.degree v : ℝ) =
      √((G.degree v : ℝ) / G.degree u) *
        ((normAdjMatrix G ^ t) u v - sqrtStationary G u * sqrtStationary G v) := by
    rw [Real.sqrt_div' _ hu.le]
    field_simp
  rw [hfac, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left hcore (Real.sqrt_nonneg _)

end Averaging
