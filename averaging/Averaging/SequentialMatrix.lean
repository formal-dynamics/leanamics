import Averaging.SequentialDefs
import Averaging.RateMatrix

/-! # The step matrix of sequential averaging: entries and weighted sums

Helpers for `Averaging.Sequential`: the entries of `W(i, j) = I - (eᵢ - eⱼ)(eᵢ - eⱼ)ᵀ / 2`
(Survey, equation (2)), its action on a state, its symmetry and idempotence, the weighted sum
`∑ᵢⱼ Qᵢⱼ W(i, j)` for an arbitrary weight matrix `Q` (the common computation behind equation (4)
and the uniform-edge identity), and sums over the darts of a graph as sums over adjacent pairs.
-/

namespace Averaging.Sequential
open Finset Matrix Dynamics

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- The entries of `W(i, j)`: `δₐᵦ - (δₐᵢ - δₐⱼ)(δᵦᵢ - δᵦⱼ) / 2`. -/
lemma edgeMatrix_apply (i j a b : V) :
    edgeMatrix i j a b = (if a = b then 1 else 0) -
      ((if a = i then 1 else 0) - (if a = j then 1 else 0)) *
        ((if b = i then 1 else 0) - (if b = j then 1 else 0)) / 2 := by
  simp only [edgeMatrix, Matrix.sub_apply, one_apply, Matrix.smul_apply, vecMulVec_apply,
    Pi.sub_apply, Pi.single_apply, smul_eq_mul]
  ring

omit [Fintype V] in
/-- `W(i, j)` is symmetric. -/
lemma edgeMatrix_transpose (i j : V) : (edgeMatrix i j)ᵀ = edgeMatrix i j := by
  ext a b
  simp only [transpose_apply, edgeMatrix_apply]
  by_cases h : a = b
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]
    ring

/-- One step on the edge `(i, j)` averages the values of the two endpoints. -/
lemma edgeMatrix_mulVec_eq (i j : V) (x : V → ℝ) :
    edgeMatrix i j *ᵥ x = fun w => if w = i ∨ w = j then (x i + x j) / 2 else x w := by
  ext w
  simp only [edgeMatrix, sub_mulVec, one_mulVec, smul_mulVec, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [vecMulVec_mulVec]
  simp only [Pi.smul_apply, sub_dotProduct, single_one_dotProduct, Pi.sub_apply,
    Pi.single_apply]
  by_cases hi : w = i <;> by_cases hj : w = j <;> subst_vars <;> simp_all <;> ring

/-- Averaging the same edge twice is averaging it once. -/
lemma edgeMatrix_mulVec_mulVec (i j : V) (x : V → ℝ) :
    edgeMatrix i j *ᵥ (edgeMatrix i j *ᵥ x) = edgeMatrix i j *ᵥ x := by
  simp only [edgeMatrix_mulVec_eq]
  ext w
  by_cases h : w = i ∨ w = j
  · simp only [h, if_true, true_or, or_true]
    ring
  · simp only [h, if_false]

/-- `W(i, j)` is idempotent. -/
lemma edgeMatrix_mul_self (i j : V) : edgeMatrix i j * edgeMatrix i j = edgeMatrix i j := by
  refine ext_of_mulVec_single fun k => ?_
  rw [← mulVec_mulVec, edgeMatrix_mulVec_mulVec]

lemma sum_sum_ite_left_left (Q : V → V → ℝ) (a b : V) :
    ∑ i, ∑ j, (if a = i then Q i j else 0) * (if b = i then 1 else 0) =
      (if a = b then 1 else 0) * ∑ j, Q a j := by
  rw [Finset.sum_eq_single a (fun i _ hi => by simp [Ne.symm hi]) (by simp)]
  simp only [if_true, ← Finset.sum_mul, mul_comm]
  by_cases h : a = b <;> simp [h, eq_comm]

lemma sum_sum_ite_left_right (Q : V → V → ℝ) (a b : V) :
    ∑ i, ∑ j, (if a = i then Q i j else 0) * (if b = j then 1 else 0) = Q a b := by
  rw [Finset.sum_eq_single a (fun i _ hi => by simp [Ne.symm hi]) (by simp)]
  simp

lemma sum_sum_ite_right_left (Q : V → V → ℝ) (a b : V) :
    ∑ i, ∑ j, (if a = j then Q i j else 0) * (if b = i then 1 else 0) = Q b a := by
  rw [Finset.sum_comm, Finset.sum_eq_single a (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
  simp

lemma sum_sum_ite_right_right (Q : V → V → ℝ) (a b : V) :
    ∑ i, ∑ j, (if a = j then Q i j else 0) * (if b = j then 1 else 0) =
      (if a = b then 1 else 0) * ∑ i, Q i a := by
  rw [Finset.sum_comm, Finset.sum_eq_single a (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
  simp only [if_true, ← Finset.sum_mul, mul_comm]
  by_cases h : a = b <;> simp [h, eq_comm]

/-- The weighted sum `∑ᵢⱼ Qᵢⱼ W(i, j)`, entrywise: the total weight times `I`, minus half of
`D̄ - Q - Qᵀ` with `D̄ₐₐ = ∑ⱼ (Qₐⱼ + Qⱼₐ)`. -/
lemma sum_mul_edgeMatrix_apply (Q : V → V → ℝ) (a b : V) :
    ∑ i, ∑ j, Q i j * edgeMatrix i j a b =
      (∑ i, ∑ j, Q i j) * (if a = b then 1 else 0) -
        ((if a = b then 1 else 0) * ∑ j, (Q a j + Q j a) - Q a b - Q b a) / 2 := by
  have hexp (i j : V) : Q i j * edgeMatrix i j a b =
      Q i j * (if a = b then 1 else 0) -
        ((if a = i then Q i j else 0) * (if b = i then 1 else 0) -
          (if a = i then Q i j else 0) * (if b = j then 1 else 0) -
          (if a = j then Q i j else 0) * (if b = i then 1 else 0) +
          (if a = j then Q i j else 0) * (if b = j then 1 else 0)) / 2 := by
    rw [edgeMatrix_apply]
    split_ifs <;> ring
  simp only [hexp, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_div]
  rw [sum_sum_ite_left_left, sum_sum_ite_left_right, sum_sum_ite_right_left,
    sum_sum_ite_right_right]
  simp only [← Finset.sum_mul]
  ring

variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
/-- The darts of `G` are the adjacent ordered pairs. -/
def dartEquiv : G.Dart ≃ {p : V × V // G.Adj p.1 p.2} where
  toFun d := ⟨d.toProd, d.adj⟩
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [DecidableEq V] in
/-- A sum over the darts of `G` is a sum over the adjacent ordered pairs. -/
lemma sum_dart (f : V → V → ℝ) :
    ∑ d : G.Dart, f d.fst d.snd = ∑ a, ∑ b, if G.Adj a b then f a b else 0 := by
  rw [← Fintype.sum_prod_type' (f := fun a b => if G.Adj a b then f a b else 0),
    ← Finset.sum_filter,
    Finset.sum_subtype (p := fun p : V × V => G.Adj p.1 p.2) _ (by simp)]
  exact Fintype.sum_equiv (dartEquiv G) _ _ fun _ => rfl

/-- `∑_{darts} W(d)`, entrywise: `2m I - L`. -/
lemma sum_dart_edgeMatrix_apply (a b : V) :
    ∑ d : G.Dart, edgeMatrix d.fst d.snd a b =
      2 * (#G.edgeFinset : ℝ) * (if a = b then 1 else 0) - G.lapMatrix ℝ a b := by
  have h := sum_mul_edgeMatrix_apply (G.adjMatrix ℝ) a b
  simp only [SimpleGraph.adjMatrix_apply, ite_mul, one_mul, zero_mul] at h
  rw [show ∑ d : G.Dart, edgeMatrix d.fst d.snd a b =
      ∑ i, ∑ j, if G.Adj i j then edgeMatrix i j a b else 0 from
    sum_dart G (fun i j => edgeMatrix i j a b), h]
  have hrow (v : V) : ∑ j, (if G.Adj v j then (1 : ℝ) else 0) = G.degree v := by
    rw [Finset.sum_boole, ← SimpleGraph.card_neighborFinset_eq_degree,
      SimpleGraph.neighborFinset_eq_filter]
  have hcol (v : V) : ∑ j, (if G.Adj j v then (1 : ℝ) else 0) = G.degree v := by
    simp_rw [G.adj_comm _ v]
    exact hrow v
  have htot : ∑ i, ∑ j, (if G.Adj i j then (1 : ℝ) else 0) = 2 * (#G.edgeFinset : ℝ) := by
    simp_rw [hrow]
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  rw [htot, Finset.sum_add_distrib, hrow, hcol]
  simp only [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, Matrix.sub_apply, diagonal_apply,
    SimpleGraph.adjMatrix_apply]
  by_cases h : a = b
  · subst h
    simp
  · simp only [h, if_false, G.adj_comm b a]
    split_ifs <;> ring

/-- The squared norm after one step is the quadratic form of `W`: `‖W x‖² = xᵀ W x`, since
`W` is a symmetric projection. -/
lemma sum_sq_edgeMatrix_mulVec (i j : V) (x : V → ℝ) :
    ∑ v, (edgeMatrix i j *ᵥ x) v ^ 2 = x ⬝ᵥ (edgeMatrix i j *ᵥ x) := by
  rw [← edgeMatrix_mulVec_mulVec i j x, dotProduct_mulVec, ← edgeMatrix_transpose i j,
    vecMul_transpose, edgeMatrix_transpose, edgeMatrix_mulVec_mulVec]
  simp only [dotProduct, sq]

/-- The average of `W(d) x` over a uniformly random dart is `(I - L/(2m)) x`. -/
lemma avg_edgeMatrix_mulVec_apply [Nonempty G.Dart] (x : V → ℝ) (c : V)
    (hW : ∀ a b, avg (fun d : G.Dart => edgeMatrix d.fst d.snd a b) = meanMatrix G a b) :
    avg (fun d : G.Dart => (edgeMatrix d.fst d.snd *ᵥ x) c) = (meanMatrix G *ᵥ x) c := by
  simp only [mulVec, dotProduct]
  rw [avg_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp_rw [mul_comm _ (x b)]
  rw [avg_const_mul, hW]

end Averaging.Sequential
