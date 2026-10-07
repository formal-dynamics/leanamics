import Averaging.SequentialMatrix

/-! # Averaging in the random sequential model: the expected step matrix

Section 7.2 of Becchetti, Clementi, Natale, *Consensus Dynamics: An Overview*, SIGACT News
51(1), 2020 (the Survey), equations (2)–(5), after Boyd, Ghosh, Prabhakar, Shah, *Randomized
gossip algorithms*, IEEE Trans. Inf. Theory 52(6), 2006 (BGPS06).

One step on the edge `(i, j)` multiplies the state by `W = I - (e_i - e_j)(e_i - e_j)ᵀ / 2`
(equation (2)), a doubly stochastic symmetric projection. Equation (4) is the expectation of `W`
when a uniformly random node `i` contacts a node `j` drawn from row `i` of a stochastic matrix
`P` (the model of BGPS06): `𝔼[W] = I - D̄/(2n) + (P + Pᵀ)/(2n)`. In the Survey's random
sequential model one oriented edge is selected uniformly at random; then `𝔼[W] = I - L/(2m)`.
On a regular graph both read `(1 - 1/n) I + P/n` with `P = D⁻¹A` (equation (5)). Since
`WᵀW = W`, the second moment is `𝔼[WᵀW] = 𝔼[W]` (BGPS06), and since the steps are independent,
`𝔼[x⁽ᵗ⁾] = W̄ᵗ x⁽⁰⁾` (Survey, Section 7.3.2).
-/

namespace Averaging.Sequential
open Finset Matrix Dynamics

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- One step on the edge `(i, j)` replaces the values of both endpoints by their average and
leaves the other values unchanged (Survey, Section 7.2, before equation (2)). -/
theorem edgeMatrix_mulVec (i j : V) (x : V → ℝ) :
    edgeMatrix i j *ᵥ x = fun w => if w = i ∨ w = j then (x i + x j) / 2 else x w :=
  edgeMatrix_mulVec_eq i j x

/-- Each `W(t)` is doubly stochastic (Survey, Section 7.2, remark ii after equation (3)). -/
theorem edgeMatrix_mem_doublyStochastic (i j : V) : edgeMatrix i j ∈ doublyStochastic ℝ V := by
  refine mem_doublyStochastic.2 ⟨fun a b => ?_, ?_, ?_⟩
  · rw [edgeMatrix_apply]
    split_ifs <;> subst_vars <;> norm_num at *
  · rw [edgeMatrix_mulVec_eq]
    ext w
    split_ifs <;> simp
  · rw [← mulVec_transpose, edgeMatrix_transpose, edgeMatrix_mulVec_eq]
    ext w
    split_ifs <;> simp

/-- `W = I - (e_i - e_j)(e_i - e_j)ᵀ / 2` is a symmetric projection, `WᵀW = W` (BGPS06,
Section IV; the source of the second-moment identity). -/
theorem transpose_edgeMatrix_mul_self (i j : V) :
    (edgeMatrix i j)ᵀ * edgeMatrix i j = edgeMatrix i j := by
  rw [edgeMatrix_transpose, edgeMatrix_mul_self]

/-- **Equation (4)** (Survey; BGPS06). If a uniformly random node `i` selects the edge `(i, j)`
with `j` drawn from the kernel `K` (row `i` of the stochastic matrix `P`), the expected step
matrix is `𝔼[W] = I - D̄/(2n) + (P + Pᵀ)/(2n)`, `D̄ᵢᵢ = ∑ⱼ (Pᵢⱼ + Pⱼᵢ)`. Stated entrywise. -/
theorem avg_expect_edgeMatrix (K : Kernel V) (a b : V) :
    avg (fun i => (K i).expect fun j => edgeMatrix i j a b) = gossipMeanMatrix K a b := by
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos_iff.2 ⟨a⟩
  have h := sum_mul_edgeMatrix_apply (fun i j => (K i).weight j) a b
  simp only [(K _).sum_one, Finset.sum_const, card_univ, nsmul_eq_mul, mul_one] at h
  simp only [avg, Distribution.expect]
  rw [h]
  simp only [gossipMeanMatrix, kernelMatrix, Matrix.add_apply, Matrix.sub_apply, one_apply,
    Matrix.smul_apply, diagonal_apply, transpose_apply, of_apply, smul_eq_mul]
  by_cases hab : a = b
  · subst hab
    simp only [if_true]
    field_simp
    ring
  · simp only [hab, if_false]
    field_simp
    ring

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Equation (5)** (Survey). On a regular graph, equation (4) for the random walk `P = D⁻¹A`
(a uniformly random node contacts a uniformly random neighbour) reads
`𝔼[W] = (1 - 1/n) I + P / n`. -/
theorem gossipMeanMatrix_of_isRegular (K : Kernel V) (hK : kernelMatrix K = walkMatrix G)
    {d : ℕ} (hreg : G.IsRegularOfDegree d) :
    gossipMeanMatrix K =
      (1 - (Fintype.card V : ℝ)⁻¹) • (1 : Matrix V V ℝ) +
        (Fintype.card V : ℝ)⁻¹ • walkMatrix G := by
  have hsym (a b : V) : walkMatrix G b a = walkMatrix G a b := by
    rw [walkMatrix_apply, walkMatrix_apply, hreg.degree_eq a, hreg.degree_eq b]
    simp only [G.adj_comm b a]
  have hrow (a : V) : ∑ j, walkMatrix G a j = 1 := by
    rw [← hK]
    exact (K a).sum_one
  have hcol (a : V) : ∑ j, walkMatrix G j a = 1 := by simp_rw [hsym]; exact hrow a
  ext a b
  simp only [gossipMeanMatrix, hK, Matrix.add_apply, Matrix.sub_apply, one_apply,
    Matrix.smul_apply, diagonal_apply, transpose_apply, smul_eq_mul, Finset.sum_add_distrib,
    hrow, hcol, hsym a b]
  by_cases hab : a = b
  · subst hab
    simp only [if_true]
    ring
  · simp only [hab, if_false]
    ring

/-- The expected step matrix of the random sequential model (Survey, Section 7.2): if one
oriented edge is selected uniformly at random, `𝔼[W] = I - L / (2m)`. Stated entrywise. -/
theorem avg_edgeMatrix [Nonempty G.Dart] (a b : V) :
    avg (fun d : G.Dart => edgeMatrix d.fst d.snd a b) = meanMatrix G a b := by
  have hm : (0 : ℝ) < #G.edgeFinset := by
    have h := Fintype.card_pos (α := G.Dart)
    rw [G.dart_card_eq_twice_card_edges] at h
    exact_mod_cast (by omega : 0 < #G.edgeFinset)
  rw [avg, sum_dart_edgeMatrix_apply, G.dart_card_eq_twice_card_edges]
  simp only [meanMatrix, Matrix.sub_apply, one_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  field_simp

/-- **Equation (5)** for the random sequential model: on a `d`-regular graph with `d > 0`,
`I - L / (2m) = (1 - 1/n) I + P / n`. -/
theorem meanMatrix_of_isRegular {d : ℕ} (hreg : G.IsRegularOfDegree d) (hd : 0 < d) :
    meanMatrix G =
      (1 - (Fintype.card V : ℝ)⁻¹) • (1 : Matrix V V ℝ) +
        (Fintype.card V : ℝ)⁻¹ • walkMatrix G := by
  have h2m : 2 * (#G.edgeFinset : ℝ) = Fintype.card V * d := by
    have h := G.sum_degrees_eq_twice_card_edges
    simp only [hreg.degree_eq, Finset.sum_const, card_univ, smul_eq_mul] at h
    exact_mod_cast h.symm
  ext a b
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos_iff.2 ⟨a⟩
  simp only [meanMatrix, h2m, SimpleGraph.lapMatrix, SimpleGraph.degMatrix, walkMatrix,
    Matrix.sub_apply, Matrix.add_apply, one_apply, Matrix.smul_apply, diagonal_apply,
    diagonal_mul, SimpleGraph.adjMatrix_apply, hreg.degree_eq, smul_eq_mul]
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  by_cases hab : a = b
  · subst hab
    simp only [if_true, G.irrefl, if_false]
    field_simp
    ring
  · simp only [hab, if_false]
    split_ifs <;> field_simp <;> ring

/-- The second-moment identity `𝔼[WᵀW] = 𝔼[W] = I - L / (2m)` (BGPS06, Section IV) for a
uniformly random oriented edge. Stated entrywise. -/
theorem avg_transpose_edgeMatrix_mul_self [Nonempty G.Dart] (a b : V) :
    avg (fun d : G.Dart => ((edgeMatrix d.fst d.snd)ᵀ * edgeMatrix d.fst d.snd) a b) =
      meanMatrix G a b := by
  simp only [transpose_edgeMatrix_mul_self]
  exact avg_edgeMatrix G a b

/-- The second-moment identity on a state: `𝔼 ‖W x‖² = xᵀ W̄ x` for a uniformly random oriented
edge. -/
theorem avg_sum_sq_edgeMatrix_mulVec [Nonempty G.Dart] (x : V → ℝ) :
    avg (fun d : G.Dart => ∑ v, (edgeMatrix d.fst d.snd *ᵥ x) v ^ 2) =
      x ⬝ᵥ (meanMatrix G *ᵥ x) := by
  simp only [sum_sq_edgeMatrix_mulVec, dotProduct]
  rw [avg_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [avg_const_mul, avg_edgeMatrix_mulVec_apply G x c (avg_edgeMatrix G)]

/-- First-moment evolution (Survey, Section 7.3.2): over `t` independent uniformly random
oriented edges, `𝔼[x⁽ᵗ⁾] = W̄ᵗ x⁽⁰⁾`. -/
theorem expList_seqRun [Nonempty G.Dart] (x : V → ℝ) (t : ℕ) (v : V) :
    expList G.Dart t (fun l => seqRun G x l v) = (meanMatrix G ^ t *ᵥ x) v := by
  induction t generalizing x with
  | zero => simp [seqRun]
  | succ t ih =>
    rw [expList_succ]
    simp only [seqRun, List.foldl_cons]
    have hstep (d : G.Dart) :
        expList G.Dart t (fun l => (l.foldl (fun y d => edgeMatrix d.fst d.snd *ᵥ y)
          (edgeMatrix d.fst d.snd *ᵥ x)) v) =
          (meanMatrix G ^ t *ᵥ (edgeMatrix d.fst d.snd *ᵥ x)) v :=
      ih (edgeMatrix d.fst d.snd *ᵥ x)
    simp_rw [hstep]
    rw [pow_succ, ← mulVec_mulVec]
    show avg (fun d : G.Dart => ∑ c, (meanMatrix G ^ t) v c * (edgeMatrix d.fst d.snd *ᵥ x) c) =
      ∑ c, (meanMatrix G ^ t) v c * (meanMatrix G *ᵥ x) c
    rw [avg_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [avg_const_mul, avg_edgeMatrix_mulVec_apply G x c (avg_edgeMatrix G)]

end Averaging.Sequential
