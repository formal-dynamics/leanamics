import Dynamics.GraphRounds
import Averaging.OpportunisticModel
import Averaging.Sequential

/-! # Averaging whenever you meet: the expected matrix and the first moment

One round of the averaging process is `x⁽ᵗ⁾ = W_t x⁽ᵗ⁻¹⁾` with the random matrix `W_t` of
equation (1) of arXiv:1703.05045 (v3). Its expectation over a uniformly random edge is
`W̄ = I - L / (2m)` (equation (2), Observation A.2), `L = D - A` the Laplacian and `m` the number of
edges, a symmetric doubly stochastic matrix. Since the rounds are independent, the expected state
evolves linearly: `E[x⁽ᵗ⁾ | x⁽⁰⁾ = x] = W̄ᵗ x` (equation (15)). Since `W_t` is symmetric and
idempotent, the expected squared norm after one round is the quadratic form of `W̄` (the identity
behind Lemma C.1).

These are the matrices of the random sequential model of `Averaging.Sequential` (AVG-1):
`stepMatrix G d` is `Sequential.edgeMatrix d.fst d.snd`, `meanStepMatrix G` is
`Sequential.meanMatrix G`, and the averaging process `avgRun` is `Sequential.seqRun`
(`avgRun_eq_seqRun`), so the statements below are those of AVG-1.
-/

namespace Averaging.Opportunistic
open Finset Matrix Dynamics

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The random matrix `W_t` of one round on the active edge `{d.fst, d.snd}` (equation (1)):
`1/2` on the diagonal at the two endpoints and at the two entries of the active edge, `1` on the
rest of the diagonal, `0` elsewhere. It is `I - (e_u - e_v)(e_u - e_v)ᵀ / 2`, the step matrix
`Sequential.edgeMatrix` of AVG-1. -/
noncomputable abbrev stepMatrix (d : G.Dart) : Matrix V V ℝ := Sequential.edgeMatrix d.fst d.snd

/-- The expected matrix `W̄ = I - L / (2m)` of one round (equation (2)), where `L = D - A` is the
Laplacian of `G` and `m` its number of edges: `Sequential.meanMatrix` of AVG-1. -/
noncomputable abbrev meanStepMatrix : Matrix V V ℝ := Sequential.meanMatrix G

/-! ### One round as a matrix step -/

omit [DecidableEq V] in
lemma card_dart_eq : (Fintype.card G.Dart : ℝ) = 2 * #G.edgeFinset := by
  rw [G.dart_card_eq_twice_card_edges]; push_cast; ring

omit [DecidableRel G.Adj] in
/-- One round of averaging is the multiplication by AVG-1's step matrix `W_t`. -/
lemma edgeAvg_eq_mulVec (x : V → ℝ) (d : G.Dart) :
    edgeAvg G x d = Sequential.edgeMatrix d.fst d.snd *ᵥ x :=
  (Sequential.edgeMatrix_mulVec_eq d.fst d.snd x).symm

omit [DecidableRel G.Adj] in
/-- The averaging process is AVG-1's sequential averaging `x⁽ᵗ⁾ = W(t) ⋯ W(1) x⁽⁰⁾`. -/
lemma avgRun_eq_seqRun (x : V → ℝ) (l : List G.Dart) : avgRun G x l = Sequential.seqRun G x l := by
  unfold avgRun Sequential.seqRun
  congr 1
  funext y d
  exact edgeAvg_eq_mulVec G y d

omit [DecidableRel G.Adj] in
lemma sum_sq_edgeAvg (x : V → ℝ) (d : G.Dart) :
    ∑ v, edgeAvg G x d v ^ 2 = ∑ v, x v ^ 2 - (x d.fst - x d.snd) ^ 2 / 2 := by
  have hne : d.fst ≠ d.snd := d.adj.ne
  have h := Fintype.sum_eq_add d.fst d.snd hne (f := fun w => edgeAvg G x d w ^ 2 - x w ^ 2)
    (fun w hw => by simp [edgeAvg, hw.1, hw.2])
  rw [Finset.sum_sub_distrib] at h
  have hf : edgeAvg G x d d.fst = (x d.fst + x d.snd) / 2 := by simp [edgeAvg]
  have hs : edgeAvg G x d d.snd = (x d.fst + x d.snd) / 2 := by simp [edgeAvg]
  rw [hf, hs] at h
  linarith [show ((x d.fst + x d.snd) / 2) ^ 2 - x d.fst ^ 2 +
    (((x d.fst + x d.snd) / 2) ^ 2 - x d.snd ^ 2) = -(x d.fst - x d.snd) ^ 2 / 2 by ring]

lemma meanStepMatrix_mulVec (x : V → ℝ) (v : V) :
    (meanStepMatrix G *ᵥ x) v = x v - (2 * (#G.edgeFinset : ℝ))⁻¹ * (G.lapMatrix ℝ *ᵥ x) v := by
  simp [Sequential.meanMatrix, sub_mulVec, smul_mulVec]

lemma sum_dart_sq (x : V → ℝ) :
    ∑ d : G.Dart, (x d.fst - x d.snd) ^ 2 = 2 * (x ⬝ᵥ (G.lapMatrix ℝ *ᵥ x)) := by
  rw [sum_dart G (fun u v => (x u - x v) ^ 2), ← toLinearMap₂'_apply',
    SimpleGraph.lapMatrix_toLinearMap₂' ℝ G x]
  ring

/-! ### Main statements -/

section NoDec
omit [DecidableRel G.Adj]

/-- `W_t x` is one round of averaging on the active edge. -/
theorem stepMatrix_mulVec (d : G.Dart) (x : V → ℝ) : stepMatrix G d *ᵥ x = edgeAvg G x d :=
  (edgeAvg_eq_mulVec G x d).symm

section NoFin
omit [Fintype V]

/-- `W_t` is symmetric (proof of Lemma C.1). -/
theorem stepMatrix_isSymm (d : G.Dart) : (stepMatrix G d).IsSymm :=
  Sequential.edgeMatrix_transpose d.fst d.snd

end NoFin

/-- `W_t` is idempotent (proof of Lemma C.1). -/
theorem stepMatrix_mul_self (d : G.Dart) : stepMatrix G d * stepMatrix G d = stepMatrix G d :=
  Sequential.edgeMatrix_mul_self d.fst d.snd

end NoDec

/-- Observation A.2, equation (2): over a uniformly random edge, `E[W_t] = I - L / (2m)`. -/
theorem avg_stepMatrix [Nonempty G.Dart] (i j : V) :
    avg (fun d : G.Dart => stepMatrix G d i j) = meanStepMatrix G i j :=
  Sequential.avg_edgeMatrix G i j

/-- `W̄` is symmetric (Section 3). -/
theorem meanStepMatrix_isSymm : (meanStepMatrix G).IsSymm :=
  isSymm_one.sub ((G.isSymm_lapMatrix ℝ).smul _)

/-- `W̄` is doubly stochastic (Section 3). -/
theorem meanStepMatrix_mem_doublyStochastic : meanStepMatrix G ∈ doublyStochastic ℝ V := by
  have hrow : meanStepMatrix G *ᵥ 1 = 1 := by
    funext v
    rw [meanStepMatrix_mulVec, show (1 : V → ℝ) = fun _ => 1 from rfl,
      G.lapMatrix_mulVec_const_eq_zero]
    simp
  refine ⟨fun i j => ?_, hrow, ?_⟩
  · simp only [meanStepMatrix, Sequential.meanMatrix, SimpleGraph.lapMatrix,
      SimpleGraph.degMatrix, Matrix.sub_apply, Matrix.smul_apply, diagonal_apply,
      SimpleGraph.adjMatrix_apply, Matrix.one_apply, smul_eq_mul]
    by_cases h : i = j
    · subst h
      simp only [if_true, G.irrefl, if_false, sub_zero]
      rcases eq_or_ne (#G.edgeFinset : ℝ) 0 with h0 | h0
      · simp [h0]
      · have hdeg : (G.degree i : ℝ) ≤ #G.edgeFinset := by
          exact_mod_cast G.degree_le_card_edgeFinset i
        have hpos : (0 : ℝ) < #G.edgeFinset := lt_of_le_of_ne (by positivity) (Ne.symm h0)
        rw [sub_nonneg, inv_mul_le_iff₀ (by positivity)]
        linarith
    · simp only [h, if_false]
      split_ifs <;> simp
  · rw [← mulVec_transpose, meanStepMatrix_isSymm, hrow]

/-- Equation (2) applied to a state: the expected state after one round is `W̄ x`. -/
theorem avg_edgeAvg [Nonempty G.Dart] (x : V → ℝ) (v : V) :
    avg (fun d : G.Dart => edgeAvg G x d v) = (meanStepMatrix G *ᵥ x) v := by
  simp_rw [edgeAvg_eq_mulVec]
  exact Sequential.avg_edgeMatrix_mulVec_apply G x v (Sequential.avg_edgeMatrix G)

/-- First-moment evolution, equation (15): `E[x⁽ᵗ⁾ | x⁽⁰⁾ = x] = W̄ᵗ x` over `t` i.i.d. uniform
rounds. -/
theorem expList_avgRun [Nonempty G.Dart] (x : V → ℝ) (t : ℕ) (v : V) :
    expList G.Dart t (fun l => avgRun G x l v) = (meanStepMatrix G ^ t *ᵥ x) v := by
  simp_rw [avgRun_eq_seqRun]
  exact Sequential.expList_seqRun G x t v

/-- Second moment of one round (proof of Lemma C.1): `E‖W x‖² = xᵀ W̄ x`, since `W` is symmetric
and idempotent. -/
theorem avg_sum_sq_edgeAvg [Nonempty G.Dart] (x : V → ℝ) :
    avg (fun d : G.Dart => ∑ v, edgeAvg G x d v ^ 2) = x ⬝ᵥ (meanStepMatrix G *ᵥ x) := by
  simp_rw [edgeAvg_eq_mulVec]
  exact Sequential.avg_sum_sq_edgeMatrix_mulVec G x

end Averaging.Opportunistic
