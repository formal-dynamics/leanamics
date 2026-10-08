import Averaging.OpportunisticModel

/-! # Averaging whenever you meet: the expected matrix and the first moment

One round of the averaging process is `x⁽ᵗ⁾ = W_t x⁽ᵗ⁻¹⁾` with the random matrix `W_t` of
equation (1) of arXiv:1703.05045 (v3). Its expectation over a uniformly random edge is
`W̄ = I - L / (2m)` (equation (2), Observation A.2), `L = D - A` the Laplacian and `m` the number of
edges, a symmetric doubly stochastic matrix. Since the rounds are independent, the expected state
evolves linearly: `E[x⁽ᵗ⁾ | x⁽⁰⁾ = x] = W̄ᵗ x` (equation (15)). Since `W_t` is symmetric and
idempotent, the expected squared norm after one round is the quadratic form of `W̄` (the identity
behind Lemma C.1).
-/

namespace Averaging.Opportunistic
open Finset Matrix Dynamics

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The random matrix `W_t` of one round on the active edge `{d.fst, d.snd}` (equation (1)):
`1/2` on the diagonal at the two endpoints and at the two entries of the active edge, `1` on the
rest of the diagonal, `0` elsewhere. -/
noncomputable def stepMatrix (d : G.Dart) : Matrix V V ℝ := fun i j =>
  if i = j then (if i = d.fst ∨ i = d.snd then 1 / 2 else 1)
  else if s(i, j) = d.edge then 1 / 2 else 0

/-- The expected matrix `W̄ = I - L / (2m)` of one round (equation (2)), where `L = D - A` is the
Laplacian of `G` and `m` its number of edges. -/
noncomputable def meanStepMatrix : Matrix V V ℝ :=
  1 - (2 * (#G.edgeFinset : ℝ))⁻¹ • G.lapMatrix ℝ

/-! ### Sums over darts -/

omit [DecidableEq V] in
/-- A sum over the darts is a double sum over the ordered adjacent pairs. -/
lemma sum_dart (f : V → V → ℝ) :
    ∑ d : G.Dart, f d.fst d.snd = ∑ u, ∑ v, if G.Adj u v then f u v else 0 := by
  rw [← Fintype.sum_prod_type' (f := fun u v => if G.Adj u v then f u v else 0),
    ← Finset.sum_filter]
  refine Finset.sum_bij (fun d _ => d.toProd) (fun d _ => by simp [d.adj])
    (fun d _ d' _ h => SimpleGraph.Dart.ext _ _ h) (fun p hp => ?_) (fun _ _ => rfl)
  exact ⟨⟨p, (Finset.mem_filter.mp hp).2⟩, Finset.mem_univ _, rfl⟩

omit [DecidableEq V] in
lemma card_dart_eq : (Fintype.card G.Dart : ℝ) = 2 * #G.edgeFinset := by
  rw [G.dart_card_eq_twice_card_edges]; push_cast; ring

omit [DecidableEq V] in
/-- The average over darts, written with the number of edges. -/
lemma avg_dart (f : G.Dart → ℝ) :
    avg f = (∑ d, f d) / (2 * #G.edgeFinset) := by
  rw [avg, card_dart_eq]

omit [DecidableEq V] in
lemma two_mul_card_edgeFinset_pos [Nonempty G.Dart] : (0 : ℝ) < 2 * #G.edgeFinset := by
  rw [← card_dart_eq]; exact_mod_cast Fintype.card_pos

omit [Fintype V] [DecidableRel G.Adj] in
lemma edgeAvg_apply (x : V → ℝ) (d : G.Dart) (v : V) :
    edgeAvg G x d v = x v + (if v = d.fst then (x d.snd - x v) / 2 else 0) +
      (if v = d.snd then (x d.fst - x v) / 2 else 0) := by
  have hne : d.fst ≠ d.snd := d.adj.ne
  unfold edgeAvg
  by_cases h1 : v = d.fst
  · subst h1; simp [hne]; ring
  · by_cases h2 : v = d.snd
    · subst h2; simp [h1]; ring
    · simp [h1, h2]

omit [Fintype V] [DecidableRel G.Adj] in
lemma edgeAvg_edgeAvg (x : V → ℝ) (d : G.Dart) :
    edgeAvg G (edgeAvg G x d) d = edgeAvg G x d := by
  funext w
  simp only [edgeAvg, true_or, or_true, if_true]
  split_ifs <;> ring

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
  simp [meanStepMatrix, sub_mulVec, smul_mulVec]

lemma sum_dart_sq (x : V → ℝ) :
    ∑ d : G.Dart, (x d.fst - x d.snd) ^ 2 = 2 * (x ⬝ᵥ (G.lapMatrix ℝ *ᵥ x)) := by
  rw [sum_dart G (fun u v => (x u - x v) ^ 2), ← toLinearMap₂'_apply',
    SimpleGraph.lapMatrix_toLinearMap₂' ℝ G x]
  ring

lemma sum_dart_fst_eq (f : V → V → ℝ) (v : V) :
    ∑ d : G.Dart, (if v = d.fst then f d.fst d.snd else 0) =
      ∑ w ∈ G.neighborFinset v, f v w := by
  rw [sum_dart G (fun a b => if v = a then f a b else 0), Finset.sum_eq_single v]
  · simp [Finset.sum_ite, G.neighborFinset_eq_filter]
  · intro b _ hb; simp [Ne.symm hb]
  · simp

lemma sum_dart_snd_eq (f : V → V → ℝ) (v : V) :
    ∑ d : G.Dart, (if v = d.snd then f d.snd d.fst else 0) =
      ∑ w ∈ G.neighborFinset v, f v w := by
  rw [sum_dart G (fun a b => if v = b then f b a else 0), Finset.sum_comm, Finset.sum_eq_single v]
  · simp [Finset.sum_ite, G.adj_comm, G.neighborFinset_eq_filter]
  · intro b _ hb; simp [Ne.symm hb]
  · simp

/-- Core of equation (2): the sum over the darts of one round of averaging. -/
lemma sum_dart_edgeAvg (x : V → ℝ) (v : V) :
    ∑ d : G.Dart, edgeAvg G x d v =
      2 * #G.edgeFinset * x v - (G.lapMatrix ℝ *ᵥ x) v := by
  simp_rw [edgeAvg_apply]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, card_dart_eq]
  have h1 := sum_dart_fst_eq G (fun a b => (x b - x a) / 2) v
  have h2 := sum_dart_snd_eq G (fun a b => (x b - x a) / 2) v
  have e1 : ∑ d : G.Dart, (if v = d.fst then (x d.snd - x v) / 2 else 0) =
      ∑ d : G.Dart, (if v = d.fst then (x d.snd - x d.fst) / 2 else 0) :=
    Finset.sum_congr rfl fun d _ => by split_ifs with h <;> simp [h]
  have e2 : ∑ d : G.Dart, (if v = d.snd then (x d.fst - x v) / 2 else 0) =
      ∑ d : G.Dart, (if v = d.snd then (x d.fst - x d.snd) / 2 else 0) :=
    Finset.sum_congr rfl fun d _ => by split_ifs with h <;> simp [h]
  have hS : ∑ w ∈ G.neighborFinset v, (x w - x v) / 2 =
      (∑ w ∈ G.neighborFinset v, x w - G.degree v * x v) / 2 := by
    rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const,
      G.card_neighborFinset_eq_degree, nsmul_eq_mul]
  rw [e1, e2, h1, h2, G.lapMatrix_mulVec_apply, hS]
  ring

lemma avg_edgeAvg_aux [Nonempty G.Dart] (x : V → ℝ) (v : V) :
    avg (fun d : G.Dart => edgeAvg G x d v) = (meanStepMatrix G *ᵥ x) v := by
  have hm := two_mul_card_edgeFinset_pos G
  have hE : (#G.edgeFinset : ℝ) ≠ 0 := fun h => by simp [h] at hm
  rw [avg_dart, sum_dart_edgeAvg, meanStepMatrix_mulVec]
  field_simp

/-! ### The pinned statements -/

section NoDec
omit [DecidableRel G.Adj]

/-- `W_t x` is one round of averaging on the active edge. -/
theorem stepMatrix_mulVec (d : G.Dart) (x : V → ℝ) : stepMatrix G d *ᵥ x = edgeAvg G x d := by
  have hne : d.fst ≠ d.snd := d.adj.ne
  have hedge (i j : V) :
      s(i, j) = d.edge ↔ (i = d.fst ∧ j = d.snd) ∨ (i = d.snd ∧ j = d.fst) := by
    rw [SimpleGraph.Dart.edge, Sym2.eq_iff]
  funext i
  simp only [mulVec, dotProduct, stepMatrix, edgeAvg]
  by_cases hi : i = d.fst ∨ i = d.snd
  · rw [if_pos hi]
    rcases hi with rfl | rfl
    · rw [Fintype.sum_eq_add d.fst d.snd hne fun j hj => by
        simp [Ne.symm hj.1, hedge, hj.2, hne]]
      simp [hne, hedge]; ring
    · rw [Fintype.sum_eq_add d.fst d.snd hne fun j hj => by
        simp [Ne.symm hj.2, hedge, hj.1, Ne.symm hne]]
      simp [Ne.symm hne, hedge]; ring
  · rw [if_neg hi]
    push Not at hi
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj, hedge, hi.1, hi.2])
      (fun h => absurd (Finset.mem_univ i) h)]
    simp [hi.1, hi.2]

section NoFin
omit [Fintype V]

/-- `W_t` is symmetric (proof of Lemma C.1). -/
theorem stepMatrix_isSymm (d : G.Dart) : (stepMatrix G d).IsSymm := by
  ext i j
  simp only [transpose_apply, stepMatrix]
  by_cases h : i = j
  · subst h; rfl
  · rw [if_neg (Ne.symm h), if_neg h, Sym2.eq_swap]

end NoFin

/-- `W_t` is idempotent (proof of Lemma C.1). -/
theorem stepMatrix_mul_self (d : G.Dart) : stepMatrix G d * stepMatrix G d = stepMatrix G d := by
  rw [ext_iff_mulVec]
  intro x
  simp only [← mulVec_mulVec, stepMatrix_mulVec, edgeAvg_edgeAvg]

end NoDec

/-- Observation A.2, equation (2): over a uniformly random edge, `E[W_t] = I - L / (2m)`. -/
theorem avg_stepMatrix [Nonempty G.Dart] (i j : V) :
    avg (fun d : G.Dart => stepMatrix G d i j) = meanStepMatrix G i j := by
  have h := avg_edgeAvg_aux G (Pi.single j 1) i
  simp_rw [← stepMatrix_mulVec, mulVec_single_one] at h
  exact h

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
  · simp only [meanStepMatrix, SimpleGraph.lapMatrix, SimpleGraph.degMatrix, Matrix.sub_apply,
      Matrix.smul_apply, diagonal_apply, SimpleGraph.adjMatrix_apply, Matrix.one_apply,
      smul_eq_mul]
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
    avg (fun d : G.Dart => edgeAvg G x d v) = (meanStepMatrix G *ᵥ x) v :=
  avg_edgeAvg_aux G x v

/-- First-moment evolution, equation (15): `E[x⁽ᵗ⁾ | x⁽⁰⁾ = x] = W̄ᵗ x` over `t` i.i.d. uniform
rounds. -/
theorem expList_avgRun [Nonempty G.Dart] (x : V → ℝ) (t : ℕ) (v : V) :
    expList G.Dart t (fun l => avgRun G x l v) = (meanStepMatrix G ^ t *ᵥ x) v := by
  induction t generalizing x v with
  | zero => simp [avgRun]
  | succ t ih =>
    rw [expList_succ]
    have h1 : ∀ d : G.Dart, expList G.Dart t (fun l => avgRun G x (d :: l) v) =
        ∑ w, (meanStepMatrix G ^ t) v w * edgeAvg G x d w := fun d => ih _ _
    simp_rw [h1]
    rw [avg_sum]
    simp_rw [avg_const_mul, avg_edgeAvg, pow_succ, ← mulVec_mulVec]
    rfl

/-- Second moment of one round (proof of Lemma C.1): `E‖W x‖² = xᵀ W̄ x`, since `W` is symmetric
and idempotent. -/
theorem avg_sum_sq_edgeAvg [Nonempty G.Dart] (x : V → ℝ) :
    avg (fun d : G.Dart => ∑ v, edgeAvg G x d v ^ 2) = x ⬝ᵥ (meanStepMatrix G *ᵥ x) := by
  have hm := two_mul_card_edgeFinset_pos G
  simp_rw [sum_sq_edgeAvg]
  rw [avg_dart, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    card_dart_eq, ← Finset.sum_div, sum_dart_sq]
  have : x ⬝ᵥ (meanStepMatrix G *ᵥ x) =
      ∑ v, x v ^ 2 - (2 * (#G.edgeFinset : ℝ))⁻¹ * (x ⬝ᵥ (G.lapMatrix ℝ *ᵥ x)) := by
    simp only [dotProduct, meanStepMatrix_mulVec, mul_sub, Finset.mul_sum]
    rw [Finset.sum_sub_distrib]
    congr 1
    · simp [sq]
    · exact Finset.sum_congr rfl fun v _ => by ring
  have hE : (#G.edgeFinset : ℝ) ≠ 0 := fun h => by simp [h] at hm
  rw [this]
  field_simp

end Averaging.Opportunistic
