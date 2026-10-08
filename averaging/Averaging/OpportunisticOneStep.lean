import Averaging.OpportunisticClustered
import Averaging.OpportunisticSigns

/-! # One round of averaging on a clustered regular graph (Lemmas C.1 to C.3)

On an `(n, d, b)`-clustered regular graph write the state as `x = x_∥ + y + z` (equation (7)) with
`y = β χ`, `β = ⟨x, χ⟩/n` (`cutCoef`) and `‖z‖² = restSq`. For one round of `Averaging(1/2)` on a
uniformly random dart (`λ₂ = 2b/d`, `λ₃ ≥ lam3`):

* `sum_sq_eq`: `‖x‖² = n α² + n β² + ‖z‖²` (Pythagoras).
* `cutCoef_sq_add_restSq_edgeAvg_le`: `n β² + ‖z‖²` never increases.
* `avg_cutCoef_edgeAvg`: `E β' = (1 - λ₂/n) β`.
* `avg_restSq_edgeAvg_le` (Lemma C.3): `E ‖z'‖² ≤ (1 - λ₃/n) ‖z‖² + λ₂ β²`.
* `avg_cutDev_edgeAvg_le` (Lemma C.2, in the form used here): for every reference `γ`,
  `E n (β' - γ)² ≤ (1 - λ₂/n) n (β - γ)² + λ₂ γ² + (4λ₂/n²)(n β² + ‖z‖²)`.

The proofs avoid the explicit eigen-decomposition: `E‖W x‖² = xᵀ W̄ x` (`W` is a symmetric
idempotent), Jensen for `E β'²`, and a direct count over the cut darts for the variance of `β'`.
-/

namespace Averaging.Opportunistic
open Finset Matrix Dynamics

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {V₁ : Finset V} {d b : ℕ} {lam3 : ℝ}

/-- The coefficient `β = ⟨x, χ⟩/n` of `x` along the cut vector: `y = Q₂ x = β χ`. -/
noncomputable def cutCoef (V₁ : Finset V) (x : V → ℝ) : ℝ := avg fun w => cutVec V₁ w * x w

/-- `‖z‖² = ‖Q_{3⋯n} x‖²`. -/
noncomputable def restSq (V₁ : Finset V) (x : V → ℝ) : ℝ := ∑ v, projRest V₁ x v ^ 2

lemma restSq_nonneg (x : V → ℝ) : 0 ≤ restSq V₁ x := sum_nonneg fun _ _ => sq_nonneg _

lemma projCut_eq (x : V → ℝ) (v : V) : projCut V₁ x v = cutCoef V₁ x * cutVec V₁ v := rfl

lemma eq_decomp (x : V → ℝ) (v : V) :
    x v = avg x + cutCoef V₁ x * cutVec V₁ v + projRest V₁ x v := by
  simp only [projRest, projOne, projCut, cutCoef]; ring

omit [Fintype V] in
/-- The weight `((χ_u - χ_v)/2)²` of a pair: `1` across the cut, `0` inside a community. -/
lemma cutWeight_eq (u v : V) :
    ((cutVec V₁ u - cutVec V₁ v) / 2) ^ 2 = if (v ∈ V₁ ↔ u ∉ V₁) then 1 else 0 := by
  unfold cutVec
  by_cases hu : u ∈ V₁ <;> by_cases hv : v ∈ V₁ <;> norm_num [hu, hv]

namespace IsClusteredRegular
variable (hG : IsClusteredRegular G V₁ d b)
include hG

lemma card_real_pos : (0 : ℝ) < Fintype.card V := hG.card_pos_real

lemma d_real_pos : (0 : ℝ) < d := by exact_mod_cast hG.d_pos

omit [DecidableRel G.Adj] hG in
lemma sum_sq_projCut (x : V → ℝ) :
    ∑ v, projCut V₁ x v ^ 2 = Fintype.card V * cutCoef V₁ x ^ 2 := by
  simp only [projCut_eq, mul_pow, cutVec_sq, mul_one, sum_const, card_univ, nsmul_eq_mul]

/-- Pythagoras for the decomposition `x = x_∥ + y + z`. -/
lemma sum_sq_eq (x : V → ℝ) :
    ∑ v, x v ^ 2 = Fintype.card V * avg x ^ 2 + Fintype.card V * cutCoef V₁ x ^ 2 +
      restSq V₁ x := by
  have key : ∑ v, x v ^ 2 = ∑ v, (avg x ^ 2 + 2 * avg x * cutCoef V₁ x * cutVec V₁ v +
      cutCoef V₁ x ^ 2 * cutVec V₁ v ^ 2) + 2 * avg x * ∑ v, projRest V₁ x v +
      2 * cutCoef V₁ x * ∑ v, cutVec V₁ v * projRest V₁ x v + restSq V₁ x := by
    rw [restSq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    conv_lhs => rw [eq_decomp (V₁ := V₁) x v]
    ring
  rw [key, hG.sum_projRest, hG.sum_cutVec_mul_projRest]
  simp only [cutVec_sq, Finset.sum_add_distrib, Finset.sum_const, card_univ, nsmul_eq_mul,
    ← Finset.mul_sum, hG.sum_cutVec]
  ring

omit [DecidableRel G.Adj] hG in
lemma avg_edgeAvg_eq (x : V → ℝ) (e : G.Dart) : avg (edgeAvg G x e) = avg x := by
  simp only [avg, sum_edgeAvg]

/-- `n β² + ‖z‖²` (the squared distance to the consensus) never increases. -/
lemma cutCoef_sq_add_restSq_edgeAvg_le (x : V → ℝ) (e : G.Dart) :
    Fintype.card V * cutCoef V₁ (edgeAvg G x e) ^ 2 + restSq V₁ (edgeAvg G x e) ≤
      Fintype.card V * cutCoef V₁ x ^ 2 + restSq V₁ x := by
  have h1 := hG.sum_sq_eq (edgeAvg G x e)
  have h2 := hG.sum_sq_eq x
  have h3 := sum_sq_edgeAvg G x e
  rw [avg_edgeAvg_eq] at h1
  have : 0 ≤ (x e.fst - x e.snd) ^ 2 / 2 := by positivity
  linarith

/-- The change of `n β` in one round: `(χ_a - χ_b)(x_b - x_a)/2` on the dart `(a, b)`. -/
lemma card_mul_cutCoef_edgeAvg_sub (x : V → ℝ) (e : G.Dart) :
    Fintype.card V * (cutCoef V₁ (edgeAvg G x e) - cutCoef V₁ x) =
      (cutVec V₁ e.fst - cutVec V₁ e.snd) * (x e.snd - x e.fst) / 2 := by
  have hne : e.fst ≠ e.snd := e.adj.ne
  rw [mul_sub, cutCoef, cutCoef, hG.card_mul_avg, hG.card_mul_avg, ← Finset.sum_sub_distrib,
    Fintype.sum_eq_add e.fst e.snd hne fun w hw => by simp [edgeAvg, hw.1, hw.2]]
  simp only [edgeAvg, true_or, or_true, if_true]
  ring

/-- `E β' = (1 - λ₂/n) β`. -/
lemma avg_cutCoef_edgeAvg (x : V → ℝ) :
    avg (fun e : G.Dart => cutCoef V₁ (edgeAvg G x e)) =
      (1 - (2 * b / d : ℝ) / Fintype.card V) * cutCoef V₁ x := by
  haveI := hG.nonempty_dart
  have hn := hG.card_real_pos.ne'
  have h : ∀ e : G.Dart, cutCoef V₁ (edgeAvg G x e) =
      (∑ v, cutVec V₁ v * edgeAvg G x e v) / Fintype.card V := fun e => by
    rw [cutCoef, avg]
  simp_rw [h]
  have h2 : avg (fun e : G.Dart => (∑ v, cutVec V₁ v * edgeAvg G x e v) / Fintype.card V) =
      (∑ v, cutVec V₁ v * avg (fun e : G.Dart => edgeAvg G x e v)) / Fintype.card V := by
    simp_rw [div_eq_mul_inv, mul_comm _ ((Fintype.card V : ℝ))⁻¹, avg_const_mul, avg_sum,
      avg_const_mul]
  rw [h2]
  simp_rw [avg_edgeAvg]
  rw [hG.cutVec_dot_meanStepMatrix, cutCoef, avg]
  ring

/-- Number of cut darts leaving each node: `∑_{(a,b)} w(a, b) f(a) = b ∑ f`. -/
lemma sum_dart_cutWeight_fst (f : V → ℝ) :
    ∑ e : G.Dart, ((cutVec V₁ e.fst - cutVec V₁ e.snd) / 2) ^ 2 * f e.fst =
      b * ∑ v, f v := by
  rw [sum_dart G (fun u v => ((cutVec V₁ u - cutVec V₁ v) / 2) ^ 2 * f u), Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  have : ∀ v, (if G.Adj u v then ((cutVec V₁ u - cutVec V₁ v) / 2) ^ 2 * f u else 0) =
      if v ∈ G.neighborFinset u ∧ (v ∈ V₁ ↔ u ∉ V₁) then f u else 0 := fun v => by
    simp only [cutWeight_eq, SimpleGraph.mem_neighborFinset]
    by_cases h1 : G.Adj u v <;> by_cases h2 : (v ∈ V₁ ↔ u ∉ V₁) <;> simp [h1, h2]
  simp_rw [this]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hc : (univ.filter fun v => v ∈ G.neighborFinset u ∧ (v ∈ V₁ ↔ u ∉ V₁)) =
      {v ∈ G.neighborFinset u | (v ∈ V₁ ↔ u ∉ V₁)} := by
    ext v; simp
  rw [hc, hG.cross u]

omit [DecidableEq V] hG in
lemma sum_dart_symm (F : G.Dart → ℝ) : ∑ e : G.Dart, F e.symm = ∑ e : G.Dart, F e :=
  Equiv.sum_comp (Function.Involutive.toPerm _ SimpleGraph.Dart.symm_involutive) F

lemma sum_dart_cutWeight_snd (f : V → ℝ) :
    ∑ e : G.Dart, ((cutVec V₁ e.fst - cutVec V₁ e.snd) / 2) ^ 2 * f e.snd =
      b * ∑ v, f v := by
  rw [← hG.sum_dart_cutWeight_fst f,
    ← sum_dart_symm (fun e => ((cutVec V₁ e.fst - cutVec V₁ e.snd) / 2) ^ 2 * f e.fst)]
  refine Finset.sum_congr rfl fun e _ => ?_
  show _ = ((cutVec V₁ e.snd - cutVec V₁ e.fst) / 2) ^ 2 * f e.snd
  ring

/-- The cut darts against the decomposition: `∑ w (x_a - x_b)² ≤ 8 n b β² + 8 b ‖z‖²`. -/
lemma sum_dart_cutWeight_sq_le (x : V → ℝ) :
    ∑ e : G.Dart, ((cutVec V₁ e.fst - cutVec V₁ e.snd) / 2) ^ 2 * (x e.fst - x e.snd) ^ 2 ≤
      8 * Fintype.card V * b * cutCoef V₁ x ^ 2 + 8 * b * restSq V₁ x := by
  set β := cutCoef V₁ x
  set z := projRest V₁ x
  have hpt : ∀ e : G.Dart,
      ((cutVec V₁ e.fst - cutVec V₁ e.snd) / 2) ^ 2 * (x e.fst - x e.snd) ^ 2 ≤
        8 * β ^ 2 * (((cutVec V₁ e.fst - cutVec V₁ e.snd) / 2) ^ 2 * 1) +
        4 * (((cutVec V₁ e.fst - cutVec V₁ e.snd) / 2) ^ 2 * z e.fst ^ 2) +
        4 * (((cutVec V₁ e.fst - cutVec V₁ e.snd) / 2) ^ 2 * z e.snd ^ 2) := fun e => by
    have hx : x e.fst - x e.snd =
        β * (cutVec V₁ e.fst - cutVec V₁ e.snd) + (z e.fst - z e.snd) := by
      rw [eq_decomp (V₁ := V₁) x e.fst, eq_decomp (V₁ := V₁) x e.snd]; ring
    rw [hx]
    set w := (cutVec V₁ e.fst - cutVec V₁ e.snd) / 2 with hw
    have hc : cutVec V₁ e.fst - cutVec V₁ e.snd = 2 * w := by rw [hw]; ring
    have hw2 : w ^ 2 * w ^ 2 = w ^ 2 := by
      rw [hw, cutWeight_eq]; split_ifs <;> norm_num
    rw [hc]
    have h0 : 0 ≤ w ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg h0 (sq_nonneg (2 * β * w - (z e.fst - z e.snd))),
      mul_nonneg h0 (sq_nonneg (z e.fst + z e.snd)), hw2]
  refine (Finset.sum_le_sum fun e _ => hpt e).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, hG.sum_dart_cutWeight_fst (fun _ => 1),
    hG.sum_dart_cutWeight_fst (fun v => z v ^ 2), hG.sum_dart_cutWeight_snd (fun v => z v ^ 2)]
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one, restSq, z]
  ring

lemma card_dart_real : (Fintype.card G.Dart : ℝ) = Fintype.card V * d := by
  rw [card_dart_eq, hG.two_mul_card_edgeFinset]

/-- Variance of `β'`: `n E (β' - β)² ≤ (4λ₂/n²)(n β² + ‖z‖²)`. -/
lemma avg_cutCoef_edgeAvg_sub_sq_le (x : V → ℝ) :
    Fintype.card V * avg (fun e : G.Dart => (cutCoef V₁ (edgeAvg G x e) - cutCoef V₁ x) ^ 2) ≤
      4 * (2 * b / d) / Fintype.card V ^ 2 *
        (Fintype.card V * cutCoef V₁ x ^ 2 + restSq V₁ x) := by
  have hn := hG.card_real_pos
  have hd := hG.d_real_pos
  have h : ∀ e : G.Dart, (cutCoef V₁ (edgeAvg G x e) - cutCoef V₁ x) ^ 2 =
      ((cutVec V₁ e.fst - cutVec V₁ e.snd) / 2) ^ 2 * (x e.fst - x e.snd) ^ 2 /
        (Fintype.card V : ℝ) ^ 2 := fun e => by
    have h1 := hG.card_mul_cutCoef_edgeAvg_sub x e
    rw [eq_div_iff (by positivity)]
    have : (cutCoef V₁ (edgeAvg G x e) - cutCoef V₁ x) ^ 2 * (Fintype.card V : ℝ) ^ 2 =
        (Fintype.card V * (cutCoef V₁ (edgeAvg G x e) - cutCoef V₁ x)) ^ 2 := by ring
    rw [this, h1]; ring
  simp_rw [h]
  rw [avg, ← Finset.sum_div, hG.card_dart_real]
  have hs := hG.sum_dart_cutWeight_sq_le x
  have hb : (0 : ℝ) ≤ b := by positivity
  rw [show (Fintype.card V : ℝ) *
      ((∑ e : G.Dart, ((cutVec V₁ e.fst - cutVec V₁ e.snd) / 2) ^ 2 * (x e.fst - x e.snd) ^ 2) /
        (Fintype.card V : ℝ) ^ 2 / (Fintype.card V * d)) =
      (∑ e : G.Dart, ((cutVec V₁ e.fst - cutVec V₁ e.snd) / 2) ^ 2 * (x e.fst - x e.snd) ^ 2) /
        ((Fintype.card V : ℝ) ^ 2 * d) by field_simp]
  rw [div_le_iff₀ (by positivity)]
  refine hs.trans (le_of_eq ?_)
  field_simp
  ring

/-- The Laplacian form splits along the decomposition: `xᵀ L x = 2 b n β² + zᵀ L z`. -/
lemma dotProduct_lap_eq (x : V → ℝ) :
    x ⬝ᵥ (G.lapMatrix ℝ *ᵥ x) = 2 * b * Fintype.card V * cutCoef V₁ x ^ 2 +
      projRest V₁ x ⬝ᵥ (G.lapMatrix ℝ *ᵥ projRest V₁ x) := by
  set z := projRest V₁ x
  set β := cutCoef V₁ x
  have hx : x = (fun _ => avg x) + β • cutVec V₁ + z := by
    funext v; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; exact eq_decomp x v
  have hL1 : G.lapMatrix ℝ *ᵥ (fun _ : V => avg x) = 0 := by
    have := SimpleGraph.lapMatrix_mulVec_const_eq_zero (R := ℝ) G
    rw [show (fun _ : V => avg x) = avg x • (fun _ : V => (1 : ℝ)) by
      funext; simp, mulVec_smul]
    rw [this, smul_zero]
  have hsym : ∀ u v : V → ℝ, u ⬝ᵥ (G.lapMatrix ℝ *ᵥ v) = (G.lapMatrix ℝ *ᵥ u) ⬝ᵥ v :=
    fun u v => by rw [dotProduct_mulVec, ← mulVec_transpose, (G.isSymm_lapMatrix ℝ).eq]
  have hχz : cutVec V₁ ⬝ᵥ (G.lapMatrix ℝ *ᵥ z) = 0 := by
    rw [hsym, hG.lapMatrix_mulVec_cutVec, smul_dotProduct, dotProduct, hG.sum_cutVec_mul_projRest,
      smul_zero]
  have h1z : (fun _ : V => avg x) ⬝ᵥ (G.lapMatrix ℝ *ᵥ z) = 0 := by
    rw [hsym, hL1, zero_dotProduct]
  have hχχ : cutVec V₁ ⬝ᵥ (G.lapMatrix ℝ *ᵥ cutVec V₁) = 2 * b * Fintype.card V := by
    rw [hG.lapMatrix_mulVec_cutVec, dotProduct_smul, smul_eq_mul, dotProduct]
    simp [cutVec_mul_self]
  have h1χ : (fun _ : V => avg x) ⬝ᵥ (G.lapMatrix ℝ *ᵥ cutVec V₁) = 0 := by
    rw [hsym, hL1, zero_dotProduct]
  have hzχ : z ⬝ᵥ (G.lapMatrix ℝ *ᵥ cutVec V₁) = 0 := by
    rw [hsym, dotProduct_comm]; exact hχz
  conv_lhs => rw [hx]
  simp only [mulVec_add, mulVec_smul, hL1, add_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, hχz, h1z, hχχ, h1χ, hzχ, dotProduct_zero]
  ring

/-- **Lemma C.3**: `E ‖z'‖² ≤ (1 - λ₃/n) ‖z‖² + λ₂ β²`. -/
lemma avg_restSq_edgeAvg_le (h3 : ThirdEigenvalueLB G V₁ d lam3) (x : V → ℝ) :
    avg (fun e : G.Dart => restSq V₁ (edgeAvg G x e)) ≤
      (1 - lam3 / Fintype.card V) * restSq V₁ x + (2 * b / d) * cutCoef V₁ x ^ 2 := by
  haveI := hG.nonempty_dart
  have hn := hG.card_real_pos
  have hd := hG.d_real_pos
  set N : ℝ := (Fintype.card V : ℝ)
  have hR : ∀ e : G.Dart, restSq V₁ (edgeAvg G x e) =
      ∑ v, edgeAvg G x e v ^ 2 - N * avg x ^ 2 - N * cutCoef V₁ (edgeAvg G x e) ^ 2 := by
    intro e; have := hG.sum_sq_eq (edgeAvg G x e); rw [avg_edgeAvg_eq] at this; linarith
  simp_rw [hR]
  rw [avg_sub, avg_sub, avg_const, avg_const_mul, avg_sum_sq_edgeAvg,
    dotProduct_meanStepMatrix, hG.two_mul_card_edgeFinset, hG.dotProduct_lap_eq x]
  have hJ := sq_avg_le_avg_sq (fun e : G.Dart => cutCoef V₁ (edgeAvg G x e))
  rw [hG.avg_cutCoef_edgeAvg] at hJ
  have hz := h3 (projRest V₁ x) (hG.sum_projRest x) (hG.sum_cutVec_mul_projRest x)
  have hsx := hG.sum_sq_eq x
  rw [← restSq] at hz
  set β := cutCoef V₁ x
  set R := restSq V₁ x
  set Q := projRest V₁ x ⬝ᵥ (G.lapMatrix ℝ *ᵥ projRest V₁ x)
  set A := avg fun e : G.Dart => cutCoef V₁ (edgeAvg G x e) ^ 2
  have hQ : lam3 * R / N ≤ Q / (N * d) := by
    rw [div_le_div_iff₀ hn (by positivity)]; nlinarith
  have hinv : (N * d)⁻¹ * (2 * b * N * β ^ 2 + Q) = (2 * b / d) * β ^ 2 + Q / (N * d) := by
    field_simp
  rw [hinv]
  have hl : (2 * b / d : ℝ) / N * ((2 * b / d) / N) * β ^ 2 ≥ 0 := by positivity
  have hJ' : (1 - (2 * b / d : ℝ) / N) ^ 2 * β ^ 2 ≤ A := by rw [← mul_pow]; exact hJ
  have e1 : N * ((1 - (2 * b / d : ℝ) / N) ^ 2 * β ^ 2) =
      N * β ^ 2 - 2 * (2 * b / d) * β ^ 2 +
        N * ((2 * b / d : ℝ) / N * ((2 * b / d) / N) * β ^ 2) := by
    field_simp; ring
  have : N * ((1 - (2 * b / d : ℝ) / N) ^ 2 * β ^ 2) ≤ N * A := by gcongr
  have hlamR : (1 - lam3 / N) * R = R - lam3 * R / N := by ring
  rw [hlamR]
  nlinarith

/-- **Lemma C.2** (in the form used here): for every reference coefficient `γ`,
`E n (β' - γ)² ≤ (1 - λ₂/n) n (β - γ)² + λ₂ γ² + (4λ₂/n²)(n β² + ‖z‖²)`. -/
lemma avg_cutDev_edgeAvg_le (x : V → ℝ) (γ : ℝ) :
    avg (fun e : G.Dart => Fintype.card V * (cutCoef V₁ (edgeAvg G x e) - γ) ^ 2) ≤
      (1 - (2 * b / d : ℝ) / Fintype.card V) * (Fintype.card V * (cutCoef V₁ x - γ) ^ 2) +
        (2 * b / d) * γ ^ 2 + 4 * (2 * b / d) / Fintype.card V ^ 2 *
          (Fintype.card V * cutCoef V₁ x ^ 2 + restSq V₁ x) := by
  haveI := hG.nonempty_dart
  have hn := hG.card_real_pos
  set N : ℝ := (Fintype.card V : ℝ)
  set β := cutCoef V₁ x
  set l2 : ℝ := 2 * b / d
  have hexp : ∀ e : G.Dart, N * (cutCoef V₁ (edgeAvg G x e) - γ) ^ 2 =
      N * (cutCoef V₁ (edgeAvg G x e) - β) ^ 2 +
        2 * N * (β - γ) * cutCoef V₁ (edgeAvg G x e) + (N * (β - γ) ^ 2 - 2 * N * (β - γ) * β) :=
    fun e => by ring
  simp_rw [hexp]
  rw [avg_add, avg_add, avg_const, avg_const_mul, avg_const_mul, hG.avg_cutCoef_edgeAvg]
  have hv := hG.avg_cutCoef_edgeAvg_sub_sq_le x
  have key : 2 * N * (β - γ) * ((1 - l2 / N) * β) + (N * (β - γ) ^ 2 - 2 * N * (β - γ) * β) =
      (1 - l2 / N) * (N * (β - γ) ^ 2) + l2 * γ ^ 2 - l2 * β ^ 2 := by
    field_simp; ring
  have hl2 : 0 ≤ l2 := by positivity
  nlinarith [mul_nonneg hl2 (sq_nonneg β)]

end IsClusteredRegular

end Averaging.Opportunistic
