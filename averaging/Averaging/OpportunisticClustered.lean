import Averaging.OpportunisticFirstMoment
import Averaging.Basic

/-! # Averaging whenever you meet: clustered regular graphs and the first-moment criteria

An `(n, d, b)`-clustered regular graph (Definition 2.2 of arXiv:1703.05045, v3) is `d`-regular with
two communities `V₁, V₂` of size `n/2`, every node having exactly `b` neighbours in the other
community. Then the cut vector `χ = 𝟙_{V₁} - 𝟙_{V₂}` is an eigenvector of the normalized Laplacian
`𝓛 = L/d` with eigenvalue `λ₂ = 2b/d`, and of `W̄ = I - 𝓛/n` with eigenvalue `1 - λ₂/n`
(Section 4.1). The state splits as `x = x_∥ + y + z` (equation (7)) along `𝟙`, along `χ`, and
orthogonally to both.

The third eigenvalue `λ₃` of `𝓛` enters only through the bound `zᵀ𝓛z ≥ λ₃ ‖z‖²` for `z ⟂ 𝟙, χ`
(`ThirdEigenvalueLB`). With these, the first-moment decomposition (Lemma B.1) is exact, the set of
bad nodes of Definition B.1 is empty, and Lemmas B.3 (monotonicity) and B.4 (sign) hold for every
node: this is Theorem 3.1 on clustered regular graphs.
-/

namespace Averaging.Opportunistic
open Finset Matrix Dynamics

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Definition 2.2: `G` is an `(n, d, b)`-clustered regular graph with communities `V₁` and
`V₂ = V₁ᶜ`, where `n` is the number of nodes: `|V₁| = |V₂| = n/2`, every node has degree `d`,
every node has exactly `b` neighbours in the other community, and `0 < b`, `2b < d < n`. -/
structure IsClusteredRegular (V₁ : Finset V) (d b : ℕ) : Prop where
  card_eq : 2 * #V₁ = Fintype.card V
  regular : G.IsRegularOfDegree d
  cross : ∀ v, #{u ∈ G.neighborFinset v | (u ∈ V₁ ↔ v ∉ V₁)} = b
  pos : 0 < b
  lt_deg : 2 * b < d
  deg_lt : d < Fintype.card V

/-- The cut vector `χ = 𝟙_{V₁} - 𝟙_{V₂}`. -/
def cutVec (V₁ : Finset V) : V → ℝ := fun v => if v ∈ V₁ then 1 else -1

/-- `x_∥ = Q₁ x`, the projection of `x` on the constant vectors: every entry is the average
`α₁ = ⟨x, 𝟙⟩/n` of `x`. -/
noncomputable def projOne (x : V → ℝ) : V → ℝ := fun _ => avg x

/-- `y = Q₂ x`, the projection of `x` on the cut vector: `(⟨x, χ⟩/n) χ`. -/
noncomputable def projCut (V₁ : Finset V) (x : V → ℝ) : V → ℝ :=
  fun v => avg (fun w => cutVec V₁ w * x w) * cutVec V₁ v

/-- `z = Q_{3⋯n} x = x - x_∥ - y`, the projection of `x` orthogonally to `𝟙` and `χ`. -/
noncomputable def projRest (V₁ : Finset V) (x : V → ℝ) : V → ℝ :=
  fun v => x v - projOne x v - projCut V₁ x v

/-- `λ₃ ≥ lam3` for a `d`-regular graph with cut vector `χ`: the Rayleigh quotient of the
normalized Laplacian `𝓛 = L/d` is at least `lam3` on the vectors orthogonal to `𝟙` and `χ`. For a
clustered regular graph with `λ₃ > 2b/d` (so that `χ` spans the second eigenspace), the largest
such `lam3` is the third eigenvalue `λ₃` of `𝓛`. -/
def ThirdEigenvalueLB (V₁ : Finset V) (d : ℕ) (lam3 : ℝ) : Prop :=
  ∀ z : V → ℝ, ∑ v, z v = 0 → ∑ v, cutVec V₁ v * z v = 0 →
    lam3 * d * ∑ v, z v ^ 2 ≤ z ⬝ᵥ (G.lapMatrix ℝ *ᵥ z)

variable {G} {V₁ : Finset V} {d b : ℕ} {lam3 : ℝ}

/-! ### Auxiliary lemmas -/

omit [Fintype V] in
lemma cutVec_sq (v : V) : cutVec V₁ v ^ 2 = 1 := by
  unfold cutVec; split_ifs <;> norm_num

omit [Fintype V] in
lemma cutVec_mul_self (v : V) : cutVec V₁ v * cutVec V₁ v = 1 := by
  rw [← sq, cutVec_sq]

omit [Fintype V] in
lemma abs_cutVec (v : V) : |cutVec V₁ v| = 1 := by
  unfold cutVec; split_ifs <;> norm_num

namespace IsClusteredRegular
variable (hG : IsClusteredRegular G V₁ d b)
include hG

lemma degree_eq (v : V) : G.degree v = d := hG.regular.degree_eq v

lemma four_le_card : 4 ≤ Fintype.card V := by
  have := hG.pos; have := hG.lt_deg; have := hG.deg_lt; omega

lemma d_pos : 0 < d := by have := hG.pos; have := hG.lt_deg; omega

lemma card_pos_real : (0 : ℝ) < Fintype.card V := by
  have := hG.four_le_card; exact_mod_cast (by omega : 0 < Fintype.card V)

lemma two_mul_card_edgeFinset : (2 * #G.edgeFinset : ℝ) = Fintype.card V * d := by
  have h := G.sum_degrees_eq_twice_card_edges
  simp only [hG.degree_eq, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
  exact_mod_cast h.symm

lemma nonempty_dart : Nonempty G.Dart := by
  have : Nonempty V := ⟨(Fintype.card_pos_iff.mp (by have := hG.four_le_card; omega)).some⟩
  obtain ⟨v⟩ := this
  have hv : 0 < G.degree v := by rw [hG.degree_eq]; exact hG.d_pos
  obtain ⟨w, hw⟩ := (G.degree_pos_iff_exists_adj v).mp hv
  exact ⟨⟨(v, w), hw⟩⟩

lemma b_lt_d_real : (2 * b / d : ℝ) < 1 := by
  have hd : (0 : ℝ) < d := by exact_mod_cast hG.d_pos
  rw [div_lt_one hd]; exact_mod_cast hG.lt_deg

lemma two_div_card_lt : 2 / (Fintype.card V : ℝ) < 2 * b / d := by
  have hd : (0 : ℝ) < d := by exact_mod_cast hG.d_pos
  have hn := hG.card_pos_real
  rw [div_lt_div_iff₀ hn hd]
  have h1 : (1 : ℝ) ≤ b := by exact_mod_cast hG.pos
  have h2 : (d : ℝ) < Fintype.card V := by exact_mod_cast hG.deg_lt
  nlinarith

lemma sum_cutVec : ∑ v, cutVec V₁ v = 0 := by
  have h := hG.card_eq
  simp only [cutVec, Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, mul_one, mul_neg]
  have e1 : (univ.filter fun v => v ∈ V₁) = V₁ := by ext; simp
  have e2 : #(univ.filter fun v => v ∉ V₁) = Fintype.card V - #V₁ := by
    rw [Finset.filter_not, Finset.card_sdiff, e1]; simp
  rw [e1, e2, Nat.cast_sub (by omega)]
  have : (Fintype.card V : ℝ) = 2 * #V₁ := by exact_mod_cast h.symm
  linarith

lemma card_same (v : V) : #{u ∈ G.neighborFinset v | ¬(u ∈ V₁ ↔ v ∉ V₁)} = d - b := by
  have h := Finset.card_filter_add_card_filter_not (s := G.neighborFinset v)
    (fun u => (u ∈ V₁ ↔ v ∉ V₁))
  rw [hG.cross v, G.card_neighborFinset_eq_degree, hG.degree_eq] at h
  omega

lemma lapMatrix_mulVec_cutVec : G.lapMatrix ℝ *ᵥ cutVec V₁ = (2 * b : ℝ) • cutVec V₁ := by
  funext v
  rw [G.lapMatrix_mulVec_apply, hG.degree_eq, Pi.smul_apply, smul_eq_mul]
  have hsplit : ∑ u ∈ G.neighborFinset v, cutVec V₁ u =
      ∑ u ∈ G.neighborFinset v, if (u ∈ V₁ ↔ v ∉ V₁) then -cutVec V₁ v else cutVec V₁ v := by
    refine Finset.sum_congr rfl fun u _ => ?_
    unfold cutVec
    by_cases hu : u ∈ V₁ <;> by_cases hv : v ∈ V₁ <;> simp [hu, hv]
  rw [hsplit, Finset.sum_ite, Finset.sum_const, Finset.sum_const, hG.cross v, hG.card_same v,
    nsmul_eq_mul, nsmul_eq_mul, Nat.cast_sub (by have := hG.lt_deg; omega)]
  ring

lemma card_mul_avg (x : V → ℝ) : (Fintype.card V : ℝ) * avg x = ∑ v, x v := by
  unfold avg; field_simp [hG.card_pos_real.ne']

lemma sum_projRest (x : V → ℝ) : ∑ v, projRest V₁ x v = 0 := by
  simp only [projRest, projOne, projCut, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, hG.sum_cutVec, mul_zero, sub_zero]
  rw [hG.card_mul_avg]; ring

lemma sum_cutVec_mul_projRest (x : V → ℝ) : ∑ v, cutVec V₁ v * projRest V₁ x v = 0 := by
  have h1 : ∑ v, cutVec V₁ v * projRest V₁ x v = ∑ v, cutVec V₁ v * x v -
      avg x * ∑ v, cutVec V₁ v - avg (fun w => cutVec V₁ w * x w) * ∑ v, cutVec V₁ v ^ 2 := by
    simp only [projRest, projOne, projCut, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    · congr 1; exact Finset.sum_congr rfl fun v _ => by ring
    · exact Finset.sum_congr rfl fun v _ => by ring
  simp only [cutVec_sq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h1
  rw [h1, hG.sum_cutVec, mul_comm (avg (fun w => cutVec V₁ w * x w)) (Fintype.card V : ℝ),
    hG.card_mul_avg]
  ring

lemma sum_sq_projRest_le (x : V → ℝ) : ∑ v, projRest V₁ x v ^ 2 ≤ ∑ v, x v ^ 2 := by
  set a := avg x
  set c := avg (fun w => cutVec V₁ w * x w)
  have hx : ∀ v, x v = (a + c * cutVec V₁ v) + projRest V₁ x v := fun v => by
    simp only [projRest, projOne, projCut]; ring
  have key : ∑ v, x v ^ 2 - ∑ v, projRest V₁ x v ^ 2 =
      ∑ v, (a + c * cutVec V₁ v) ^ 2 + 2 * a * ∑ v, projRest V₁ x v +
        2 * c * ∑ v, cutVec V₁ v * projRest V₁ x v := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [hx v]; ring
  rw [hG.sum_projRest, hG.sum_cutVec_mul_projRest] at key
  have : 0 ≤ ∑ v, (a + c * cutVec V₁ v) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

lemma dotProduct_lap_le (z : V → ℝ) :
    z ⬝ᵥ (G.lapMatrix ℝ *ᵥ z) ≤ 2 * d * ∑ v, z v ^ 2 := by
  have h := sum_dart_sq G z
  have h2 : ∑ e : G.Dart, (z e.fst - z e.snd) ^ 2 ≤
      ∑ e : G.Dart, (2 * z e.fst ^ 2 + 2 * z e.snd ^ 2) :=
    Finset.sum_le_sum fun e _ => by nlinarith [sq_nonneg (z e.fst + z e.snd)]
  have h3 : ∑ e : G.Dart, (2 * z e.fst ^ 2 + 2 * z e.snd ^ 2) = 4 * d * ∑ v, z v ^ 2 := by
    rw [sum_dart G (fun a b => 2 * z a ^ 2 + 2 * z b ^ 2)]
    have : ∀ u, (∑ v, if G.Adj u v then 2 * z u ^ 2 + 2 * z v ^ 2 else 0) =
        ∑ v ∈ G.neighborFinset u, (2 * z u ^ 2 + 2 * z v ^ 2) := fun u => by
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, G.neighborFinset_eq_filter]
    simp_rw [this, Finset.sum_add_distrib, Finset.sum_const, G.card_neighborFinset_eq_degree,
      hG.degree_eq, nsmul_eq_mul, ← Finset.mul_sum]
    rw [Averaging.sum_sum_neighbor G (fun v => z v ^ 2)]
    simp_rw [hG.degree_eq, ← Finset.mul_sum]
    ring
  linarith

omit hG in
lemma dotProduct_lap_nonneg (z : V → ℝ) : 0 ≤ z ⬝ᵥ (G.lapMatrix ℝ *ᵥ z) := by
  have h := sum_dart_sq G z
  have : 0 ≤ ∑ e : G.Dart, (z e.fst - z e.snd) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

lemma lam3_le_two (h3 : ThirdEigenvalueLB G V₁ d lam3) : lam3 ≤ 2 := by
  have hcard : 1 < #V₁ := by have := hG.card_eq; have := hG.four_le_card; omega
  obtain ⟨a, ha, c, hc, hac⟩ := Finset.one_lt_card.mp hcard
  set z : V → ℝ := Pi.single a 1 - Pi.single c 1 with hz
  have hz1 : ∑ v, z v = 0 := by simp [hz, Finset.sum_sub_distrib]
  have hz2 : ∑ v, cutVec V₁ v * z v = 0 := by
    rw [Fintype.sum_eq_add a c hac fun v hv => by simp [hz, hv.1, hv.2]]
    simp [hz, hac, Ne.symm hac, cutVec, ha, hc]
  have hz3 : ∑ v, z v ^ 2 = 2 := by
    rw [Fintype.sum_eq_add a c hac fun v hv => by simp [hz, hv.1, hv.2]]
    simp [hz, hac, Ne.symm hac]; norm_num
  have h := h3 z hz1 hz2
  have hle := hG.dotProduct_lap_le z
  rw [hz3] at h hle
  have hd : (0 : ℝ) < d := by exact_mod_cast hG.d_pos
  nlinarith

end IsClusteredRegular

lemma meanStepMatrix_mulVec_const (c : ℝ) : meanStepMatrix G *ᵥ (fun _ => c) = fun _ => c := by
  funext v
  rw [meanStepMatrix_mulVec, G.lapMatrix_mulVec_apply]
  simp [Finset.sum_const, G.card_neighborFinset_eq_degree]

lemma meanStepMatrix_pow_mulVec_const (t : ℕ) (c : ℝ) :
    meanStepMatrix G ^ t *ᵥ (fun _ => c) = fun _ => c := by
  induction t with
  | zero => simp
  | succ t ih => rw [pow_succ', ← mulVec_mulVec, ih, meanStepMatrix_mulVec_const]

lemma dotProduct_meanStepMatrix_comm (x y : V → ℝ) :
    x ⬝ᵥ (meanStepMatrix G *ᵥ y) = (meanStepMatrix G *ᵥ x) ⬝ᵥ y := by
  rw [dotProduct_mulVec, ← mulVec_transpose, (meanStepMatrix_isSymm G).eq]

lemma sum_meanStepMatrix_mulVec (z : V → ℝ) : ∑ v, (meanStepMatrix G *ᵥ z) v = ∑ v, z v := by
  have h := dotProduct_meanStepMatrix_comm (G := G) (fun _ => (1 : ℝ)) z
  rw [meanStepMatrix_mulVec_const] at h
  simpa [dotProduct] using h

omit [DecidableEq V] in
lemma sum_sq_eq_dotProduct (z : V → ℝ) : ∑ v, z v ^ 2 = z ⬝ᵥ z := by simp [dotProduct, sq]

omit [DecidableEq V] in
lemma quad_expand (A : Matrix V V ℝ) (z p : V → ℝ) (t : ℝ) :
    (z + t • p) ⬝ᵥ (A *ᵥ (z + t • p)) = z ⬝ᵥ (A *ᵥ z) + t * (z ⬝ᵥ (A *ᵥ p)) +
      t * (p ⬝ᵥ (A *ᵥ z)) + t ^ 2 * (p ⬝ᵥ (A *ᵥ p)) := by
  simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul]
  ring

omit [DecidableEq V] in
lemma norm_expand (z p : V → ℝ) (t : ℝ) :
    (z + t • p) ⬝ᵥ (z + t • p) = z ⬝ᵥ z + 2 * t * (z ⬝ᵥ p) + t ^ 2 * (p ⬝ᵥ p) := by
  simp only [dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul,
    dotProduct_comm p z]
  ring

lemma dotProduct_meanStepMatrix (z : V → ℝ) :
    z ⬝ᵥ (meanStepMatrix G *ᵥ z) =
      ∑ v, z v ^ 2 - (2 * (#G.edgeFinset : ℝ))⁻¹ * (z ⬝ᵥ (G.lapMatrix ℝ *ᵥ z)) := by
  simp only [dotProduct, meanStepMatrix_mulVec, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  · simp [sq]
  · exact Finset.sum_congr rfl fun v _ => by ring

omit [DecidableRel G.Adj] in
lemma projOne_add (x : V → ℝ) (v : V) :
    x v = projOne x v + projCut V₁ x v + projRest V₁ x v := by
  simp only [projRest]; ring

namespace IsClusteredRegular
variable (hG : IsClusteredRegular G V₁ d b)
include hG

lemma meanStepMatrix_mulVec_cutVec_aux :
    meanStepMatrix G *ᵥ cutVec V₁ = (1 - (2 * b / d : ℝ) / Fintype.card V) • cutVec V₁ := by
  have hd : (d : ℝ) ≠ 0 := by have := hG.d_pos; positivity
  have hn := hG.card_pos_real.ne'
  funext v
  rw [meanStepMatrix_mulVec, hG.lapMatrix_mulVec_cutVec, hG.two_mul_card_edgeFinset]
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp

lemma meanStepMatrix_pow_mulVec_cutVec (t : ℕ) :
    meanStepMatrix G ^ t *ᵥ cutVec V₁ =
      (1 - (2 * b / d : ℝ) / Fintype.card V) ^ t • cutVec V₁ := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, hG.meanStepMatrix_mulVec_cutVec_aux, smul_smul,
      pow_succ]

lemma cutVec_dot_meanStepMatrix (z : V → ℝ) :
    ∑ v, cutVec V₁ v * (meanStepMatrix G *ᵥ z) v =
      (1 - (2 * b / d : ℝ) / Fintype.card V) * ∑ v, cutVec V₁ v * z v := by
  have h := dotProduct_meanStepMatrix_comm (G := G) (cutVec V₁) z
  rw [hG.meanStepMatrix_mulVec_cutVec_aux] at h
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul] at h
  rw [h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun v _ => by ring

/-- `W̄` maps the orthogonal complement of `𝟙` and `χ` to itself. -/
lemma meanStepMatrix_pow_mulVec_compl (z : V → ℝ) (hz : ∑ v, z v = 0)
    (hχ : ∑ v, cutVec V₁ v * z v = 0) (t : ℕ) :
    ∑ v, (meanStepMatrix G ^ t *ᵥ z) v = 0 ∧
      ∑ v, cutVec V₁ v * (meanStepMatrix G ^ t *ᵥ z) v = 0 := by
  induction t with
  | zero => simpa using ⟨hz, hχ⟩
  | succ t ih =>
    rw [pow_succ', ← mulVec_mulVec, sum_meanStepMatrix_mulVec, hG.cutVec_dot_meanStepMatrix,
      ih.2, mul_zero]
    exact ⟨ih.1, rfl⟩

lemma beta_pos (h3 : ThirdEigenvalueLB G V₁ d lam3) : 0 < 1 - lam3 / Fintype.card V := by
  have h2 := hG.lam3_le_two h3
  have hn : (4 : ℝ) ≤ Fintype.card V := by exact_mod_cast hG.four_le_card
  rw [sub_pos, div_lt_one (by linarith)]
  linarith

lemma half_le_beta (h3 : ThirdEigenvalueLB G V₁ d lam3) : 1 / 2 ≤ 1 - lam3 / Fintype.card V := by
  have h2 := hG.lam3_le_two h3
  have hn : (4 : ℝ) ≤ Fintype.card V := by exact_mod_cast hG.four_le_card
  have : lam3 / Fintype.card V ≤ 1 / 2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  linarith

/-- The Rayleigh bounds of `W̄`: at most `λ̄₃ = 1 - λ₃/n` on the complement of `𝟙, χ`, and at
least `-λ̄₃` everywhere. -/
lemma dotProduct_meanStepMatrix_le (h3 : ThirdEigenvalueLB G V₁ d lam3) (z : V → ℝ)
    (hz : ∑ v, z v = 0) (hχ : ∑ v, cutVec V₁ v * z v = 0) :
    z ⬝ᵥ (meanStepMatrix G *ᵥ z) ≤ (1 - lam3 / Fintype.card V) * ∑ v, z v ^ 2 := by
  have hd : (0 : ℝ) < d := by exact_mod_cast hG.d_pos
  have hn := hG.card_pos_real
  have hL := h3 z hz hχ
  rw [dotProduct_meanStepMatrix, hG.two_mul_card_edgeFinset]
  set S := ∑ v, z v ^ 2
  set Q := z ⬝ᵥ (G.lapMatrix ℝ *ᵥ z)
  have : lam3 / Fintype.card V * S ≤ (Fintype.card V * d : ℝ)⁻¹ * Q := by
    rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
    calc lam3 / Fintype.card V * S * (Fintype.card V * d) = lam3 * d * S := by field_simp
      _ ≤ Q := hL
  linarith

lemma neg_le_dotProduct_meanStepMatrix (h3 : ThirdEigenvalueLB G V₁ d lam3) (z : V → ℝ) :
    -((1 - lam3 / Fintype.card V) * ∑ v, z v ^ 2) ≤ z ⬝ᵥ (meanStepMatrix G *ᵥ z) := by
  have hd : (0 : ℝ) < d := by exact_mod_cast hG.d_pos
  have hn := hG.card_pos_real
  have hn4 : (4 : ℝ) ≤ Fintype.card V := by exact_mod_cast hG.four_le_card
  have h2 := hG.lam3_le_two h3
  have hle := hG.dotProduct_lap_le z
  have hs : 0 ≤ ∑ v, z v ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [dotProduct_meanStepMatrix, hG.two_mul_card_edgeFinset]
  set S := ∑ v, z v ^ 2
  set Q := z ⬝ᵥ (G.lapMatrix ℝ *ᵥ z)
  have h1 : (Fintype.card V * d : ℝ)⁻¹ * Q ≤ 2 / Fintype.card V * S := by
    rw [inv_mul_eq_div, div_le_iff₀ (by positivity)]
    calc Q ≤ 2 * d * S := hle
      _ = 2 / Fintype.card V * S * (Fintype.card V * d) := by field_simp
  have h4 : lam3 / Fintype.card V ≤ 2 / Fintype.card V :=
    div_le_div_of_nonneg_right h2 hn.le
  have h5 : 2 / (Fintype.card V : ℝ) ≤ 1 / 2 := by
    rw [div_le_iff₀ hn]; linarith
  nlinarith

/-- One step of the contraction of Lemma B.1, by polarization. -/
lemma sum_sq_meanStepMatrix_mulVec_le (h3 : ThirdEigenvalueLB G V₁ d lam3) (z : V → ℝ)
    (hz : ∑ v, z v = 0) (hχ : ∑ v, cutVec V₁ v * z v = 0) :
    ∑ v, (meanStepMatrix G *ᵥ z) v ^ 2 ≤ (1 - lam3 / Fintype.card V) ^ 2 * ∑ v, z v ^ 2 := by
  set β := 1 - lam3 / Fintype.card V with hβ
  have hβpos : 0 < β := hG.beta_pos h3
  set A := meanStepMatrix G
  set p := A *ᵥ z
  set ib := β⁻¹
  have hib : β * ib = 1 := mul_inv_cancel₀ hβpos.ne'
  have hp := hG.meanStepMatrix_pow_mulVec_compl z hz hχ 1
  simp only [pow_one] at hp
  have hp1 : ∑ v, p v = 0 := hp.1
  have hc (t : ℝ) : ∑ v, (z + t • p) v = 0 ∧ ∑ v, cutVec V₁ v * (z + t • p) v = 0 := by
    constructor
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, hz, hp1]
      ring
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib, hχ,
        zero_add]
      rw [show ∑ v, cutVec V₁ v * (t * p v) = t * ∑ v, cutVec V₁ v * p v by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => by ring, hp.2, mul_zero]
  have hup := hG.dotProduct_meanStepMatrix_le h3 _ (hc ib).1 (hc ib).2
  have hlow := hG.neg_le_dotProduct_meanStepMatrix h3 (z + (-ib) • p)
  rw [sum_sq_eq_dotProduct, norm_expand, quad_expand] at hup hlow
  have hzAp : z ⬝ᵥ (A *ᵥ p) = p ⬝ᵥ p := dotProduct_meanStepMatrix_comm z p
  have hpAz : p ⬝ᵥ (A *ᵥ z) = p ⬝ᵥ p := rfl
  have hzp : z ⬝ᵥ p = z ⬝ᵥ (A *ᵥ z) := rfl
  rw [hzAp, hpAz, hzp] at hup hlow
  rw [sum_sq_eq_dotProduct, sum_sq_eq_dotProduct]
  set a := z ⬝ᵥ z
  set q := p ⬝ᵥ p
  set s := z ⬝ᵥ (A *ᵥ z)
  set r := p ⬝ᵥ (A *ᵥ p)
  have e1 : β * (a + 2 * ib * s + ib ^ 2 * q) = β * a + 2 * (β * ib) * s + (β * ib) * ib * q := by
    ring
  have e2 : β * (a + 2 * -ib * s + (-ib) ^ 2 * q) =
      β * a - 2 * (β * ib) * s + (β * ib) * ib * q := by ring
  rw [hib] at e1 e2
  have key : ib * q ≤ β * a := by nlinarith
  calc q = β * (ib * q) := by rw [← mul_assoc, hib, one_mul]
    _ ≤ β * (β * a) := mul_le_mul_of_nonneg_left key hβpos.le
    _ = β ^ 2 * a := by ring

lemma sum_sq_lap_le (z : V → ℝ) :
    ∑ v, (G.lapMatrix ℝ *ᵥ z) v ^ 2 ≤ 4 * d ^ 2 * ∑ v, z v ^ 2 := by
  have hd : (0 : ℝ) ≤ d := by positivity
  have h1 : ∀ v, (G.lapMatrix ℝ *ᵥ z) v ^ 2 ≤
      2 * d ^ 2 * z v ^ 2 + 2 * d * ∑ u ∈ G.neighborFinset v, z u ^ 2 := fun v => by
    rw [G.lapMatrix_mulVec_apply, hG.degree_eq]
    have hcs := sq_sum_le_card_mul_sum_sq (s := G.neighborFinset v) (f := z)
    rw [G.card_neighborFinset_eq_degree, hG.degree_eq] at hcs
    nlinarith [sq_nonneg ((d : ℝ) * z v + ∑ u ∈ G.neighborFinset v, z u)]
  calc ∑ v, (G.lapMatrix ℝ *ᵥ z) v ^ 2
      ≤ ∑ v, (2 * d ^ 2 * z v ^ 2 + 2 * d * ∑ u ∈ G.neighborFinset v, z u ^ 2) :=
        Finset.sum_le_sum fun v _ => h1 v
    _ = 4 * d ^ 2 * ∑ v, z v ^ 2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        Averaging.sum_sum_neighbor G (fun u => z u ^ 2)]
      simp_rw [hG.degree_eq, ← Finset.mul_sum]
      ring

/-- The iterated contraction of Lemma B.1. -/
lemma sum_sq_meanStepMatrix_pow_mulVec_le (h3 : ThirdEigenvalueLB G V₁ d lam3) (z : V → ℝ)
    (hz : ∑ v, z v = 0) (hχ : ∑ v, cutVec V₁ v * z v = 0) (t : ℕ) :
    ∑ v, (meanStepMatrix G ^ t *ᵥ z) v ^ 2 ≤
      (1 - lam3 / Fintype.card V) ^ (2 * t) * ∑ v, z v ^ 2 := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hc := hG.meanStepMatrix_pow_mulVec_compl z hz hχ t
    rw [pow_succ', ← mulVec_mulVec]
    calc _ ≤ (1 - lam3 / Fintype.card V) ^ 2 * ∑ v, (meanStepMatrix G ^ t *ᵥ z) v ^ 2 :=
          hG.sum_sq_meanStepMatrix_mulVec_le h3 _ hc.1 hc.2
      _ ≤ (1 - lam3 / Fintype.card V) ^ 2 * ((1 - lam3 / Fintype.card V) ^ (2 * t) *
            ∑ v, z v ^ 2) := mul_le_mul_of_nonneg_left ih (sq_nonneg _)
      _ = _ := by ring

lemma expList_avgRun_decomp_aux (x : V → ℝ) (t : ℕ) (v : V) :
    expList G.Dart t (fun l => avgRun G x l v) =
      projOne x v + (1 - (2 * b / d : ℝ) / Fintype.card V) ^ t * projCut V₁ x v +
        (meanStepMatrix G ^ t *ᵥ projRest V₁ x) v := by
  haveI := hG.nonempty_dart
  rw [expList_avgRun]
  have hx : x = (fun _ => avg x) + avg (fun w => cutVec V₁ w * x w) • cutVec V₁ +
      projRest V₁ x := by
    funext w; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; exact projOne_add x w
  conv_lhs => rw [hx]
  rw [mulVec_add, mulVec_add, mulVec_smul, meanStepMatrix_pow_mulVec_const,
    hG.meanStepMatrix_pow_mulVec_cutVec]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, projOne, projCut]
  ring

end IsClusteredRegular

lemma dotProduct_meanStepMatrix_pow_comm (x y : V → ℝ) (t : ℕ) :
    x ⬝ᵥ (meanStepMatrix G ^ t *ᵥ y) = (meanStepMatrix G ^ t *ᵥ x) ⬝ᵥ y := by
  induction t generalizing x y with
  | zero => simp
  | succ t ih =>
    rw [pow_succ, ← mulVec_mulVec, ih, dotProduct_meanStepMatrix_comm, mulVec_mulVec,
      ← pow_succ', ← pow_succ]

omit [DecidableEq V] in
/-- The sum of `n` signs `±1` has the parity of `n`. -/
lemma sum_units_eq (τ : V → ℤˣ) :
    ∑ v, ((τ v : ℤ) : ℝ) = Fintype.card V - 2 * #{v | τ v = -1} := by
  have h : ∀ v, ((τ v : ℤ) : ℝ) = 1 - 2 * (if τ v = -1 then 1 else 0) := fun v => by
    rcases Int.units_eq_one_or (τ v) with h | h
    · simp [h]
    · simp [h]; norm_num
  simp_rw [h, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole]
  simp

/-- The cut vector as a vector of units. -/
def cutUnit (V₁ : Finset V) : V → ℤˣ := fun v => if v ∈ V₁ then 1 else -1

omit [Fintype V] in
lemma cutVec_mul_signVec (σ : V → ℤˣ) (v : V) :
    cutVec V₁ v * signVec σ v = signVec (cutUnit V₁ * σ) v := by
  simp only [cutVec, signVec, cutUnit, Pi.mul_apply]
  split_ifs <;> simp

lemma two_le_abs_sum_cutVec (hG : IsClusteredRegular G V₁ d b) (σ : V → ℤˣ)
    (h : ∑ v, cutVec V₁ v * signVec σ v ≠ 0) : 2 ≤ |∑ v, cutVec V₁ v * signVec σ v| := by
  simp_rw [cutVec_mul_signVec] at h ⊢
  simp only [signVec] at h ⊢
  rw [sum_units_eq] at h ⊢
  set k := #{v | (cutUnit V₁ * σ) v = -1}
  have hc := hG.card_eq
  have : (Fintype.card V : ℝ) - 2 * k = 2 * ((#V₁ : ℤ) - k : ℤ) := by
    push_cast; rw [← hc]; push_cast; ring
  rw [this] at h ⊢
  have hne : ((#V₁ : ℤ) - k) ≠ 0 := by
    intro h0; apply h; rw [show (((#V₁ : ℤ) - k : ℤ) : ℝ) = 0 by exact_mod_cast h0]; ring
  have h1 : (1 : ℝ) ≤ |(((#V₁ : ℤ) - k : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hne
  rw [abs_mul, abs_two]; linarith

lemma sign_add_of_sq_lt {m e : ℝ} (h : e ^ 2 < m ^ 2) :
    SignType.sign (m + e) = SignType.sign m := by
  have h' := sq_lt_sq.mp h
  rcases lt_trichotomy m 0 with hm | hm | hm
  · rw [abs_of_neg hm] at h'
    rw [sign_neg hm, sign_neg (by linarith [neg_abs_le e, le_abs_self e])]
  · subst hm; simp at h'; linarith [abs_nonneg e]
  · rw [abs_of_pos hm] at h'
    rw [sign_pos hm, sign_pos (by linarith [neg_abs_le e])]

omit [DecidableEq V] in
lemma sq_le_sum_sq (f : V → ℝ) (u : V) : f u ^ 2 ≤ ∑ v, f v ^ 2 :=
  Finset.single_le_sum (f := fun v => f v ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ u)

omit [DecidableEq V] in
lemma sum_sq_signVec (σ : V → ℤˣ) : ∑ v, signVec σ v ^ 2 = Fintype.card V := by
  have : ∀ v, signVec σ v ^ 2 = 1 := fun v => by
    rcases Int.units_eq_one_or (σ v) with h | h <;> simp [signVec, h]
  simp [this]

namespace IsClusteredRegular
variable (hG : IsClusteredRegular G V₁ d b)
include hG

lemma expList_projCut_aux (x : V → ℝ) (t : ℕ) (v : V) :
    expList G.Dart t (fun l => projCut V₁ (avgRun G x l) v) =
      (1 - (2 * b / d : ℝ) / Fintype.card V) ^ t * projCut V₁ x v := by
  haveI := hG.nonempty_dart
  have h : ∀ l, projCut V₁ (avgRun G x l) v =
      ∑ w, (cutVec V₁ v / Fintype.card V * cutVec V₁ w) * avgRun G x l w := by
    intro l
    simp only [projCut, avg, Finset.sum_div, Finset.sum_mul]
    exact Finset.sum_congr rfl fun w _ => by ring
  simp_rw [h]
  rw [expList_sum]
  simp_rw [expList_const_mul, expList_avgRun]
  have h2 := dotProduct_meanStepMatrix_pow_comm (G := G) (cutVec V₁) x t
  rw [hG.meanStepMatrix_pow_mulVec_cutVec] at h2
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul] at h2
  have h3 : ∑ w, cutVec V₁ v / Fintype.card V * cutVec V₁ w * (meanStepMatrix G ^ t *ᵥ x) w =
      cutVec V₁ v / Fintype.card V * ∑ w, cutVec V₁ w * (meanStepMatrix G ^ t *ᵥ x) w := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun w _ => by ring
  rw [h3, h2]
  simp only [projCut, avg]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  ring

lemma sign_criterion_aux (h3 : ThirdEigenvalueLB G V₁ d lam3)
    (σ : V → ℤˣ) (t : ℕ)
    (h1 : (Fintype.card V : ℝ) * (1 - lam3 / Fintype.card V) ^ t ≤ |avg (signVec σ)|)
    (h2 : 2 * |avg (signVec σ)| <
      |avg (fun w => cutVec V₁ w * signVec σ w)| * (1 - (2 * b / d : ℝ) / Fintype.card V) ^ t)
    (u : V) :
    SignType.sign (expList G.Dart t (fun l => avgRun G (signVec σ) l u)) =
      SignType.sign (avg (fun w => cutVec V₁ w * signVec σ w) * cutVec V₁ u) := by
  set n : ℝ := (Fintype.card V : ℝ)
  set L2 : ℝ := 1 - (2 * b / d : ℝ) / n
  set β : ℝ := 1 - lam3 / n
  set α1 := avg (signVec σ)
  set α2 := avg (fun w => cutVec V₁ w * signVec σ w)
  set z0 := projRest V₁ (signVec σ)
  have hn1 : (1 : ℝ) ≤ n := by have := hG.four_le_card; simp only [n]; exact_mod_cast (by omega)
  have hβ := hG.beta_pos h3
  have hL2 : 0 < L2 := by
    have := hG.b_lt_d_real
    have : (2 * b / d : ℝ) / n < 1 := by rw [div_lt_one (by linarith)]; linarith
    simp only [L2]; linarith
  rw [hG.expList_avgRun_decomp_aux (signVec σ) t u]
  set e := (meanStepMatrix G ^ t *ᵥ z0) u
  have hz0 : ∑ v, z0 v = 0 := hG.sum_projRest (signVec σ)
  have hz0' : ∑ v, cutVec V₁ v * z0 v = 0 := hG.sum_cutVec_mul_projRest (signVec σ)
  have he : e ^ 2 ≤ α1 ^ 2 := by
    have h1' := sq_le_sum_sq (meanStepMatrix G ^ t *ᵥ z0) u
    have h2' := hG.sum_sq_meanStepMatrix_pow_mulVec_le h3 z0 hz0 hz0' t
    have h3' := hG.sum_sq_projRest_le (signVec σ)
    rw [sum_sq_signVec] at h3'
    have hbt : 0 ≤ β ^ t := pow_nonneg hβ.le t
    calc e ^ 2 ≤ β ^ (2 * t) * ∑ v, z0 v ^ 2 := h1'.trans h2'
      _ ≤ β ^ (2 * t) * n := mul_le_mul_of_nonneg_left h3' (by positivity)
      _ ≤ (n * β ^ t) ^ 2 := by rw [pow_mul']; nlinarith [sq_nonneg (β ^ t)]
      _ ≤ α1 ^ 2 := by
        rw [← sq_abs α1]
        exact pow_le_pow_left₀ (by positivity) h1 2
  have hrest : |α1 + e| ≤ 2 * |α1| := by
    have : |e| ≤ |α1| := sq_le_sq.mp he
    calc |α1 + e| ≤ |α1| + |e| := abs_add_le _ _
      _ ≤ 2 * |α1| := by linarith
  have hmain : |L2 ^ t * (α2 * cutVec V₁ u)| = |α2| * L2 ^ t := by
    rw [abs_mul, abs_mul, abs_cutVec, abs_of_pos (pow_pos hL2 t)]; ring
  have key : (α1 + e) ^ 2 < (L2 ^ t * (α2 * cutVec V₁ u)) ^ 2 := by
    rw [sq_lt_sq, hmain]; linarith
  simp only [projOne, projCut]
  rw [show α1 + L2 ^ t * (α2 * cutVec V₁ u) + e = L2 ^ t * (α2 * cutVec V₁ u) + (α1 + e) by ring,
    sign_add_of_sq_lt key, sign_mul, sign_pos (pow_pos hL2 t), one_mul]

lemma monotone_criterion_aux (h3 : ThirdEigenvalueLB G V₁ d lam3) (σ : V → ℤˣ)
    (hσ : avg (fun w => cutVec V₁ w * signVec σ w) ≠ 0) (t : ℕ)
    (ht : (Fintype.card V : ℝ) ^ 3 * (1 - lam3 / Fintype.card V) ^ t ≤
      (1 - (2 * b / d : ℝ) / Fintype.card V) ^ t) (u : V) :
    SignType.sign (expList G.Dart (t - 1) (fun l => avgRun G (signVec σ) l u) -
        expList G.Dart t (fun l => avgRun G (signVec σ) l u)) =
      SignType.sign (avg (fun w => cutVec V₁ w * signVec σ w) * cutVec V₁ u) := by
  set n : ℝ := (Fintype.card V : ℝ)
  set L2 : ℝ := 1 - (2 * b / d : ℝ) / n
  set β : ℝ := 1 - lam3 / n
  set α2 := avg (fun w => cutVec V₁ w * signVec σ w)
  set z0 := projRest V₁ (signVec σ)
  have hn4 : (4 : ℝ) ≤ n := by simp only [n]; exact_mod_cast hG.four_le_card
  have hβ : 0 < β := hG.beta_pos h3
  have hβ2 : 1 / 2 ≤ β := hG.half_le_beta h3
  have hl : 2 / n < (2 * b / d : ℝ) := hG.two_div_card_lt
  have hl1 := hG.b_lt_d_real
  have hlpos : 0 < (2 * b / d : ℝ) / n :=
    div_pos (lt_trans (by positivity) hl) (by linarith)
  have hL2 : 0 < L2 := by
    have : (2 * b / d : ℝ) / n < 1 := by rw [div_lt_one (by linarith)]; linarith
    simp only [L2]; linarith
  have hL2le : L2 ≤ 1 := by
    have : 0 ≤ (2 * b / d : ℝ) / n := by positivity
    simp only [L2]; linarith
  -- `t ≥ 1`
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := by
    rcases t with _ | s
    · simp at ht; nlinarith [pow_le_pow_left₀ (by norm_num) hn4 3]
    · exact ⟨s, rfl⟩
  rw [Nat.add_sub_cancel, hG.expList_avgRun_decomp_aux (signVec σ) s u,
    hG.expList_avgRun_decomp_aux (signVec σ) (s + 1) u]
  -- the deviation `e = (W̄ˢ (z₀ - W̄ z₀))_u`
  set r := z0 - meanStepMatrix G *ᵥ z0
  have hz0 : ∑ v, z0 v = 0 := hG.sum_projRest (signVec σ)
  have hz0' : ∑ v, cutVec V₁ v * z0 v = 0 := hG.sum_cutVec_mul_projRest (signVec σ)
  have hW := hG.meanStepMatrix_pow_mulVec_compl z0 hz0 hz0' 1
  simp only [pow_one] at hW
  have hr1 : ∑ v, r v = 0 := by simp [r, Finset.sum_sub_distrib, hz0, hW.1]
  have hr2 : ∑ v, cutVec V₁ v * r v = 0 := by
    simp [r, mul_sub, Finset.sum_sub_distrib, hz0', hW.2]
  have hdiff : (meanStepMatrix G ^ s *ᵥ z0) u - (meanStepMatrix G ^ (s + 1) *ᵥ z0) u =
      (meanStepMatrix G ^ s *ᵥ r) u := by
    rw [pow_succ, ← mulVec_mulVec, mulVec_sub]; rfl
  set e := (meanStepMatrix G ^ s *ᵥ r) u
  -- `‖r‖² ≤ 4/n`
  have hr : ∑ v, r v ^ 2 ≤ 4 / n := by
    have hd : (0 : ℝ) < d := by exact_mod_cast hG.d_pos
    have hrv : ∀ v, r v = (n * d)⁻¹ * (G.lapMatrix ℝ *ᵥ z0) v := fun v => by
      simp only [r, Pi.sub_apply, meanStepMatrix_mulVec, hG.two_mul_card_edgeFinset]; ring
    have hL := hG.sum_sq_lap_le z0
    have h3' := hG.sum_sq_projRest_le (signVec σ)
    rw [sum_sq_signVec] at h3'
    simp_rw [hrv, mul_pow, ← Finset.mul_sum]
    calc (n * d)⁻¹ ^ 2 * ∑ v, (G.lapMatrix ℝ *ᵥ z0) v ^ 2
        ≤ (n * d)⁻¹ ^ 2 * (4 * d ^ 2 * n) :=
          mul_le_mul_of_nonneg_left (hL.trans (mul_le_mul_of_nonneg_left h3' (by positivity)))
            (by positivity)
      _ = 4 / n := by field_simp
  have he : e ^ 2 ≤ β ^ (2 * s) * (4 / n) :=
    (sq_le_sum_sq _ u).trans ((hG.sum_sq_meanStepMatrix_pow_mulVec_le h3 r hr1 hr2 s).trans
      (mul_le_mul_of_nonneg_left hr (by positivity)))
  -- `β^s ≤ 2 L2^s / n³`
  have hbs : β ^ s ≤ 2 * L2 ^ s / n ^ 3 := by
    have h1 : n ^ 3 * β ^ s * β ≤ L2 ^ s * L2 := by rw [mul_assoc, ← pow_succ, ← pow_succ]; exact ht
    rw [le_div_iff₀ (by positivity)]
    have : L2 ^ s * L2 ≤ L2 ^ s := mul_le_of_le_one_right (pow_nonneg hL2.le s) hL2le
    nlinarith [mul_le_mul_of_nonneg_left hβ2 (by positivity : (0 : ℝ) ≤ n ^ 3 * β ^ s)]
  have hα2 : 2 / n ≤ |α2| := by
    have h2 := two_le_abs_sum_cutVec hG σ (fun h => hσ (by simp [α2, avg, h]))
    have e : α2 = (∑ v, cutVec V₁ v * signVec σ v) / n := rfl
    rw [e, abs_div, abs_of_pos (by linarith : (0 : ℝ) < n)]
    exact div_le_div_of_nonneg_right h2 (by linarith)
  -- the main term dominates
  set m := L2 ^ s * ((2 * b / d : ℝ) / n) * (α2 * cutVec V₁ u)
  have hm : |m| = L2 ^ s * ((2 * b / d : ℝ) / n) * |α2| := by
    simp only [m, abs_mul, abs_cutVec, abs_of_pos (pow_pos hL2 s), mul_one,
      abs_of_pos hlpos]
  have hm2 : 4 * L2 ^ s / n ^ 3 < |m| := by
    rw [hm]
    have hln : 2 / n ^ 2 < (2 * b / d : ℝ) / n := by
      rw [show 2 / n ^ 2 = (2 / n) / n by ring]
      exact div_lt_div_of_pos_right hl (by linarith)
    calc 4 * L2 ^ s / n ^ 3 = L2 ^ s * (2 / n ^ 2) * (2 / n) := by field_simp; ring
      _ < L2 ^ s * ((2 * b / d : ℝ) / n) * (2 / n) := by
        gcongr
      _ ≤ L2 ^ s * ((2 * b / d : ℝ) / n) * |α2| := by gcongr
  have key : e ^ 2 < m ^ 2 := by
    have hbs2 : β ^ (2 * s) ≤ (2 * L2 ^ s / n ^ 3) ^ 2 := by
      rw [pow_mul', ← sq_abs (β ^ s), abs_of_nonneg (pow_nonneg hβ.le s)]
      exact pow_le_pow_left₀ (pow_nonneg hβ.le s) hbs 2
    calc e ^ 2 ≤ (2 * L2 ^ s / n ^ 3) ^ 2 * (4 / n) :=
          he.trans (mul_le_mul_of_nonneg_right hbs2 (by positivity))
      _ = (4 * L2 ^ s / n ^ 3) ^ 2 / n := by ring
      _ ≤ (4 * L2 ^ s / n ^ 3) ^ 2 := div_le_self (sq_nonneg _) (by linarith)
      _ < |m| ^ 2 := pow_lt_pow_left₀ hm2 (by positivity) (by norm_num)
      _ = m ^ 2 := sq_abs m
  simp only [projOne, projCut]
  rw [show avg (signVec σ) + L2 ^ s * (α2 * cutVec V₁ u) + (meanStepMatrix G ^ s *ᵥ z0) u -
      (avg (signVec σ) + L2 ^ (s + 1) * (α2 * cutVec V₁ u) +
        (meanStepMatrix G ^ (s + 1) *ᵥ z0) u) = m + e by
    rw [← hdiff]; simp only [m, L2]; ring]
  rw [sign_add_of_sq_lt key, sign_mul, sign_mul, sign_pos (pow_pos hL2 s),
    sign_pos hlpos, one_mul, one_mul]

end IsClusteredRegular

/-! ### The pinned statements -/

/-- Section 4.1: on an `(n, d, b)`-clustered regular graph, `W̄ χ = (1 - λ₂/n) χ` with
`λ₂ = 2b/d`. -/
theorem meanStepMatrix_mulVec_cutVec (hG : IsClusteredRegular G V₁ d b) :
    meanStepMatrix G *ᵥ cutVec V₁ = (1 - (2 * b / d : ℝ) / Fintype.card V) • cutVec V₁ :=
  hG.meanStepMatrix_mulVec_cutVec_aux

/-- Equation (12) with `δ = 1/2`: the expected component along `χ` decays geometrically,
`E[y⁽ᵗ⁾] = (1 - λ₂/n)ᵗ y⁽⁰⁾`. -/
theorem expList_projCut (hG : IsClusteredRegular G V₁ d b) (x : V → ℝ) (t : ℕ) (v : V) :
    expList G.Dart t (fun l => projCut V₁ (avgRun G x l) v) =
      (1 - (2 * b / d : ℝ) / Fintype.card V) ^ t * projCut V₁ x v :=
  hG.expList_projCut_aux x t v

/-- Lemma B.1 (main decomposition) on a clustered regular graph:
`E[x⁽ᵗ⁾ | x⁽⁰⁾ = x] = x_∥ + (1 - λ₂/n)ᵗ y + e⁽ᵗ⁾` with `e⁽ᵗ⁾ = W̄ᵗ z`. -/
theorem expList_avgRun_decomp (hG : IsClusteredRegular G V₁ d b) (x : V → ℝ) (t : ℕ) (v : V) :
    expList G.Dart t (fun l => avgRun G x l v) =
      projOne x v + (1 - (2 * b / d : ℝ) / Fintype.card V) ^ t * projCut V₁ x v +
        (meanStepMatrix G ^ t *ᵥ projRest V₁ x) v :=
  hG.expList_avgRun_decomp_aux x t v

/-- The bound of Lemma B.1 on `e⁽ᵗ⁾`: on the vectors orthogonal to `𝟙` and `χ`, `W̄ᵗ` contracts the
norm by `λ̄₃ᵗ`, where `λ̄₃ = 1 - λ₃/n` is the third eigenvalue of `W̄`. -/
theorem sum_sq_meanStepMatrix_pow_le (hG : IsClusteredRegular G V₁ d b)
    (h3 : ThirdEigenvalueLB G V₁ d lam3) (z : V → ℝ) (hz : ∑ v, z v = 0)
    (hχ : ∑ v, cutVec V₁ v * z v = 0) (t : ℕ) :
    ∑ v, (meanStepMatrix G ^ t *ᵥ z) v ^ 2 ≤
      (1 - lam3 / Fintype.card V) ^ (2 * t) * ∑ v, z v ^ 2 :=
  hG.sum_sq_meanStepMatrix_pow_mulVec_le h3 z hz hχ t

/-- Lemma B.3 (monotonicity property) on a clustered regular graph, where no node is bad: for an
initial vector `x ∈ {-1, 1}ⁿ` with `α₂ = ⟨x, χ⟩/n ≠ 0` and every round `t` with
`t ≥ 3 log n / log (λ̄₂/λ̄₃)` (that is, `n³ λ̄₃ᵗ ≤ λ̄₂ᵗ`, where `λ̄₂ = 1 - λ₂/n` and
`λ̄₃ = 1 - λ₃/n`), the expected value of every node `u` moves in the direction given by its
community: `sgn(E[x⁽ᵗ⁻¹⁾_u] - E[x⁽ᵗ⁾_u]) = sgn(α₂ χ_u)`. -/
theorem monotone_criterion (hG : IsClusteredRegular G V₁ d b)
    (h3 : ThirdEigenvalueLB G V₁ d lam3) (σ : V → ℤˣ)
    (hσ : avg (fun w => cutVec V₁ w * signVec σ w) ≠ 0) (t : ℕ)
    (ht : (Fintype.card V : ℝ) ^ 3 * (1 - lam3 / Fintype.card V) ^ t ≤
      (1 - (2 * b / d : ℝ) / Fintype.card V) ^ t) (u : V) :
    SignType.sign (expList G.Dart (t - 1) (fun l => avgRun G (signVec σ) l u) -
        expList G.Dart t (fun l => avgRun G (signVec σ) l u)) =
      SignType.sign (avg (fun w => cutVec V₁ w * signVec σ w) * cutVec V₁ u) :=
  hG.monotone_criterion_aux h3 σ hσ t ht u

/-- Lemma B.4 (sign property) on a clustered regular graph, where no node is bad: for an initial
vector `x ∈ {-1, 1}ⁿ` with averages `α₁ = ⟨x, 𝟙⟩/n` and `α₂ = ⟨x, χ⟩/n`, and every round `t` in the
window `log (n/|α₁|) / log (1/λ̄₃) ≤ t` (that is, `n λ̄₃ᵗ ≤ |α₁|`) and `2|α₁| < |α₂| λ̄₂ᵗ`, the
sign of the expected value of every node `u` is `sgn(α₂ χ_u)`. -/
theorem sign_criterion (hG : IsClusteredRegular G V₁ d b) (h3 : ThirdEigenvalueLB G V₁ d lam3)
    (σ : V → ℤˣ) (t : ℕ)
    (h1 : (Fintype.card V : ℝ) * (1 - lam3 / Fintype.card V) ^ t ≤ |avg (signVec σ)|)
    (h2 : 2 * |avg (signVec σ)| <
      |avg (fun w => cutVec V₁ w * signVec σ w)| * (1 - (2 * b / d : ℝ) / Fintype.card V) ^ t)
    (u : V) :
    SignType.sign (expList G.Dart t (fun l => avgRun G (signVec σ) l u)) =
      SignType.sign (avg (fun w => cutVec V₁ w * signVec σ w) * cutVec V₁ u) :=
  hG.sign_criterion_aux h3 σ t h1 h2 u

end Averaging.Opportunistic
