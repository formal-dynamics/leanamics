import Voter.Model

/-! # Uniform neighbor sampling and degree weights (Corollary 2.2) -/
namespace Voter
open Finset Dynamics
variable {V : Type*} [Fintype V] [Nonempty V]

/-- Uniform sampling among adjacent vertices. -/
noncomputable def uniformNeighbor (G : SimpleGraph V) [DecidableRel G.Adj]
    (hd : ∀ i, 0 < G.degree i) : Kernel V := fun i => {
  weight := fun j => if G.Adj i j then (G.degree i : ℝ)⁻¹ else 0
  nonneg := fun j => by split <;> positivity
  sum_one := by
    rw [← Finset.sum_filter]
    have he : univ.filter (G.Adj i) = G.neighborFinset i := by ext j; simp
    rw [he]
    simp [ne_of_gt (hd i)] }

/-- Total degree, equal to twice the number of undirected edges. -/
noncomputable def volume (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ := ∑ i, (G.degree i : ℝ)

lemma volume_pos (G : SimpleGraph V) [DecidableRel G.Adj] (hd : ∀ i, 0 < G.degree i) :
    0 < volume G := sum_pos (fun i _ => by exact_mod_cast hd i) univ_nonempty

omit [Nonempty V] in
lemma volume_eq_twice_edges (G : SimpleGraph V) [DecidableRel G.Adj] :
    volume G = 2 * (G.edgeFinset.card : ℝ) := by
  unfold volume
  exact_mod_cast G.sum_degrees_eq_twice_card_edges

/-- The normalized degree distribution. -/
noncomputable def degreeDistribution (G : SimpleGraph V) [DecidableRel G.Adj]
    (hd : ∀ i, 0 < G.degree i) : Distribution V where
  weight i := (G.degree i : ℝ) / volume G
  nonneg i := div_nonneg (by positivity) (volume_pos G hd).le
  sum_one := by rw [← sum_div]; exact div_self (volume_pos G hd).ne'

lemma degree_weight (G : SimpleGraph V) [DecidableRel G.Adj] (hd : ∀ i, 0 < G.degree i)
    (i : V) : (degreeDistribution G hd).weight i = (G.degree i : ℝ) / (2 * G.edgeFinset.card) := by
  simp [degreeDistribution, volume_eq_twice_edges]

/-- Degree weights are stationary for uniform neighbor sampling. -/
theorem degree_stationary (G : SimpleGraph V) [DecidableRel G.Adj]
    (hd : ∀ i, 0 < G.degree i) : (uniformNeighbor G hd).Stationary (degreeDistribution G hd) := by
  intro j
  change (∑ i, ((G.degree i : ℝ) / volume G) *
    (if G.Adj i j then (G.degree i : ℝ)⁻¹ else 0)) = (G.degree j : ℝ) / volume G
  have h (i : V) : ((G.degree i : ℝ) / volume G) *
      (if G.Adj i j then (G.degree i : ℝ)⁻¹ else 0) =
      if G.Adj j i then (volume G)⁻¹ else 0 := by
    simp only [G.adj_comm i j]
    split
    · have hi : (G.degree i : ℝ) ≠ 0 := by exact_mod_cast (hd i).ne'
      field_simp
    · simp
  simp_rw [h]
  rw [← sum_filter]
  have he : univ.filter (G.Adj j) = G.neighborFinset j := by ext i; simp
  rw [he]
  simp [div_eq_mul_inv]

/-- Regular graphs give the uniform vertex distribution. -/
lemma degree_mass_regular (G : SimpleGraph V) [DecidableRel G.Adj]
    (hd : ∀ i, 0 < G.degree i) (d : ℕ) (hreg : ∀ i, G.degree i = d)
    (s : Config V Bool) :
    mass (degreeDistribution G hd) (fun b => if b then 1 else 0) s =
      ((univ.filter fun i => s i = true).card : ℝ) / Fintype.card V := by
  have hvol : volume G = (Fintype.card V : ℝ) * d := by simp [volume, hreg]
  have hdpos : (0 : ℝ) < d := by
    obtain ⟨i⟩ := ‹Nonempty V›
    exact_mod_cast hreg i ▸ hd i
  have hw (i : V) : (degreeDistribution G hd).weight i = (Fintype.card V : ℝ)⁻¹ := by
    simp only [degreeDistribution, hreg, hvol]
    field_simp
  change (∑ i, (degreeDistribution G hd).weight i * (if s i then 1 else 0)) = _
  simp_rw [hw]
  rw [← mul_sum, sum_boole]
  rw [div_eq_mul_inv, mul_comm]

end Voter
