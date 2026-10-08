import Median.ExpanderDefs

/-! # The expander mixing lemma

The expander mixing lemma (Alon and Chung 1988; Lemma 5 of Cooper, Elsässer and Radzik) for a
`d`-regular graph, with `λ_G = max {λ₂, |λₙ|}` computed from Mathlib's sorted eigenvalues of
the transition matrix `P = A / d`:

  `|E(S, T) − d |S| |T| / n| ≤ λ_G d √(|S| |T|)`.

Proof. With an orthonormal eigenbasis `b₁, …, bₙ` of `P` (Mathlib's `eigenvectorBasis`) and the
coefficients `sₖ = bₖ ⬝ 1_S`, `tₖ = bₖ ⬝ 1_T`, Parseval gives
`1_S ⬝ P 1_T = ∑ₖ μₖ sₖ tₖ`. The all-ones vector satisfies `P 1 = 1`; when `λ_G < 1`, every
eigenvector other than the top one `b_{k₀}` has an eigenvalue `≤ λ₂ < 1`, hence is orthogonal to
`1`. So `1` is a multiple `c b_{k₀}` with `c² = n`, the top term is `μ_{k₀} s_{k₀} t_{k₀} =
|S| |T| / n`, and the other terms are bounded by Cauchy-Schwarz,
`|∑_{k ≠ k₀} μₖ sₖ tₖ| ≤ λ_G √(∑ sₖ²) √(∑ tₖ²) = λ_G √(|S| |T|)`. When `λ_G ≥ 1` the bound is
trivial (`0 ≤ E(S, T) ≤ d min (|S|, |T|)`).
-/

namespace Median
open Finset Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Spectral facts for a real symmetric matrix -/

section Spectral
variable {A : Matrix V V ℝ} (hA : A.IsHermitian)

omit [DecidableEq V] in
/-- Completeness of the eigenbasis: `∑ₖ bₖ(u) bₖ(v) = δᵤᵥ`. -/
private lemma sum_eigvec_mul_eigvec [DecidableEq V] (u v : V) :
    ∑ k, hA.eigenvectorBasis k u * hA.eigenvectorBasis k v = if u = v then 1 else 0 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2) u) v
  simpa [Matrix.mul_apply, one_apply] using h

/-- Parseval: `y ⬝ z = ∑ₖ (bₖ ⬝ y)(bₖ ⬝ z)`. -/
lemma dotProduct_eq_sum_eigvec (y z : V → ℝ) :
    y ⬝ᵥ z = ∑ k, (⇑(hA.eigenvectorBasis k) ⬝ᵥ y) * (⇑(hA.eigenvectorBasis k) ⬝ᵥ z) := by
  calc y ⬝ᵥ z = ∑ u, ∑ v, y u * z v * (if u = v then 1 else 0) := by
        simp [dotProduct]
    _ = ∑ u, ∑ v, y u * z v *
          ∑ k, hA.eigenvectorBasis k u * hA.eigenvectorBasis k v := by
        simp_rw [sum_eigvec_mul_eigvec]
    _ = ∑ u, ∑ v, ∑ k, (hA.eigenvectorBasis k u * y u) *
          (hA.eigenvectorBasis k v * z v) := by
        refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
    _ = ∑ u, ∑ k, ∑ v, (hA.eigenvectorBasis k u * y u) *
          (hA.eigenvectorBasis k v * z v) :=
        Finset.sum_congr rfl fun u _ => Finset.sum_comm
    _ = ∑ k, ∑ u, ∑ v, (hA.eigenvectorBasis k u * y u) *
          (hA.eigenvectorBasis k v * z v) := Finset.sum_comm
    _ = _ := by
        simp only [dotProduct, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_comm

/-- The coefficients of `A z`: `bₖ ⬝ (A z) = μₖ (bₖ ⬝ z)`. -/
lemma eigvec_dotProduct_mulVec (k : V) (z : V → ℝ) :
    ⇑(hA.eigenvectorBasis k) ⬝ᵥ (A *ᵥ z) =
      hA.eigenvalues k * (⇑(hA.eigenvectorBasis k) ⬝ᵥ z) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, ← conjTranspose_eq_transpose_of_trivial, hA.eq,
    hA.mulVec_eigenvectorBasis, smul_dotProduct, smul_eq_mul]

/-- Spectral expansion of the bilinear form: `y ⬝ A z = ∑ₖ μₖ (bₖ ⬝ y)(bₖ ⬝ z)`. -/
lemma dotProduct_mulVec_eq_sum_eigvec (y z : V → ℝ) :
    y ⬝ᵥ (A *ᵥ z) = ∑ k, hA.eigenvalues k *
      ((⇑(hA.eigenvectorBasis k) ⬝ᵥ y) * (⇑(hA.eigenvectorBasis k) ⬝ᵥ z)) := by
  rw [dotProduct_eq_sum_eigvec hA]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [eigvec_dotProduct_mulVec hA]
  ring

end Spectral

/-! ### Indicator vectors and edge counts -/

/-- The indicator vector `1_S`. -/
def indVec (S : Finset V) : V → ℝ := fun v => if v ∈ S then 1 else 0

lemma indVec_dotProduct_self (S : Finset V) : indVec S ⬝ᵥ indVec S = S.card := by
  simp only [dotProduct, indVec, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_mem, univ_inter]
  simp

lemma one_dotProduct_indVec (S : Finset V) : (fun _ => (1 : ℝ)) ⬝ᵥ indVec S = S.card := by
  simp [dotProduct, indVec]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `E(S, T) = 1_S ⬝ A 1_T`. -/
lemma edgeCount_eq_dotProduct (S T : Finset V) :
    (edgeCount G S T : ℝ) = indVec S ⬝ᵥ (G.adjMatrix ℝ *ᵥ indVec T) := by
  simp only [dotProduct, SimpleGraph.adjMatrix_mulVec_apply, indVec, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_mem, univ_inter, edgeCount]
  push_cast
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_boole, Finset.filter_mem_eq_inter]

/-- `E(S, T) = d (1_S ⬝ P 1_T)` for the transition matrix `P = A / d`, `d > 0`. -/
lemma edgeCount_eq_transition {d : ℕ} (hd : 0 < d) (S T : Finset V) :
    (edgeCount G S T : ℝ) = d * (indVec S ⬝ᵥ (transitionMatrix G d *ᵥ indVec T)) := by
  rw [edgeCount_eq_dotProduct, transitionMatrix, smul_mulVec, dotProduct_smul, smul_eq_mul,
    ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hd.ne'), one_mul]

/-- `E(S, T) ≤ d |S|` on a `d`-regular graph. -/
lemma edgeCount_le_left {d : ℕ} (hreg : G.IsRegularOfDegree d) (S T : Finset V) :
    edgeCount G S T ≤ d * S.card := by
  unfold edgeCount
  calc ∑ u ∈ S, (G.neighborFinset u ∩ T).card ≤ ∑ _u ∈ S, d :=
        Finset.sum_le_sum fun u _ => by
          rw [← hreg u, ← G.card_neighborFinset_eq_degree]
          exact Finset.card_le_card Finset.inter_subset_left
    _ = d * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- `E(S, T) = E(T, S)`. -/
lemma edgeCount_comm (S T : Finset V) : edgeCount G S T = edgeCount G T S := by
  have h (S T : Finset V) : (edgeCount G S T : ℝ) = ∑ u ∈ S, ∑ w ∈ T, if G.Adj u w then 1 else 0 := by
    unfold edgeCount
    push_cast
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_boole]
    congr 2
    ext w
    simp [and_comm]
  have := h S T
  rw [Finset.sum_comm] at this
  simp_rw [G.adj_comm] at this
  exact_mod_cast this.trans (h T S).symm

omit [DecidableEq V] in
/-- `P 1 = 1` on a `d`-regular graph, `d > 0`. -/
lemma transitionMatrix_mulVec_one {d : ℕ} (hd : 0 < d) (hreg : G.IsRegularOfDegree d) :
    transitionMatrix G d *ᵥ (fun _ => (1 : ℝ)) = fun _ => 1 := by
  funext v
  rw [transitionMatrix, smul_mulVec, Pi.smul_apply, SimpleGraph.adjMatrix_mulVec_apply,
    Finset.sum_const, G.card_neighborFinset_eq_degree, hreg v, smul_eq_mul, nsmul_eq_mul,
    mul_one, inv_mul_cancel₀ (by exact_mod_cast hd.ne')]

omit [DecidableEq V] in
lemma lambdaG_nonneg (d : ℕ) [DecidableEq V] : 0 ≤ lambdaG G d := by
  unfold lambdaG
  split_ifs
  · exact (abs_nonneg _).trans (le_max_right _ _)
  · exact le_rfl

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

/-- The spectral core of the mixing lemma: if `λ_G < 1`, then
`|1_S ⬝ P 1_T − |S| |T| / n| ≤ λ_G √(|S| |T|)`. -/
lemma mixing_transition [Nonempty V] {d : ℕ} (hd : 0 < d) (hreg : G.IsRegularOfDegree d)
    (hL : lambdaG G d < 1) (S T : Finset V) :
    |indVec S ⬝ᵥ (transitionMatrix G d *ᵥ indVec T) - S.card * T.card / Fintype.card V|
      ≤ lambdaG G d * √((S.card : ℝ) * T.card) := by
  have hP := transitionMatrix_isHermitian G d
  set P := transitionMatrix G d with hPdef
  set b : V → V → ℝ := fun k => ⇑(hP.eigenvectorBasis k) with hb
  set μ : V → ℝ := hP.eigenvalues with hμ
  set one : V → ℝ := fun _ => 1 with hone
  have hn : 0 < Fintype.card V := Fintype.card_pos
  set e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card V)) with he
  set k₀ : V := e ⟨0, hn⟩ with hk₀
  have hsmall : ∀ k, k ≠ k₀ → |μ k| ≤ lambdaG G d := by
    intro k hk
    refine abs_eigenvalues_le_lambdaG G d k ?_
    intro h
    apply hk
    rw [hk₀, ← h, Equiv.apply_symm_apply]
  have hP1 : P *ᵥ one = one := transitionMatrix_mulVec_one G hd hreg
  -- the eigenvectors other than the top one are orthogonal to `1`
  have horth : ∀ k, k ≠ k₀ → b k ⬝ᵥ one = 0 := by
    intro k hk
    have h := eigvec_dotProduct_mulVec hP k one
    rw [hP1] at h
    have hμk : μ k < 1 := lt_of_le_of_lt ((le_abs_self _).trans (hsmall k hk)) hL
    have : (1 - μ k) * (b k ⬝ᵥ one) = 0 := by
      simp only [hb, hμ] at h ⊢
      linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · linarith
    · exact h0
  set c := b k₀ ⬝ᵥ one with hc
  have hsum_single (f : V → ℝ) : ∑ k, (b k ⬝ᵥ one) * f k = c * f k₀ := by
    rw [Finset.sum_eq_single k₀ (fun k _ hk => by rw [horth k hk, zero_mul]) (by simp)]
  -- `c² = n`
  have hc2 : c * c = Fintype.card V := by
    have h := dotProduct_eq_sum_eigvec hP one one
    rw [hsum_single] at h
    rw [← h]
    simp [dotProduct, hone]
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, mul_zero] at hc2
    exact (Nat.cast_pos.mpr hn).ne' hc2.symm
  -- `c sₖ₀ = |S|`
  have hcs (S : Finset V) : c * (b k₀ ⬝ᵥ indVec S) = S.card := by
    have h := dotProduct_eq_sum_eigvec hP one (indVec S)
    rw [hsum_single, one_dotProduct_indVec] at h
    exact h.symm
  -- the top eigenvalue is `1`
  have hμ0 : μ k₀ = 1 := by
    have h := eigvec_dotProduct_mulVec hP k₀ one
    rw [hP1] at h
    have : (μ k₀ - 1) * c = 0 := by
      simp only [hb, hμ, hc] at h ⊢
      linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · linarith
    · exact absurd h0 hc0
  set s : V → ℝ := fun k => b k ⬝ᵥ indVec S with hs
  set t : V → ℝ := fun k => b k ⬝ᵥ indVec T with ht
  have hexp := dotProduct_mulVec_eq_sum_eigvec hP (indVec S) (indVec T)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k₀)] at hexp
  have htop : μ k₀ * (s k₀ * t k₀) = S.card * T.card / Fintype.card V := by
    rw [hμ0, one_mul, ← hc2, ← hcs S, ← hcs T]
    field_simp
    rfl
  have hS2 : ∑ k, s k ^ 2 = S.card := by
    have h := dotProduct_eq_sum_eigvec hP (indVec S) (indVec S)
    rw [indVec_dotProduct_self] at h
    rw [h]
    simp only [hs, sq]
    rfl
  have hT2 : ∑ k, t k ^ 2 = T.card := by
    have h := dotProduct_eq_sum_eigvec hP (indVec T) (indVec T)
    rw [indVec_dotProduct_self] at h
    rw [h]
    simp only [ht, sq]
    rfl
  have hL0 := lambdaG_nonneg G d
  have hrest : |∑ k ∈ univ.erase k₀, μ k * (s k * t k)|
      ≤ lambdaG G d * √((S.card : ℝ) * T.card) := by
    calc |∑ k ∈ univ.erase k₀, μ k * (s k * t k)|
        ≤ ∑ k ∈ univ.erase k₀, |μ k * (s k * t k)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ univ.erase k₀, lambdaG G d * (|s k| * |t k|) := by
          refine Finset.sum_le_sum fun k hk => ?_
          rw [abs_mul, abs_mul]
          exact mul_le_mul_of_nonneg_right (hsmall k (Finset.ne_of_mem_erase hk))
            (by positivity)
      _ = lambdaG G d * ∑ k ∈ univ.erase k₀, |s k| * |t k| := by rw [Finset.mul_sum]
      _ ≤ lambdaG G d * (√(∑ k ∈ univ.erase k₀, |s k| ^ 2) *
            √(∑ k ∈ univ.erase k₀, |t k| ^ 2)) :=
          mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt _ _ _) hL0
      _ ≤ lambdaG G d * (√(∑ k, s k ^ 2) * √(∑ k, t k ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ hL0
          simp only [sq_abs]
          exact mul_le_mul
            (Real.sqrt_le_sqrt (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
              fun _ _ _ => sq_nonneg _))
            (Real.sqrt_le_sqrt (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
              fun _ _ _ => sq_nonneg _))
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = lambdaG G d * √((S.card : ℝ) * T.card) := by
          rw [hS2, hT2, ← Real.sqrt_mul (Nat.cast_nonneg _)]
  have hexp' : indVec S ⬝ᵥ (P *ᵥ indVec T)
      = S.card * T.card / Fintype.card V + ∑ k ∈ univ.erase k₀, μ k * (s k * t k) := by
    rw [hexp, ← htop]
  rw [hexp', add_sub_cancel_left]
  exact hrest

/-- **Expander mixing lemma**: `|E(S, T) − d |S| |T| / n| ≤ λ_G d √(|S| |T|)` on every
`d`-regular graph. -/
theorem expander_mixing_aux {d : ℕ} (hreg : G.IsRegularOfDegree d) (S T : Finset V) :
    |(edgeCount G S T : ℝ) - d * S.card * T.card / Fintype.card V|
      ≤ lambdaG G d * d * √((S.card : ℝ) * T.card) := by
  have hL0 := lambdaG_nonneg G d
  rcases isEmpty_or_nonempty V with hV | hV
  · simp [Finset.eq_empty_of_isEmpty S, edgeCount]
  have heS := edgeCount_le_left G hreg S T
  have heT := edgeCount_le_left G hreg T S
  rw [edgeCount_comm] at heT
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have : edgeCount G S T = 0 := by simpa using heS
    simp only [this, Nat.cast_zero, zero_mul, zero_div, sub_zero, abs_zero, mul_zero]
    exact le_rfl
  by_cases hL : lambdaG G d < 1
  · rw [edgeCount_eq_transition G hd]
    have h := mixing_transition G hd hreg hL S T
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    calc |(d : ℝ) * (indVec S ⬝ᵥ (transitionMatrix G d *ᵥ indVec T))
            - d * S.card * T.card / Fintype.card V|
        = d * |indVec S ⬝ᵥ (transitionMatrix G d *ᵥ indVec T)
            - S.card * T.card / Fintype.card V| := by
          rw [← abs_of_pos hd', ← abs_mul, abs_of_pos hd']
          congr 1
          ring
      _ ≤ d * (lambdaG G d * √((S.card : ℝ) * T.card)) :=
          mul_le_mul_of_nonneg_left h hd'.le
      _ = _ := by ring
  · push Not at hL
    have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
    have hSn : (S.card : ℝ) ≤ Fintype.card V := by exact_mod_cast Finset.card_le_univ S
    have hTn : (T.card : ℝ) ≤ Fintype.card V := by exact_mod_cast Finset.card_le_univ T
    set r := √((S.card : ℝ) * T.card) with hr
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    have hr2 : r * r = S.card * T.card := Real.mul_self_sqrt (by positivity)
    have hrn : r ≤ Fintype.card V := by
      rw [hr, Real.sqrt_le_left (by positivity)]
      nlinarith [Nat.cast_nonneg (α := ℝ) S.card, Nat.cast_nonneg (α := ℝ) T.card]
    have he : (edgeCount G S T : ℝ) ≤ d * r := by
      have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
      have h1 : (edgeCount G S T : ℝ) ≤ d * S.card := by exact_mod_cast heS
      have h2 : (edgeCount G S T : ℝ) ≤ d * T.card := by exact_mod_cast heT
      have h0 : (0 : ℝ) ≤ edgeCount G S T := Nat.cast_nonneg _
      have hsq : (edgeCount G S T : ℝ) * edgeCount G S T ≤ (d * r) * (d * r) := by
        rw [show (d : ℝ) * r * (d * r) = (d * S.card) * (d * T.card) by
          linear_combination (d : ℝ) ^ 2 * hr2]
        exact mul_le_mul h1 h2 h0 (by positivity)
      nlinarith [mul_self_nonneg ((edgeCount G S T : ℝ) - d * r), mul_nonneg hd0 hr0]
    have hb : (d : ℝ) * S.card * T.card / Fintype.card V ≤ d * r := by
      rw [div_le_iff₀ hn, mul_assoc, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      rw [← hr2]
      exact mul_le_mul_of_nonneg_left hrn hr0
    have hb0 : 0 ≤ (d : ℝ) * S.card * T.card / Fintype.card V := by positivity
    have hd0 : (0 : ℝ) ≤ d * r := by positivity
    calc |(edgeCount G S T : ℝ) - d * S.card * T.card / Fintype.card V| ≤ d * r := by
          rw [abs_le]; constructor <;> linarith [Nat.cast_nonneg (α := ℝ) (edgeCount G S T)]
      _ ≤ lambdaG G d * d * r := by nlinarith

end Median
