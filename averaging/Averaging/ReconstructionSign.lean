import Averaging.ReconstructionDecomp

/-! # The deterministic core of Theorem 3.2

Proof of Theorem 3.2 of Becchetti et al. (arXiv:1511.03927), inequality (3), with the explicit
number of rounds `T(n, δ) = ⌈log (4n³) / log (1 + δ)⌉ + 1`. By Lemma C.1,
`x⁽ᵗ⁻¹⁾(u) - x⁽ᵗ⁾(u) = α₂ λ₂ᵗ⁻¹ (1 - λ₂) χ(u) + (e⁽ᵗ⁻¹⁾(u) - e⁽ᵗ⁾(u))`. The main term has absolute
value at least `2b λ₂ᵗ⁻¹ / (nd)` because `⟨x, χ⟩` is a nonzero even integer, while the error is at
most `2 λᵗ⁻¹ √(2n)`. Since `λ₂ ≥ (1 + δ) λ`, `(1 + δ)ᵗ⁻¹ ≥ 4n³`, `b ≥ 1` (connectivity) and
`d < 2n`, the main term wins and fixes the sign.
-/

namespace Averaging
open Finset Matrix SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {V₁ V₂ : Finset V} {n d b : ℕ}

/-- On a connected clustered graph, some edge crosses the cut, so `b ≥ 1`. -/
lemma one_le_cross (hG : IsClusteredRegular G V₁ V₂ n d b) (hconn : G.Connected) (hn : 0 < n) :
    1 ≤ b := by
  have hP := hG.toIsBalancedPartition
  obtain ⟨v₁, hv₁⟩ : V₁.Nonempty := card_pos.mp (hP.card_left ▸ hn)
  obtain ⟨v₂, hv₂⟩ : V₂.Nonempty := card_pos.mp (hP.card_right ▸ hn)
  obtain ⟨p⟩ := hconn.preconnected v₁ v₂
  obtain ⟨e, -, he₁, he₂⟩ := p.exists_boundary_dart (V₁ : Set V) (by simpa using hv₁)
    (by simpa using disjoint_right.mp hP.disjoint hv₂)
  have he₁' : e.fst ∈ V₁ := by simpa using he₁
  have h2 : e.snd ∈ V₂ := (hP.mem_or _).resolve_left (by simpa using he₂)
  have hmem : e.snd ∈ G.neighborFinset e.fst ∩ V₂ :=
    mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr e.adj, h2⟩
  rw [← hG.cross_left e.fst he₁']
  exact card_pos.mpr ⟨_, hmem⟩

lemma cross_le_degree (hG : IsClusteredRegular G V₁ V₂ n d b) (hn : 0 < n) : b ≤ d := by
  obtain ⟨v₁, hv₁⟩ : V₁.Nonempty := card_pos.mp (hG.card_left ▸ hn)
  rw [← hG.cross_left v₁ hv₁, ← hG.regular v₁, ← card_neighborFinset_eq_degree]
  exact card_le_card inter_subset_left

lemma degree_lt_two_mul (hG : IsClusteredRegular G V₁ V₂ n d b) (v : V) : d < 2 * n := by
  rw [← hG.regular v, ← hG.toIsBalancedPartition.card_eq]
  exact G.degree_lt_card_verts v

/-- For a sign vector `x`, `⟨x, χ⟩ = 2 (k - n)` where `k` counts the nodes with `x v = χ v`. -/
lemma dotProduct_clusterIndicator_eq (hP : IsBalancedPartition V₁ V₂ n) {x : V → ℝ}
    (hx : ∀ v, x v = 1 ∨ x v = -1) :
    x ⬝ᵥ clusterIndicator V₁ V₂ =
      2 * (((univ.filter fun v => x v = clusterIndicator V₁ V₂ v).card : ℝ) - n) := by
  set χ := clusterIndicator V₁ V₂
  have hterm (v : V) : x v * χ v = 2 * (if x v = χ v then 1 else 0) - 1 := by
    have hχv : χ v = 1 ∨ χ v = -1 := hP.clusterIndicator_eq_one_or v
    rcases hx v with h1 | h1 <;> rcases hχv with h2 | h2 <;> simp [h1, h2] <;> norm_num
  rw [dotProduct, sum_congr rfl fun v _ => hterm v, sum_sub_distrib, ← mul_sum, sum_boole,
    sum_const, card_univ, hP.card_eq]
  ring

/-- `⟨x, χ⟩` is a sum of `2n` signs, hence even: if nonzero, it is at least `2` in absolute
value. -/
lemma two_le_abs_dotProduct (hP : IsBalancedPartition V₁ V₂ n) {x : V → ℝ}
    (hx : ∀ v, x v = 1 ∨ x v = -1) (h : x ⬝ᵥ clusterIndicator V₁ V₂ ≠ 0) :
    2 ≤ |x ⬝ᵥ clusterIndicator V₁ V₂| := by
  have hS := dotProduct_clusterIndicator_eq hP hx
  set k := (univ.filter fun v => x v = clusterIndicator V₁ V₂ v).card
  rw [hS] at h ⊢
  have hk : ((k : ℤ) - n : ℤ) ≠ 0 := by
    intro h0
    apply h
    have : ((k : ℝ) - n) = (((k : ℤ) - n : ℤ) : ℝ) := by push_cast; ring
    rw [this, h0]
    simp
  have h1 : (1 : ℤ) ≤ |(k : ℤ) - n| := Int.one_le_abs hk
  have h2 : (1 : ℝ) ≤ |(k : ℝ) - n| := by
    have := (Int.cast_le (R := ℝ)).mpr h1
    push_cast at this
    exact this
  rw [abs_mul, abs_two]
  linarith

lemma one_le_reconstructionTime (n : ℕ) (δ : ℝ) : 1 ≤ reconstructionTime n δ := by
  unfold reconstructionTime
  omega

/-- After `T(n, δ)` rounds, `(1 + δ)ᵗ⁻¹ ≥ 4n³`. -/
lemma four_mul_cube_le_one_add_pow (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) {t : ℕ}
    (ht : reconstructionTime n δ ≤ t) : 4 * (n : ℝ) ^ 3 ≤ (1 + δ) ^ (t - 1) := by
  have hlog : 0 < Real.log (1 + δ) := Real.log_pos (by linarith)
  have hpos : 0 < 4 * (n : ℝ) ^ 3 := by positivity
  have hceil : Real.log (4 * (n : ℝ) ^ 3) / Real.log (1 + δ) ≤ ((t - 1 : ℕ) : ℝ) := by
    have : ⌈Real.log (4 * (n : ℝ) ^ 3) / Real.log (1 + δ)⌉₊ ≤ t - 1 := by
      unfold reconstructionTime at ht
      omega
    exact (Nat.le_ceil _).trans (by exact_mod_cast this)
  rw [div_le_iff₀ hlog, ← Real.log_pow] at hceil
  exact (Real.log_le_log_iff hpos (by positivity)).mp hceil

/-- A perturbation smaller than the main term does not change the sign. -/
lemma sign_add_eq_of_abs_lt {M E : ℝ} (h : |E| < |M|) :
    SignType.sign (M + E) = SignType.sign M := by
  have h1 := le_abs_self E
  have h2 := neg_abs_le E
  rcases lt_trichotomy M 0 with hM | hM | hM
  · rw [abs_of_neg hM] at h
    rw [sign_neg hM, sign_neg (by linarith)]
  · rw [hM, abs_zero] at h
    exact absurd h (not_lt.mpr (abs_nonneg _))
  · rw [abs_of_pos hM] at h
    rw [sign_pos hM, sign_pos (by linarith)]

/-- Real-arithmetic core of inequality (3): if two consecutive values are within `λˢ K` and
`λˢ⁺¹ K` of `α₁ + (S/N) μˢ c` and `α₁ + (S/N) μˢ⁺¹ c`, and the error bound `2 λˢ K` is below the
main term `|S| μˢ (1 - μ) / N`, then `sgn (y₀ - y₁) = sgn (S c)`. -/
lemma sign_sub_eq_of_bounds {y₀ y₁ α₁ S c μ lam K N : ℝ} {s : ℕ}
    (h₀ : |y₀ - (α₁ + S / N * μ ^ s * c)| ≤ lam ^ s * K)
    (h₁ : |y₁ - (α₁ + S / N * μ ^ (s + 1) * c)| ≤ lam ^ (s + 1) * K)
    (hc : |c| = 1) (hN : 0 < N) (hμ : 0 < μ) (hμ1 : μ < 1) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hK : 0 ≤ K) (hdom : 2 * lam ^ s * K < |S| * (μ ^ s * (1 - μ) / N)) :
    SignType.sign (y₀ - y₁) = SignType.sign (S * c) := by
  set q := μ ^ s * (1 - μ) / N with hq
  have hqpos : 0 < q := by
    have : 0 < 1 - μ := by linarith
    positivity
  set e₀ := y₀ - (α₁ + S / N * μ ^ s * c) with he₀
  set e₁ := y₁ - (α₁ + S / N * μ ^ (s + 1) * c) with he₁
  have hdiff : y₀ - y₁ = S * c * q + (e₀ - e₁) := by
    rw [he₀, he₁, hq, pow_succ]
    ring
  have hls : lam ^ (s + 1) ≤ lam ^ s := pow_le_pow_of_le_one hlam0 hlam1 (Nat.le_succ s)
  have hE : |e₀ - e₁| ≤ 2 * lam ^ s * K := by
    calc |e₀ - e₁| ≤ |e₀| + |e₁| := abs_sub _ _
      _ ≤ lam ^ s * K + lam ^ (s + 1) * K := add_le_add h₀ h₁
      _ ≤ 2 * lam ^ s * K := by nlinarith [mul_le_mul_of_nonneg_right hls hK]
  have hM : |S * c * q| = |S| * q := by
    rw [abs_mul, abs_mul, hc, mul_one, abs_of_pos hqpos]
  rw [hdiff, sign_add_eq_of_abs_lt (by rw [hM]; exact hE.trans_lt hdom), sign_mul (S * c),
    sign_pos hqpos, mul_one]

/-- **Theorem 3.2, deterministic core** (inequality (3) of its proof). -/
theorem sign_avgIter_sub_eq_aux (hG : IsClusteredRegular G V₁ V₂ n d b) (hconn : G.Connected)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : (1 + δ) * maxAbsOtherEigenvalue G d < 1 - 2 * (b : ℝ) / d) {x : V → ℝ}
    (hx : ∀ v, x v = 1 ∨ x v = -1) (hχ : x ⬝ᵥ clusterIndicator V₁ V₂ ≠ 0) {t : ℕ}
    (ht : reconstructionTime n δ ≤ t) (u : V) :
    SignType.sign (avgIter G (t - 1) x u - avgIter G t x u) =
      SignType.sign ((x ⬝ᵥ clusterIndicator V₁ V₂) * clusterIndicator V₁ V₂ u) := by
  have hP := hG.toIsBalancedPartition
  have hn : 0 < n := by
    have h1 := hP.card_eq
    have h2 : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨u⟩
    omega
  have hb := one_le_cross hG hconn hn
  have hbd := cross_le_degree hG hn
  have hd : 0 < d := by omega
  have hd2n := degree_lt_two_mul hG u
  have hpow := four_mul_cube_le_one_add_pow hn hδ ht
  have ht1 := (one_le_reconstructionTime n δ).trans ht
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hpow ⊢
  have hlam0 := maxAbsOtherEigenvalue_nonneg G d
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hd2nR : (d : ℝ) + 1 ≤ 2 * n := by exact_mod_cast hd2n
  have h1μ : 1 - (1 - 2 * (b : ℝ) / d) = 2 * b / d := by ring
  have h2bd : 0 < 2 * (b : ℝ) / d := by positivity
  have hlamμ : maxAbsOtherEigenvalue G d < 1 - 2 * (b : ℝ) / d := by nlinarith
  have hμ0 : 0 < 1 - 2 * (b : ℝ) / d := by linarith
  have hC₀ := abs_avgIter_sub_le_aux hG hd hlamμ hx s u
  have hC₁ := abs_avgIter_sub_le_aux hG hd hlamμ hx (s + 1) u
  refine sign_sub_eq_of_bounds hC₀ hC₁ ?_ (by positivity) hμ0 (by linarith) hlam0 (by linarith)
    (Real.sqrt_nonneg _) ?_
  · rcases hP.clusterIndicator_eq_one_or u with h | h <;> rw [h] <;> norm_num
  -- the main term dominates the error
  have hS2 := two_le_abs_dotProduct hP hx hχ
  set lam := maxAbsOtherEigenvalue G d
  set μ := 1 - 2 * (b : ℝ) / d with hμ
  set K := √(2 * (n : ℝ)) with hK
  set S := x ⬝ᵥ clusterIndicator V₁ V₂
  have hK0 : 0 ≤ K := Real.sqrt_nonneg _
  have hK2n : K ≤ 2 * n := by
    rw [hK, Real.sqrt_le_left (by positivity)]
    nlinarith
  have hKnd : K * n * d < 4 * (n : ℝ) ^ 3 := by
    have h1 : K * n * d ≤ 2 * n * n * d := by
      have := mul_le_mul_of_nonneg_right hK2n (by positivity : (0 : ℝ) ≤ n * d)
      nlinarith
    have h2 : 2 * n * n * ((d : ℝ) + 1) ≤ 2 * n * n * (2 * n) :=
      mul_le_mul_of_nonneg_left hd2nR (by positivity)
    nlinarith [mul_pos hnR hnR]
  have hμs : (1 + δ) ^ s * lam ^ s ≤ μ ^ s := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hgap.le s
  have hkey : lam ^ s * K * n * d < μ ^ s * b := by
    rcases (pow_nonneg hlam0 s).eq_or_lt with h0 | hpos
    · rw [← h0]
      simp only [zero_mul]
      positivity
    · calc lam ^ s * K * n * d = lam ^ s * (K * n * d) := by ring
        _ < lam ^ s * (4 * (n : ℝ) ^ 3) := mul_lt_mul_of_pos_left hKnd hpos
        _ ≤ lam ^ s * (1 + δ) ^ s := mul_le_mul_of_nonneg_left hpow hpos.le
        _ ≤ μ ^ s := by rw [mul_comm]; exact hμs
        _ ≤ μ ^ s * b := le_mul_of_one_le_right (by positivity) hbR
  have hq : μ ^ s * (1 - μ) / (2 * n) = μ ^ s * b / (n * d) := by
    rw [h1μ]
    field_simp
  rw [hq]
  have hlt : lam ^ s * K < μ ^ s * b / (n * d) := by
    rw [lt_div_iff₀ (by positivity)]
    linarith
  have hqpos : 0 ≤ μ ^ s * b / (n * d) := by positivity
  nlinarith

/-- **Theorem 3.2, deterministic core, cluster form**: from round `T(n, δ)` on, the sign of
`x⁽ᵗ⁻¹⁾(u) - x⁽ᵗ⁾(u)` is `sgn ⟨x, χ⟩` on `V₁` and `-sgn ⟨x, χ⟩` on `V₂`. -/
theorem exists_sign_avgIter_sub_clusters_aux (hG : IsClusteredRegular G V₁ V₂ n d b)
    (hconn : G.Connected) {δ : ℝ} (hδ : 0 < δ)
    (hgap : (1 + δ) * maxAbsOtherEigenvalue G d < 1 - 2 * (b : ℝ) / d) {x : V → ℝ}
    (hx : ∀ v, x v = 1 ∨ x v = -1) (hχ : x ⬝ᵥ clusterIndicator V₁ V₂ ≠ 0) :
    ∃ s : SignType, s ≠ 0 ∧ ∀ t, reconstructionTime n δ ≤ t →
      (∀ u ∈ V₁, SignType.sign (avgIter G (t - 1) x u - avgIter G t x u) = s) ∧
        ∀ u ∈ V₂, SignType.sign (avgIter G (t - 1) x u - avgIter G t x u) = -s := by
  have hP := hG.toIsBalancedPartition
  refine ⟨SignType.sign (x ⬝ᵥ clusterIndicator V₁ V₂), sign_ne_zero.mpr hχ,
    fun t ht => ⟨fun u hu => ?_, fun u hu => ?_⟩⟩
  · rw [sign_avgIter_sub_eq_aux hG hconn hδ hgap hx hχ ht u,
      hP.clusterIndicator_of_mem_left hu, mul_one]
  · rw [sign_avgIter_sub_eq_aux hG hconn hδ hgap hx hχ ht u,
      hP.clusterIndicator_of_mem_right hu, mul_neg_one, Right.sign_neg]

omit [DecidableEq V] in
/-- The protocol's coloring: blue (`true`) exactly when `x⁽ᵗ⁻¹⁾(u) - x⁽ᵗ⁾(u)` is not positive. -/
lemma color_eq_true_iff (x : V → ℝ) (t : ℕ) (u : V) :
    color G x t u = true ↔ SignType.sign (avgIter G (t - 1) x u - avgIter G t x u) ≠ 1 := by
  simp [color, sign_eq_one_iff]

/-- **Theorem 3.2, deterministic core, coloring form**. -/
theorem isStrongReconstruction_color_aux (hG : IsClusteredRegular G V₁ V₂ n d b)
    (hconn : G.Connected) {δ : ℝ} (hδ : 0 < δ)
    (hgap : (1 + δ) * maxAbsOtherEigenvalue G d < 1 - 2 * (b : ℝ) / d) {x : V → ℝ}
    (hx : ∀ v, x v = 1 ∨ x v = -1) (hχ : x ⬝ᵥ clusterIndicator V₁ V₂ ≠ 0) {t : ℕ}
    (ht : reconstructionTime n δ ≤ t) :
    IsStrongReconstruction V₁ V₂ (color G x t) := by
  obtain ⟨s, hs0, hs⟩ := exists_sign_avgIter_sub_clusters_aux hG hconn hδ hgap hx hχ
  obtain ⟨h₁, h₂⟩ := hs t ht
  rw [IsStrongReconstruction, Finset.disjoint_left]
  intro c hc₁ hc₂
  obtain ⟨u₁, hu₁, rfl⟩ := mem_image.mp hc₁
  obtain ⟨u₂, hu₂, heq⟩ := mem_image.mp hc₂
  have e₁ := color_eq_true_iff (G := G) x t u₁
  have e₂ := color_eq_true_iff (G := G) x t u₂
  rw [h₁ u₁ hu₁] at e₁
  rw [h₂ u₂ hu₂] at e₂
  rcases s with _ | _ | _
  · exact hs0 rfl
  · -- `s = -1`: `V₁` is blue, `V₂` is red
    have hb₁ : color G x t u₁ = true := e₁.mpr (by decide)
    have hb₂ : color G x t u₂ ≠ true := fun h => (e₂.mp h) (by decide)
    exact hb₂ (heq.trans hb₁)
  · -- `s = 1`: `V₁` is red, `V₂` is blue
    have hb₁ : color G x t u₁ ≠ true := fun h => (e₁.mp h) (by decide)
    have hb₂ : color G x t u₂ = true := e₂.mpr (by decide)
    exact hb₁ (heq ▸ hb₂)

end Averaging
