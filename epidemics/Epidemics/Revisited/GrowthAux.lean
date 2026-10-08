import Epidemics.Revisited.Defs

/-! # Distribution lemmas for the exponential-growth upper bound

Finite-distribution support, variance of a sum of indicators (Lemma 9), Chebyshev and Cantelli,
and the partial geometric sum. Nothing here uses measure theory.

`Distribution.prob` elaborates its indicator with `Classical.propDecidable`, while a hand-written
`if` on a decidable predicate (membership, subset) uses that decidable instance. The two
functions are propositionally equal but not definitionally equal, so every bridge goes through
`prob_indicator_eq`.
-/

namespace Epidemics.Revisited
open Finset Dynamics

variable {α : Type*} [Fintype α]

/-- `prob` agrees with the expectation of any function that is the indicator of `p`. -/
lemma prob_indicator_eq (D : Distribution α) (p : α → Prop) (f : α → ℝ)
    (h0 : ∀ a, ¬ p a → f a = 0) (h1 : ∀ a, p a → f a = 1) :
    D.prob p = D.expect f := by
  classical
  simp only [Distribution.prob]
  refine congrArg D.expect ?_
  funext a
  by_cases ha : p a
  · rw [if_pos ha, h1 a ha]
  · rw [if_neg ha, h0 a ha]

lemma expect_sq_centered (D : Distribution α) (X : α → ℝ) :
    D.expect (fun a => (X a - D.expect X) ^ 2) =
      D.expect (fun a => X a ^ 2) - (D.expect X) ^ 2 := by
  have h : ∀ a, (X a - D.expect X) ^ 2 =
      X a ^ 2 - 2 * D.expect X * X a + (D.expect X) ^ 2 := fun a => by ring
  simp_rw [h, D.expect_add, D.expect_sub, D.expect_mul, D.expect_const]
  ring

lemma expect_div (D : Distribution α) (W : α → ℝ) (d : ℝ) :
    D.expect (fun a => W a / d) = D.expect W / d := by
  have hfun : (fun a => W a / d) = fun a => d⁻¹ * W a := by
    funext a
    rw [div_eq_mul_inv, mul_comm]
  rw [hfun, D.expect_mul, div_eq_mul_inv, mul_comm]

/-- Markov on the square: `P[|Z| ≥ c] ≤ E[Z²] / c²`. -/
lemma markov_sq (D : Distribution α) (Z : α → ℝ) {c : ℝ} (hc : 0 < c) :
    D.prob (fun a => c ≤ |Z a|) ≤ D.expect (fun a => Z a ^ 2) / c ^ 2 := by
  classical
  have hc2 : 0 < c ^ 2 := pow_pos hc 2
  have hpt : ∀ a, (if c ≤ |Z a| then (1 : ℝ) else 0) ≤ Z a ^ 2 / c ^ 2 := by
    intro a
    by_cases h : c ≤ |Z a|
    · rw [if_pos h, le_div_iff₀ hc2]
      have hsq : c ^ 2 ≤ |Z a| ^ 2 := pow_le_pow_left₀ hc.le h 2
      simpa [one_mul, sq_abs] using hsq
    · rw [if_neg h]
      exact div_nonneg (sq_nonneg _) hc2.le
  have hE := D.expect_mono hpt
  rw [expect_div D _] at hE
  have hp : D.prob (fun a => c ≤ |Z a|) =
      D.expect (fun a => if c ≤ |Z a| then (1 : ℝ) else 0) :=
    prob_indicator_eq D _ _ (fun a h => by simp [h]) (fun a h => by simp [h])
  rw [← hp] at hE
  exact hE

/-- Chebyshev: `P[|X - EX| ≥ lam] ≤ Var(X) / lam²`. -/
lemma chebyshev (D : Distribution α) (X : α → ℝ) {lam : ℝ} (hlam : 0 < lam) :
    D.prob (fun a => lam ≤ |X a - D.expect X|) ≤
      D.expect (fun a => (X a - D.expect X) ^ 2) / lam ^ 2 :=
  markov_sq D (fun a => X a - D.expect X) hlam

/-- One-sided Chebyshev (Cantelli), lower tail: `P[X ≤ EX - lam] ≤ Var / (Var + lam²)`. -/
lemma cantelli_lower (D : Distribution α) (X : α → ℝ) {lam : ℝ} (hlam : 0 < lam) :
    D.prob (fun a => X a ≤ D.expect X - lam) ≤
      D.expect (fun a => (X a - D.expect X) ^ 2) /
        (D.expect (fun a => (X a - D.expect X) ^ 2) + lam ^ 2) := by
  classical
  let μ : ℝ := D.expect X
  let Y : α → ℝ := fun a => X a - μ
  let v : ℝ := D.expect (fun a => Y a ^ 2)
  have hEY : D.expect Y = 0 := by
    simp [Y, μ, Distribution.expect_sub, Distribution.expect_const]
  have hv : 0 ≤ v := D.expect_nonneg fun _ => sq_nonneg _
  have hind : ∀ a, (if X a ≤ μ - lam then (1 : ℝ) else 0) =
      if Y a ≤ -lam then (1 : ℝ) else 0 := by
    intro a
    by_cases h : X a ≤ μ - lam
    · have h' : Y a ≤ -lam := by
        simp only [Y]
        linarith only [h]
      simp [h, h']
    · have h' : ¬ Y a ≤ -lam := by
        intro hY
        apply h
        simp only [Y] at hY
        linarith only [hY]
      simp [h, h']
  have hprob : D.prob (fun a => X a ≤ μ - lam) = D.prob (fun a => Y a ≤ -lam) := by
    rw [prob_indicator_eq D (fun a => X a ≤ μ - lam)
        (fun a => if X a ≤ μ - lam then (1 : ℝ) else 0)
        (fun a h => by simp [h]) (fun a h => by simp [h]),
      prob_indicator_eq D (fun a => Y a ≤ -lam)
        (fun a => if Y a ≤ -lam then (1 : ℝ) else 0)
        (fun a h => by simp [h]) (fun a h => by simp [h])]
    simp_rw [hind]
  have hmarkov : ∀ t : ℝ, 0 < t →
      D.prob (fun a => Y a ≤ -lam) ≤
        D.expect (fun a => (t - Y a) ^ 2) / (t + lam) ^ 2 := by
    intro t ht
    have hden : 0 < (t + lam) ^ 2 := pow_pos (add_pos ht hlam) 2
    have hpt : ∀ a, (if Y a ≤ -lam then (1 : ℝ) else 0) ≤
        (t - Y a) ^ 2 / (t + lam) ^ 2 := by
      intro a
      by_cases h : Y a ≤ -lam
      · rw [if_pos h, le_div_iff₀ hden]
        have hge : t + lam ≤ t - Y a := by linarith only [h, ht, hlam]
        have hlow : -(t - Y a) ≤ t + lam := by linarith only [h, ht, hlam]
        have hsq : (t + lam) ^ 2 ≤ (t - Y a) ^ 2 := sq_le_sq' hlow hge
        simpa [one_mul] using hsq
      · rw [if_neg h]
        exact div_nonneg (sq_nonneg _) hden.le
    have hE := D.expect_mono hpt
    rw [expect_div D _] at hE
    have hp : D.prob (fun a => Y a ≤ -lam) =
        D.expect (fun a => if Y a ≤ -lam then (1 : ℝ) else 0) :=
      prob_indicator_eq D _ _ (fun a h => by simp [h]) (fun a h => by simp [h])
    rw [← hp] at hE
    exact hE
  rw [hprob]
  by_cases hv0 : v = 0
  · have hle : D.prob (fun a => Y a ≤ -lam) ≤ v / lam ^ 2 := by
      have hlam2 : 0 < lam ^ 2 := pow_pos hlam 2
      have hpt : ∀ a, (if Y a ≤ -lam then (1 : ℝ) else 0) ≤ Y a ^ 2 / lam ^ 2 := by
        intro a
        by_cases h : Y a ≤ -lam
        · rw [if_pos h, le_div_iff₀ hlam2]
          have hneg : lam ≤ -Y a := by linarith only [h]
          have hsq : lam ^ 2 ≤ Y a ^ 2 := by
            calc
              lam ^ 2 ≤ (-Y a) ^ 2 := pow_le_pow_left₀ hlam.le hneg 2
              _ = Y a ^ 2 := by ring
          simpa [one_mul] using hsq
        · rw [if_neg h]
          exact div_nonneg (sq_nonneg _) hlam2.le
      have hE := D.expect_mono hpt
      rw [expect_div D _] at hE
      have hp : D.prob (fun a => Y a ≤ -lam) =
          D.expect (fun a => if Y a ≤ -lam then (1 : ℝ) else 0) :=
        prob_indicator_eq D _ _ (fun a h => by simp [h]) (fun a h => by simp [h])
      rw [← hp] at hE
      simpa [v] using hE
    rw [hv0] at hle
    have hnonpos : D.prob (fun a => Y a ≤ -lam) ≤ 0 := by simpa using hle
    have hzero : D.prob (fun a => Y a ≤ -lam) = 0 :=
      le_antisymm hnonpos (D.prob_nonneg _)
    rw [hzero]
    have hvexp : D.expect (fun a => (X a - D.expect X) ^ 2) = v := rfl
    rw [hvexp, hv0]
    simp
  · have hvpos : 0 < v := lt_of_le_of_ne hv (Ne.symm hv0)
    let t : ℝ := v / lam
    have ht : 0 < t := div_pos hvpos hlam
    have ht_def : t = v / lam := rfl
    have hsec : D.expect (fun a => (t - Y a) ^ 2) = t ^ 2 + v := by
      have hlin : ∀ a, (t - Y a) ^ 2 = t ^ 2 - 2 * t * Y a + Y a ^ 2 := fun a => by ring
      simp_rw [hlin, D.expect_add, D.expect_sub, D.expect_mul, D.expect_const, hEY]
      ring
    have hbound := hmarkov t ht
    rw [hsec] at hbound
    have hid : (t ^ 2 + v) / (t + lam) ^ 2 = v / (v + lam ^ 2) := by
      rw [ht_def]
      have hlam0 : lam ≠ 0 := hlam.ne'
      have hsum : v + lam ^ 2 ≠ 0 := (add_pos_of_pos_of_nonneg hvpos (sq_nonneg lam)).ne'
      field_simp
    rw [hid] at hbound
    have hvexp : v = D.expect (fun a => (X a - D.expect X) ^ 2) := rfl
    rw [hvexp] at hbound
    exact hbound

lemma geom_partial_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (R : ℕ) :
    ∑ i ∈ range R, q ^ i ≤ (1 - q)⁻¹ := by
  have hqne : q ≠ 1 := ne_of_lt hq1
  rw [geom_sum_eq hqne]
  have hden : 0 < 1 - q := by linarith only [hq1]
  have hrewrite : (q ^ R - 1) / (q - 1) = (1 - q ^ R) / (1 - q) := by
    field_simp
    ring
  rw [hrewrite, inv_eq_one_div, div_le_div_iff_of_pos_right hden]
  have hpow : 0 ≤ q ^ R := pow_nonneg hq0 _
  linarith only [hpow]

variable {n : ℕ}

/-- States outside the monotone support have weight zero. -/
lemma weight_zero_of_not_subset (P : RumorProcess n) {S T : Finset (Fin n)}
    (hT : ¬ S ⊆ T) : (P.K S).weight T = 0 := by
  classical
  let D := P.K S
  have hone : D.expect (fun U => if S ⊆ U then (1 : ℝ) else 0) = 1 := by
    rw [← prob_indicator_eq D (fun U => S ⊆ U) _
      (fun U h => by simp [h]) (fun U h => by simp [h])]
    exact P.mono S
  have hcomp : D.expect (fun U => if S ⊆ U then (0 : ℝ) else 1) = 0 := by
    have hfun : (fun U => if S ⊆ U then (0 : ℝ) else 1) =
        fun U => (1 : ℝ) - (if S ⊆ U then 1 else 0) := by
      funext U
      by_cases hU : S ⊆ U <;> simp [hU]
    rw [hfun, D.expect_sub, D.expect_const, hone, sub_self]
  have hnn : ∀ U ∈ univ, 0 ≤ D.weight U * (if S ⊆ U then (0 : ℝ) else 1) := by
    intro U _
    exact mul_nonneg (D.nonneg U) (by split_ifs <;> norm_num)
  have hsum0 : ∑ U, D.weight U * (if S ⊆ U then (0 : ℝ) else 1) = 0 := by
    simpa [Distribution.expect] using hcomp
  have hterm := (sum_eq_zero_iff_of_nonneg hnn).mp hsum0 T (mem_univ T)
  rw [if_neg hT, mul_one] at hterm
  exact hterm

lemma expect_eq_of_agree_on_superset (P : RumorProcess n) (S : Finset (Fin n))
    {f g : Finset (Fin n) → ℝ} (h : ∀ T, S ⊆ T → f T = g T) :
    (P.K S).expect f = (P.K S).expect g := by
  classical
  apply sum_congr rfl
  intro T _
  by_cases hsub : S ⊆ T
  · rw [h T hsub]
  · simp [weight_zero_of_not_subset P hsub]

lemma expect_le_of_weight (P : RumorProcess n) (S : Finset (Fin n))
    {f g : Finset (Fin n) → ℝ}
    (h : ∀ T, S ⊆ T → f T ≤ g T) :
    (P.K S).expect f ≤ (P.K S).expect g := by
  classical
  apply sum_le_sum
  intro T _
  by_cases hsub : S ⊆ T
  · exact mul_le_mul_of_nonneg_left (h T hsub) ((P.K S).nonneg T)
  · simp [weight_zero_of_not_subset P hsub]

lemma card_compl_cast (S : Finset (Fin n)) :
    (((univ : Finset (Fin n)) \ S).card : ℝ) = (n : ℝ) - S.card := by
  have hle : S.card ≤ n := by
    simpa [Fintype.card_fin] using card_le_univ (s := S)
  rw [card_sdiff, inter_univ, card_univ, Fintype.card_fin]
  exact Nat.cast_sub hle

lemma card_eq_add_indicators {S T : Finset (Fin n)} (h : S ⊆ T) :
    (T.card : ℝ) =
      (S.card : ℝ) + ∑ x ∈ (univ : Finset (Fin n)) \ S, (if x ∈ T then (1 : ℝ) else 0) := by
  classical
  have hunion : S ∪ (T \ S) = T := by
    ext x
    constructor
    · intro hx
      simp only [mem_union, mem_sdiff] at hx
      rcases hx with hx | hx
      · exact h hx
      · exact hx.1
    · intro hx
      by_cases hxS : x ∈ S
      · exact mem_union_left _ hxS
      · exact mem_union_right _ (mem_sdiff.mpr ⟨hx, hxS⟩)
  have hdisj : Disjoint S (T \ S) := disjoint_sdiff
  have hcard : T.card = S.card + (T \ S).card := by
    simpa [hunion] using card_union_of_disjoint hdisj
  have hfilter : ((univ : Finset (Fin n)) \ S).filter (fun x => x ∈ T) = T \ S := by
    ext x
    simp [mem_sdiff, and_comm]
  have hsum : ∑ x ∈ (univ : Finset (Fin n)) \ S, (if x ∈ T then (1 : ℝ) else 0) =
      ((T \ S).card : ℝ) := by
    rw [sum_ite, sum_const_zero, add_zero, hfilter, sum_const, nsmul_one]
  rw [hcard, Nat.cast_add, hsum]

lemma indicator_mul_indicator (x y : Fin n) (T : Finset (Fin n)) :
    (if x ∈ T then (1 : ℝ) else 0) * (if y ∈ T then 1 else 0) =
      if x ∈ T ∧ y ∈ T then 1 else 0 := by
  classical
  by_cases hx : x ∈ T <;> by_cases hy : y ∈ T <;> simp [hx, hy]

lemma expect_finset_sum {ι : Type*} (D : Distribution α) (s : Finset ι) (f : ι → α → ℝ) :
    D.expect (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, D.expect (fun a => f i a) := by
  unfold Distribution.expect
  simp_rw [mul_sum]
  rw [sum_comm]

lemma indicator_sq (x : Fin n) (T : Finset (Fin n)) :
    (if x ∈ T then (1 : ℝ) else 0) ^ 2 = if x ∈ T then (1 : ℝ) else 0 := by
  classical
  by_cases hx : x ∈ T <;> simp [hx]

/-- Variance of `∑_{x ∈ comp} 1[x ∈ T]`, with pairwise covariances at most `c`. -/
lemma variance_sum_indicator_le (D : Distribution (Finset (Fin n))) (comp : Finset (Fin n))
    {c : ℝ} (hc : 0 ≤ c)
    (hcov : ∀ x ∈ comp, ∀ y ∈ comp, x ≠ y →
      D.expect (fun T => if x ∈ T ∧ y ∈ T then (1 : ℝ) else 0) -
        D.expect (fun T => if x ∈ T then (1 : ℝ) else 0) *
          D.expect (fun T => if y ∈ T then (1 : ℝ) else 0) ≤ c) :
    D.expect (fun T =>
        ((∑ x ∈ comp, if x ∈ T then (1 : ℝ) else 0) -
          D.expect (fun U => ∑ x ∈ comp, if x ∈ U then (1 : ℝ) else 0)) ^ 2) ≤
      D.expect (fun T => ∑ x ∈ comp, if x ∈ T then (1 : ℝ) else 0) +
        c * (comp.card : ℝ) ^ 2 := by
  classical
  let I (x : Fin n) (T : Finset (Fin n)) : ℝ := if x ∈ T then 1 else 0
  let X (T : Finset (Fin n)) : ℝ := ∑ x ∈ comp, I x T
  let μ : ℝ := D.expect X
  have hvar : D.expect (fun T => (X T - μ) ^ 2) =
      D.expect (fun T => X T ^ 2) - μ ^ 2 := by
    simpa [μ] using expect_sq_centered D X
  have hsq : ∀ T, X T ^ 2 = ∑ x ∈ comp, ∑ y ∈ comp, I x T * I y T := by
    intro T
    unfold X
    rw [sq, sum_mul_sum]
  have hEX2 : D.expect (fun T => X T ^ 2) =
      ∑ x ∈ comp, ∑ y ∈ comp, D.expect (fun T => I x T * I y T) := by
    simp_rw [hsq, expect_finset_sum]
  have hμ : μ = ∑ x ∈ comp, D.expect (I x) := by
    simp only [μ, X, expect_finset_sum]
  have hμ2 : μ ^ 2 =
      ∑ x ∈ comp, ∑ y ∈ comp, D.expect (I x) * D.expect (I y) := by
    rw [hμ, sq, sum_mul_sum]
  let θ (x y : Fin n) : ℝ :=
    D.expect (fun T => I x T * I y T) - D.expect (I x) * D.expect (I y)
  have hdiff : D.expect (fun T => X T ^ 2) - μ ^ 2 = ∑ x ∈ comp, ∑ y ∈ comp, θ x y := by
    rw [hEX2, hμ2]
    simp_rw [θ, sum_sub_distrib]
  rw [show D.expect (fun T => (X T - μ) ^ 2) = ∑ x ∈ comp, ∑ y ∈ comp, θ x y from
    hvar.trans hdiff]
  have hsplit : ∀ x ∈ comp, ∑ y ∈ comp, θ x y =
      θ x x + ∑ y ∈ comp.erase x, θ x y := by
    intro x hx
    simpa using (add_sum_erase comp (θ x) hx).symm
  rw [sum_congr rfl hsplit, sum_add_distrib]
  have hdiag_one : ∀ x, ∀ T, I x T * I x T = I x T := by
    intro x T
    unfold I
    by_cases hx : x ∈ T <;> simp [hx]
  have hdiag : ∑ x ∈ comp, θ x x ≤ ∑ x ∈ comp, D.expect (I x) := by
    refine sum_le_sum ?_
    intro x _
    unfold θ
    simp_rw [hdiag_one]
    have hsq_nonneg : 0 ≤ D.expect (I x) ^ 2 := sq_nonneg _
    linarith only [hsq_nonneg]
  have hoff : ∑ x ∈ comp, ∑ y ∈ comp.erase x, θ x y ≤
      c * (comp.card : ℝ) ^ 2 := by
    have hθ : ∀ x ∈ comp, ∀ y ∈ comp.erase x, θ x y ≤ c := by
      intro x hx y hy
      have hy' : y ∈ comp := mem_of_mem_erase hy
      have hne : x ≠ y := by
        intro hxy
        exact notMem_erase x comp (hxy ▸ hy)
      unfold θ
      have hmul : ∀ T, I x T * I y T = if x ∈ T ∧ y ∈ T then (1 : ℝ) else 0 := by
        intro T
        simpa [I] using indicator_mul_indicator x y T
      simp_rw [hmul]
      exact hcov x hx y hy' hne
    have hsum_le : ∑ x ∈ comp, ∑ y ∈ comp.erase x, θ x y ≤
        ∑ x ∈ comp, ∑ y ∈ comp.erase x, c := by
      refine sum_le_sum ?_
      intro x hx
      exact sum_le_sum fun y hy => hθ x hx y hy
    have hconst : ∑ x ∈ comp, ∑ y ∈ comp.erase x, c =
        c * ((comp.card : ℝ) * ((comp.card : ℝ) - 1)) := by
      have hinner : ∀ x ∈ comp, ∑ y ∈ comp.erase x, c =
          ((comp.erase x).card : ℝ) * c := by
        intro x _
        simp [sum_const, nsmul_eq_mul]
      rw [sum_congr rfl hinner]
      have hcard : ∀ x ∈ comp, ((comp.erase x).card : ℝ) = (comp.card : ℝ) - 1 := by
        intro x hx
        have hpos : 0 < comp.card := card_pos.mpr ⟨x, hx⟩
        rw [card_erase_of_mem hx, Nat.cast_sub (Nat.succ_le_of_lt hpos), Nat.cast_one]
      have hreplace : ∀ x ∈ comp, ((comp.erase x).card : ℝ) * c =
          ((comp.card : ℝ) - 1) * c := by
        intro x hx
        rw [hcard x hx]
      rw [sum_congr rfl hreplace, sum_const, nsmul_eq_mul]
      ring
    have hcount : (comp.card : ℝ) * ((comp.card : ℝ) - 1) ≤ (comp.card : ℝ) ^ 2 := by
      have hnonneg : 0 ≤ (comp.card : ℝ) := by positivity
      have hlin : (comp.card : ℝ) * ((comp.card : ℝ) - 1) =
          (comp.card : ℝ) ^ 2 - (comp.card : ℝ) := by ring
      linarith only [hlin, hnonneg]
    calc
      ∑ x ∈ comp, ∑ y ∈ comp.erase x, θ x y ≤
          ∑ x ∈ comp, ∑ y ∈ comp.erase x, c := hsum_le
      _ = c * ((comp.card : ℝ) * ((comp.card : ℝ) - 1)) := hconst
      _ ≤ c * (comp.card : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hcount hc
  have hμ_le : ∑ x ∈ comp, D.expect (I x) = μ := hμ.symm
  calc
    ∑ x ∈ comp, θ x x + ∑ x ∈ comp, ∑ y ∈ comp.erase x, θ x y ≤
        ∑ x ∈ comp, D.expect (I x) + c * (comp.card : ℝ) ^ 2 := by
          linarith only [hdiag, hoff]
    _ = D.expect X + c * (comp.card : ℝ) ^ 2 := by rw [hμ_le]

/-- Lemma 9, proved for `variance_card_le`. -/
theorem variance_card_le_proof (P : RumorProcess n) (S : Finset (Fin n)) {c : ℝ} (hc : 0 ≤ c)
    (hcov : ∀ x ∉ S, ∀ y ∉ S, x ≠ y → P.cov S x y ≤ c) :
    (P.K S).expect (fun S' => ((S'.card : ℝ) - (P.K S).expect (fun S'' => (S''.card : ℝ))) ^ 2)
      ≤ (P.K S).expect (fun S' => (S'.card : ℝ)) - S.card + c * ((n : ℝ) - S.card) ^ 2 := by
  classical
  let D := P.K S
  let comp := (univ : Finset (Fin n)) \ S
  let I (x : Fin n) (T : Finset (Fin n)) : ℝ := if x ∈ T then 1 else 0
  let extra (T : Finset (Fin n)) : ℝ := ∑ x ∈ comp, I x T
  have hagree : ∀ T, S ⊆ T → (T.card : ℝ) = (S.card : ℝ) + extra T := by
    intro T hT
    simpa [extra, I, comp] using card_eq_add_indicators hT
  have hmean : D.expect (fun T => (T.card : ℝ)) = (S.card : ℝ) + D.expect extra := by
    have h := expect_eq_of_agree_on_superset P S hagree
    simpa [D, Distribution.expect_add, Distribution.expect_const] using h
  have hvar : D.expect (fun T => ((T.card : ℝ) - D.expect (fun U => (U.card : ℝ))) ^ 2) =
      D.expect (fun T => (extra T - D.expect extra) ^ 2) := by
    apply expect_eq_of_agree_on_superset P S
    intro T hT
    rw [hagree T hT, hmean]
    ring
  have hcov' : ∀ x ∈ comp, ∀ y ∈ comp, x ≠ y →
      D.expect (fun T => if x ∈ T ∧ y ∈ T then (1 : ℝ) else 0) -
        D.expect (fun T => if x ∈ T then (1 : ℝ) else 0) *
          D.expect (fun T => if y ∈ T then (1 : ℝ) else 0) ≤ c := by
    intro x hx y hy hne
    have hxS : x ∉ S := (mem_sdiff.mp hx).2
    have hyS : y ∉ S := (mem_sdiff.mp hy).2
    have hident : D.expect (fun T => if x ∈ T ∧ y ∈ T then (1 : ℝ) else 0) -
        D.expect (fun T => if x ∈ T then (1 : ℝ) else 0) *
          D.expect (fun T => if y ∈ T then (1 : ℝ) else 0) = P.cov S x y := by
      rw [← prob_indicator_eq D (fun T => x ∈ T ∧ y ∈ T) _
          (fun T h => by simp [h]) (fun T h => by simp [h]),
        ← prob_indicator_eq D (fun T => x ∈ T) _
          (fun T h => by simp [h]) (fun T h => by simp [h]),
        ← prob_indicator_eq D (fun T => y ∈ T) _
          (fun T h => by simp [h]) (fun T h => by simp [h])]
      simp [D, RumorProcess.cov, RumorProcess.informProb]
    rw [hident]
    exact hcov x hxS y hyS hne
  have hvar_extra := variance_sum_indicator_le D comp hc hcov'
  have hcard : (comp.card : ℝ) = (n : ℝ) - S.card := card_compl_cast S
  calc
    D.expect (fun T => ((T.card : ℝ) - D.expect (fun U => (U.card : ℝ))) ^ 2)
        = D.expect (fun T => (extra T - D.expect extra) ^ 2) := hvar
    _ ≤ D.expect extra + c * (comp.card : ℝ) ^ 2 := by
          simpa [extra, I] using hvar_extra
    _ = D.expect (fun T => (T.card : ℝ)) - S.card + c * ((n : ℝ) - S.card) ^ 2 := by
          rw [hcard, hmean]
          ring

end Epidemics.Revisited
