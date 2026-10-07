import Epidemics.Revisited.GrowthReal

/-! # Exponential growth: one round, phases, and the tail

The round target `E0` and the thresholds `k_j` are already in `GrowthReal.lean`. Here a single
round misses its target with probability at most `Q(k) = q(k) / (1 + q(k))` (Cantelli), the
phase index is controlled by a potential on `Kernel.iterate`, and Lemma 19 crosses from `k_J`
to `f n`.
-/

namespace Epidemics.Revisited
open Finset Dynamics Classical

variable {n : ℕ}

lemma threeFourth_sq {k : ℝ} (hk : 0 ≤ k) : threeFourth k ^ 2 = k * Real.sqrt k := by
  unfold threeFourth fourthRoot
  rw [mul_pow, Real.sq_sqrt (Real.sqrt_nonneg k), Real.sq_sqrt hk]

lemma stdFacts {γlo γ a b f : ℝ} {n : ℕ} (hγlo : 0 < γlo) (hγ : γlo ≤ γ) (ha : 0 ≤ a)
    (hf0 : 0 < f) (hn : growthN a b f ≤ n) :
    0 < γ ∧ 0 < Real.log (n : ℝ) ∧ 0 < (n : ℝ) ∧ b / Real.log n ≤ 1 / 4 ∧
      (a + 1) * fShrink a f ≤ 1 / 8 ∧ 1 ≤ fShrink a f * n ∧
      growthA γlo b ≤ γ / 6 ∧ 0 < growthA γlo b := by
  refine ⟨lt_of_lt_of_le hγlo hγ, log_pos_of_large (a := a) (b := b) (f := f) hn,
    n_cast_pos (a := a) (b := b) (f := f) hn, blog_quarter (a := a) (b := b) (f := f) hn,
    fShrink_a_le (a := a) (f := f) ha, shrink_n_ge_one hf0 ha hn, ?_, growthA_pos (b := b) hγlo⟩
  have h6 : (0 : ℝ) ≤ 6 := by norm_num
  exact le_trans growthA_le_gamma (div_le_div_of_nonneg_right hγ h6)

lemma card_lt_fn {a f : ℝ} {n : ℕ} {k : ℝ} (hf0 : 0 < f) (hn : 0 < (n : ℝ))
    (hk : k ≤ fShrink a f * n) : k < f * n := by
  have hhalf : fShrink a f * n ≤ (f / 2) * n :=
    mul_le_mul_of_nonneg_right (fShrink_le_half (a := a) (f := f)) hn.le
  have hlt : (f / 2) * n < f * n := by
    have hf : f / 2 < f := by linarith only [hf0]
    exact mul_lt_mul_of_pos_right hf hn
  exact lt_of_le_of_lt (le_trans hk hhalf) hlt

lemma prob_mono {α : Type*} [Fintype α] (D : Distribution α) {p q : α → Prop}
    (h : ∀ a, p a → q a) : D.prob p ≤ D.prob q := by
  classical
  have hfun : ∀ a, (if p a then (1 : ℝ) else 0) ≤ (if q a then 1 else 0) := by
    intro a
    by_cases hp : p a
    · have hq : q a := h a hp
      rw [if_pos hp, if_pos hq]
    · by_cases hq : q a
      · rw [if_neg hp, if_pos hq]
        norm_num
      · rw [if_neg hp, if_neg hq]
  simpa [Distribution.prob] using D.expect_mono hfun

lemma expect_new_eq (P : RumorProcess n) (S : Finset (Fin n)) :
    (P.K S).expect (fun T => (T.card : ℝ) - (S.card : ℝ)) =
      ∑ x ∈ (univ : Finset (Fin n)) \ S, P.informProb S x := by
  rw [Distribution.expect_sub, Distribution.expect_const, expect_card_eq]
  ring

lemma expect_new_ge {γ a b c f : ℝ} (P : RumorProcess n) (hγ : 0 ≤ γ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hlog : 0 < Real.log (n : ℝ)) (hn : 0 < (n : ℝ))
    (hUG : P.UpperGrowth γ a b c f) {S : Finset (Fin n)} (hS : S.Nonempty)
    (hcard : (S.card : ℝ) < f * n) :
    growthE γ a b n (S.card : ℝ) ≤
      (P.K S).expect (fun T => (T.card : ℝ) - (S.card : ℝ)) := by
  classical
  let k : ℝ := (S.card : ℝ)
  rw [expect_new_eq]
  have hinfo := (hUG S hS hcard).1
  have hterm : ∀ x ∈ (univ : Finset (Fin n)) \ S,
      γ * (k / n) * (1 - a * (k / n) - b / Real.log n) ≤ P.informProb S x := by
    intro x hx
    simpa [k] using hinfo x (mem_sdiff.mp hx).2
  have hsum := sum_le_sum hterm
  have hcount : ∑ x ∈ (univ : Finset (Fin n)) \ S,
      γ * (k / n) * (1 - a * (k / n) - b / Real.log n) =
      ((n : ℝ) - k) * (γ * (k / n) * (1 - a * (k / n) - b / Real.log n)) := by
    rw [sum_const, nsmul_eq_mul, card_compl_cast]
  have hcross : γ * k * (1 - (a + 1) * k / n - b / Real.log n) ≤
      ((n : ℝ) - k) * (γ * (k / n) * (1 - a * (k / n) - b / Real.log n)) := by
    have hdiff : ((n : ℝ) - k) * (γ * (k / n) * (1 - a * (k / n) - b / Real.log n)) -
        γ * k * (1 - (a + 1) * k / n - b / Real.log n) =
        γ * k * (k / n) * (a * (k / n) + b / Real.log n) := by
      field_simp [hn.ne', hlog.ne']
      ring
    have hnn : 0 ≤ γ * k * (k / n) * (a * (k / n) + b / Real.log n) := by
      have hk0 : 0 ≤ k := Nat.cast_nonneg S.card
      have hkn : 0 ≤ k / n := div_nonneg hk0 hn.le
      have hsum0 : 0 ≤ a * (k / n) + b / Real.log n := by
        have haρ : 0 ≤ a * (k / n) := mul_nonneg ha hkn
        have hbL : 0 ≤ b / Real.log n := div_nonneg hb hlog.le
        linarith only [haρ, hbL]
      exact mul_nonneg (mul_nonneg (mul_nonneg hγ hk0) hkn) hsum0
    linarith only [hdiff, hnn]
  have hE : growthE γ a b n k =
      γ * k * (1 - (a + 1) * k / n - b / Real.log n) := rfl
  have hgoal : growthE γ a b n (S.card : ℝ) =
      γ * k * (1 - (a + 1) * k / n - b / Real.log n) := by
    simpa [k] using hE
  linarith only [hsum, hcount, hcross, hgoal]

lemma variance_new_le (P : RumorProcess n) {c : ℝ} (hc : 0 ≤ c) (hn : 0 < (n : ℝ))
    (S : Finset (Fin n))
    (hcov : ∀ x ∉ S, ∀ y ∉ S, x ≠ y →
      P.cov S x y ≤ c * (S.card : ℝ) / (n : ℝ) ^ 2) :
    (P.K S).expect (fun T =>
        ((T.card : ℝ) - (P.K S).expect (fun U => (U.card : ℝ))) ^ 2) ≤
      (P.K S).expect (fun T => (T.card : ℝ) - (S.card : ℝ)) + c * (S.card : ℝ) := by
  have hc' : 0 ≤ c * (S.card : ℝ) / (n : ℝ) ^ 2 :=
    div_nonneg (mul_nonneg hc (Nat.cast_nonneg _)) (sq_nonneg _)
  have hvar := variance_card_le_proof P S hc' hcov
  have hcard : S.card ≤ n := by simpa [Fintype.card_fin] using card_le_univ (s := S)
  have hsq : ((n : ℝ) - (S.card : ℝ)) ^ 2 ≤ (n : ℝ) ^ 2 := by
    have h1 : -(n : ℝ) ≤ (n : ℝ) - (S.card : ℝ) := by
      have hk : (S.card : ℝ) ≤ n := Nat.cast_le.mpr hcard
      linarith only [hk]
    have h2 : (n : ℝ) - (S.card : ℝ) ≤ n := by
      have hk : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
      linarith only [hk]
    exact sq_le_sq' h1 h2
  have hmul := mul_le_mul_of_nonneg_left hsq hc'
  have hcancel : c * (S.card : ℝ) / (n : ℝ) ^ 2 * (n : ℝ) ^ 2 = c * (S.card : ℝ) := by
    field_simp [hn.ne']
  have hEx : (P.K S).expect (fun T => (T.card : ℝ)) - (S.card : ℝ) =
      (P.K S).expect (fun T => (T.card : ℝ) - (S.card : ℝ)) := by
    rw [Distribution.expect_sub, Distribution.expect_const]
  linarith only [hvar, hmul, hcancel, hEx]

lemma shift_le {E μ A t : ℝ} (hE : 0 < E) (hμ : E ≤ μ) (hAt : A * t ≤ E) :
    E - A * t ≤ μ - A * t * μ / E := by
  have hfac : 0 ≤ 1 - A * t / E := by
    rw [sub_nonneg]
    exact div_le_one_of_le₀ hAt hE.le
  have hneg : E - μ ≤ 0 := by linarith only [hμ]
  have hmul : (E - μ) * (1 - A * t / E) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg hfac
  have hident : (E - μ) * (1 - A * t / E) =
      (E - A * t) - (μ - A * t * μ / E) := by
    field_simp [hE.ne']
  linarith only [hmul, hident]

lemma ratio_bound {μ E A t c k γ : ℝ} (hμ : E ≤ μ) (hE : 0 < E) (hA : 0 < A) (ht : 0 < t)
    (hc : 0 ≤ c) (hk : 0 < k) (hElin : E ≤ γ * k) (ht2 : t ^ 2 = k * Real.sqrt k) :
    (μ + c * k) * E ^ 2 / (A ^ 2 * t ^ 2 * μ ^ 2) ≤ (γ + c) / (A ^ 2 * Real.sqrt k) := by
  have hμ0 : 0 < μ := lt_of_lt_of_le hE hμ
  have hsqrt : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk
  have ht2pos : 0 < t ^ 2 := pow_pos ht 2
  have hstep1 : (μ + c * k) * E ^ 2 / (A ^ 2 * t ^ 2 * μ ^ 2) =
      (1 + c * k / μ) * (E / μ) * E / (A ^ 2 * t ^ 2) := by
    field_simp [hμ0.ne', hA.ne', ht.ne']
  have hEμ : E / μ ≤ 1 := by
    rw [div_le_one hμ0]
    exact hμ
  have hck : c * k / μ ≤ c * k / E := by
    have hnum : 0 ≤ c * k := mul_nonneg hc hk.le
    exact div_le_div_of_nonneg_left hnum hE hμ
  have hone : 1 + c * k / μ ≤ 1 + c * k / E := by linarith only [hck]
  have hnon1 : 0 ≤ 1 + c * k / μ := by
    have hckμ : 0 ≤ c * k / μ := div_nonneg (mul_nonneg hc hk.le) hμ0.le
    linarith only [hckμ]
  have hnonE : 0 ≤ E / μ := div_nonneg hE.le hμ0.le
  have hnon2 : 0 ≤ 1 + c * k / E := by
    have hckE : 0 ≤ c * k / E := div_nonneg (mul_nonneg hc hk.le) hE.le
    linarith only [hckE]
  have hmul1 : (1 + c * k / μ) * (E / μ) ≤ (1 + c * k / E) * 1 :=
    mul_le_mul hone hEμ hnonE hnon2
  have hmul2 : (1 + c * k / μ) * (E / μ) * E ≤ (1 + c * k / E) * E := by
    have h := mul_le_mul_of_nonneg_right hmul1 hE.le
    simpa [mul_one, mul_assoc] using h
  have hden : 0 < A ^ 2 * t ^ 2 := mul_pos (pow_pos hA 2) ht2pos
  have hdiv : (1 + c * k / μ) * (E / μ) * E / (A ^ 2 * t ^ 2) ≤
      (1 + c * k / E) * E / (A ^ 2 * t ^ 2) :=
    div_le_div_of_nonneg_right hmul2 hden.le
  have hcancel : (1 + c * k / E) * E / (A ^ 2 * t ^ 2) = (E + c * k) / (A ^ 2 * t ^ 2) := by
    field_simp [hE.ne', hA.ne', ht.ne']
  have hlin : E + c * k ≤ γ * k + c * k := by linarith only [hElin]
  have hdiv2 : (E + c * k) / (A ^ 2 * t ^ 2) ≤ (γ * k + c * k) / (A ^ 2 * t ^ 2) :=
    div_le_div_of_nonneg_right hlin hden.le
  have hfactor : (γ * k + c * k) / (A ^ 2 * t ^ 2) = (γ + c) * k / (A ^ 2 * t ^ 2) := by ring
  have hsq : (γ + c) * k / (A ^ 2 * (k * Real.sqrt k)) =
      (γ + c) / (A ^ 2 * Real.sqrt k) := by
    field_simp [hA.ne', hk.ne', hsqrt.ne']
  have hrewrite : (γ + c) * k / (A ^ 2 * t ^ 2) = (γ + c) / (A ^ 2 * Real.sqrt k) := by
    rw [← ht2] at hsq
    exact hsq
  calc (μ + c * k) * E ^ 2 / (A ^ 2 * t ^ 2 * μ ^ 2)
      = (1 + c * k / μ) * (E / μ) * E / (A ^ 2 * t ^ 2) := hstep1
    _ ≤ (1 + c * k / E) * E / (A ^ 2 * t ^ 2) := hdiv
    _ = (E + c * k) / (A ^ 2 * t ^ 2) := hcancel
    _ ≤ (γ * k + c * k) / (A ^ 2 * t ^ 2) := hdiv2
    _ = (γ + c) * k / (A ^ 2 * t ^ 2) := hfactor
    _ = (γ + c) / (A ^ 2 * Real.sqrt k) := hrewrite

lemma cantelli_ratio {v lam q : ℝ} (hv : 0 ≤ v) (hlam : 0 < lam) (hq : v / lam ^ 2 ≤ q) :
    v / (v + lam ^ 2) ≤ q / (1 + q) := by
  have hlam2 : 0 < lam ^ 2 := pow_pos hlam 2
  have hrho : 0 ≤ v / lam ^ 2 := div_nonneg hv hlam2.le
  have hfrac : v / (v + lam ^ 2) = (v / lam ^ 2) / (1 + v / lam ^ 2) := by
    field_simp [hlam.ne']
    ring
  rw [hfrac]
  exact Qof_mono hrho hq

lemma qTerm_antitone {γ c A k k' : ℝ} (hγ : 0 ≤ γ) (hc : 0 ≤ c) (hA : A ≠ 0)
    (hk : 0 < k) (hk' : k ≤ k') : qTerm γ c A k' ≤ qTerm γ c A k := by
  have hnum : 0 ≤ γ + c := by linarith only [hγ, hc]
  have hden : 0 < A ^ 2 * Real.sqrt k := by
    have hne : A ^ 2 ≠ 0 := fun h => hA (sq_eq_zero_iff.mp h)
    exact mul_pos (lt_of_le_of_ne (sq_nonneg A) hne.symm) (Real.sqrt_pos.mpr hk)
  have hsqrt : Real.sqrt k ≤ Real.sqrt k' := Real.sqrt_le_sqrt hk'
  have hden' : A ^ 2 * Real.sqrt k ≤ A ^ 2 * Real.sqrt k' :=
    mul_le_mul_of_nonneg_left hsqrt (sq_nonneg A)
  simpa [qTerm] using div_le_div_of_nonneg_left hnum hden hden'

/-- One round falls short of `E0(|S|)` with probability at most `q / (1 + q)`. -/
lemma fail_prob_le {γlo γ a b c f : ℝ} (P : RumorProcess n) (hγlo : 0 < γlo) (hγ : γlo ≤ γ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hf0 : 0 < f) (hn : growthN a b f ≤ n)
    (hUG : P.UpperGrowth γ a b c f) {S : Finset (Fin n)} (hS : S.Nonempty)
    (hk1 : (1 : ℝ) ≤ S.card) (hkf : (S.card : ℝ) ≤ fShrink a f * n) :
    (P.K S).prob (fun T => (T.card : ℝ) - (S.card : ℝ) ≤
        growthE0 γ a b (growthA γlo b) n (S.card : ℝ)) ≤
      qTerm γ c (growthA γlo b) (S.card : ℝ) /
        (1 + qTerm γ c (growthA γlo b) (S.card : ℝ)) := by
  obtain ⟨hγpos, hlog, hnpos, hblog, hf', _, hAγ, hA0⟩ :=
    stdFacts hγlo hγ ha hf0 hn
  let D := P.K S
  let k : ℝ := (S.card : ℝ)
  let A : ℝ := growthA γlo b
  let X : Finset (Fin n) → ℝ := fun T => (T.card : ℝ) - k
  let E : ℝ := growthE γ a b n k
  let t : ℝ := threeFourth k
  have hk0 : 0 < k := by linarith only [hk1]
  have hcard : k < f * n := card_lt_fn hf0 hnpos (by simpa [k] using hkf)
  have hElin := growthE_le_linear (n := n) (k := k) hγpos.le hk0.le ha hb hnpos hlog
  have hElow := growthE_lower (n := n) (k := k) (f' := fShrink a f) hγpos.le hk0.le
    (by simpa [k] using hkf) ha hnpos hblog hf'
  have hE0 := growthE0_lower (n := n) (k := k) (f' := fShrink a f) (A := A) hγpos.le hk1
    (by simpa [k] using hkf) ha hAγ hnpos hblog hf'
  have hEpos : 0 < E := by
    have h58 : (0 : ℝ) < 5 / 8 := by norm_num
    have hprod : 0 < γ * k * (5 / 8) := mul_pos (mul_pos hγpos hk0) h58
    exact lt_of_lt_of_le hprod (by simpa [E] using hElow)
  have hμE : E ≤ D.expect X := by
    have hnew := expect_new_ge P hγpos.le ha hb hlog hnpos hUG hS (by simpa [k] using hcard)
    simpa [D, X, E, k, Distribution.expect_sub, Distribution.expect_const] using hnew
  have htpos : 0 < t := mul_pos (Real.sqrt_pos.mpr hk0) (fourthRoot_pos hk0)
  have hAt : A * t ≤ E := by
    have h11 : 0 ≤ γ * k * (11 / 24) :=
      mul_nonneg (mul_nonneg hγpos.le hk0.le) (by norm_num)
    have hE0def : E - A * t = growthE0 γ a b A n k := by
      simp [E, t, A, growthE0]
    linarith only [hE0, h11, hE0def]
  let lam : ℝ := A * t * D.expect X / E
  have hlam : 0 < lam := by
    have hnum : 0 < A * t * D.expect X :=
      mul_pos (mul_pos hA0 htpos) (lt_of_lt_of_le hEpos hμE)
    exact div_pos hnum hEpos
  have hshift : growthE0 γ a b A n k ≤ D.expect X - lam := by
    have hE0def : growthE0 γ a b A n k = E - A * t := by simp [growthE0, E, t, A]
    have hlamdef : lam = A * t * D.expect X / E := rfl
    rw [hE0def, hlamdef]
    exact shift_le hEpos hμE hAt
  have hsub : D.prob (fun T => X T ≤ growthE0 γ a b A n k) ≤
      D.prob (fun T => X T ≤ D.expect X - lam) :=
    prob_mono D (fun T hT => le_trans hT (by simpa [k, A] using hshift))
  have hcant := cantelli_lower D X hlam
  have hvar_eq : D.expect (fun T => (X T - D.expect X) ^ 2) =
      D.expect (fun T => ((T.card : ℝ) - D.expect (fun U => (U.card : ℝ))) ^ 2) := by
    have hμ : D.expect X = D.expect (fun T => (T.card : ℝ)) - k := by
      simp [X, D, Distribution.expect_sub, Distribution.expect_const]
    simp_rw [hμ, X]
    congr 1
    funext T
    ring
  have hcov := (hUG S hS (by simpa [k] using hcard)).2
  have hvar_le := variance_new_le P hc hnpos S hcov
  have hv : D.expect (fun T => (X T - D.expect X) ^ 2) ≤ D.expect X + c * k := by
    have hvarX : D.expect (fun T => (X T - D.expect X) ^ 2) ≤
        D.expect X + c * k := by
      simpa [D, k, hvar_eq] using hvar_le
    exact hvarX
  have ht2 : t ^ 2 = k * Real.sqrt k := threeFourth_sq hk0.le
  have hratio := ratio_bound hμE hEpos hA0 htpos hc hk0 (by simpa [E] using hElin) ht2
  have hv0 : 0 ≤ D.expect (fun T => (X T - D.expect X) ^ 2) :=
    D.expect_nonneg fun _ => sq_nonneg _
  have hlam_sq : (D.expect X + c * k) / lam ^ 2 =
      (D.expect X + c * k) * E ^ 2 / (A ^ 2 * t ^ 2 * D.expect X ^ 2) := by
    have hlamdef : lam = A * t * D.expect X / E := rfl
    rw [hlamdef]
    field_simp [hEpos.ne', hA0.ne', htpos.ne', (lt_of_lt_of_le hEpos hμE).ne']
  have hq : D.expect (fun T => (X T - D.expect X) ^ 2) / lam ^ 2 ≤ qTerm γ c A k := by
    have hden : 0 < lam ^ 2 := pow_pos hlam 2
    have hcmp : D.expect (fun T => (X T - D.expect X) ^ 2) / lam ^ 2 ≤
        (D.expect X + c * k) / lam ^ 2 :=
      div_le_div_of_nonneg_right hv hden.le
    have hq' : (D.expect X + c * k) * E ^ 2 / (A ^ 2 * t ^ 2 * D.expect X ^ 2) ≤
        qTerm γ c A k := by
      simpa [qTerm] using hratio
    linarith only [hcmp, hlam_sq, hq']
  have hQ := cantelli_ratio hv0 hlam hq
  have hprob : D.prob (fun T => X T ≤ growthE0 γ a b A n k) ≤
      qTerm γ c A k / (1 + qTerm γ c A k) := by
    calc D.prob (fun T => X T ≤ growthE0 γ a b A n k)
        ≤ D.prob (fun T => X T ≤ D.expect X - lam) := hsub
      _ ≤ D.expect (fun T => (X T - D.expect X) ^ 2) /
            (D.expect (fun T => (X T - D.expect X) ^ 2) + lam ^ 2) := hcant
      _ ≤ qTerm γ c A k / (1 + qTerm γ c A k) := hQ
  simpa [D, X, k, A] using hprob

/-- Indicator of still having fewer than `m` informed nodes. -/
noncomputable def below (m : ℝ) (T : Finset (Fin n)) : ℝ :=
  if (T.card : ℝ) < m then 1 else 0

lemma notYet_below (P : RumorProcess n) (m : ℝ) (t : ℕ) (S : Finset (Fin n)) :
    P.notYet m t S = P.K.iterate t (below m) S := by
  rw [RumorProcess.notYet, event_of_indicator P.K (fun U => (U.card : ℝ) < m) (below m)
      (fun U h => by simp [below, h]) (fun U h => by simp [below, h])]

lemma apply_below_le (P : RumorProcess n) (m : ℝ) (S : Finset (Fin n)) :
    P.K.apply (below m) S ≤ below m S := by
  by_cases h : (S.card : ℝ) < m
  · have hprob : P.K.apply (below m) S =
        (P.K S).prob (fun T => (T.card : ℝ) < m) := by
      rw [Kernel.apply, ← prob_indicator_eq (P.K S) (fun T => (T.card : ℝ) < m) (below m)
          (fun T hT => by simp [below, hT]) (fun T hT => by simp [below, hT])]
    rw [below, if_pos h, hprob]
    exact (P.K S).prob_le_one _
  · have hzero : ∀ T, S ⊆ T → below m T = 0 := by
      intro T hT
      have hcard : (S.card : ℝ) ≤ T.card := Nat.cast_le.mpr (card_le_card hT)
      have hge : ¬ (T.card : ℝ) < m := fun hTlt => h (lt_of_le_of_lt hcard hTlt)
      simp [below, hge]
    have heq := expect_eq_of_agree_on_superset P S (f := below m) (g := fun _ => (0 : ℝ)) hzero
    rw [below, if_neg h, Kernel.apply, heq, Distribution.expect_const]

lemma iterate_below_succ_le (P : RumorProcess n) (m : ℝ) (t : ℕ) (S : Finset (Fin n)) :
    P.K.iterate (t + 1) (below m) S ≤ P.K.iterate t (below m) S := by
  induction t generalizing S with
  | zero =>
    simpa [Kernel.iterate_zero, Kernel.iterate_succ] using apply_below_le P m S
  | succ t ih =>
    rw [Kernel.iterate_succ, Kernel.iterate_succ]
    exact (P.K S).expect_mono (fun U => ih U)

lemma notYet_antitone (P : RumorProcess n) (m : ℝ) {s t : ℕ} (hst : s ≤ t)
    (S : Finset (Fin n)) : P.notYet m t S ≤ P.notYet m s S := by
  rw [notYet_below, notYet_below]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hst
  clear hst
  induction d with
  | zero => exact le_rfl
  | succ d ih =>
    exact le_trans (iterate_below_succ_le P m (s + d) S) ih

lemma kSeq_succ_ge {γlo γ a b f : ℝ} {n : ℕ} (hγlo : 0 < γlo) (hγ : γlo ≤ γ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hf0 : 0 < f) (hn : growthN a b f ≤ n)
    (j : ℕ) (hj : j < phaseCount γ a f n) :
    kSeq γ a b (growthA γlo b) n j ≤ kSeq γ a b (growthA γlo b) n (j + 1) := by
  obtain ⟨hγpos, _, hnpos, hblog, hf', _, hAγ, _⟩ := stdFacts hγlo hγ ha hf0 hn
  have hj' : j ≤ phaseCount γ a f n := Nat.le_of_lt hj
  obtain ⟨hk1, _⟩ := kSeq_in_range hγlo hγ ha hb hf0 hn j hj'
  have hkf := kSeq_le_shrink hγlo hγ ha hb hf0 hn j hj'
  have hE0 := growthE0_lower (n := n) (k := kSeq γ a b (growthA γlo b) n j)
    (f' := fShrink a f) (A := growthA γlo b) hγpos.le hk1 hkf ha hAγ hnpos hblog hf'
  have hdef : kSeq γ a b (growthA γlo b) n (j + 1) =
      kSeq γ a b (growthA γlo b) n j +
        growthE0 γ a b (growthA γlo b) n (kSeq γ a b (growthA γlo b) n j) := rfl
  have hpos : 0 ≤ growthE0 γ a b (growthA γlo b) n (kSeq γ a b (growthA γlo b) n j) := by
    have h11 : 0 ≤ γ * kSeq γ a b (growthA γlo b) n j * (11 / 24) :=
      mul_nonneg (mul_nonneg hγpos.le (by linarith only [hk1])) (by norm_num)
    linarith only [hE0, h11]
  linarith only [hdef, hpos]

lemma kSeq_le_add {γlo γ a b f : ℝ} {n : ℕ} (hγlo : 0 < γlo) (hγ : γlo ≤ γ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hf0 : 0 < f) (hn : growthN a b f ≤ n)
    (j d : ℕ) (hj : j + d ≤ phaseCount γ a f n) :
    kSeq γ a b (growthA γlo b) n j ≤ kSeq γ a b (growthA γlo b) n (j + d) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hlt : j + d < phaseCount γ a f n := by omega
    have hstep := kSeq_succ_ge hγlo hγ ha hb hf0 hn (j + d) hlt
    have hrec := ih (Nat.le_of_lt hlt)
    exact le_trans hrec hstep

lemma kSeq_le_count {γlo γ a b f : ℝ} {n : ℕ} (hγlo : 0 < γlo) (hγ : γlo ≤ γ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hf0 : 0 < f) (hn : growthN a b f ≤ n)
    (j : ℕ) (hj : j ≤ phaseCount γ a f n) :
    kSeq γ a b (growthA γlo b) n j ≤
      kSeq γ a b (growthA γlo b) n (phaseCount γ a f n) := by
  simpa [Nat.add_sub_of_le hj] using
    kSeq_le_add hγlo hγ ha hb hf0 hn j (phaseCount γ a f n - j)
      (le_of_eq (Nat.add_sub_of_le hj))

/-- Largest `j ≤ J` with `k_j ≤ k`, or `0` when `k < k_0`. -/
noncomputable def phaseIdx (γlo γ a b : ℝ) (n J : ℕ) (k : ℝ) : ℕ :=
  @Nat.findGreatest (fun j => kSeq γ a b (growthA γlo b) n j ≤ k) (Classical.decPred _) J

lemma phaseIdx_le (γlo γ a b : ℝ) (n J : ℕ) (k : ℝ) : phaseIdx γlo γ a b n J k ≤ J := by
  unfold phaseIdx
  exact Nat.findGreatest_le J

lemma phaseIdx_k_le {γlo γ a b : ℝ} {n J : ℕ} {k : ℝ} (hk : 1 ≤ k) :
    kSeq γ a b (growthA γlo b) n (phaseIdx γlo γ a b n J k) ≤ k := by
  have hP : kSeq γ a b (growthA γlo b) n 0 ≤ k := by simpa [kSeq] using hk
  unfold phaseIdx
  exact Nat.findGreatest_spec (m := 0) (P := fun j => kSeq γ a b (growthA γlo b) n j ≤ k)
    (Nat.zero_le J) hP

lemma le_phaseIdx {γlo γ a b : ℝ} {n J j : ℕ} {k : ℝ} (hj : j ≤ J)
    (hk : kSeq γ a b (growthA γlo b) n j ≤ k) : j ≤ phaseIdx γlo γ a b n J k := by
  unfold phaseIdx
  exact Nat.le_findGreatest hj hk

lemma phaseIdx_next {γlo γ a b : ℝ} {n J : ℕ} {k : ℝ} {j : ℕ}
    (hj : phaseIdx γlo γ a b n J k < j) (hjJ : j ≤ J) :
    ¬ kSeq γ a b (growthA γlo b) n j ≤ k := by
  unfold phaseIdx at hj
  exact Nat.findGreatest_is_greatest hj hjJ

lemma phaseIdx_of_ge {γlo γ a b : ℝ} {n J : ℕ} {k : ℝ}
    (hk : kSeq γ a b (growthA γlo b) n J ≤ k) : phaseIdx γlo γ a b n J k = J :=
  le_antisymm (phaseIdx_le γlo γ a b n J k) (le_phaseIdx le_rfl hk)

noncomputable def connectP (γlo γhi a b f : ℝ) : ℝ :=
  γlo * (alphaSeq b γlo * fShrink a f / (1 + γhi)) * ((1 - a * f) / 2)

lemma connectP_pos {γlo γhi a b f : ℝ} (hγlo : 0 < γlo) (hγ : γlo ≤ γhi) (ha : 0 ≤ a)
    (hf0 : 0 < f) (haf : a * f < 1) : 0 < connectP γlo γhi a b f := by
  have hdenγ : 0 < 1 + γhi := by linarith only [hγlo, hγ]
  have hden : 0 < 1 - a * f := by linarith only [haf]
  unfold connectP
  exact mul_pos
    (mul_pos hγlo (div_pos (mul_pos (alphaSeq_pos b γlo) (fShrink_pos hf0 ha)) hdenγ))
    (div_pos hden (by norm_num))

lemma connectP_le_half {γlo γhi a b f : ℝ} (hγlo : 0 < γlo) (hγ : γlo ≤ γhi) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hf0 : 0 < f) (haf : a * f < 1) : connectP γlo γhi a b f ≤ 1 / 2 := by
  have hγfrac : γlo / (1 + γhi) ≤ 1 := by
    rw [div_le_one (by linarith only [hγlo, hγ] : (0 : ℝ) < 1 + γhi)]
    linarith only [hγlo, hγ]
  have hα : alphaSeq b γlo ≤ 1 := alphaSeq_le_one hb hγlo
  have hf' : fShrink a f ≤ 1 := fShrink_le_one ha
  have hhalf : (1 - a * f) / 2 ≤ 1 / 2 := by
    have haf0 : 0 ≤ a * f := mul_nonneg ha hf0.le
    have hle : 1 - a * f ≤ 1 := by linarith only [haf0]
    exact div_le_div_of_nonneg_right hle (by norm_num)
  have hident : connectP γlo γhi a b f =
      (γlo / (1 + γhi)) * alphaSeq b γlo * fShrink a f * ((1 - a * f) / 2) := by
    unfold connectP
    field_simp [(by linarith only [hγlo, hγ] : (1 + γhi) ≠ 0)]
  have h1 : (γlo / (1 + γhi)) * alphaSeq b γlo ≤ 1 := by
    have h := mul_le_mul hγfrac hα (alphaSeq_pos b γlo).le (by norm_num : (0 : ℝ) ≤ 1)
    simpa [one_mul] using h
  have h2 : (γlo / (1 + γhi)) * alphaSeq b γlo * fShrink a f ≤ 1 := by
    have h := mul_le_mul h1 hf' (fShrink_pos hf0 ha).le (by norm_num : (0 : ℝ) ≤ 1)
    simpa [mul_one] using h
  have hhalf0 : 0 ≤ (1 - a * f) / 2 :=
    div_nonneg (by linarith only [haf]) (by norm_num)
  have h3 := mul_le_mul h2 hhalf hhalf0 (by norm_num : (0 : ℝ) ≤ 1)
  rw [hident]
  simpa [one_mul] using h3

lemma Q_le_q {q : ℝ} (hq : 0 ≤ q) : q / (1 + q) ≤ q := by
  have h1 : 0 < 1 + q := by linarith only [hq]
  rw [div_le_iff₀ h1]
  have hmul : q * (1 + q) = q + q * q := by ring
  have hnn : 0 ≤ q * q := mul_nonneg hq hq
  linarith only [hmul, hnn]

lemma contract {Q x g : ℝ} (hx : x ≠ 0) (hden : 1 - x * Q ≠ 0) :
    Q * ((x * (1 - Q) / (1 - x * Q)) * g) + (1 - Q) * g =
      ((x * (1 - Q) / (1 - x * Q)) * g) / x := by
  have hcoef : Q * (x * (1 - Q) / (1 - x * Q)) + (1 - Q) =
      (1 - Q) / (1 - x * Q) := by
    apply (mul_right_inj' hden).mp
    field_simp [hden]
    ring
  have hright : (x * (1 - Q) / (1 - x * Q)) / x = (1 - Q) / (1 - x * Q) := by
    field_simp [hx, hden]
  calc Q * ((x * (1 - Q) / (1 - x * Q)) * g) + (1 - Q) * g
      = (Q * (x * (1 - Q) / (1 - x * Q)) + (1 - Q)) * g := by ring
    _ = ((1 - Q) / (1 - x * Q)) * g := by rw [hcoef]
    _ = ((x * (1 - Q) / (1 - x * Q)) / x) * g := by rw [← hright]
    _ = ((x * (1 - Q) / (1 - x * Q)) * g) / x := by ring

lemma pow_inv_shift {x : ℝ} (hx : x ≠ 0) (J s : ℕ) (p : ℝ) :
    (x⁻¹) ^ (J + s) * (x ^ J * p) = (x⁻¹) ^ s * p := by
  have hcancel : (x⁻¹) ^ J * x ^ J = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hx, one_pow]
  calc (x⁻¹) ^ (J + s) * (x ^ J * p)
      = (x⁻¹) ^ J * (x⁻¹) ^ s * (x ^ J * p) := by rw [pow_add]
    _ = (x⁻¹) ^ J * x ^ J * ((x⁻¹) ^ s * p) := by ring
    _ = 1 * ((x⁻¹) ^ s * p) := by rw [hcancel]
    _ = (x⁻¹) ^ s * p := by rw [one_mul]

lemma exp_rate_le {a b r : ℝ} (hab : a ≤ b) (hr : 0 ≤ r) :
    Real.exp (-b * r) ≤ Real.exp (-a * r) :=
  (Real.exp_le_exp).mpr (by
    have h := mul_le_mul_of_nonneg_right hab hr
    linarith only [h])

noncomputable def phaseQ (γ c A k : ℝ) : ℝ :=
  qTerm γ c A k / (1 + qTerm γ c A k)

lemma phaseQ_nonneg {γ c A k : ℝ} (hγ : 0 ≤ γ) (hc : 0 ≤ c) : 0 ≤ phaseQ γ c A k := by
  have hq := qTerm_nonneg (γ := γ) (c := c) (A := A) (k := k) hγ hc
  have hden : 0 < 1 + qTerm γ c A k := by linarith only [hq]
  exact div_nonneg hq hden.le

lemma phaseQ_le_q {γ c A k : ℝ} (hγ : 0 ≤ γ) (hc : 0 ≤ c) :
    phaseQ γ c A k ≤ qTerm γ c A k := by
  simpa [phaseQ] using Q_le_q (qTerm_nonneg (γ := γ) (c := c) (A := A) (k := k) hγ hc)

lemma phaseQ_antitone {γ c A k k' : ℝ} (hγ : 0 ≤ γ) (hc : 0 ≤ c) (hA : A ≠ 0)
    (hk : 0 < k) (hk' : k ≤ k') : phaseQ γ c A k' ≤ phaseQ γ c A k := by
  have hq := qTerm_nonneg (γ := γ) (c := c) (A := A) (k := k') hγ hc
  simpa [phaseQ] using Qof_mono hq (qTerm_antitone hγ hc hA hk hk')

lemma qTerm_le_qCap {γlo γhi γ b c k : ℝ} (hγlo : 0 < γlo) (hγhi : γ ≤ γhi)
    (hγ0 : 0 ≤ γhi) (hc : 0 ≤ c) (hk : 1 ≤ k) :
    qTerm γ c (growthA γlo b) k ≤ qCap γlo γhi b c := by
  have hk0 : 0 < k := by linarith only [hk]
  have hsqrt : 1 ≤ Real.sqrt k := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hk
  have hA := growthA_pos (b := b) hγlo
  have hden : 0 < (growthA γlo b) ^ 2 := pow_pos hA 2
  have hdenS : 0 < (growthA γlo b) ^ 2 * Real.sqrt k :=
    mul_pos hden (Real.sqrt_pos.mpr hk0)
  have hnum : γ + c ≤ γhi + c := by linarith only [hγhi]
  have hdiv := div_le_div_of_nonneg_right hnum hdenS.le
  have hdenle : (growthA γlo b) ^ 2 ≤ (growthA γlo b) ^ 2 * Real.sqrt k := by
    have h := mul_le_mul_of_nonneg_left hsqrt (sq_nonneg (growthA γlo b))
    simpa [mul_one] using h
  have hinv : (γhi + c) / ((growthA γlo b) ^ 2 * Real.sqrt k) ≤
      (γhi + c) / (growthA γlo b) ^ 2 :=
    div_le_div_of_nonneg_left (by linarith only [hγ0, hc]) hden hdenle
  unfold qTerm qCap
  linarith only [hdiv, hinv]

lemma phaseQ_le_Qstar {γlo γhi γ b c k : ℝ} (hγlo : 0 < γlo) (hγ : γlo ≤ γ)
    (hγhi : γ ≤ γhi) (hc : 0 ≤ c) (hk : 1 ≤ k) :
    phaseQ γ c (growthA γlo b) k ≤ Qstar γlo γhi b c := by
  have hγ0 : 0 ≤ γhi := le_trans hγlo.le (le_trans hγ hγhi)
  have hq : qTerm γ c (growthA γlo b) k ≤ qCap γlo γhi b c :=
    qTerm_le_qCap hγlo hγhi hγ0 hc hk
  have hmono := Qof_mono (qTerm_nonneg (γ := γ) (c := c) (A := growthA γlo b) (k := k)
    (le_trans hγlo.le hγ) hc) hq
  simpa [phaseQ, Qstar] using hmono

noncomputable def phaseRatio (γlo γhi γ a b c : ℝ) (n i : ℕ) : ℝ :=
  xDecay γlo γhi b c *
      (1 - phaseQ γ c (growthA γlo b) (kSeq γ a b (growthA γlo b) n i)) /
    (1 - xDecay γlo γhi b c *
      phaseQ γ c (growthA γlo b) (kSeq γ a b (growthA γlo b) n i))

noncomputable def phaseG (γlo γhi γ a b c f : ℝ) (n j : ℕ) : ℝ :=
  ∏ i ∈ Ico j (phaseCount γ a f n), phaseRatio γlo γhi γ a b c n i

lemma phaseQ_k_le {γlo γhi γ a b c f : ℝ} {n : ℕ} (hγlo : 0 < γlo) (hγ : γlo ≤ γ)
    (hγhi : γ ≤ γhi) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hf0 : 0 < f)
    (hn : growthN a b f ≤ n) (i : ℕ) (hi : i ≤ phaseCount γ a f n) :
    phaseQ γ c (growthA γlo b) (kSeq γ a b (growthA γlo b) n i) ≤
      Qstar γlo γhi b c := by
  have hk := (kSeq_in_range hγlo hγ ha hb hf0 hn i hi).1
  exact phaseQ_le_Qstar hγlo hγ hγhi hc hk

lemma phaseRatio_ge_one {γlo γhi γ a b c f : ℝ} {n : ℕ} (hγlo : 0 < γlo) (hγ : γlo ≤ γ)
    (hγhi : γ ≤ γhi) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hf0 : 0 < f)
    (hn : growthN a b f ≤ n) {i : ℕ} (hi : i < phaseCount γ a f n) :
    1 ≤ phaseRatio γlo γhi γ a b c n i := by
  let Q : ℝ := phaseQ γ c (growthA γlo b) (kSeq γ a b (growthA γlo b) n i)
  let x : ℝ := xDecay γlo γhi b c
  have hx : 1 < x := xDecay_gt_one hγlo (le_trans hγ hγhi) hc
  have hxQ : x * Qstar γlo γhi b c < 1 :=
    xDecay_Qstar_lt_one hγlo (le_trans hγ hγhi) hc
  have hQ := phaseQ_k_le hγlo hγ hγhi ha hb hc hf0 hn i (Nat.le_of_lt hi)
  have hx0 : 0 ≤ x := le_trans zero_le_one (le_of_lt hx)
  have hden : 0 < 1 - x * Q := by
    have hmul : x * Q ≤ x * Qstar γlo γhi b c := mul_le_mul_of_nonneg_left hQ hx0
    linarith only [hmul, hxQ]
  have hdiff : x * (1 - Q) - (1 - x * Q) = x - 1 := by ring
  have hnum : 1 - x * Q ≤ x * (1 - Q) := by linarith only [hdiff, hx]
  unfold phaseRatio
  rw [le_div_iff₀ hden]
  simpa [Q, x, one_mul] using hnum

lemma phaseG_top {γlo γhi γ a b c f : ℝ} {n : ℕ} :
    phaseG γlo γhi γ a b c f n (phaseCount γ a f n) = 1 := by
  simp [phaseG]

lemma phaseG_succ {γlo γhi γ a b c f : ℝ} {n j : ℕ} (hj : j < phaseCount γ a f n) :
    phaseG γlo γhi γ a b c f n j =
      phaseRatio γlo γhi γ a b c n j * phaseG γlo γhi γ a b c f n (j + 1) := by
  simpa [phaseG] using
    Finset.prod_eq_prod_Ico_succ_bot hj (phaseRatio γlo γhi γ a b c n)

lemma phaseG_ge_one {γlo γhi γ a b c f : ℝ} {n : ℕ} (hγlo : 0 < γlo) (hγ : γlo ≤ γ)
    (hγhi : γ ≤ γhi) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hf0 : 0 < f)
    (hn : growthN a b f ≤ n) {j : ℕ} (_hj : j ≤ phaseCount γ a f n) :
    1 ≤ phaseG γlo γhi γ a b c f n j := by
  refine Finset.one_le_prod ?_
  intro i hi
  exact phaseRatio_ge_one hγlo hγ hγhi ha hb hc hf0 hn (mem_Ico.mp hi).2

lemma phaseG_antitone {γlo γhi γ a b c f : ℝ} {n : ℕ} (hγlo : 0 < γlo) (hγ : γlo ≤ γ)
    (hγhi : γ ≤ γhi) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hf0 : 0 < f)
    (hn : growthN a b f ≤ n) {j j' : ℕ} (hjj : j ≤ j') (hj' : j' ≤ phaseCount γ a f n) :
    phaseG γlo γhi γ a b c f n j' ≤ phaseG γlo γhi γ a b c f n j := by
  have hsplit : phaseG γlo γhi γ a b c f n j =
      (∏ i ∈ Ico j j', phaseRatio γlo γhi γ a b c n i) *
        phaseG γlo γhi γ a b c f n j' := by
    simpa [phaseG] using
      (Finset.prod_Ico_consecutive (phaseRatio γlo γhi γ a b c n) hjj hj').symm
  have hprod : 1 ≤ ∏ i ∈ Ico j j', phaseRatio γlo γhi γ a b c n i := by
    refine Finset.one_le_prod ?_
    intro i hi
    exact phaseRatio_ge_one hγlo hγ hγhi ha hb hc hf0 hn
      (lt_of_lt_of_le (mem_Ico.mp hi).2 hj')
  have hG : 0 ≤ phaseG γlo γhi γ a b c f n j' :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1) (phaseG_ge_one hγlo hγ hγhi ha hb hc hf0 hn hj')
  have hmul := mul_le_mul_of_nonneg_right hprod hG
  rw [one_mul] at hmul
  exact le_trans hmul (le_of_eq hsplit.symm)

lemma phase_contract {γlo γhi γ a b c f : ℝ} {n : ℕ} (hγlo : 0 < γlo) (hγ : γlo ≤ γ)
    (hγhi : γ ≤ γhi) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hf0 : 0 < f)
    (hn : growthN a b f ≤ n) {j : ℕ} (hj : j < phaseCount γ a f n) :
    phaseQ γ c (growthA γlo b) (kSeq γ a b (growthA γlo b) n j) *
        phaseG γlo γhi γ a b c f n j +
      (1 - phaseQ γ c (growthA γlo b) (kSeq γ a b (growthA γlo b) n j)) *
        phaseG γlo γhi γ a b c f n (j + 1) =
      phaseG γlo γhi γ a b c f n j / xDecay γlo γhi b c := by
  let Q : ℝ := phaseQ γ c (growthA γlo b) (kSeq γ a b (growthA γlo b) n j)
  let x : ℝ := xDecay γlo γhi b c
  have hx : 1 < x := xDecay_gt_one hγlo (le_trans hγ hγhi) hc
  have hxQ : x * Qstar γlo γhi b c < 1 :=
    xDecay_Qstar_lt_one hγlo (le_trans hγ hγhi) hc
  have hQ := phaseQ_k_le hγlo hγ hγhi ha hb hc hf0 hn j (Nat.le_of_lt hj)
  have hden : 1 - x * Q ≠ 0 := by
    have hmul : x * Q ≤ x * Qstar γlo γhi b c :=
      mul_le_mul_of_nonneg_left hQ (le_trans zero_le_one (le_of_lt hx))
    linarith only [hmul, hxQ]
  have hC := contract (Q := Q) (x := x) (g := phaseG γlo γhi γ a b c f n (j + 1))
    (ne_of_gt (lt_trans (by norm_num : (0 : ℝ) < 1) hx)) hden
  rw [phaseG_succ hj]
  exact hC

lemma kSeq_le_of_phase {γlo γ a b : ℝ} {n J : ℕ} {k : ℝ} (hk : 1 ≤ k)
    (hidx : phaseIdx γlo γ a b n J k = J) :
    kSeq γ a b (growthA γlo b) n J ≤ k := by
  by_cases hJ : J = 0
  · simpa [hJ, kSeq] using hk
  · exact @Nat.findGreatest_of_ne_zero J
      (fun j => kSeq γ a b (growthA γlo b) n j ≤ k) (Classical.decPred _) J
      (by simpa [phaseIdx] using hidx) hJ

lemma e0_mono {γlo γ a b f : ℝ} {n : ℕ} (hγlo : 0 < γlo) (hγ : γlo ≤ γ) (ha : 0 ≤ a)
    (hf0 : 0 < f) (hn : growthN a b f ≤ n) {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y)
    (hy : y ≤ fShrink a f * n) :
    growthE0 γ a b (growthA γlo b) n x ≤ growthE0 γ a b (growthA γlo b) n y := by
  obtain ⟨hγpos, hlog, hnpos, hblog, hf', _, hAγ, _⟩ := stdFacts hγlo hγ ha hf0 hn
  have hdiff := growthE0_diff (n := n) (x := x) (y := y) (f' := fShrink a f)
    (A := growthA γlo b) hγpos.le hx hxy hy ha hAγ hnpos hlog hblog hf'
  have hnn : 0 ≤ γ * (y - x) * (3 / 8) :=
    mul_nonneg (mul_nonneg hγpos.le (by linarith only [hxy])) (by norm_num)
  linarith only [hdiff, hnn]

lemma k_shortfall {γlo γ a b f : ℝ} {n : ℕ} (hγlo : 0 < γlo) (hγ : γlo ≤ γ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hf0 : 0 < f) (hn : growthN a b f ≤ n)
    {k : ℝ} (hkf : k ≤ fShrink a f * n) {j : ℕ}
    (hj : j < phaseCount γ a f n) (hkj : kSeq γ a b (growthA γlo b) n j ≤ k) :
    kSeq γ a b (growthA γlo b) n (j + 1) - k ≤
      growthE0 γ a b (growthA γlo b) n k := by
  have hkSeq := (kSeq_in_range hγlo hγ ha hb hf0 hn j (Nat.le_of_lt hj)).1
  have hkf' : kSeq γ a b (growthA γlo b) n j ≤ fShrink a f * n :=
    kSeq_le_shrink hγlo hγ ha hb hf0 hn j (Nat.le_of_lt hj)
  have hmono := e0_mono hγlo hγ ha hf0 hn hkSeq hkj (le_trans hkf (le_refl _))
  have hdef : kSeq γ a b (growthA γlo b) n (j + 1) =
      kSeq γ a b (growthA γlo b) n j +
        growthE0 γ a b (growthA γlo b) n (kSeq γ a b (growthA γlo b) n j) := rfl
  linarith only [hdef, hmono, hkj, hkf']

lemma short_prob_le {γlo γ a b c f : ℝ} (P : RumorProcess n) (hγlo : 0 < γlo)
    (hγ : γlo ≤ γ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hf0 : 0 < f)
    (hn : growthN a b f ≤ n) (hUG : P.UpperGrowth γ a b c f) {S : Finset (Fin n)}
    (hk1 : (1 : ℝ) ≤ S.card) (hkf : (S.card : ℝ) ≤ fShrink a f * n) {j : ℕ}
    (hj : j < phaseCount γ a f n) (hkj : kSeq γ a b (growthA γlo b) n j ≤ S.card) :
    (P.K S).prob (fun T => (T.card : ℝ) < kSeq γ a b (growthA γlo b) n (j + 1)) ≤
      phaseQ γ c (growthA γlo b) (kSeq γ a b (growthA γlo b) n j) := by
  have hcard_pos : 0 < S.card := by
    have : (0 : ℝ) < S.card := by linarith only [hk1]
    exact_mod_cast this
  have hS : S.Nonempty := card_pos.mp hcard_pos
  have hshort := k_shortfall hγlo hγ ha hb hf0 hn hkf hj hkj
  have hsub : (P.K S).prob (fun T => (T.card : ℝ) <
        kSeq γ a b (growthA γlo b) n (j + 1)) ≤
      (P.K S).prob (fun T => (T.card : ℝ) - (S.card : ℝ) ≤
        growthE0 γ a b (growthA γlo b) n (S.card : ℝ)) := by
    refine prob_mono (P.K S) ?_
    intro T hT
    have hlt : (T.card : ℝ) - (S.card : ℝ) <
        kSeq γ a b (growthA γlo b) n (j + 1) - (S.card : ℝ) := by linarith only [hT]
    exact le_of_lt (lt_of_lt_of_le hlt hshort)
  have hfail := fail_prob_le P hγlo hγ ha hb hc hf0 hn hUG hS hk1 hkf
  have hk0 : 0 < kSeq γ a b (growthA γlo b) n j := by
    have hk := (kSeq_in_range hγlo hγ ha hb hf0 hn j (Nat.le_of_lt hj)).1
    linarith only [hk]
  have hanti := phaseQ_antitone (le_trans hγlo.le hγ) hc (growthA_pos (b := b) hγlo).ne'
    hk0 hkj
  exact le_trans hsub (le_trans (by simpa [phaseQ] using hfail) hanti)

lemma phasePot_mix {γlo γhi γ a b c f : ℝ} {n : ℕ} (hγlo : 0 < γlo) (hγ : γlo ≤ γ)
    (hγhi : γ ≤ γhi) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hf0 : 0 < f)
    (hn : growthN a b f ≤ n) {j : ℕ} (hj : j < phaseCount γ a f n)
    {T : Finset (Fin n)} (hkj : kSeq γ a b (growthA γlo b) n j ≤ T.card) :
    phaseG γlo γhi γ a b c f n
        (phaseIdx γlo γ a b n (phaseCount γ a f n) (T.card : ℝ)) ≤
      phaseG γlo γhi γ a b c f n (j + 1) +
        (phaseG γlo γhi γ a b c f n j - phaseG γlo γhi γ a b c f n (j + 1)) *
          below (kSeq γ a b (growthA γlo b) n (j + 1)) T := by
  let J : ℕ := phaseCount γ a f n
  let p : ℕ := phaseIdx γlo γ a b n J (T.card : ℝ)
  by_cases hlt : (T.card : ℝ) < kSeq γ a b (growthA γlo b) n (j + 1)
  · have hp : j ≤ p := le_phaseIdx (Nat.le_of_lt hj) hkj
    have hanti := phaseG_antitone hγlo hγ hγhi ha hb hc hf0 hn hp (phaseIdx_le _ _ _ _ _ _ _)
    rw [below, if_pos hlt]
    linarith only [hanti]
  · have hge : kSeq γ a b (growthA γlo b) n (j + 1) ≤ T.card := not_lt.mp hlt
    have hp : j + 1 ≤ p := le_phaseIdx (Nat.succ_le_of_lt hj) hge
    have hanti := phaseG_antitone hγlo hγ hγhi ha hb hc hf0 hn hp (phaseIdx_le _ _ _ _ _ _ _)
    rw [below, if_neg hlt]
    linarith only [hanti]

lemma expect_phase_le {γlo γhi γ a b c f : ℝ} (P : RumorProcess n) (hγlo : 0 < γlo)
    (hγ : γlo ≤ γ) (hγhi : γ ≤ γhi) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hf0 : 0 < f) (hn : growthN a b f ≤ n) (hUG : P.UpperGrowth γ a b c f)
    {S : Finset (Fin n)} (hk1 : (1 : ℝ) ≤ S.card)
    (hj : phaseIdx γlo γ a b n (phaseCount γ a f n) (S.card : ℝ) < phaseCount γ a f n) :
    (P.K S).expect (fun T => phaseG γlo γhi γ a b c f n
        (phaseIdx γlo γ a b n (phaseCount γ a f n) (T.card : ℝ))) ≤
      phaseG γlo γhi γ a b c f n
          (phaseIdx γlo γ a b n (phaseCount γ a f n) (S.card : ℝ)) /
        xDecay γlo γhi b c := by
  let J : ℕ := phaseCount γ a f n
  let j : ℕ := phaseIdx γlo γ a b n J (S.card : ℝ)
  have hkj : kSeq γ a b (growthA γlo b) n j ≤ S.card := phaseIdx_k_le hk1
  have hnot := phaseIdx_next (j := j + 1) (Nat.lt_succ_self j) (Nat.succ_le_of_lt hj)
  have hlt : (S.card : ℝ) < kSeq γ a b (growthA γlo b) n (j + 1) := lt_of_not_ge hnot
  have hkf : (S.card : ℝ) ≤ fShrink a f * n :=
    le_trans (le_of_lt hlt) (kSeq_le_shrink hγlo hγ ha hb hf0 hn (j + 1)
      (Nat.succ_le_of_lt hj))
  have hmix : ∀ T, S ⊆ T → phaseG γlo γhi γ a b c f n
        (phaseIdx γlo γ a b n J (T.card : ℝ)) ≤
      phaseG γlo γhi γ a b c f n (j + 1) +
        (phaseG γlo γhi γ a b c f n j - phaseG γlo γhi γ a b c f n (j + 1)) *
          below (kSeq γ a b (growthA γlo b) n (j + 1)) T := by
    intro T hT
    have hcard : kSeq γ a b (growthA γlo b) n j ≤ T.card :=
      le_trans hkj (Nat.cast_le.mpr (card_le_card hT))
    exact phasePot_mix hγlo hγ hγhi ha hb hc hf0 hn hj hcard
  have hE := expect_le_of_weight P S hmix
  have hexp : (P.K S).expect (fun T => phaseG γlo γhi γ a b c f n (j + 1) +
        (phaseG γlo γhi γ a b c f n j - phaseG γlo γhi γ a b c f n (j + 1)) *
          below (kSeq γ a b (growthA γlo b) n (j + 1)) T) =
      phaseG γlo γhi γ a b c f n (j + 1) +
        (phaseG γlo γhi γ a b c f n j - phaseG γlo γhi γ a b c f n (j + 1)) *
          (P.K S).expect (below (kSeq γ a b (growthA γlo b) n (j + 1))) := by
    rw [Distribution.expect_add, Distribution.expect_mul, Distribution.expect_const]
  have hprob : (P.K S).expect (below (kSeq γ a b (growthA γlo b) n (j + 1))) =
      (P.K S).prob (fun T => (T.card : ℝ) < kSeq γ a b (growthA γlo b) n (j + 1)) :=
    (prob_indicator_eq (P.K S) (fun T => (T.card : ℝ) <
        kSeq γ a b (growthA γlo b) n (j + 1))
      (below (kSeq γ a b (growthA γlo b) n (j + 1)))
      (fun T hT => by simp [below, hT]) (fun T hT => by simp [below, hT])).symm
  have hQ := short_prob_le P hγlo hγ ha hb hc hf0 hn hUG hk1 hkf hj hkj
  have hcoeff : 0 ≤ phaseG γlo γhi γ a b c f n j -
      phaseG γlo γhi γ a b c f n (j + 1) := by
    have hanti := phaseG_antitone hγlo hγ hγhi ha hb hc hf0 hn
      (Nat.le_succ j) (Nat.succ_le_of_lt hj)
    linarith only [hanti]
  have hscaled := mul_le_mul_of_nonneg_left hQ hcoeff
  have hident : phaseG γlo γhi γ a b c f n (j + 1) +
        (phaseG γlo γhi γ a b c f n j - phaseG γlo γhi γ a b c f n (j + 1)) *
          phaseQ γ c (growthA γlo b) (kSeq γ a b (growthA γlo b) n j) =
      phaseQ γ c (growthA γlo b) (kSeq γ a b (growthA γlo b) n j) *
          phaseG γlo γhi γ a b c f n j +
        (1 - phaseQ γ c (growthA γlo b) (kSeq γ a b (growthA γlo b) n j)) *
          phaseG γlo γhi γ a b c f n (j + 1) := by ring
  have hcontract := phase_contract hγlo hγ hγhi ha hb hc hf0 hn hj
  calc (P.K S).expect (fun T => phaseG γlo γhi γ a b c f n
          (phaseIdx γlo γ a b n (phaseCount γ a f n) (T.card : ℝ)))
      ≤ (P.K S).expect (fun T => phaseG γlo γhi γ a b c f n (j + 1) +
          (phaseG γlo γhi γ a b c f n j - phaseG γlo γhi γ a b c f n (j + 1)) *
            below (kSeq γ a b (growthA γlo b) n (j + 1)) T) := hE
    _ = phaseG γlo γhi γ a b c f n (j + 1) +
          (phaseG γlo γhi γ a b c f n j - phaseG γlo γhi γ a b c f n (j + 1)) *
            (P.K S).expect (below (kSeq γ a b (growthA γlo b) n (j + 1))) := hexp
    _ = phaseG γlo γhi γ a b c f n (j + 1) +
          (phaseG γlo γhi γ a b c f n j - phaseG γlo γhi γ a b c f n (j + 1)) *
            (P.K S).prob (fun T => (T.card : ℝ) <
              kSeq γ a b (growthA γlo b) n (j + 1)) := by rw [hprob]
    _ = (phaseG γlo γhi γ a b c f n j - phaseG γlo γhi γ a b c f n (j + 1)) *
          (P.K S).prob (fun T => (T.card : ℝ) <
            kSeq γ a b (growthA γlo b) n (j + 1)) +
        phaseG γlo γhi γ a b c f n (j + 1) := by ring
    _ ≤ (phaseG γlo γhi γ a b c f n j - phaseG γlo γhi γ a b c f n (j + 1)) *
          phaseQ γ c (growthA γlo b) (kSeq γ a b (growthA γlo b) n j) +
        phaseG γlo γhi γ a b c f n (j + 1) :=
          add_le_add_left hscaled (phaseG γlo γhi γ a b c f n (j + 1))
    _ = phaseG γlo γhi γ a b c f n (j + 1) +
          (phaseG γlo γhi γ a b c f n j - phaseG γlo γhi γ a b c f n (j + 1)) *
            phaseQ γ c (growthA γlo b) (kSeq γ a b (growthA γlo b) n j) := by ring
    _ = phaseQ γ c (growthA γlo b) (kSeq γ a b (growthA γlo b) n j) *
            phaseG γlo γhi γ a b c f n j +
          (1 - phaseQ γ c (growthA γlo b) (kSeq γ a b (growthA γlo b) n j)) *
            phaseG γlo γhi γ a b c f n (j + 1) := hident
    _ = phaseG γlo γhi γ a b c f n
          (phaseIdx γlo γ a b n (phaseCount γ a f n) (S.card : ℝ)) /
        xDecay γlo γhi b c := hcontract

lemma below_le_phaseG {γlo γhi γ a b c f : ℝ} {n : ℕ} (hγlo : 0 < γlo) (hγ : γlo ≤ γ)
    (hγhi : γ ≤ γhi) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hf0 : 0 < f)
    (hn : growthN a b f ≤ n) {S : Finset (Fin n)} (hk : (1 : ℝ) ≤ S.card) :
    below (kSeq γ a b (growthA γlo b) n (phaseCount γ a f n)) S ≤
      phaseG γlo γhi γ a b c f n
        (phaseIdx γlo γ a b n (phaseCount γ a f n) (S.card : ℝ)) := by
  let J : ℕ := phaseCount γ a f n
  by_cases hJ : phaseIdx γlo γ a b n J (S.card : ℝ) = J
  · have hge := kSeq_le_of_phase hk hJ
    rw [below, if_neg (not_lt.mpr hge)]
    exact le_trans (by norm_num : (0 : ℝ) ≤ 1)
      (phaseG_ge_one hγlo hγ hγhi ha hb hc hf0 hn (phaseIdx_le _ _ _ _ _ _ _))
  · have hj : phaseIdx γlo γ a b n J (S.card : ℝ) < J :=
      lt_of_le_of_ne (phaseIdx_le _ _ _ _ _ _ _) hJ
    let j : ℕ := phaseIdx γlo γ a b n J (S.card : ℝ)
    have hnot := phaseIdx_next (j := j + 1) (Nat.lt_succ_self j) (Nat.succ_le_of_lt hj)
    have hlt : (S.card : ℝ) < kSeq γ a b (growthA γlo b) n (j + 1) := lt_of_not_ge hnot
    have hstep := kSeq_le_count hγlo hγ ha hb hf0 hn (j + 1) (Nat.succ_le_of_lt hj)
    have hbelow : (S.card : ℝ) < kSeq γ a b (growthA γlo b) n J := lt_of_lt_of_le hlt hstep
    rw [below, if_pos hbelow]
    exact phaseG_ge_one hγlo hγ hγhi ha hb hc hf0 hn (Nat.le_of_lt hj)

lemma iterate_below_phase_le {γlo γhi γ a b c f : ℝ} (P : RumorProcess n)
    (hγlo : 0 < γlo) (hγ : γlo ≤ γ) (hγhi : γ ≤ γhi) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hf0 : 0 < f) (hn : growthN a b f ≤ n) (hUG : P.UpperGrowth γ a b c f)
    (t : ℕ) {S : Finset (Fin n)} (hk : (1 : ℝ) ≤ S.card) :
    P.K.iterate t (below (kSeq γ a b (growthA γlo b) n (phaseCount γ a f n))) S ≤
      (xDecay γlo γhi b c)⁻¹ ^ t * phaseG γlo γhi γ a b c f n
        (phaseIdx γlo γ a b n (phaseCount γ a f n) (S.card : ℝ)) := by
  induction t generalizing S with
  | zero =>
    simpa [Kernel.iterate_zero, pow_zero, one_mul] using
      below_le_phaseG hγlo hγ hγhi ha hb hc hf0 hn hk
  | succ t ih =>
    by_cases htop : phaseIdx γlo γ a b n (phaseCount γ a f n) (S.card : ℝ) =
        phaseCount γ a f n
    · have hge := kSeq_le_of_phase hk htop
      have hzero := notYet_eq_zero_of_ge P hge (t + 1)
      rw [notYet_below] at hzero
      have hx : 0 ≤ (xDecay γlo γhi b c)⁻¹ :=
        inv_nonneg.mpr (le_trans zero_le_one
          (le_of_lt (xDecay_gt_one hγlo (le_trans hγ hγhi) hc)))
      rw [hzero, htop, phaseG_top]
      exact mul_nonneg (pow_nonneg hx _) (by norm_num)
    · rw [Kernel.iterate_succ]
      have hj : phaseIdx γlo γ a b n (phaseCount γ a f n) (S.card : ℝ) <
          phaseCount γ a f n :=
        lt_of_le_of_ne (phaseIdx_le _ _ _ _ _ _ _) htop
      have hpt : ∀ T, S ⊆ T → P.K.iterate t
          (below (kSeq γ a b (growthA γlo b) n (phaseCount γ a f n))) T ≤
          (xDecay γlo γhi b c)⁻¹ ^ t * phaseG γlo γhi γ a b c f n
            (phaseIdx γlo γ a b n (phaseCount γ a f n) (T.card : ℝ)) := by
        intro T hT
        exact ih (le_trans hk (Nat.cast_le.mpr (card_le_card hT)))
      have hE := expect_le_of_weight P S hpt
      rw [Distribution.expect_mul] at hE
      have hpot := expect_phase_le P hγlo hγ hγhi ha hb hc hf0 hn hUG hk hj
      have hpow : 0 ≤ (xDecay γlo γhi b c)⁻¹ ^ t :=
        pow_nonneg (inv_nonneg.mpr (le_trans zero_le_one
          (le_of_lt (xDecay_gt_one hγlo (le_trans hγ hγhi) hc)))) _
      calc P.K.apply (P.K.iterate t
            (below (kSeq γ a b (growthA γlo b) n (phaseCount γ a f n)))) S
          ≤ (xDecay γlo γhi b c)⁻¹ ^ t * (P.K S).expect (fun T =>
              phaseG γlo γhi γ a b c f n
                (phaseIdx γlo γ a b n (phaseCount γ a f n) (T.card : ℝ))) := hE
        _ ≤ (xDecay γlo γhi b c)⁻¹ ^ t *
            (phaseG γlo γhi γ a b c f n
              (phaseIdx γlo γ a b n (phaseCount γ a f n) (S.card : ℝ)) /
              xDecay γlo γhi b c) :=
            mul_le_mul_of_nonneg_left hpot hpow
        _ = (xDecay γlo γhi b c)⁻¹ ^ (t + 1) *
            phaseG γlo γhi γ a b c f n
              (phaseIdx γlo γ a b n (phaseCount γ a f n) (S.card : ℝ)) := by
            rw [div_eq_mul_inv]
            have hassoc : (xDecay γlo γhi b c)⁻¹ ^ t *
                (phaseG γlo γhi γ a b c f n
                    (phaseIdx γlo γ a b n (phaseCount γ a f n) (S.card : ℝ)) *
                  (xDecay γlo γhi b c)⁻¹) =
                ((xDecay γlo γhi b c)⁻¹ ^ t * (xDecay γlo γhi b c)⁻¹) *
                  phaseG γlo γhi γ a b c f n
                    (phaseIdx γlo γ a b n (phaseCount γ a f n) (S.card : ℝ)) := by
              ring
            rw [hassoc, ← pow_succ]

lemma phaseG_as_prod {γlo γhi γ a b c f : ℝ} {n : ℕ} :
    phaseG γlo γhi γ a b c f n 0 =
      xDecay γlo γhi b c ^ phaseCount γ a f n *
        ∏ i ∈ range (phaseCount γ a f n),
          (1 - phaseQ γ c (growthA γlo b) (kSeq γ a b (growthA γlo b) n i)) /
            (1 - xDecay γlo γhi b c *
              phaseQ γ c (growthA γlo b) (kSeq γ a b (growthA γlo b) n i)) := by
  have hrange : Ico 0 (phaseCount γ a f n) = range (phaseCount γ a f n) := by
    ext i
    simp
  unfold phaseG
  rw [hrange]
  have hterm : ∀ i ∈ range (phaseCount γ a f n),
      phaseRatio γlo γhi γ a b c n i =
        xDecay γlo γhi b c * ((1 - phaseQ γ c (growthA γlo b)
            (kSeq γ a b (growthA γlo b) n i)) /
          (1 - xDecay γlo γhi b c * phaseQ γ c (growthA γlo b)
            (kSeq γ a b (growthA γlo b) n i))) := by
    intro i _
    unfold phaseRatio
    rw [← mul_div_assoc]
  rw [prod_congr rfl hterm, prod_mul_distrib, prod_const, card_range]

lemma sum_phaseQ_le {γlo γhi γ a b c f : ℝ} {n : ℕ} (hγlo : 0 < γlo) (hγ : γlo ≤ γ)
    (hγhi : γ ≤ γhi) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hf0 : 0 < f)
    (hn : growthN a b f ≤ n) :
    ∑ i ∈ range (phaseCount γ a f n),
        phaseQ γ c (growthA γlo b) (kSeq γ a b (growthA γlo b) n i) ≤
      tailQSum γlo γhi b c := by
  have hterm : ∀ i ∈ range (phaseCount γ a f n),
      phaseQ γ c (growthA γlo b) (kSeq γ a b (growthA γlo b) n i) ≤
        qTerm γ c (growthA γlo b) (kSeq γ a b (growthA γlo b) n i) := by
    intro i _
    exact phaseQ_le_q (le_trans hγlo.le hγ) hc
  exact le_trans (sum_le_sum hterm) (sum_qTerm_le hγlo hγ hγhi ha hb hc hf0 hn)

noncomputable def tailProd (γlo γhi b c : ℝ) : ℝ :=
  Real.exp (((xDecay γlo γhi b c - 1) /
      (1 - xDecay γlo γhi b c * Qstar γlo γhi b c)) * tailQSum γlo γhi b c)

lemma prod_phase_le {γlo γhi γ a b c f : ℝ} {n : ℕ} (hγlo : 0 < γlo) (hγ : γlo ≤ γ)
    (hγhi : γ ≤ γhi) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hf0 : 0 < f)
    (hn : growthN a b f ≤ n) :
    ∏ i ∈ range (phaseCount γ a f n),
        (1 - phaseQ γ c (growthA γlo b) (kSeq γ a b (growthA γlo b) n i)) /
          (1 - xDecay γlo γhi b c *
            phaseQ γ c (growthA γlo b) (kSeq γ a b (growthA γlo b) n i)) ≤
      tailProd γlo γhi b c := by
  have hx : 1 < xDecay γlo γhi b c := xDecay_gt_one hγlo (le_trans hγ hγhi) hc
  have hxQ : xDecay γlo γhi b c * Qstar γlo γhi b c < 1 :=
    xDecay_Qstar_lt_one hγlo (le_trans hγ hγhi) hc
  have hprod := prod_ratio_le_exp (Q := fun i => phaseQ γ c (growthA γlo b)
      (kSeq γ a b (growthA γlo b) n i)) (J := phaseCount γ a f n)
    (x := xDecay γlo γhi b c) (Qs := Qstar γlo γhi b c) (le_of_lt hx) hxQ
    (fun i _ => phaseQ_nonneg (le_trans hγlo.le hγ) hc)
    (fun i hi => phaseQ_k_le hγlo hγ hγhi ha hb hc hf0 hn i
      (Nat.le_of_lt (mem_range.mp hi)))
  have hsum := sum_phaseQ_le hγlo hγ hγhi ha hb hc hf0 hn
  have hden : 0 < 1 - xDecay γlo γhi b c * Qstar γlo γhi b c := by linarith only [hxQ]
  have hcoef : 0 ≤ (xDecay γlo γhi b c - 1) /
      (1 - xDecay γlo γhi b c * Qstar γlo γhi b c) :=
    div_nonneg (by linarith only [hx]) hden.le
  have hmul := mul_le_mul_of_nonneg_left hsum hcoef
  unfold tailProd
  exact le_trans hprod ((Real.exp_le_exp).mpr hmul)

lemma phase_iterate_exp {γlo γhi γ a b c f : ℝ} (P : RumorProcess n) (hγlo : 0 < γlo)
    (hγ : γlo ≤ γ) (hγhi : γ ≤ γhi) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hf0 : 0 < f) (hn : growthN a b f ≤ n) (hUG : P.UpperGrowth γ a b c f)
    (r : ℕ) {S : Finset (Fin n)} (hk : (1 : ℝ) ≤ S.card) :
    P.K.iterate (phaseCount γ a f n + r / 2)
        (below (kSeq γ a b (growthA γlo b) n (phaseCount γ a f n))) S ≤
      tailProd γlo γhi b c * Real.sqrt (xDecay γlo γhi b c) *
        Real.exp (-(Real.log (xDecay γlo γhi b c) / 2) * r) := by
  let J : ℕ := phaseCount γ a f n
  let x : ℝ := xDecay γlo γhi b c
  have hx : 1 < x := xDecay_gt_one hγlo (le_trans hγ hγhi) hc
  have hstep := iterate_below_phase_le P hγlo hγ hγhi ha hb hc hf0 hn hUG (J + r / 2) hk
  have hanti := phaseG_antitone hγlo hγ hγhi ha hb hc hf0 hn
    (Nat.zero_le (phaseIdx γlo γ a b n J (S.card : ℝ)))
    (phaseIdx_le γlo γ a b n J (S.card : ℝ))
  have hpow : 0 ≤ (x⁻¹) ^ (J + r / 2) :=
    pow_nonneg (inv_nonneg.mpr (le_trans zero_le_one (le_of_lt hx))) _
  have hG : (x⁻¹) ^ (J + r / 2) * phaseG γlo γhi γ a b c f n
        (phaseIdx γlo γ a b n J (S.card : ℝ)) ≤
      (x⁻¹) ^ (J + r / 2) * phaseG γlo γhi γ a b c f n 0 :=
    mul_le_mul_of_nonneg_left hanti hpow
  have hshift := pow_inv_shift (ne_of_gt (lt_trans (by norm_num : (0 : ℝ) < 1) hx)) J (r / 2)
    (∏ i ∈ range J, (1 - phaseQ γ c (growthA γlo b) (kSeq γ a b (growthA γlo b) n i)) /
      (1 - x * phaseQ γ c (growthA γlo b) (kSeq γ a b (growthA γlo b) n i)))
  have hprod := prod_phase_le hγlo hγ hγhi ha hb hc hf0 hn
  have hhalf := inv_pow_half_le hx r
  have htail : 0 ≤ tailProd γlo γhi b c := (Real.exp_pos _).le
  have hsqrt : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
  calc P.K.iterate (J + r / 2) (below (kSeq γ a b (growthA γlo b) n J)) S
      ≤ (x⁻¹) ^ (J + r / 2) * phaseG γlo γhi γ a b c f n
          (phaseIdx γlo γ a b n J (S.card : ℝ)) := hstep
    _ ≤ (x⁻¹) ^ (J + r / 2) * phaseG γlo γhi γ a b c f n 0 := hG
    _ = (x⁻¹) ^ (J + r / 2) * (x ^ J *
          ∏ i ∈ range J, (1 - phaseQ γ c (growthA γlo b)
              (kSeq γ a b (growthA γlo b) n i)) /
            (1 - x * phaseQ γ c (growthA γlo b)
              (kSeq γ a b (growthA γlo b) n i))) := by
        rw [phaseG_as_prod]
    _ = (x⁻¹) ^ (r / 2) * ∏ i ∈ range J,
          (1 - phaseQ γ c (growthA γlo b) (kSeq γ a b (growthA γlo b) n i)) /
            (1 - x * phaseQ γ c (growthA γlo b)
              (kSeq γ a b (growthA γlo b) n i)) := hshift
    _ ≤ (x⁻¹) ^ (r / 2) * tailProd γlo γhi b c :=
        mul_le_mul_of_nonneg_left hprod
          (pow_nonneg (inv_nonneg.mpr (le_trans zero_le_one (le_of_lt hx))) _)
    _ ≤ Real.sqrt x * Real.exp (-(Real.log x / 2) * r) * tailProd γlo γhi b c :=
        mul_le_mul_of_nonneg_right hhalf htail
    _ = tailProd γlo γhi b c * Real.sqrt x *
          Real.exp (-(Real.log x / 2) * r) := by ring

lemma inform_ge_connect {γlo γhi γ a b c f : ℝ} (P : RumorProcess n) (hγlo : 0 < γlo)
    (hγ : γlo ≤ γ) (hγhi : γ ≤ γhi) (ha : 0 ≤ a) (hb : 0 ≤ b) (hf0 : 0 < f)
    (haf : a * f < 1) (hn : growthN a b f ≤ n) (hUG : P.UpperGrowth γ a b c f)
    {S : Finset (Fin n)}
    (hℓ : Nat.ceil (kSeq γ a b (growthA γlo b) n (phaseCount γ a f n)) ≤ S.card)
    (hlt : (S.card : ℝ) < f * n) {x : Fin n} (hx : x ∉ S) :
    connectP γlo γhi a b f ≤ P.informProb S x := by
  obtain ⟨hγpos, hlog, hnpos, _, _, _, _, _⟩ := stdFacts hγlo hγ ha hf0 hn
  let kJ : ℝ := kSeq γ a b (growthA γlo b) n (phaseCount γ a f n)
  have hkJ1 := (kSeq_in_range hγlo hγ ha hb hf0 hn (phaseCount γ a f n) le_rfl).1
  have hceil : 1 ≤ Nat.ceil kJ := by
    have hpos : 0 < Nat.ceil kJ := Nat.ceil_pos.mpr (by linarith only [hkJ1])
    omega
  have hS : S.Nonempty := card_pos.mp (lt_of_lt_of_le hceil hℓ)
  have hinfo := (hUG S hS hlt).1 x hx
  have hkJ : kJ ≤ S.card := by
    have hcast : (Nat.ceil kJ : ℝ) ≤ S.card := Nat.cast_le.mpr hℓ
    have hceil_ge : kJ ≤ Nat.ceil kJ := Nat.gc_ceil_coe.le_u_l kJ
    linarith only [hcast, hceil_ge]
  have hkn : kJ / n ≤ (S.card : ℝ) / n := div_le_div_of_nonneg_right hkJ hnpos.le
  have hdivk : (S.card : ℝ) / n ≤ f := by
    rw [div_le_iff₀ hnpos]
    exact le_of_lt hlt
  have hslack : (1 - a * f) / 2 ≤
      1 - a * ((S.card : ℝ) / n) - b / Real.log n := by
    have hblog := blog_connect (a := a) (b := b) (f := f) haf hn
    have ha' : a * ((S.card : ℝ) / n) ≤ a * f := mul_le_mul_of_nonneg_left hdivk ha
    linarith only [hblog, ha']
  have hbase := kSeq_div_ge hγlo hγ hγhi ha hb hf0 hn
  have hγk : γlo * (kJ / n) ≤ γ * ((S.card : ℝ) / n) := by
    have hleft := mul_le_mul_of_nonneg_right hγ (div_nonneg (by linarith only [hkJ1]) hnpos.le)
    have hright := mul_le_mul_of_nonneg_left hkn hγpos.le
    linarith only [hleft, hright]
  have hslack0 : 0 ≤ (1 - a * f) / 2 := div_nonneg (by linarith only [haf]) (by norm_num)
  have hprod := mul_le_mul hγk hslack hslack0
    (mul_nonneg hγpos.le (div_nonneg (by linarith only [hkJ]) hnpos.le))
  have hconst : connectP γlo γhi a b f ≤ γlo * (kJ / n) * ((1 - a * f) / 2) := by
    have hmul := mul_le_mul_of_nonneg_left hbase (mul_nonneg hγlo.le hslack0)
    have hL : connectP γlo γhi a b f =
        γlo * ((1 - a * f) / 2) * (alphaSeq b γlo * fShrink a f / (1 + γhi)) := by
      unfold connectP
      ring
    have hR : γlo * (kJ / n) * ((1 - a * f) / 2) =
        γlo * ((1 - a * f) / 2) * (kJ / n) := by ring
    linarith only [hmul, hL, hR]
  calc connectP γlo γhi a b f
      ≤ γlo * (kJ / n) * ((1 - a * f) / 2) := hconst
    _ ≤ γ * ((S.card : ℝ) / n) *
        (1 - a * ((S.card : ℝ) / n) - b / Real.log n) := hprod
    _ ≤ P.informProb S x := by
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hinfo

lemma bridge_le {γlo γhi γ a b c f : ℝ} (P : RumorProcess n) (hγlo : 0 < γlo)
    (hγ : γlo ≤ γ) (hγhi : γ ≤ γhi) (ha : 0 ≤ a) (hb : 0 ≤ b) (hf0 : 0 < f)
    (hf1 : f < 1) (haf : a * f < 1) (hn : growthN a b f ≤ n)
    (hUG : P.UpperGrowth γ a b c f) (t : ℕ) (U : Finset (Fin n)) :
    P.K.iterate t (below (f * n)) U ≤
      below (kSeq γ a b (growthA γlo b) n (phaseCount γ a f n)) U +
        ((n : ℝ) - Nat.ceil (kSeq γ a b (growthA γlo b) n (phaseCount γ a f n))) /
          ((n : ℝ) - f * n) * (1 - connectP γlo γhi a b f) ^ t := by
  let kJ : ℝ := kSeq γ a b (growthA γlo b) n (phaseCount γ a f n)
  let ℓ : ℕ := Nat.ceil kJ
  let p : ℝ := connectP γlo γhi a b f
  have hnpos := n_cast_pos (a := a) (b := b) (f := f) hn
  have hmn : f * (n : ℝ) < n := by
    simpa [one_mul] using mul_lt_mul_of_pos_right hf1 hnpos
  have hkJ := kSeq_le_shrink hγlo hγ ha hb hf0 hn (phaseCount γ a f n) le_rfl
  have hk1 := (kSeq_in_range hγlo hγ ha hb hf0 hn (phaseCount γ a f n) le_rfl).1
  have hℓm : (ℓ : ℝ) < f * n := by
    have hceil : (ℓ : ℝ) < kJ + 1 := Nat.ceil_lt_add_one (by linarith only [hk1])
    have hslack := shrink_slack (a := a) (b := b) (f := f) hf0 hn
    linarith only [hceil, hkJ, hslack]
  have hp0 : 0 < p := connectP_pos hγlo (le_trans hγ hγhi) ha hf0 haf
  have hp1 : p ≤ 1 := le_trans (connectP_le_half hγlo (le_trans hγ hγhi) ha hb hf0 haf) (by norm_num)
  have hratio0 : 0 ≤ ((n : ℝ) - ℓ) / ((n : ℝ) - f * n) := by
    have hden : 0 < (n : ℝ) - f * n := by linarith only [hmn]
    have hnum : 0 ≤ (n : ℝ) - ℓ := by
      have hℓn : (ℓ : ℝ) ≤ n := le_trans (le_of_lt hℓm) hmn.le
      linarith only [hℓn]
    exact div_nonneg hnum hden.le
  have hpow : 0 ≤ (1 - p) ^ t := pow_nonneg (sub_nonneg.mpr hp1) t
  by_cases hlt : (U.card : ℝ) < kJ
  · have hone : P.K.iterate t (below (f * n)) U ≤ 1 := by
      rw [← notYet_below]
      exact P.K.event_le_one _ t U
    rw [below, if_pos hlt]
    have hnn : 0 ≤ ((n : ℝ) - ℓ) / ((n : ℝ) - f * n) * (1 - p) ^ t :=
      mul_nonneg hratio0 hpow
    linarith only [hone, hnn]
  · have hge : kJ ≤ U.card := not_lt.mp hlt
    have hℓ : ℓ ≤ U.card := Nat.ceil_le.mpr hge
    have hp : ∀ V : Finset (Fin n), ℓ ≤ V.card → (V.card : ℝ) < f * n →
        ∀ y ∉ V, p ≤ P.informProb V y := by
      intro V hV hVm y hy
      exact inform_ge_connect P hγlo hγ hγhi ha hb hf0 haf hn hUG hV hVm hy
    have htail := connect_tail_proof P hℓm hmn hp0.le hp1 hp U hℓ t
    rw [notYet_below] at htail
    rw [below, if_neg hlt]
    linarith only [htail]

lemma connect_ratio_le {γlo γ a b f : ℝ} {n : ℕ} (_hγlo : 0 < γlo) (_hγ : γlo ≤ γ)
    (_ha : 0 ≤ a) (_hb : 0 ≤ b) (_hf0 : 0 < f) (hf1 : f < 1) (hn : growthN a b f ≤ n) :
    ((n : ℝ) - Nat.ceil (kSeq γ a b (growthA γlo b) n (phaseCount γ a f n))) /
        ((n : ℝ) - f * n) ≤ 1 / (1 - f) := by
  have hnpos := n_cast_pos (a := a) (b := b) (f := f) hn
  have hdenf : 0 < 1 - f := by linarith only [hf1]
  have hsub : (n : ℝ) - f * n = (n : ℝ) * (1 - f) := by ring
  have hceil : (0 : ℝ) ≤ Nat.ceil (kSeq γ a b (growthA γlo b) n (phaseCount γ a f n)) :=
    Nat.cast_nonneg _
  have hnum : (n : ℝ) - Nat.ceil (kSeq γ a b (growthA γlo b) n (phaseCount γ a f n)) ≤ n := by
    linarith only [hceil]
  have hden : 0 < (n : ℝ) * (1 - f) := mul_pos hnpos hdenf
  have hdiv := div_le_div_of_nonneg_right hnum hden.le
  have hcancel : (n : ℝ) / ((n : ℝ) * (1 - f)) = 1 / (1 - f) := by
    field_simp [hnpos.ne', hdenf.ne']
  rw [hsub]
  linarith only [hdiv, hcancel]

noncomputable def decayAlpha (γlo γhi a b c f : ℝ) : ℝ :=
  min (Real.log (xDecay γlo γhi b c) / 2)
    (-Real.log (1 - connectP γlo γhi a b f) / 2)

noncomputable def tailPrefactor (γlo γhi _a b c f : ℝ) : ℝ :=
  tailProd γlo γhi b c * Real.sqrt (xDecay γlo γhi b c) + 1 / (1 - f)

lemma decayAlpha_pos {γlo γhi a b c f : ℝ} (hγlo : 0 < γlo) (hγ : γlo ≤ γhi)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hf0 : 0 < f) (haf : a * f < 1) :
    0 < decayAlpha γlo γhi a b c f := by
  have hx : 1 < xDecay γlo γhi b c := xDecay_gt_one hγlo hγ hc
  have hlogx : 0 < Real.log (xDecay γlo γhi b c) / 2 :=
    div_pos (Real.log_pos hx) (by norm_num)
  have hp : 0 < connectP γlo γhi a b f := connectP_pos hγlo hγ ha hf0 haf
  have hp1 : connectP γlo γhi a b f ≤ 1 / 2 :=
    connectP_le_half hγlo hγ ha hb hf0 haf
  have h1p : 0 < 1 - connectP γlo γhi a b f := by linarith only [hp1]
  have hlogp : Real.log (1 - connectP γlo γhi a b f) < 0 := by
    rw [← Real.log_one]
    exact Real.log_lt_log h1p (by linarith only [hp])
  have hlogn : 0 < -Real.log (1 - connectP γlo γhi a b f) / 2 :=
    div_pos (neg_pos.mpr hlogp) (by norm_num)
  unfold decayAlpha
  exact lt_min hlogx hlogn

lemma tailPrefactor_nonneg {γlo γhi a b c f : ℝ} (hf1 : f < 1) :
    0 ≤ tailPrefactor γlo γhi a b c f := by
  have hden : 0 < 1 - f := by linarith only [hf1]
  exact add_nonneg
    (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _))
    (div_nonneg (by norm_num) hden.le)

lemma notYet_growth_le {γlo γhi γ a b c f : ℝ} (P : RumorProcess n) (hγlo : 0 < γlo)
    (hγ : γlo ≤ γ) (hγhi : γ ≤ γhi) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hf0 : 0 < f) (hf1 : f < 1) (haf : a * f < 1) (hn : growthN a b f ≤ n)
    (hUG : P.UpperGrowth γ a b c f) {S : Finset (Fin n)} (hk : (1 : ℝ) ≤ S.card)
    (r : ℕ) :
    P.notYet (f * n) (⌈Real.logb (1 + γ) (n : ℝ)⌉₊ + r) S ≤
      tailPrefactor γlo γhi a b c f * Real.exp (-decayAlpha γlo γhi a b c f * r) := by
  let J : ℕ := phaseCount γ a f n
  let L : ℕ := Nat.ceil (Real.logb (1 + γ) (n : ℝ))
  let x : ℝ := xDecay γlo γhi b c
  let p : ℝ := connectP γlo γhi a b f
  let α : ℝ := decayAlpha γlo γhi a b c f
  have hγpos : 0 < γ := lt_of_lt_of_le hγlo hγ
  have hJ : J ≤ L := phaseCount_le_ceil hγpos ha hf0 hn
  have htime : J + r ≤ L + r := Nat.add_le_add_right hJ r
  have hanti := notYet_antitone P (f * n) htime S
  let s : ℕ := r / 2
  let t : ℕ := r - r / 2
  have hadd : s + t = r := Nat.add_sub_of_le (Nat.div_le_self r 2)
  have hsplit : P.notYet (f * n) (J + r) S ≤
      P.K.iterate (J + s) (below (kSeq γ a b (growthA γlo b) n J)) S +
        ((n : ℝ) - Nat.ceil (kSeq γ a b (growthA γlo b) n J)) / ((n : ℝ) - f * n) *
          (1 - p) ^ t := by
    rw [notYet_below]
    have htime' : P.K.iterate (J + r) (below (f * n)) S =
        P.K.iterate (J + s) (P.K.iterate t (below (f * n))) S := by
      have hassoc : J + r = (J + s) + t := by omega
      rw [hassoc]
      exact congrFun (P.K.iterate_add_time (J + s) t (below (f * n))) S
    have hpt : ∀ U, P.K.iterate t (below (f * n)) U ≤
        below (kSeq γ a b (growthA γlo b) n J) U +
          ((n : ℝ) - Nat.ceil (kSeq γ a b (growthA γlo b) n J)) /
            ((n : ℝ) - f * n) * (1 - p) ^ t :=
      fun U => bridge_le P hγlo hγ hγhi ha hb hf0 hf1 haf hn hUG t U
    have hmono := P.K.iterate_mono (J + s) hpt S
    have haddF : P.K.iterate (J + s) (fun U =>
          below (kSeq γ a b (growthA γlo b) n J) U +
            ((n : ℝ) - Nat.ceil (kSeq γ a b (growthA γlo b) n J)) /
              ((n : ℝ) - f * n) * (1 - p) ^ t) S =
        P.K.iterate (J + s) (below (kSeq γ a b (growthA γlo b) n J)) S +
          ((n : ℝ) - Nat.ceil (kSeq γ a b (growthA γlo b) n J)) /
            ((n : ℝ) - f * n) * (1 - p) ^ t := by
      rw [P.K.iterate_add, P.K.iterate_const]
    linarith only [htime', hmono, haddF]
  have hphase := phase_iterate_exp P hγlo hγ hγhi ha hb hc hf0 hn hUG r hk
  have hratio := connect_ratio_le hγlo hγ ha hb hf0 hf1 hn
  have hp0 : 0 < p := connectP_pos hγlo (le_trans hγ hγhi) ha hf0 haf
  have hp1 : p < 1 := lt_of_le_of_lt (connectP_le_half hγlo (le_trans hγ hγhi) ha hb hf0 haf) (by norm_num)
  have hconn := one_sub_pow_half hp0 hp1 r
  have hpow0 : 0 ≤ (1 - p) ^ t := pow_nonneg (sub_nonneg.mpr hp1.le) t
  have hconnR : ((n : ℝ) - Nat.ceil (kSeq γ a b (growthA γlo b) n J)) /
        ((n : ℝ) - f * n) * (1 - p) ^ t ≤
      (1 / (1 - f)) * Real.exp (-(-Real.log (1 - p) / 2) * r) := by
    exact mul_le_mul hratio hconn hpow0 (by
      have hden : 0 < 1 - f := by linarith only [hf1]
      exact div_nonneg (by norm_num) hden.le)
  have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  have hmin1 : α ≤ Real.log x / 2 := by
    have hdef : α = decayAlpha γlo γhi a b c f := rfl
    rw [hdef, decayAlpha]
    exact min_le_left _ _
  have hmin2 : α ≤ -Real.log (1 - p) / 2 := by
    have hdef : α = decayAlpha γlo γhi a b c f := rfl
    rw [hdef, decayAlpha]
    exact min_le_right _ _
  have he1 := exp_rate_le hmin1 hr
  have he2 := exp_rate_le hmin2 hr
  have hA1 : 0 ≤ tailProd γlo γhi b c * Real.sqrt x :=
    mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)
  have hA2 : 0 ≤ 1 / (1 - f) := by
    have hden : 0 < 1 - f := by linarith only [hf1]
    exact div_nonneg (by norm_num) hden.le
  have hphase' : tailProd γlo γhi b c * Real.sqrt x *
        Real.exp (-(Real.log x / 2) * r) ≤
      tailProd γlo γhi b c * Real.sqrt x * Real.exp (-α * r) :=
    mul_le_mul_of_nonneg_left he1 hA1
  have hconn' : (1 / (1 - f)) * Real.exp (-(-Real.log (1 - p) / 2) * r) ≤
      (1 / (1 - f)) * Real.exp (-α * r) :=
    mul_le_mul_of_nonneg_left he2 hA2
  have hsum : tailProd γlo γhi b c * Real.sqrt x * Real.exp (-α * r) +
        (1 / (1 - f)) * Real.exp (-α * r) =
      tailPrefactor γlo γhi a b c f * Real.exp (-α * r) := by
    unfold tailPrefactor
    ring
  linarith only [hanti, hsplit, hphase, hconnR, hphase', hconn', hsum]

theorem growth_upper_tail_proof {γlo γhi a b c f : ℝ} (hγlo : 0 < γlo) (hγ : γlo ≤ γhi)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hf0 : 0 < f) (hf1 : f < 1) (haf : a * f < 1) :
    ∃ A α : ℝ, 0 < α ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ γ : ℝ, γlo ≤ γ → γ ≤ γhi →
      ∀ P : RumorProcess n, P.UpperGrowth γ a b c f →
      ∀ S : Finset (Fin n), S.Nonempty → ∀ r : ℕ,
        P.notYet (f * n) (⌈Real.logb (1 + γ) n⌉₊ + r) S ≤ A * Real.exp (-α * r) := by
  refine ⟨tailPrefactor γlo γhi a b c f, decayAlpha γlo γhi a b c f,
    decayAlpha_pos hγlo hγ ha hb hc hf0 haf, growthN a b f, ?_⟩
  intro n hn γ hγlo' hγhi' P hUG S hS r
  have hcard : 0 < S.card := card_pos.mpr hS
  have hk : (1 : ℝ) ≤ S.card := by exact_mod_cast (Nat.succ_le_of_lt hcard)
  exact notYet_growth_le P hγlo hγlo' hγhi' ha hb hc hf0 hf1 haf hn hUG hk r

theorem growth_upper_expect_proof {γlo γhi a b c f : ℝ} (hγlo : 0 < γlo) (hγ : γlo ≤ γhi)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hf0 : 0 < f) (hf1 : f < 1) (haf : a * f < 1) :
    ∃ B : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ γ : ℝ, γlo ≤ γ → γ ≤ γhi →
      ∀ P : RumorProcess n, P.UpperGrowth γ a b c f →
      ∀ S : Finset (Fin n), S.Nonempty → ∀ R : ℕ,
        ∑ t ∈ range R, P.notYet (f * n) t S ≤ Real.logb (1 + γ) n + B := by
  let A : ℝ := tailPrefactor γlo γhi a b c f
  let α : ℝ := decayAlpha γlo γhi a b c f
  have hα : 0 < α := decayAlpha_pos hγlo hγ ha hb hc hf0 haf
  have hq : Real.exp (-α) < 1 := by
    have hneg : -α < 0 := by linarith only [hα]
    simpa [Real.exp_zero] using (Real.exp_lt_exp).mpr hneg
  have hden : 0 < 1 - Real.exp (-α) := by linarith only [hq]
  refine ⟨1 + A / (1 - Real.exp (-α)), growthN a b f, ?_⟩
  intro n hn γ hγlo' hγhi' P hUG S hS R
  have hcard : 0 < S.card := card_pos.mpr hS
  have hk : (1 : ℝ) ≤ S.card := by exact_mod_cast (Nat.succ_le_of_lt hcard)
  let L : ℕ := Nat.ceil (Real.logb (1 + γ) (n : ℝ))
  have hρ : 1 < 1 + γ := by linarith only [hγlo, hγlo']
  have hn1 : (1 : ℝ) ≤ n := by
    have hn0 : n ≠ 0 := by
      exact_mod_cast (n_cast_pos (a := a) (b := b) (f := f) hn).ne'
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
  have hlog0 : 0 ≤ Real.logb (1 + γ) (n : ℝ) := logb_nonneg_of_one_le hρ hn1
  have hL : (L : ℝ) < Real.logb (1 + γ) (n : ℝ) + 1 := Nat.ceil_lt_add_one hlog0
  have hone : ∀ t, P.notYet (f * n) t S ≤ 1 := fun t => by
    simpa [RumorProcess.notYet] using P.K.event_le_one (fun U => (U.card : ℝ) < f * n) t S
  have hA0 : 0 ≤ A := tailPrefactor_nonneg hf1
  by_cases hR : R ≤ L
  · have hsum : ∑ t ∈ range R, P.notYet (f * n) t S ≤ (R : ℝ) := by
      have hle := sum_le_sum (fun t (_ : t ∈ range R) => hone t)
      simpa [sum_const, card_range, nsmul_eq_mul, mul_one] using hle
    have hRL : (R : ℝ) ≤ L := by exact_mod_cast hR
    have hB : (1 : ℝ) ≤ 1 + A / (1 - Real.exp (-α)) := by
      have hdiv : 0 ≤ A / (1 - Real.exp (-α)) := div_nonneg hA0 hden.le
      linarith only [hdiv]
    linarith only [hsum, hRL, hL, hB]
  · have hLle : L ≤ R := le_of_not_ge hR
    have hsplit := sum_range_add (fun t => P.notYet (f * n) t S) L (R - L)
    have hRsum : L + (R - L) = R := Nat.add_sub_of_le hLle
    rw [hRsum] at hsplit
    have hhead : ∑ t ∈ range L, P.notYet (f * n) t S ≤ (L : ℝ) := by
      have hle := sum_le_sum (fun t (_ : t ∈ range L) => hone t)
      simpa [sum_const, card_range, nsmul_eq_mul, mul_one] using hle
    have htail : ∑ i ∈ range (R - L), P.notYet (f * n) (L + i) S ≤
        A * ∑ i ∈ range (R - L), Real.exp (-α) ^ i := by
      have hterm : ∀ i ∈ range (R - L),
          P.notYet (f * n) (L + i) S ≤ A * Real.exp (-α) ^ i := by
        intro i _
        have hnot := notYet_growth_le P hγlo hγlo' hγhi' ha hb hc hf0 hf1 haf hn hUG hk i
        have hpow : Real.exp (-α * (i : ℝ)) = Real.exp (-α) ^ i := by
          rw [mul_comm, ← Real.exp_nat_mul]
        rw [hpow] at hnot
        exact hnot
      have hsum := sum_le_sum hterm
      rwa [mul_sum]
    have hgeom := geom_partial_le (Real.exp_nonneg _) hq (R - L)
    have htail' : ∑ i ∈ range (R - L), P.notYet (f * n) (L + i) S ≤
        A / (1 - Real.exp (-α)) := by
      have hmul := mul_le_mul_of_nonneg_left hgeom hA0
      have hinv : A * (1 - Real.exp (-α))⁻¹ = A / (1 - Real.exp (-α)) := by
        rw [div_eq_mul_inv]
      linarith only [htail, hmul, hinv]
    have hB : (L : ℝ) + A / (1 - Real.exp (-α)) <
        Real.logb (1 + γ) (n : ℝ) + (1 + A / (1 - Real.exp (-α))) := by
      linarith only [hL]
    linarith only [hsplit, hhead, htail', hB]

end Epidemics.Revisited
