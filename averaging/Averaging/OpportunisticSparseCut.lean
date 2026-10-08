import Averaging.OpportunisticSignEvents

/-! # Averaging whenever you meet: community recovery on clustered graphs with a sparse cut

Section 4 of arXiv:1703.05045 (v3) analyses `Averaging(1/2)` on an `(n, d, b)`-clustered regular
graph whose cut is sparse with respect to the inner expansion, `λ₂ = 2b/d ≪ λ₃`. The randomness is
the uniform initial vector `x⁽⁰⁾ ∈ {-1, 1}ⁿ` (the first-activation coins, see
`Averaging.Opportunistic.oppRun_getD`) together with i.i.d. uniform edges.

* Theorem 4.1 (second moment): for `3 (n/λ₃) log n ≤ t ≤ n/(4λ₂)`,
  `E‖y⁽ᵗ⁾ + z⁽ᵗ⁾ - y⁽⁰⁾‖² ≤ 3 λ₂ t / n`.
* Lemma 4.2 (non-ephemeral good nodes): if `λ₂/λ₃ ≤ λ₃ ε⁴/(c log² n)`, then with probability at
  least `1 - ε` at least `(1 - 3ε) n` nodes are `ε`-good (Definition 4.1) at every round of the
  phase `6 (n/λ₃) log n ≤ t ≤ 12 (n/λ₃) log n`.
* Main theorem (sign recovery over the phase, Sections 4.2 and C.4): an `ε`-good node `v` has the
  sign of `x_∥,v + y⁽⁰⁾_v`, the initial average of its own community, unless this average is too
  small, which has probability `O(ε)` (Lemma A.1). So, with probability `1 - O(ε)`, all but `O(ε) n`
  nodes have the sign of their community's initial average throughout the phase
  (`sign_phase`). The two initial averages have opposite signs with probability `1/2 - o(1)`;
  hence, with probability `1/2 - O(ε)`, the sign of the values (`+1` if positive, `-1`
  otherwise) is an `O(ε)`-weak reconstruction (Definition 2.3) of the communities at every round
  of the phase (`weakReconstruction_phase`).

Logarithms are natural. The constant `c` ("large enough" in the paper) and the constant `C` of the
`O(ε)` terms are existential.
-/

namespace Averaging.Opportunistic
open Finset Dynamics
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Definition 4.1: node `v` is `ε`-good in the state `x = x⁽ᵗ⁾` reached from the initial state
`x₀ = x⁽⁰⁾` if `(x_v - (x_∥,v + y⁽⁰⁾_v))² ≤ (ε²/n) ‖y⁽⁰⁾‖²`. -/
def IsGood (V₁ : Finset V) (ε : ℝ) (x₀ x : V → ℝ) (v : V) : Prop :=
  (x v - (projOne x₀ v + projCut V₁ x₀ v)) ^ 2 ≤
    ε ^ 2 / Fintype.card V * ∑ w, projCut V₁ x₀ w ^ 2

/-- Definition 2.3: the labelling `f : V → {±1}` is an `ε`-weak reconstruction of the communities
`V₁` and `V₂ = V₁ᶜ` if some `W₁ ⊆ V₁` and `W₂ ⊆ V₂`, each of size at least `(1 - ε) n/2`, receive
disjoint sets of labels. -/
def IsWeakReconstruction (V₁ : Finset V) (ε : ℝ) (f : V → ℤˣ) : Prop :=
  ∃ W₁ ⊆ V₁, ∃ W₂ ⊆ V₁ᶜ, (1 - ε) * Fintype.card V / 2 ≤ #W₁ ∧
    (1 - ε) * Fintype.card V / 2 ≤ #W₂ ∧ Disjoint (f '' (W₁ : Set V)) (f '' (W₂ : Set V))

/-! ### Lemma 4.2 on a general vertex type -/

section General
variable {G : SimpleGraph V} [DecidableRel G.Adj] {V₁ : Finset V} {d b : ℕ} {lam3 : ℝ}

/-- The phase `6 (n/λ₃) log n ≤ t ≤ 12 (n/λ₃) log n` in integer form. -/
lemma window_nat {a : ℝ} (ha : 1 ≤ a) :
    ⌈a⌉₊ ≤ ⌊2 * a⌋₊ ∧ a ≤ ⌈a⌉₊ ∧ (⌈a⌉₊ : ℝ) ≤ a + 1 ∧ (⌊2 * a⌋₊ : ℝ) ≤ 2 * a := by
  refine ⟨?_, Nat.le_ceil a, (Nat.ceil_lt_add_one (by linarith)).le, Nat.floor_le (by linarith)⟩
  apply Nat.le_floor
  have := Nat.ceil_lt_add_one (show 0 ≤ a by linarith)
  linarith

/-- **Lemma 4.2** (`c = 10⁶`) on a general vertex type, for `ε ≤ 1`. -/
theorem IsClusteredRegular.prob_good_window (hG : IsClusteredRegular G V₁ d b)
    (h3 : ThirdEigenvalueLB G V₁ d lam3) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hl3 : 0 < lam3)
    (hc : (2 * b / d : ℝ) / lam3 ≤ lam3 * ε ^ 4 / (10 ^ 6 * Real.log (Fintype.card V) ^ 2)) :
    1 - ε ≤ avg fun σ : V → ℤˣ =>
      expList G.Dart ⌊12 * Fintype.card V / lam3 * Real.log (Fintype.card V)⌋₊ fun l =>
        if (1 - 3 * ε) * Fintype.card V ≤ #{v | ∀ t : ℕ,
            6 * Fintype.card V / lam3 * Real.log (Fintype.card V) ≤ t →
            (t : ℝ) ≤ 12 * Fintype.card V / lam3 * Real.log (Fintype.card V) →
            IsGood V₁ ε (signVec σ) (avgRun G (signVec σ) (l.take t)) v}
        then 1 else 0 := by
  have hn := hG.card_real_pos
  have hl3le := hG.lam3_le_two h3
  set N : ℝ := (Fintype.card V : ℝ) with hN_def
  set a := 6 * N / lam3 * Real.log N with ha_def
  have hN4 : (4 : ℝ) ≤ N := by rw [hN_def]; exact_mod_cast hG.four_le_card
  have hlog : 1 ≤ Real.log N := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_le_log (by norm_num) hN4
    have := Real.log_two_gt_d9
    linarith
  have ha1 : 1 ≤ a := by
    rw [ha_def]
    have : 6 * N / lam3 ≥ 1 := by rw [ge_iff_le, le_div_iff₀ hl3]; linarith
    nlinarith
  have h12 : 12 * N / lam3 * Real.log N = 2 * a := by rw [ha_def]; ring
  obtain ⟨hle, ht1, ht1', hT⟩ := window_nat ha1
  rw [h12]
  have hTeq : ⌈a⌉₊ + (⌊2 * a⌋₊ - ⌈a⌉₊) = ⌊2 * a⌋₊ := Nat.add_sub_cancel' hle
  have hT' : ((⌈a⌉₊ : ℕ) : ℝ) + ((⌊2 * a⌋₊ - ⌈a⌉₊ : ℕ) : ℝ) ≤ 12 * N / lam3 * Real.log N := by
    rw [← Nat.cast_add, hTeq, h12]; exact hT
  have haux := hG.nonEphemeral_aux h3 hε0 hε1 hl3 hc ⌈a⌉₊ (⌊2 * a⌋₊ - ⌈a⌉₊) ht1 ht1' hT'
  rw [hTeq] at haux
  refine haux.trans (avg_le_avg fun σ => expList_le_expList fun l => ?_)
  split_ifs with h1 h2 h2 <;> try norm_num
  refine absurd (h1.trans ?_) h2
  exact_mod_cast Finset.card_le_card fun v hv => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    intro t hta htb
    exact hv t (Nat.ceil_le.mpr hta) (Nat.le_floor htb)

/-- The hypothesis of Lemma 4.2 forces `n ε⁴ ≥ 5·10⁵`. -/
lemma IsClusteredRegular.card_mul_pow_four_ge (hG : IsClusteredRegular G V₁ d b)
    (h3 : ThirdEigenvalueLB G V₁ d lam3) {ε : ℝ} (hε0 : 0 < ε) (hl3 : 0 < lam3)
    (hc : (2 * b / d : ℝ) / lam3 ≤ lam3 * ε ^ 4 / (10 ^ 6 * Real.log (Fintype.card V) ^ 2)) :
    5 * 10 ^ 5 ≤ (Fintype.card V : ℝ) * ε ^ 4 := by
  have hn := hG.card_real_pos
  have hl3le := hG.lam3_le_two h3
  have hl2N := hG.two_div_card_lt
  set N : ℝ := (Fintype.card V : ℝ) with hN_def
  set LN := Real.log N
  set l2 : ℝ := 2 * b / d
  have hN4 : (4 : ℝ) ≤ N := by rw [hN_def]; exact_mod_cast hG.four_le_card
  have hLN1 : 1 ≤ LN := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_le_log (by norm_num) hN4
    have := Real.log_two_gt_d9
    linarith
  have hcr : l2 / lam3 * (10 ^ 6 * LN ^ 2) ≤ lam3 * ε ^ 4 := by
    rwa [le_div_iff₀ (by positivity)] at hc
  have hrN : 2 / (N * lam3) < l2 / lam3 := by
    rw [div_lt_div_iff₀ (by positivity) hl3]
    rw [div_lt_iff₀ hn] at hl2N
    nlinarith
  have hC : 2 * 10 ^ 6 * LN ^ 2 ≤ N * lam3 ^ 2 * ε ^ 4 := by
    have h1 : 2 / (N * lam3) * (10 ^ 6 * LN ^ 2) ≤ lam3 * ε ^ 4 := by
      have := mul_le_mul_of_nonneg_right hrN.le (show 0 ≤ 10 ^ 6 * LN ^ 2 by positivity)
      linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at h1
    nlinarith
  have h1 : lam3 ^ 2 ≤ 4 := by nlinarith
  have h2 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ N * ε ^ 4 by positivity)
  have h4 : (1 : ℝ) ≤ LN ^ 2 := by nlinarith
  nlinarith

lemma inv_sqrt_half_le {N ε : ℝ} (hN : 0 ≤ N) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (h : 5 * 10 ^ 5 ≤ N * ε ^ 4) : 1 / Real.sqrt (N / 2 + 1) ≤ ε / 10 := by
  refine one_div_sqrt_le (by positivity) (by positivity) ?_
  have h42 : ε ^ 4 ≤ ε ^ 2 := pow_le_pow_of_le_one hε0.le hε1 (by norm_num)
  have h1 : N * ε ^ 4 ≤ N * ε ^ 2 := mul_le_mul_of_nonneg_left h42 hN
  have e : (ε / 10) ^ 2 * (N / 2 + 1) = N * ε ^ 2 / 200 + ε ^ 2 / 100 := by ring
  rw [e]
  have : 0 ≤ ε ^ 2 / 100 := by positivity
  linarith

/-- A small initial community average forces one block sum to be small. -/
lemma IsClusteredRegular.blockSum_small (hG : IsClusteredRegular G V₁ d b) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (σ : V → ℤˣ) (v : V)
    (h : (projOne (signVec σ) v + projCut V₁ (signVec σ) v) ^ 2 ≤
      ε ^ 2 / Fintype.card V * ∑ w, projCut V₁ (signVec σ) w ^ 2) :
    |blockSum V₁ σ| ≤ ε * |blockSum V₁ᶜ σ| ∨ |blockSum V₁ᶜ σ| ≤ ε * |blockSum V₁ σ| := by
  have hn := hG.card_real_pos
  rw [hG.projOne_add_projCut_signVec, hG.sum_sq_projCut_signVec] at h
  set S₁ := blockSum V₁ σ
  set S₂ := blockSum V₁ᶜ σ
  have key : ∀ A B : ℝ, (2 * A / Fintype.card V) ^ 2 ≤
      ε ^ 2 / Fintype.card V * ((A - B) ^ 2 / Fintype.card V) → |A| ≤ ε * |B| := by
    intro A B hAB
    have h1 : (2 * A) ^ 2 ≤ (ε * (A - B)) ^ 2 := by
      have e1 : (2 * A / Fintype.card V) ^ 2 = (2 * A) ^ 2 / (Fintype.card V : ℝ) ^ 2 := by ring
      have e2 : ε ^ 2 / Fintype.card V * ((A - B) ^ 2 / Fintype.card V) =
          (ε * (A - B)) ^ 2 / (Fintype.card V : ℝ) ^ 2 := by ring
      rw [e1, e2] at hAB
      exact (div_le_div_iff_of_pos_right (by positivity)).mp hAB
    have h2 := sq_le_sq.mp h1
    rw [abs_mul, abs_mul, abs_of_nonneg hε0, abs_two] at h2
    have h3 : |A - B| ≤ |A| + |B| := abs_sub _ _
    have h4 : 2 * |A| ≤ ε * |A| + ε * |B| := by nlinarith [abs_nonneg A, abs_nonneg B]
    nlinarith [abs_nonneg A]
  split_ifs at h with hv
  · exact Or.inl (key S₁ S₂ h)
  · exact Or.inr (key S₂ S₁ (by rwa [show (S₂ - S₁) ^ 2 = (S₁ - S₂) ^ 2 by ring]))

lemma pos_iff_of_sq_lt {x μ : ℝ} (h : (x - μ) ^ 2 < μ ^ 2) : 0 < x ↔ 0 < μ := by
  constructor
  · intro hx; nlinarith
  · intro hμ; nlinarith

/-- Good nodes, when the community averages are not too small, have the right sign. -/
lemma sq_sub_lt_of_good {ε : ℝ} {x₀ x : V → ℝ} {v : V} (hgood : IsGood V₁ ε x₀ x v)
    (hs : ε ^ 2 / Fintype.card V * ∑ w, projCut V₁ x₀ w ^ 2 <
      (projOne x₀ v + projCut V₁ x₀ v) ^ 2) :
    (x v - (projOne x₀ v + projCut V₁ x₀ v)) ^ 2 < (projOne x₀ v + projCut V₁ x₀ v) ^ 2 :=
  lt_of_le_of_lt hgood hs

/-- **Sign recovery over the phase** (`c = 10⁶`, `C = 4`) on a general vertex type. -/
theorem IsClusteredRegular.prob_sign_window (hG : IsClusteredRegular G V₁ d b)
    (h3 : ThirdEigenvalueLB G V₁ d lam3) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hl3 : 0 < lam3)
    (hc : (2 * b / d : ℝ) / lam3 ≤ lam3 * ε ^ 4 / (10 ^ 6 * Real.log (Fintype.card V) ^ 2)) :
    1 - 4 * ε ≤ avg fun σ : V → ℤˣ =>
      expList G.Dart ⌊12 * Fintype.card V / lam3 * Real.log (Fintype.card V)⌋₊ fun l =>
        if (1 - 4 * ε) * Fintype.card V ≤ #{v | ∀ t : ℕ,
            6 * Fintype.card V / lam3 * Real.log (Fintype.card V) ≤ t →
            (t : ℝ) ≤ 12 * Fintype.card V / lam3 * Real.log (Fintype.card V) →
            SignType.sign (avgRun G (signVec σ) (l.take t) v) =
              SignType.sign (projOne (signVec σ) v + projCut V₁ (signVec σ) v)}
        then 1 else 0 := by
  haveI := hG.nonempty_dart
  have hn := hG.card_real_pos
  have hgood := hG.prob_good_window h3 hε0 hε1 hl3 hc
  have hA := hG.avg_abs_blockSum_le_mul (V₁ := V₁) hε0.le
  have hB := hG.avg_abs_blockSum_compl_le_mul (V₁ := V₁) hε0.le
  have hsq := inv_sqrt_half_le hn.le hε0 hε1 (hG.card_mul_pow_four_ge h3 hε0 hl3 hc)
  set T := ⌊12 * (Fintype.card V : ℝ) / lam3 * Real.log (Fintype.card V)⌋₊
  set a := 6 * (Fintype.card V : ℝ) / lam3 * Real.log (Fintype.card V)
  set a2 := 12 * (Fintype.card V : ℝ) / lam3 * Real.log (Fintype.card V)
  have hpt : ∀ σ : V → ℤˣ,
      expList G.Dart T (fun l => if (1 - 3 * ε) * Fintype.card V ≤ #{v | ∀ t : ℕ, a ≤ t →
          (t : ℝ) ≤ a2 → IsGood V₁ ε (signVec σ) (avgRun G (signVec σ) (l.take t)) v}
        then 1 else 0) -
        ((if |blockSum V₁ σ| ≤ ε * |blockSum V₁ᶜ σ| then (1 : ℝ) else 0) +
          (if |blockSum V₁ᶜ σ| ≤ ε * |blockSum V₁ σ| then (1 : ℝ) else 0)) ≤
      expList G.Dart T (fun l => if (1 - 4 * ε) * Fintype.card V ≤ #{v | ∀ t : ℕ, a ≤ t →
          (t : ℝ) ≤ a2 → SignType.sign (avgRun G (signVec σ) (l.take t) v) =
            SignType.sign (projOne (signVec σ) v + projCut V₁ (signVec σ) v)} then 1 else 0) := by
    intro σ
    have hI0 : ∀ (P : Prop) [Decidable P], (0 : ℝ) ≤ if P then 1 else 0 := fun P _ => by
      split_ifs <;> norm_num
    have hle1 : expList G.Dart T (fun l => if (1 - 3 * ε) * Fintype.card V ≤ #{v | ∀ t : ℕ,
        a ≤ t → (t : ℝ) ≤ a2 → IsGood V₁ ε (signVec σ) (avgRun G (signVec σ) (l.take t)) v}
          then (1 : ℝ) else 0) ≤ 1 :=
      (expList_le_expList fun l => by split_ifs <;> norm_num).trans (expList_const T 1).le
    have hR0 : 0 ≤ expList G.Dart T (fun l => if (1 - 4 * ε) * Fintype.card V ≤ #{v | ∀ t : ℕ,
        a ≤ t → (t : ℝ) ≤ a2 → SignType.sign (avgRun G (signVec σ) (l.take t) v) =
          SignType.sign (projOne (signVec σ) v + projCut V₁ (signVec σ) v)} then (1 : ℝ)
            else 0) := expList_nonneg fun l => by split_ifs <;> norm_num
    by_cases hs : ∀ v, ε ^ 2 / Fintype.card V * ∑ w, projCut V₁ (signVec σ) w ^ 2 <
        (projOne (signVec σ) v + projCut V₁ (signVec σ) v) ^ 2
    · have hmono : expList G.Dart T (fun l => if (1 - 3 * ε) * Fintype.card V ≤ #{v | ∀ t : ℕ,
          a ≤ t → (t : ℝ) ≤ a2 → IsGood V₁ ε (signVec σ) (avgRun G (signVec σ) (l.take t)) v}
            then (1 : ℝ) else 0) ≤
          expList G.Dart T (fun l => if (1 - 4 * ε) * Fintype.card V ≤ #{v | ∀ t : ℕ, a ≤ t →
            (t : ℝ) ≤ a2 → SignType.sign (avgRun G (signVec σ) (l.take t) v) =
              SignType.sign (projOne (signVec σ) v + projCut V₁ (signVec σ) v)}
                then 1 else 0) := by
        refine expList_le_expList fun l => ?_
        split_ifs with h1 h2 <;> try norm_num
        refine absurd ?_ h2
        have hsub : #{v | ∀ t : ℕ, a ≤ t → (t : ℝ) ≤ a2 →
            IsGood V₁ ε (signVec σ) (avgRun G (signVec σ) (l.take t)) v} ≤
            #{v | ∀ t : ℕ, a ≤ t → (t : ℝ) ≤ a2 →
              SignType.sign (avgRun G (signVec σ) (l.take t) v) =
                SignType.sign (projOne (signVec σ) v + projCut V₁ (signVec σ) v)} := by
          refine Finset.card_le_card fun v hv => ?_
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
          intro t ht1 ht2
          have h := sq_sub_lt_of_good (hv t ht1 ht2) (hs v)
          have := sign_add_of_sq_lt h
          rwa [add_sub_cancel] at this
        have : (#{v | ∀ t : ℕ, a ≤ t → (t : ℝ) ≤ a2 →
            IsGood V₁ ε (signVec σ) (avgRun G (signVec σ) (l.take t)) v} : ℝ) ≤
            #{v | ∀ t : ℕ, a ≤ t → (t : ℝ) ≤ a2 →
              SignType.sign (avgRun G (signVec σ) (l.take t) v) =
                SignType.sign (projOne (signVec σ) v + projCut V₁ (signVec σ) v)} := by
          exact_mod_cast hsub
        nlinarith
      have := hI0 (|blockSum V₁ σ| ≤ ε * |blockSum V₁ᶜ σ|)
      have := hI0 (|blockSum V₁ᶜ σ| ≤ ε * |blockSum V₁ σ|)
      linarith
    · simp only [not_forall, not_lt] at hs
      obtain ⟨v, hv⟩ := hs
      rcases hG.blockSum_small hε0.le hε1 σ v hv with h | h
      · rw [if_pos h]
        have := hI0 (|blockSum V₁ᶜ σ| ≤ ε * |blockSum V₁ σ|)
        linarith
      · rw [if_pos h]
        have := hI0 (|blockSum V₁ σ| ≤ ε * |blockSum V₁ᶜ σ|)
        linarith
  refine le_trans ?_ (avg_le_avg hpt)
  rw [avg_sub, avg_add]
  linarith

end General

/-- Theorem 4.1 (second moment analysis): on an `(n, d, b)`-clustered regular graph with
`λ₂ = 2b/d = o(λ₃ / log n)` (here `c λ₂ log n ≤ λ₃` for a large enough constant `c`), for every
round `3 (n/λ₃) log n ≤ t ≤ n/(4λ₂)`, `E‖y⁽ᵗ⁾ + z⁽ᵗ⁾ - y⁽⁰⁾‖² ≤ 3 λ₂ t / n`, the expectation
being over the uniform initial vector and the `t` uniform edges. -/
theorem secondMoment_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (V₁ : Finset (Fin n)) (d b : ℕ) (lam3 : ℝ), IsClusteredRegular G V₁ d b →
      ThirdEigenvalueLB G V₁ d lam3 → c * (2 * b / d) * Real.log n ≤ lam3 →
      ∀ t : ℕ, 3 * n / lam3 * Real.log n ≤ t → (t : ℝ) ≤ n / (4 * (2 * b / d)) →
        avg (fun σ : Fin n → ℤˣ => expList G.Dart t fun l =>
          ∑ v, (projCut V₁ (avgRun G (signVec σ) l) v + projRest V₁ (avgRun G (signVec σ) l) v -
            projCut V₁ (signVec σ) v) ^ 2) ≤ (3 * (2 * b / d) * t / n : ℝ) := by
  refine ⟨100, by norm_num, fun n G _ V₁ d b lam3 hG h3 hc t ht _ => ?_⟩
  have := hG.secondMoment_bound_aux h3 (by simpa using hc) t (by simpa using ht)
  simpa using this

/-- Lemma 4.2 (non-ephemeral good nodes): on an `(n, d, b)`-clustered regular graph with
`λ₂/λ₃ ≤ λ₃ ε⁴/(c log² n)` for a large enough constant `c` (`λ₂ = 2b/d`), with probability at least
`1 - ε` over the initial vector and the edges, at least `(1 - 3ε) n` nodes are `ε`-good at every
round `t` of the phase `6 (n/λ₃) log n ≤ t ≤ 12 (n/λ₃) log n`. -/
theorem nonEphemeral_good :
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (V₁ : Finset (Fin n)) (d b : ℕ) (lam3 ε : ℝ), IsClusteredRegular G V₁ d b →
      ThirdEigenvalueLB G V₁ d lam3 → 0 < lam3 → 0 < ε →
      (2 * b / d : ℝ) / lam3 ≤ lam3 * ε ^ 4 / (c * Real.log n ^ 2) →
      1 - ε ≤ avg fun σ : Fin n → ℤˣ =>
        expList G.Dart ⌊12 * n / lam3 * Real.log n⌋₊ fun l =>
          if (1 - 3 * ε) * n ≤ #{v | ∀ t : ℕ, 6 * n / lam3 * Real.log n ≤ t →
              (t : ℝ) ≤ 12 * n / lam3 * Real.log n →
              IsGood V₁ ε (signVec σ) (avgRun G (signVec σ) (l.take t)) v}
          then 1 else 0 := by
  refine ⟨10 ^ 6, by norm_num, fun n G _ V₁ d b lam3 ε hG h3 hl3 hε hc => ?_⟩
  rcases le_or_gt 1 ε with hε1 | hε1
  · refine le_trans (by linarith) (avg_nonneg fun σ => expList_nonneg fun l => ?_)
    split_ifs <;> norm_num
  have := hG.prob_good_window h3 hε hε1.le hl3 (by simpa using hc)
  simpa using this

/-- Sign recovery over the phase (Lemma 4.2 with Lemma A.1, as in Section 4.2 and in the proof of
Lemma C.7): under the hypotheses of Lemma 4.2, with probability at least `1 - C ε`, at least
`(1 - C ε) n` nodes `v` have, at every round of the phase, the sign of `x_∥,v + y⁽⁰⁾_v`, the
initial average of the community of `v`. -/
theorem sign_phase :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (V₁ : Finset (Fin n)) (d b : ℕ) (lam3 ε : ℝ), IsClusteredRegular G V₁ d b →
      ThirdEigenvalueLB G V₁ d lam3 → 0 < lam3 → 0 < ε →
      (2 * b / d : ℝ) / lam3 ≤ lam3 * ε ^ 4 / (c * Real.log n ^ 2) →
      1 - C * ε ≤ avg fun σ : Fin n → ℤˣ =>
        expList G.Dart ⌊12 * n / lam3 * Real.log n⌋₊ fun l =>
          if (1 - C * ε) * n ≤ #{v | ∀ t : ℕ, 6 * n / lam3 * Real.log n ≤ t →
              (t : ℝ) ≤ 12 * n / lam3 * Real.log n →
              SignType.sign (avgRun G (signVec σ) (l.take t) v) =
                SignType.sign (projOne (signVec σ) v + projCut V₁ (signVec σ) v)}
          then 1 else 0 := by
  sorry

/-- **Main theorem** (averaging whenever you meet recovers the communities): on an
`(n, d, b)`-clustered regular graph with `λ₂/λ₃ ≤ λ₃ ε⁴/(c log² n)` for a large enough constant `c`
(`λ₂ = 2b/d`), with probability at least `1/2 - C ε` over the initial coins and the edges, the sign
of the values (`+1` for a positive value, `-1` otherwise) is a `C ε`-weak reconstruction of the two
communities at every round of the phase `6 (n/λ₃) log n ≤ t ≤ 12 (n/λ₃) log n`. -/
theorem weakReconstruction_phase :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (V₁ : Finset (Fin n)) (d b : ℕ) (lam3 ε : ℝ), IsClusteredRegular G V₁ d b →
      ThirdEigenvalueLB G V₁ d lam3 → 0 < lam3 → 0 < ε →
      (2 * b / d : ℝ) / lam3 ≤ lam3 * ε ^ 4 / (c * Real.log n ^ 2) →
      1 / 2 - C * ε ≤ avg fun σ : Fin n → ℤˣ =>
        expList G.Dart ⌊12 * n / lam3 * Real.log n⌋₊ fun l =>
          if ∀ t : ℕ, 6 * n / lam3 * Real.log n ≤ t → (t : ℝ) ≤ 12 * n / lam3 * Real.log n →
              IsWeakReconstruction V₁ (C * ε)
                fun v => if 0 < avgRun G (signVec σ) (l.take t) v then 1 else -1
          then 1 else 0 := by
  sorry

end Averaging.Opportunistic
