import Averaging.OpportunisticNonEphemeral

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
