import Voter.ConductanceMany

/-! # Helpers for the `O(n log n / φ²)` bound (BGKM16, Lemma 2.4)

Helpers for Part 2 of Theorem 1.1 of Berenbrink, Giakkoupis, Kermarrec, Mallmann-Trenn,
*Bounds on the voter model in dynamic networks*, ICALP 2016 (BGKM16):

* `prod_one_sub_le`: `∏_{t < T} (1 - φ_t² / (32 n)) ≤ 1/n³` once `∑_{t < T} φ_t² ≥ 96 n ln n`;
* `iterateSeq_pos_le_of_mul_drift`: the multiplicative drift lemma
  `Dynamics.Kernel.multiplicative_drift_seq` with this rate, for a potential whose nonzero values
  are at least `1`;
* `iterateSeq_finset_sum`: expectations of a time-dependent chain are additive over finite sums;
* the potential is at least `1` before consensus (`one_le_potential`) and at most `n`
  (`potential_le_card`), since `vol(s_t) ≤ m ≤ n²`;
* `sq_conductance_mul_vol_le`: `(φ vol(s_t))² ≤ n ∑_{u ∈ s_t} λ_u d_u` (Cauchy–Schwarz);
* `disagreement_eq_zero_of_card_le_one`: with at most one vertex there is nothing to agree on.
-/

namespace Voter
open Dynamics Finset

/-! ### Multiplicative drift with the rate `φ_t² / (32 n)` -/

section Generic
variable {α : Type*} [Fintype α]

/-- **The product of the drift factors**: if `0 ≤ φ_t ≤ 1`, `n ≥ 1` and
`96 n ln n ≤ ∑_{t < T} φ_t²`, then `∏_{t < T} (1 - φ_t² / (32 n)) ≤ 1/n³`, by `1 - x ≤ e^{-x}`. -/
lemma prod_one_sub_le {n : ℝ} (hn : 1 ≤ n) (φ : ℕ → ℝ) (hφ0 : ∀ t, 0 ≤ φ t)
    (hφ1 : ∀ t, φ t ≤ 1) (T : ℕ) (hT : 96 * n * Real.log n ≤ ∑ t ∈ range T, φ t ^ 2) :
    ∏ t ∈ range T, (1 - φ t ^ 2 / (32 * n)) ≤ 1 / n ^ 3 := by
  have hn0 : 0 < n := by linarith
  calc ∏ t ∈ range T, (1 - φ t ^ 2 / (32 * n))
      ≤ ∏ t ∈ range T, Real.exp (-(φ t ^ 2 / (32 * n))) := by
        apply prod_le_prod
        · intro t _
          have h1 : φ t ^ 2 ≤ 1 := by nlinarith [hφ0 t, hφ1 t]
          have h2 : φ t ^ 2 / (32 * n) ≤ 1 := by
            rw [div_le_one (by positivity)]
            linarith
          linarith
        · intro t _
          linarith [Real.add_one_le_exp (-(φ t ^ 2 / (32 * n)))]
    _ = Real.exp (-((∑ t ∈ range T, φ t ^ 2) / (32 * n))) := by
        rw [← Real.exp_sum, sum_div, ← sum_neg_distrib]
    _ ≤ Real.exp (-(3 * Real.log n)) := by
        apply Real.exp_le_exp.mpr
        rw [neg_le_neg_iff, le_div_iff₀ (by positivity)]
        linarith
    _ = 1 / n ^ 3 := by
        have h3 : 3 * Real.log n = Real.log (n ^ 3) := by
          rw [Real.log_pow]
          norm_num
        rw [h3, Real.exp_neg, Real.exp_log (by positivity), one_div]

/-- **Multiplicative drift with the rate of Lemma 2.4 of BGKM16.** Let `Ψ ≥ 0` with every nonzero
value at least `1`, and `𝔼[Ψ_{t+1} | X_t = x] ≤ (1 - φ_t² / (32 n)) Ψ(x)` for every step `t < T`,
with `0 ≤ φ_t ≤ 1` and `n ≥ 1`. If `96 n ln n ≤ ∑_{t < T} φ_t²`, then `Ψ > 0` at time `T` with
probability at most `Ψ(x₀) / n³`. -/
lemma iterateSeq_pos_le_of_mul_drift (K : ℕ → Kernel α) (Ψ : α → ℝ) (hΨ : ∀ x, 0 ≤ Ψ x)
    (hgap : ∀ x, 0 < Ψ x → 1 ≤ Ψ x) {n : ℝ} (hn : 1 ≤ n) (φ : ℕ → ℝ) (hφ0 : ∀ t, 0 ≤ φ t)
    (hφ1 : ∀ t, φ t ≤ 1) (T : ℕ)
    (hdrift : ∀ t < T, ∀ x, (K t).apply Ψ x ≤ (1 - φ t ^ 2 / (32 * n)) * Ψ x)
    (hT : 96 * n * Real.log n ≤ ∑ t ∈ range T, φ t ^ 2) (x₀ : α) :
    Kernel.iterateSeq K T (fun x => if 0 < Ψ x then 1 else 0) x₀ ≤ Ψ x₀ / n ^ 3 := by
  have h := Kernel.multiplicative_drift_seq K Ψ (fun t => φ t ^ 2 / (32 * n)) T hΨ one_pos hgap
    hdrift x₀
  rw [div_one] at h
  calc Kernel.iterateSeq K T (fun x => if 0 < Ψ x then 1 else 0) x₀
      ≤ (∏ t ∈ range T, (1 - φ t ^ 2 / (32 * n))) * Ψ x₀ := h
    _ ≤ 1 / n ^ 3 * Ψ x₀ :=
        mul_le_mul_of_nonneg_right (prod_one_sub_le hn φ hφ0 hφ1 T hT) (hΨ x₀)
    _ = Ψ x₀ / n ^ 3 := by ring

/-- Expectations of a time-dependent chain are additive over finite sums of observables. -/
lemma iterateSeq_finset_sum {ι : Type*} (K : ℕ → Kernel α) (n : ℕ) (s : Finset ι)
    (F : ι → α → ℝ) (x : α) :
    Kernel.iterateSeq K n (fun y => ∑ i ∈ s, F i y) x =
      ∑ i ∈ s, Kernel.iterateSeq K n (F i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [sum_empty]
    exact congrFun (Kernel.iterateSeq_const_fun K n 0) x
  | insert a s ha ih =>
    simp only [sum_insert ha]
    rw [Kernel.iterateSeq_add]
    exact congrArg _ ih

end Generic

/-! ### The potential and the cut -/

variable {V C : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
/-- Before consensus the potential is at least `1` (volumes are integers). -/
lemma one_le_potential (s : Config V Bool) (h : 0 < potential G s) : 1 ≤ potential G s := by
  unfold potential at *
  rw [Real.sqrt_pos, Nat.cast_pos] at h
  rw [Real.one_le_sqrt]
  exact_mod_cast h

/-- The potential is at most the number of vertices: `vol(s_t) ≤ m ≤ n²`. -/
lemma potential_le_card (s : Config V Bool) : potential G s ≤ Fintype.card V := by
  have h1 : vol G (minority G s) ≤ Fintype.card V ^ 2 :=
    (vol_minority_le_edges G s).trans
      (G.card_edgeFinset_le_card_choose_two.trans (Nat.choose_le_pow _ _))
  have h2 : (vol G (minority G s) : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by exact_mod_cast h1
  exact (Real.sqrt_le_sqrt h2).trans_eq (Real.sqrt_sq (Nat.cast_nonneg _))

/-- **Cauchy–Schwarz on the minority side** (proof of Lemma 2.4 of BGKM16):
`(φ vol(s_t))² ≤ (∑_{u ∈ s_t} λ_u)² ≤ n ∑_{u ∈ s_t} λ_u² ≤ n ∑_{u ∈ s_t} λ_u d_u`. -/
lemma sq_conductance_mul_vol_le (s : Config V Bool) :
    (conductance G * vol G (minority G s)) ^ 2 ≤
      Fintype.card V * ∑ u ∈ minority G s, (discordant G s u : ℝ) * G.degree u := by
  obtain ⟨b, hb⟩ := exists_minority_eq G s
  have hcs : ((G.interedges (minority G s) (minority G s)ᶜ).card : ℝ) =
      ∑ u ∈ minority G s, (discordant G s u : ℝ) := by
    rw [hb]
    exact_mod_cast card_interedges_class G s b
  have hcut : conductance G * vol G (minority G s) ≤
      ∑ u ∈ minority G s, (discordant G s u : ℝ) := by
    rcases Nat.eq_zero_or_pos (vol G (minority G s)) with h0 | h0
    · rw [h0, Nat.cast_zero, mul_zero]
      exact sum_nonneg fun _ _ => Nat.cast_nonneg _
    · rw [← hcs]
      exact conductance_mul_vol_le G _ h0 (vol_minority_le_edges G s)
  have h0 : 0 ≤ conductance G * vol G (minority G s) :=
    mul_nonneg (conductance_nonneg G) (Nat.cast_nonneg _)
  calc (conductance G * vol G (minority G s)) ^ 2
      ≤ (∑ u ∈ minority G s, (discordant G s u : ℝ)) ^ 2 := pow_le_pow_left₀ h0 hcut 2
    _ ≤ (minority G s).card * ∑ u ∈ minority G s, (discordant G s u : ℝ) ^ 2 :=
        sq_sum_le_card_mul_sum_sq
    _ ≤ Fintype.card V * ∑ u ∈ minority G s, (discordant G s u : ℝ) * G.degree u := by
        apply mul_le_mul (by exact_mod_cast card_le_univ _) _
          (sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _)
        refine sum_le_sum fun u _ => ?_
        rw [sq]
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast discordant_le_degree G s u)
          (Nat.cast_nonneg _)

omit [Fintype V] [DecidableEq V] in
/-- With at most one vertex, every configuration is at consensus. -/
lemma disagreement_eq_zero_of_card_le_one [Fintype V] (hV : Fintype.card V ≤ 1) (c : C)
    (x : Config V C) : disagreement x = 0 := by
  classical
  have hs : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp hV
  have h : ∃ c, x = fun _ => c := by
    by_cases hne : Nonempty V
    · obtain ⟨v⟩ := hne
      exact ⟨x v, funext fun u => by rw [Subsingleton.elim u v]⟩
    · exact ⟨c, funext fun u => (hne ⟨u⟩).elim⟩
  unfold disagreement
  rw [if_pos h]

end Voter
