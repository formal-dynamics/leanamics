import Dynamics.DriftAux

/-!
# Drift theorems: from an expected potential drop to absorption

Let `Ψ ≥ 0` be a potential on a finite chain that vanishes exactly on the absorbed states, and
that stays zero once it is zero. Two ways to turn its expected one-step behaviour into a bound
on the absorption time, both from Berenbrink, Giakkoupis, Kermarrec, Mallmann-Trenn, *Bounds on
the voter model in dynamic networks*, ICALP 2016, [arXiv:1603.01895]:

* **Drift `c / Ψ`** (Lemma 2.2, used there with `Ψ = √vol(minority)` and
  `c_t = d_min φ_t / 32` from Lemma 2.1): if `𝔼[Ψ_{t+1} | X_t = x] ≤ Ψ x - c_t / Ψ x` whenever
  `Ψ x > 0`, then the chain is absorbed at time `T` with probability at least `1/2` as soon as
  `∑_{t < T} c_t ≥ 4 Ψ(x₀)²`. The proof iterates on `𝔼[Ψ_t]`: by Jensen (Cauchy–Schwarz),
  `𝔼[Ψ_{t+1}] ≤ 𝔼[Ψ_t] - c_t P(Ψ_t > 0)² / 𝔼[Ψ_t]`, so `𝔼[Ψ_t]` would become negative if the
  survival probability stayed above `1/2`. No concentration is used.
  (`drift_absorption_seq`, `drift_absorption`.)
* **Multiplicative drift** (the argument of Lemma 2.4): if `𝔼[Ψ_{t+1} | X_t = x] ≤ (1 - δ_t) Ψ x`
  for every state, then `𝔼[Ψ_T] ≤ ∏_{t < T} (1 - δ_t) Ψ(x₀)` and, by Markov's inequality, the
  chain survives to time `T` with probability at most `∏_{t < T} (1 - δ_t) Ψ(x₀) / Ψ_min`, where
  `Ψ_min` bounds the nonzero values of `Ψ` from below.
  (`multiplicative_drift_seq`, `multiplicative_drift`.)

The `_seq` versions allow a time-dependent chain (`iterateSeq`) and time-dependent drift, as for
the dynamic graphs of the paper; the others are their time-homogeneous specializations, stated
with `Kernel.event`.
-/

namespace Dynamics.Kernel
open Finset
variable {α : Type*} [Fintype α]

/-- **Drift lemma, time-dependent form** (Lemma 2.2 of Berenbrink, Giakkoupis, Kermarrec,
Mallmann-Trenn, ICALP 2016). Let `Ψ ≥ 0`. Suppose that for every step `t < T`, the kernel `K t`
lowers `Ψ` in expectation by at least `c t / Ψ x` from every state `x` with `Ψ x > 0`, and keeps
`Ψ` at zero from every state with `Ψ x = 0`. If `∑_{t < T} c t ≥ 4 Ψ(x₀)²`, then started at `x₀`
the chain has `Ψ = 0` (is absorbed) at time `T` with probability at least `1/2`. -/
theorem drift_absorption_seq (K : ℕ → Dynamics.Kernel α) (Ψ : α → ℝ) (c : ℕ → ℝ) (T : ℕ)
    (hΨ : ∀ x, 0 ≤ Ψ x) (hc : ∀ t < T, 0 ≤ c t)
    (hdrift : ∀ t < T, ∀ x, 0 < Ψ x → (K t).apply Ψ x ≤ Ψ x - c t / Ψ x)
    (habs : ∀ t < T, ∀ x, Ψ x = 0 → (K t).apply Ψ x = 0)
    (x₀ : α) (hT : 4 * Ψ x₀ ^ 2 ≤ ∑ t ∈ range T, c t) :
    1 / 2 ≤ iterateSeq K T (fun x => if Ψ x = 0 then 1 else 0) x₀ := by
  obtain ⟨m, hm, hmle⟩ := exists_pos_mul_ind_le Ψ hΨ
  -- `q`: survival probability at time `T`; `lam`: the multiplier of the linearization
  set q := iterateSeq K T (fun x => if 0 < Ψ x then 1 else 0) x₀ with hq
  have hq0 : 0 ≤ q := iterateSeq_nonneg K T (fun x => by split_ifs <;> norm_num) x₀
  set lam := q / Ψ x₀ with hlam
  have hlam0 : 0 ≤ lam := div_nonneg hq0 (hΨ x₀)
  have hid : lam ^ 2 * Ψ x₀ = lam * q := by
    rcases (hΨ x₀).eq_or_lt with h | h
    · simp [hlam, ← h]
    · have := h.ne'
      rw [hlam]
      field_simp
  have hsub := iterateSeq_le_sub_of_drift K Ψ c T hΨ hc hdrift habs x₀ hlam0 hq0 hid
    (fun t ht => iterateSeq_ind_pos_antitone K Ψ hΨ T habs x₀ ht.le) T le_rfl
  -- `m q ≤ 𝔼[Ψ_T] ≤ Ψ(x₀) - lam q ∑ c ≤ Ψ(x₀) (1 - 4 q²)`
  have hmq : m * q ≤ iterateSeq K T Ψ x₀ := by
    have h := iterateSeq_mono K T hmle x₀
    rw [iterateSeq_mul] at h
    exact h
  have hid2 : lam * q * (4 * Ψ x₀ ^ 2) = 4 * q ^ 2 * Ψ x₀ := by
    rcases (hΨ x₀).eq_or_lt with h | h
    · simp [← h]
    · have := h.ne'
      rw [hlam]
      field_simp
  have hlq := mul_le_mul_of_nonneg_left hT (mul_nonneg hlam0 hq0)
  have hq2 : q ≤ 1 / 2 := by
    by_contra hcon
    have hcon := not_le.mp hcon
    have h4 : 0 ≤ Ψ x₀ * (4 * q ^ 2 - 1) := mul_nonneg (hΨ x₀) (by nlinarith)
    have h5 : 0 < m * q := mul_pos hm (by linarith)
    nlinarith
  rw [ind_eq_zero_eq Ψ hΨ, iterateSeq_one_sub]
  linarith

/-- **Drift lemma** (Lemma 2.2 of Berenbrink, Giakkoupis, Kermarrec, Mallmann-Trenn, ICALP 2016,
for a single kernel). Let `Ψ ≥ 0` satisfy `𝔼[Ψ_{t+1} | X_t = x] ≤ Ψ x - c / Ψ x` whenever
`Ψ x > 0`, and let the states with `Ψ = 0` be absorbing for `Ψ`. Then the chain started at `x₀`
is absorbed by every time `T` with `c T ≥ 4 Ψ(x₀)²`, with probability at least `1/2`. -/
theorem drift_absorption (K : Dynamics.Kernel α) (Ψ : α → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hΨ : ∀ x, 0 ≤ Ψ x)
    (hdrift : ∀ x, 0 < Ψ x → K.apply Ψ x ≤ Ψ x - c / Ψ x)
    (habs : ∀ x, Ψ x = 0 → K.apply Ψ x = 0)
    (x₀ : α) {T : ℕ} (hT : 4 * Ψ x₀ ^ 2 ≤ c * T) :
    1 / 2 ≤ K.event (fun x => Ψ x = 0) T x₀ := by
  rw [event_eq_iterateSeq]
  refine drift_absorption_seq (fun _ => K) Ψ (fun _ => c) T hΨ (fun _ _ => hc)
    (fun _ _ => hdrift) (fun _ _ => habs) x₀ ?_
  rw [sum_const, card_range, nsmul_eq_mul]
  linarith

/-- **Multiplicative drift, time-dependent form** (the argument of Lemma 2.4 of Berenbrink,
Giakkoupis, Kermarrec, Mallmann-Trenn, ICALP 2016). Let `Ψ ≥ 0`, with every nonzero value at
least `Ψmin > 0`. If for every step `t < T` the kernel `K t` satisfies
`𝔼[Ψ_{t+1} | X_t = x] ≤ (1 - δ t) Ψ x` from every state `x` (absorbed ones included), then the
chain started at `x₀` still has `Ψ > 0` at time `T` with probability at most
`∏_{t < T} (1 - δ t) Ψ(x₀) / Ψmin`. -/
theorem multiplicative_drift_seq (K : ℕ → Dynamics.Kernel α) (Ψ : α → ℝ) (δ : ℕ → ℝ) (T : ℕ)
    {Ψmin : ℝ} (hΨ : ∀ x, 0 ≤ Ψ x) (hmin : 0 < Ψmin) (hgap : ∀ x, 0 < Ψ x → Ψmin ≤ Ψ x)
    (hdrift : ∀ t < T, ∀ x, (K t).apply Ψ x ≤ (1 - δ t) * Ψ x) (x₀ : α) :
    iterateSeq K T (fun x => if 0 < Ψ x then 1 else 0) x₀
      ≤ (∏ t ∈ range T, (1 - δ t)) * Ψ x₀ / Ψmin := by
  by_cases h0 : ∀ x, Ψ x = 0
  · have h : (fun x => if 0 < Ψ x then (1 : ℝ) else 0) = fun _ => 0 :=
      funext fun x => by simp [h0 x]
    rw [h, iterateSeq_const_fun, h0 x₀]
    simp
  obtain ⟨y, hy⟩ := not_forall.mp h0
  have hy' : 0 < Ψ y := lt_of_le_of_ne (hΨ y) (Ne.symm hy)
  -- some state has `Ψ > 0`, so `hdrift` forces every factor `1 - δ t` to be nonnegative
  have hδ : ∀ t < T, 0 ≤ 1 - δ t := fun t ht =>
    nonneg_of_mul_nonneg_left (((K t y).expect_nonneg hΨ).trans (hdrift t ht y)) hy'
  calc iterateSeq K T (fun x => if 0 < Ψ x then 1 else 0) x₀
      ≤ iterateSeq K T (fun x => Ψmin⁻¹ * Ψ x) x₀ :=
        iterateSeq_mono K T (ind_pos_le_div Ψ hΨ hmin hgap) x₀
    _ = Ψmin⁻¹ * iterateSeq K T Ψ x₀ := by rw [iterateSeq_mul]
    _ ≤ Ψmin⁻¹ * ((∏ t ∈ range T, (1 - δ t)) * Ψ x₀) :=
        mul_le_mul_of_nonneg_left (iterateSeq_le_prod_of_drift K Ψ δ T hδ hdrift x₀ T le_rfl)
          (inv_nonneg.mpr hmin.le)
    _ = (∏ t ∈ range T, (1 - δ t)) * Ψ x₀ / Ψmin := by rw [div_eq_inv_mul]

/-- **Multiplicative drift** (the argument of Lemma 2.4 of Berenbrink, Giakkoupis, Kermarrec,
Mallmann-Trenn, ICALP 2016, for a single kernel). Let `Ψ ≥ 0`, with every nonzero value at least
`Ψmin > 0`, and `𝔼[Ψ_{t+1} | X_t = x] ≤ (1 - δ) Ψ x` from every state. Then the chain started at
`x₀` is not absorbed at time `T` with probability at most `(1 - δ)^T Ψ(x₀) / Ψmin`. -/
theorem multiplicative_drift (K : Dynamics.Kernel α) (Ψ : α → ℝ) {δ Ψmin : ℝ}
    (hΨ : ∀ x, 0 ≤ Ψ x) (hmin : 0 < Ψmin) (hgap : ∀ x, 0 < Ψ x → Ψmin ≤ Ψ x)
    (hdrift : ∀ x, K.apply Ψ x ≤ (1 - δ) * Ψ x) (x₀ : α) (T : ℕ) :
    K.event (fun x => 0 < Ψ x) T x₀ ≤ (1 - δ) ^ T * Ψ x₀ / Ψmin := by
  rw [event_eq_iterateSeq]
  have h := multiplicative_drift_seq (fun _ => K) Ψ (fun _ => δ) T hΨ hmin hgap
    (fun _ _ => hdrift) x₀
  rwa [prod_const, card_range] at h

end Dynamics.Kernel
