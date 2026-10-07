import Dynamics.DriftHittingAux

/-!
# A hitting-time bound for chains with multiplicative growth

Claim 2.9 of Doerr, Goldberg, Minder, Sauerwald, Scheideler, *Stabilizing consensus with the
power of two choices*, SPAA 2011 (its proof is omitted there). It is the symmetry-breaking step
of the binary median (2-Choices) dynamics from an almost balanced configuration, see Becchetti,
Clementi, Natale, *Consensus dynamics: an overview*, SIGACT News 2020, §4 Case 3, where it is
applied to `X = ⌊s / (γ √n)⌋` (`s` the bias) with `q = ⌊(n / 2) / (γ √n)⌋`.

Let `X` be an observable of a finite chain with values in `{0, …, q}`. Suppose that from every
state below the target, `X` grows by a factor `c₁ > 1` (capped at `q`) in one step except with
probability `exp (-c₂ X)`, and that from every state with `X = 0`, `X` becomes positive with
probability at least `c₃ > 0`. Then for every `c₄, c₆ > 0` there is `c₅ > 0`, depending on
`c₁, c₂, c₃, c₄, c₆` only, such that `X` reaches `c₄ log q` within `c₅ log q + log_{c₁} (c₄ log q)`
steps with probability at least `1 - q^{-c₆}` (`drift_hitting`); equivalently within `C log q`
steps (`drift_hitting_log`).

The chain is a `Dynamics.Kernel` on any finite state space and `X` is a function of the state.
The source's Markov chain on `{0, …, q}` is the case `X = Fin.val`; the general form is the one
needed by the application, where `X` is a function of the configuration. The target must be a
value of `X`: `c₄ log q ≤ q` is assumed, since otherwise it is never hit.
-/

namespace Dynamics.Kernel

universe u

/-- **Hitting-time bound** (Claim 2.9 of Doerr, Goldberg, Minder, Sauerwald, Scheideler,
SPAA 2011). Let `c₁ > 1` and `c₂, c₃, c₄, c₆ > 0`. There is `c₅ > 0` such that the following holds
for every finite chain `K` and observable `X` with values in `{0, …, q}` such that the target
`c₄ log q` is at most `q`. Suppose that from every state `a` below the target, the next state `b`
has `X b ≥ min (c₁ X a) q` with probability at least `1 - exp (-c₂ X a)`, and that from every
state with `X a = 0`, the next state has `X b ≥ 1` with probability at least `c₃`. Then from any
start `a₀`, the hitting time `T = min {t : X_t ≥ c₄ log q}` satisfies `T ≤ t` with probability at
least `1 - q^{-c₆}`, for every `t ≥ c₅ log q + log_{c₁} (c₄ log q)`. -/
theorem drift_hitting {c₁ c₂ c₃ c₄ c₆ : ℝ} (hc₁ : 1 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hc₄ : 0 < c₄) (hc₆ : 0 < c₆) :
    ∃ c₅ : ℝ, 0 < c₅ ∧
      ∀ {α : Type u} [Fintype α] (K : Dynamics.Kernel α) (X : α → ℕ) (q : ℕ),
        (∀ a, X a ≤ q) →
        (∀ a, (X a : ℝ) < c₄ * Real.log q →
          1 - Real.exp (-(c₂ * X a)) ≤ (K a).prob (fun b => min (c₁ * X a) q ≤ X b)) →
        (∀ a, X a = 0 → c₃ ≤ (K a).prob (fun b => 1 ≤ X b)) →
        c₄ * Real.log q ≤ q →
        ∀ (a₀ : α) (t : ℕ), c₅ * Real.log q + Real.logb c₁ (c₄ * Real.log q) ≤ t →
          1 - (q : ℝ) ^ (-c₆) ≤ K.hitProb (fun b => c₄ * Real.log q ≤ X b) t a₀ := by
  -- the potential, depending on `c₁, c₂, c₃` only
  set p := min c₃ (1 - Real.exp (-c₂)) with hp
  have hexp : Real.exp (-c₂) < 1 := by
    have := Real.exp_lt_exp.mpr (neg_lt_zero.mpr hc₂)
    rwa [Real.exp_zero] at this
  have hp0 : 0 < p := lt_min hc₃ (by linarith)
  have hp1 : p < 1 := (min_le_right _ _).trans_lt (by linarith [Real.exp_pos (-c₂)])
  obtain ⟨ρ, hρ0, hρ1, g, hg, hg1, hglb, hdrift⟩ := exists_potential hc₁ hc₂ hp0 hp1
  have hg0 (x : ℕ) : 0 ≤ g x :=
    (by positivity : (0 : ℝ) ≤ 1 / 2 * Real.exp (-(c₂ / 2 * x))).trans (hglb x)
  have hlam : 0 < -Real.log ρ := neg_pos.mpr (Real.log_neg hρ0 hρ1)
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  -- the constant `c₅`; `D` absorbs a negative `log_{c₁} (c₄ log q)`
  set D := max 0 (-Real.logb c₁ (c₄ * Real.log 2)) with hD
  have hD0 : 0 ≤ D := le_max_left _ _
  refine ⟨(1 + c₂ / 2 * c₄ + c₆) / (-Real.log ρ) + D / Real.log 2, ?_, ?_⟩
  · have : 0 < 1 + c₂ / 2 * c₄ + c₆ := by positivity
    exact add_pos_of_pos_of_nonneg (div_pos this hlam) (div_nonneg hD0 hl2.le)
  intro α _ K X q _ hgrow hzero hq a₀ t ht
  by_cases h₀ : c₄ * Real.log q ≤ X a₀
  · -- started on the target
    rw [hitProb_of_mem K h₀]
    linarith [Real.rpow_nonneg (Nat.cast_nonneg q : (0 : ℝ) ≤ q) (-c₆)]
  -- below the target, so `log q > 0` and `q ≥ 2`
  set L := c₄ * Real.log q with hL
  have hL0 : 0 < L := (Nat.cast_nonneg _).trans_lt (not_le.mp h₀)
  have hlogq : 0 < Real.log q := by
    by_contra h
    nlinarith [not_lt.mp h]
  have hq2 : (2 : ℝ) ≤ q := by
    have h1 : 1 < q := Nat.one_lt_cast.mp ((Real.log_pos_iff (Nat.cast_nonneg q)).mp hlogq)
    have h2 : 2 ≤ q := h1
    exact_mod_cast h2
  have hℓ : Real.log 2 ≤ Real.log q := Real.log_le_log two_pos hq2
  have hqpos : (0 : ℝ) < q := by linarith
  -- the potential `V = g ∘ X` off the target decreases by the factor `ρ` per step
  have hVmin : 0 < 1 / 2 * Real.exp (-(c₂ / 2 * L)) := by positivity
  have key := one_sub_hitProb_le_of_drift K (fun b => L ≤ X b)
    (fun b => if L ≤ X b then 0 else g (X b)) (ρ := ρ)
    (fun b => by split_ifs; exacts [le_rfl, hg0 _]) (fun b hb => if_pos hb) hVmin
    (fun b hb => by
      have hb' : (X b : ℝ) < L := not_le.mp hb
      rw [if_neg hb]
      refine le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num))
        (hglb (X b))
      nlinarith)
    (fun b hb => by
      rw [if_neg hb]
      exact apply_potential_le K X q hc₁ hc₂.le (min_le_left _ _) (min_le_right _ _)
        hρ1.le hg hg0 hg1 hdrift hq hgrow hzero (not_le.mp hb)) t a₀
  rw [if_neg h₀] at key
  -- `ρ^t g(X a₀) / Vmin ≤ 2 ρ^t q^{c₂ c₄ / 2} ≤ q^{-c₆}`
  have hbound : ρ ^ t * g (X a₀) / (1 / 2 * Real.exp (-(c₂ / 2 * L))) ≤
      2 * ρ ^ t * Real.exp (c₂ / 2 * c₄ * Real.log q) := by
    have hu : Real.exp (-(c₂ / 2 * L)) * Real.exp (c₂ / 2 * c₄ * Real.log q) = 1 := by
      rw [← Real.exp_add, ← Real.exp_zero, hL]
      ring_nf
    have hρt : ρ ^ t = 2 * ρ ^ t * Real.exp (c₂ / 2 * c₄ * Real.log q) *
        (1 / 2 * Real.exp (-(c₂ / 2 * L))) := by
      rw [show 2 * ρ ^ t * Real.exp (c₂ / 2 * c₄ * Real.log q) *
          (1 / 2 * Real.exp (-(c₂ / 2 * L))) = ρ ^ t * (Real.exp (-(c₂ / 2 * L)) *
          Real.exp (c₂ / 2 * c₄ * Real.log q)) by ring, hu, mul_one]
    rw [div_le_iff₀ hVmin, ← hρt]
    exact mul_le_of_le_one_right (pow_nonneg hρ0.le t) (hg1 _)
  have hlogb : Real.logb c₁ (c₄ * Real.log 2) ≤ Real.logb c₁ (c₄ * Real.log q) :=
    Real.logb_le_logb_of_le hc₁ (by positivity) (mul_le_mul_of_nonneg_left hℓ hc₄.le)
  have ht' : ((1 + c₂ / 2 * c₄ + c₆) / (-Real.log ρ) + D / Real.log 2) * Real.log q - D ≤ t := by
    have : -D ≤ Real.logb c₁ (c₄ * Real.log 2) := by
      rw [neg_le]
      exact le_max_right _ _
    linarith
  have htail := two_mul_pow_mul_exp_le hρ0 hρ1 hℓ hD0 ht'
  rw [Real.rpow_def_of_pos hqpos, show Real.log q * -c₆ = -(c₆ * Real.log q) by ring]
  linarith

/-- **Hitting-time bound, `O(log q)` form** (Claim 2.9 of Doerr, Goldberg, Minder, Sauerwald,
Scheideler, SPAA 2011, with the term `log_{c₁} (c₄ log q)` absorbed into the constant). Under the
hypotheses of `drift_hitting`, there is `C > 0`, depending on `c₁, c₂, c₃, c₄, c₆` only, such that
`X` reaches `c₄ log q` within any `t ≥ C log q` steps with probability at least `1 - q^{-c₆}`. -/
theorem drift_hitting_log {c₁ c₂ c₃ c₄ c₆ : ℝ} (hc₁ : 1 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hc₄ : 0 < c₄) (hc₆ : 0 < c₆) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type u} [Fintype α] (K : Dynamics.Kernel α) (X : α → ℕ) (q : ℕ),
        (∀ a, X a ≤ q) →
        (∀ a, (X a : ℝ) < c₄ * Real.log q →
          1 - Real.exp (-(c₂ * X a)) ≤ (K a).prob (fun b => min (c₁ * X a) q ≤ X b)) →
        (∀ a, X a = 0 → c₃ ≤ (K a).prob (fun b => 1 ≤ X b)) →
        c₄ * Real.log q ≤ q →
        ∀ (a₀ : α) (t : ℕ), C * Real.log q ≤ t →
          1 - (q : ℝ) ^ (-c₆) ≤ K.hitProb (fun b => c₄ * Real.log q ≤ X b) t a₀ := by
  obtain ⟨c₅, hc₅, h⟩ := drift_hitting hc₁ hc₂ hc₃ hc₄ hc₆
  have hlc : 0 < Real.log c₁ := Real.log_pos hc₁
  refine ⟨c₅ + c₄ / Real.log c₁, by positivity, ?_⟩
  intro α _ K X q hX hgrow hzero hq a₀ t ht
  refine h K X q hX hgrow hzero hq a₀ t (le_trans ?_ ht)
  -- `log_{c₁} (c₄ log q) ≤ c₄ log q / log c₁`, as `log y ≤ y` for `y ≥ 0`
  have hℓ : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have h1 : Real.logb c₁ (c₄ * Real.log q) ≤ c₄ / Real.log c₁ * Real.log q := by
    rw [← Real.log_div_log, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hlc]
    exact Real.log_le_self (by positivity)
  rw [add_mul]
  linarith

end Dynamics.Kernel
