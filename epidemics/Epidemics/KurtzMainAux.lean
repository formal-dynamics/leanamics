import Epidemics.KurtzAzuma
import Epidemics.KurtzDrift
import Epidemics.KurtzODE
import Epidemics.KurtzGronwall

/-! # Kurtz's law of large numbers for SIR: the martingale and the good event (CRN-2, helpers)

* `incrementSum` telescopes (`incrementSum_telescope`, `incrementSum_take`);
* the coordinates `coord j` of `ℝ × ℝ × ℝ` and the martingale increments
  `mgIncr β γ j y ρ = Δ coord_j (scaled) - coord_j (F (scaled y)) / ((β + γ) N)`, centred by the
  drift identity and bounded by `2 / N`;
* `incrementSum_mgIncr`: along the rounds, the partial sums of `mgIncr β γ j` are the coordinates
  of `X_k - X_0 - h ∑_{i<k} F (X_i)`, `X_i` the scaled state after `i` rounds and
  `h = 1 / ((β + γ) N)`;
* `close_of_good`: on the event where the three martingales stay below `δ`, discrete stability
  (`norm_sub_le_of_euler`) keeps the chain within
  `(dist (scaled x₀) x(0) + δ + T (2β + γ) / N) · exp((2β + γ) T)` of the solution.
-/

namespace Epidemics.Kurtz

open Dynamics KermackMcKendrick Finset Real

/-! ### Telescoping `incrementSum` -/

section Telescope

variable {σ R : Type*}

/-- Increments of the form `φ (step y a) - φ y - ψ y` telescope. -/
lemma incrementSum_telescope (step : σ → R → σ) (φ ψ : σ → ℝ) (x : σ) (l : List R) :
    incrementSum step (fun y a ↦ φ (step y a) - φ y - ψ y) x l
      = φ (l.foldl step x) - φ x - incrementSum step (fun y _ ↦ ψ y) x l := by
  induction l generalizing x with
  | nil => simp [incrementSum]
  | cons a l ih =>
    simp only [incrementSum, ih, List.foldl_cons]
    ring

/-- The sum of a state function along the first `k` rounds. -/
lemma incrementSum_take (step : σ → R → σ) (ψ : σ → ℝ) (x : σ) (l : List R) (k : ℕ)
    (hk : k ≤ l.length) :
    incrementSum step (fun y _ ↦ ψ y) x (l.take k)
      = ∑ j ∈ range k, ψ ((l.take j).foldl step x) := by
  induction l generalizing x k with
  | nil =>
    simp only [List.length_nil, Nat.le_zero] at hk
    subst hk
    simp [incrementSum]
  | cons a l ih =>
    cases k with
    | zero => simp [incrementSum]
    | succ k =>
      rw [List.take_succ_cons, sum_range_succ']
      simp only [incrementSum, List.take_succ_cons, List.foldl_cons, List.take_zero,
        List.foldl_nil]
      rw [ih (step x a) k (by simpa using hk)]
      ring

/-- Negated increments. -/
lemma incrementSum_neg (step : σ → R → σ) (D : σ → R → ℝ) (x : σ) (l : List R) :
    incrementSum step (fun y a ↦ -D y a) x l = -incrementSum step D x l := by
  induction l generalizing x with
  | nil => simp [incrementSum]
  | cons a l ih =>
    simp only [incrementSum, ih]
    ring

end Telescope

/-! ### Coordinates -/

/-- The three coordinate functionals of `ℝ × ℝ × ℝ`. -/
def coord : Fin 3 → (ℝ × ℝ × ℝ) →ₗ[ℝ] ℝ :=
  ![LinearMap.fst ℝ ℝ (ℝ × ℝ), LinearMap.fst ℝ ℝ ℝ ∘ₗ LinearMap.snd ℝ ℝ (ℝ × ℝ),
    LinearMap.snd ℝ ℝ ℝ ∘ₗ LinearMap.snd ℝ ℝ (ℝ × ℝ)]

lemma coord_zero (p : ℝ × ℝ × ℝ) : coord 0 p = p.1 := rfl

lemma coord_one (p : ℝ × ℝ × ℝ) : coord 1 p = p.2.1 := rfl

lemma coord_two (p : ℝ × ℝ × ℝ) : coord 2 p = p.2.2 := rfl

lemma abs_coord_le_norm (j : Fin 3) (p : ℝ × ℝ × ℝ) : |coord j p| ≤ ‖p‖ := by
  fin_cases j
  · exact abs_fst_le_norm p
  · exact abs_snd_fst_le_norm p
  · exact abs_snd_snd_le_norm p

lemma norm_le_of_forall_coord {p : ℝ × ℝ × ℝ} {δ : ℝ} (h : ∀ j, |coord j p| ≤ δ) : ‖p‖ ≤ δ :=
  norm_le_of_abs_le (h 0) (h 1) (h 2)

/-! ### The martingale increments -/

variable {β γ N : ℕ}

/-- Every count is at most `N`. -/
lemma count_le (c : Compartment) (x : Config N) : count c x ≤ N :=
  (card_filter_le _ _).trans (by simp)

/-- The scaled counts lie in the unit ball (sup norm). -/
lemma norm_scaled_le_one (x : Config N) : ‖scaled x‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [scaled]
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have key (c : Compartment) : |(count c x : ℝ) / N| ≤ 1 := by
    rw [abs_of_nonneg (by positivity), div_le_one hN']
    exact_mod_cast count_le c x
  exact norm_le_of_abs_le (key _) (key _) (key _)

/-- The rounds form a nonempty type when `N > 0` and `β > 0`. -/
lemma round_nonempty (hN : 0 < N) (hβ : 0 < β) : Nonempty (Round N β γ) :=
  ⟨(⟨0, hN⟩, ⟨0, hN⟩, .inl ⟨0, hβ⟩)⟩

/-- The martingale increment of the coordinate `j`: the change of `coord j (scaled ·)` in one
step minus its conditional mean `coord j (F (scaled y)) / ((β + γ) N)`. -/
noncomputable def mgIncr (β γ : ℕ) {N : ℕ} (j : Fin 3) (y : Config N) (ρ : Round N β γ) : ℝ :=
  coord j (scaled (step β γ y ρ)) - coord j (scaled y)
    - ((β + γ) * N : ℝ)⁻¹ * coord j (sirField β γ (scaled y))

/-- The increments `mgIncr` are centred (the drift identity). -/
lemma avg_mgIncr (hN : 0 < N) (hβ : 0 < β) (j : Fin 3) (y : Config N) :
    avg (mgIncr β γ j y) = 0 := by
  haveI := round_nonempty (γ := γ) hN hβ
  have e : avg (mgIncr β γ j y)
      = avg (fun ρ : Round N β γ ↦ coord j (scaled (step β γ y ρ)) - coord j (scaled y))
        - ((β + γ) * N : ℝ)⁻¹ * coord j (sirField β γ (scaled y)) := by
    rw [← avg_const (α := Round N β γ) (((β + γ) * N : ℝ)⁻¹ * coord j (sirField β γ (scaled y))),
      ← avg_sub]
    rfl
  rw [e]
  fin_cases j
  · simp only [Fin.zero_eta, coord_zero]
    rw [drift_susceptible, div_eq_inv_mul, sub_self]
  · simp only [Fin.mk_one, coord_one]
    rw [drift_infected, div_eq_inv_mul, sub_self]
  · simp only [Fin.reduceFinMk, coord_two]
    rw [drift_recovered, div_eq_inv_mul, sub_self]

/-- The increments `mgIncr` are bounded by `2 / N`. -/
lemma abs_mgIncr_le (hN : 0 < N) (hβ : 0 < β) (j : Fin 3) (y : Config N) (ρ : Round N β γ) :
    |mgIncr β γ j y ρ| ≤ 2 / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hB : (0 : ℝ) < β + γ := by positivity
  have h1 : |coord j (scaled (step β γ y ρ)) - coord j (scaled y)| ≤ 1 / N := by
    rw [← map_sub]
    exact (abs_coord_le_norm j _).trans ((dist_eq_norm _ _).symm.le.trans
      (dist_scaled_step_le β γ y ρ))
  have h2 : |((β + γ) * N : ℝ)⁻¹ * coord j (sirField β γ (scaled y))| ≤ 1 / N := by
    rw [abs_mul, abs_of_pos (by positivity)]
    calc ((β + γ) * N : ℝ)⁻¹ * |coord j (sirField β γ (scaled y))|
        ≤ ((β + γ) * N : ℝ)⁻¹ * (β + γ) := by
          gcongr
          exact (abs_coord_le_norm j _).trans
            (norm_sirField_le (Nat.cast_nonneg _) (Nat.cast_nonneg _) (norm_scaled_le_one y))
      _ = 1 / N := by field_simp
  calc |mgIncr β γ j y ρ|
      ≤ |coord j (scaled (step β γ y ρ)) - coord j (scaled y)|
        + |((β + γ) * N : ℝ)⁻¹ * coord j (sirField β γ (scaled y))| := abs_sub _ _
    _ ≤ 1 / N + 1 / N := add_le_add h1 h2
    _ = 2 / N := by ring

/-- Along the rounds `l`, the partial sums of `mgIncr β γ j` are the coordinates of
`X_k - X_0 - h ∑_{i<k} F (X_i)`. -/
lemma incrementSum_mgIncr (j : Fin 3) (x₀ : Config N) (l : List (Round N β γ)) (k : ℕ)
    (hk : k ≤ l.length) :
    incrementSum (step β γ) (mgIncr β γ j) x₀ (l.take k)
      = coord j (scaled ((l.take k).foldl (step β γ) x₀) - scaled x₀
          - ((β + γ) * N : ℝ)⁻¹ • ∑ i ∈ range k,
              sirField β γ (scaled ((l.take i).foldl (step β γ) x₀))) := by
  have h := incrementSum_telescope (step β γ) (fun y ↦ coord j (scaled y))
    (fun y ↦ ((β + γ) * N : ℝ)⁻¹ * coord j (sirField β γ (scaled y))) x₀ (l.take k)
  rw [incrementSum_take _ _ _ l k hk] at h
  rw [show mgIncr β γ j = fun y a ↦ coord j (scaled (step β γ y a)) - coord j (scaled y)
      - ((β + γ) * N : ℝ)⁻¹ * coord j (sirField β γ (scaled y)) from rfl, h,
    map_sub, map_sub, map_smul, map_sum, smul_eq_mul, mul_sum]

/-! ### The good event -/

/-- **Closeness on the good event.** If, along rounds `l` of length `n ≤ T (β + γ) N`, the three
coordinate martingales stay within `δ` at every step `k ≤ n`, then at every step `k ≤ n` the chain
is within `(dist (scaled x₀) x(0) + δ + T (2β + γ) / N) · exp((2β + γ) T)` of the solution `x`
at time `k / ((β + γ) N)`. -/
lemma close_of_good (hβ : 0 < β) (hγ : 0 < γ) (hN : 0 < N) {x₀ : Config N} {s i r : ℝ → ℝ}
    (hx : IsIntegralCurveOn (fun t ↦ (s t, i t, r t)) (fun _ ↦ sirField β γ) (Set.Ici 0))
    (hs : 0 ≤ s 0) (hi : 0 ≤ i 0) (hr : 0 ≤ r 0) (hsum : s 0 + i 0 + r 0 = 1)
    {T δ : ℝ} (hδ : 0 ≤ δ) (l : List (Round N β γ)) (hl : (l.length : ℝ) ≤ T * (β + γ) * N)
    (hgood : ∀ j : Fin 3, ∀ k ≤ l.length,
      |incrementSum (step β γ) (mgIncr β γ j) x₀ (l.take k)| ≤ δ) :
    ∀ k ≤ l.length, dist (scaled ((l.take k).foldl (step β γ) x₀))
        (s (k / ((β + γ) * N)), i (k / ((β + γ) * N)), r (k / ((β + γ) * N)))
      ≤ (dist (scaled x₀) (s 0, i 0, r 0) + δ + T * (2 * β + γ) / N)
          * exp ((2 * β + γ) * T) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hβ' : (0 : ℝ) < β := by exact_mod_cast hβ
  have hγ' : (0 : ℝ) < γ := by exact_mod_cast hγ
  have hB : (0 : ℝ) < β + γ := by positivity
  have hBN : (0 : ℝ) < (β + γ) * N := by positivity
  set n := l.length with hn
  set h : ℝ := ((β + γ) * N : ℝ)⁻¹ with hh
  have hh0 : 0 ≤ h := by positivity
  set X : ℕ → ℝ × ℝ × ℝ := fun k ↦ scaled ((l.take k).foldl (step β γ) x₀) with hX
  set y : ℕ → ℝ × ℝ × ℝ := fun k ↦
    (s (k / ((β + γ) * N)), i (k / ((β + γ) * N)), r (k / ((β + γ) * N))) with hy
  have hT : 0 ≤ T := by
    by_contra hT
    have : T * (β + γ) * N < 0 := by
      have := mul_neg_of_neg_of_pos (not_le.mp hT) hB
      exact mul_neg_of_neg_of_pos this hN'
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hball (t : ℝ) (ht : 0 ≤ t) : ‖(s t, i t, r t)‖ ≤ 1 :=
    sir_norm_le_one hx hγ' hs hi hr hsum ht
  have hyball (k : ℕ) : ‖y k‖ ≤ 1 := hball _ (by positivity)
  have hX0 : X 0 = scaled x₀ := rfl
  have hy0 : y 0 = (s 0, i 0, r 0) := by simp [hy]
  -- the three hypotheses of discrete stability
  have hLip : ∀ j < n, ‖sirField β γ (X j) - sirField β γ (y j)‖ ≤ (2 * β + γ) * ‖X j - y j‖ :=
    fun j _ ↦ norm_sirField_sub_le hβ'.le hγ'.le (norm_scaled_le_one _) (hyball j)
  have hXm : ∀ k ≤ n, ‖X k - X 0 - h • ∑ j ∈ range k, sirField β γ (X j)‖ ≤ δ := by
    intro k hk
    refine norm_le_of_forall_coord fun j ↦ ?_
    have hj := hgood j k hk
    rw [incrementSum_mgIncr j x₀ l k hk] at hj
    exact hj
  have hyE : ∀ j < n, ‖y (j + 1) - y j - h • sirField β γ (y j)‖
      ≤ (2 * β + γ) * (β + γ) * h ^ 2 := by
    intro j _
    have ht : (0 : ℝ) ≤ j / ((β + γ) * N) := by positivity
    have hsucc : (((j + 1 : ℕ) : ℝ) / ((β + γ) * N)) = j / ((β + γ) * N) + h := by
      rw [Nat.cast_succ, add_div, hh, one_div]
    have := sir_euler_le hx hβ'.le hγ'.le ht hh0 fun u hu ↦ hball u (ht.trans hu.1)
    simp only [hy, hsucc]
    exact this
  have hst := norm_sub_le_of_euler (by positivity) hh0 hδ (by positivity) hLip hXm hyE
  intro k hk
  rw [dist_eq_norm]
  have hk' : (k : ℝ) ≤ n := by exact_mod_cast hk
  have hhk : h * (2 * β + γ) * k ≤ (2 * β + γ) * T := by
    have : h * k ≤ T := by
      rw [hh, inv_mul_le_iff₀ hBN]
      nlinarith
    nlinarith
  have hnη : (n : ℝ) * ((2 * β + γ) * (β + γ) * h ^ 2) ≤ T * (2 * β + γ) / N := by
    have e : (n : ℝ) * ((2 * β + γ) * (β + γ) * h ^ 2)
        = (2 * β + γ) / N * (n * h) := by
      rw [hh]
      field_simp
    have hnh : (n : ℝ) * h ≤ T := by
      rw [hh, mul_inv_le_iff₀ hBN]
      linarith
    rw [e, div_mul_eq_mul_div, mul_comm T]
    gcongr
  calc ‖X k - y k‖
      ≤ (‖X 0 - y 0‖ + δ + n * ((2 * β + γ) * (β + γ) * h ^ 2)) * exp (h * (2 * β + γ) * k) :=
        hst k hk
    _ ≤ (dist (scaled x₀) (s 0, i 0, r 0) + δ + T * (2 * β + γ) / N)
          * exp ((2 * β + γ) * T) := by
        rw [hX0, hy0, ← dist_eq_norm]
        gcongr

end Epidemics.Kurtz
