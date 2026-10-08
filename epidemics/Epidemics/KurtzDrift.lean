import Epidemics.KurtzCount

/-! # Kurtz's law of large numbers for SIR: one step of the chain (CRN-2)

For the uniformized SIR chain of `Epidemics.KurtzDefs`:

* the **drift identity**: the expected one-step increment of the scaled counts
  `scaled x = (S, I, R) / N` over a uniform round is exactly `sirField β γ (scaled x)`, the
  Kermack–McKendrick field of EPI-7, times the time step `1 / ((β + γ) N)`, component by
  component (the trend hypothesis (ii) of Wormald 1999, Theorem 5.1, with no error term);
* **bounded increments**: one step moves `scaled x` by at most `1 / N` in sup distance (the
  boundedness hypothesis (i) of Wormald 1999, Theorem 5.1);
* iterating the kernel `chain` is averaging over i.i.d. uniform rounds.

The expectations are `Dynamics.avg` over a uniform `Round`, i.e. the one-step operator
`(chain β γ N).apply` (`Dynamics.Kernel.apply_ofStep`).
-/

namespace Epidemics.Kurtz

open Dynamics KermackMcKendrick

/-- The expected one-step change of `count c / N` over a uniform round, from `sum_count_step`. -/
lemma avg_count_step_sub (β γ : ℕ) {N : ℕ} (x : Config N) (c : Compartment) :
    avg (fun ρ : Round N β γ ↦ (count c (step β γ x ρ) : ℝ) / N - count c x / N)
      = (β * count .infected x * count .susceptible x *
            ((if Compartment.infected = c then 1 else 0) -
              (if Compartment.susceptible = c then 1 else 0))
          + γ * N * count .infected x *
            ((if Compartment.recovered = c then 1 else 0) -
              (if Compartment.infected = c then 1 else 0))) / N / (N * (N * (β + γ))) := by
  unfold avg
  rw [card_round, ← sum_count_step]
  congr 1
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

/-- **Drift of the susceptible fraction**: over a uniform round, the expected increment of `S / N`
is `-(β (S / N) (I / N)) / ((β + γ) N)`, the first component of `sirField β γ (scaled x)` times
the time step `1 / ((β + γ) N)`. -/
theorem drift_susceptible (β γ : ℕ) {N : ℕ} (x : Config N) :
    avg (fun ρ : Round N β γ ↦ (scaled (step β γ x ρ)).1 - (scaled x).1)
      = (sirField β γ (scaled x)).1 / ((β + γ) * N) := by
  rw [show (fun ρ : Round N β γ ↦ (scaled (step β γ x ρ)).1 - (scaled x).1) = fun ρ ↦
      (count .susceptible (step β γ x ρ) : ℝ) / N - count .susceptible x / N from rfl,
    avg_count_step_sub]
  simp only [sirField, scaled, reduceCtorEq, ↓reduceIte]
  generalize (β : ℝ) + γ = B
  ring

/-- **Drift of the infected fraction**: over a uniform round, the expected increment of `I / N` is
`(β (S / N) (I / N) - γ (I / N)) / ((β + γ) N)`, the second component of `sirField β γ (scaled x)`
times the time step `1 / ((β + γ) N)`. -/
theorem drift_infected (β γ : ℕ) {N : ℕ} (x : Config N) :
    avg (fun ρ : Round N β γ ↦ (scaled (step β γ x ρ)).2.1 - (scaled x).2.1)
      = (sirField β γ (scaled x)).2.1 / ((β + γ) * N) := by
  rw [show (fun ρ : Round N β γ ↦ (scaled (step β γ x ρ)).2.1 - (scaled x).2.1) = fun ρ ↦
      (count .infected (step β γ x ρ) : ℝ) / N - count .infected x / N from rfl,
    avg_count_step_sub]
  simp only [sirField, scaled, reduceCtorEq, ↓reduceIte]
  generalize (β : ℝ) + γ = B
  rcases eq_or_ne (N : ℝ) 0 with hN | hN
  · simp [hN]
  · linear_combination (-((count .infected x : ℝ) * γ * (N : ℝ)⁻¹ ^ 2 * B⁻¹)) * mul_inv_cancel₀ hN

/-- **Drift of the recovered fraction**: over a uniform round, the expected increment of `R / N` is
`γ (I / N) / ((β + γ) N)`, the third component of `sirField β γ (scaled x)` times the time step
`1 / ((β + γ) N)`. -/
theorem drift_recovered (β γ : ℕ) {N : ℕ} (x : Config N) :
    avg (fun ρ : Round N β γ ↦ (scaled (step β γ x ρ)).2.2 - (scaled x).2.2)
      = (sirField β γ (scaled x)).2.2 / ((β + γ) * N) := by
  rw [show (fun ρ : Round N β γ ↦ (scaled (step β γ x ρ)).2.2 - (scaled x).2.2) = fun ρ ↦
      (count .recovered (step β γ x ρ) : ℝ) / N - count .recovered x / N from rfl,
    avg_count_step_sub]
  simp only [sirField, scaled, reduceCtorEq, ↓reduceIte]
  generalize (β : ℝ) + γ = B
  rcases eq_or_ne (N : ℝ) 0 with hN | hN
  · simp [hN]
  · linear_combination ((count .infected x : ℝ) * γ * (N : ℝ)⁻¹ ^ 2 * B⁻¹) * mul_inv_cancel₀ hN

/-- **Bounded increments**: one step changes the compartment of at most one agent, so it moves the
scaled counts by at most `1 / N` in sup distance. -/
theorem dist_scaled_step_le (β γ : ℕ) {N : ℕ} (x : Config N) (ρ : Round N β γ) :
    dist (scaled (step β γ x ρ)) (scaled x) ≤ 1 / N := by
  have key (c : Compartment) :
      |(count c (step β γ x ρ) : ℝ) / N - count c x / N| ≤ 1 / N := by
    rw [← sub_div, abs_div, Nat.abs_cast]
    exact div_le_div_of_nonneg_right (abs_count_step_sub_le β γ x ρ c) (Nat.cast_nonneg N)
  simp only [scaled, Prod.dist_eq, Real.dist_eq]
  exact max_le (key _) (max_le (key _) (key _))

/-- The `n`-step expectations of the kernel `chain` are averages over `n` i.i.d. uniform rounds,
the state after the rounds `l` being `l.foldl (step β γ) x₀` (`Dynamics.Kernel.iterate_ofStep`). -/
theorem iterate_chain (β γ N : ℕ) [Nonempty (Round N β γ)] (n : ℕ) (f : Config N → ℝ)
    (x₀ : Config N) :
    (chain β γ N).iterate n f x₀
      = expList (Round N β γ) n (fun l ↦ f (l.foldl (step β γ) x₀)) := by
  exact Dynamics.Kernel.iterate_ofStep (step β γ) n f x₀

end Epidemics.Kurtz
