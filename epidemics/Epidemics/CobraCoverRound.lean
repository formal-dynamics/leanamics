import Epidemics.CobraCoverSpectral
import Dynamics.GraphRounds

/-! # One round of BIPS (EPI-4)

Independence of the samples in `Choices G k`, the probability that one BIPS round infects a given
vertex, and the resulting expression for the expected size. These are the one-round inputs of
Lemma 1 and of the moment generating function (computations (3) to (5) and (12)).
-/

namespace Epidemics
open Finset Dynamics

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **Independence over vertices.** A uniform round `ρ : Choices G k` samples the vertices
independently, so an average of a product of one-vertex observables factors. -/
lemma avg_choices_prod {k : ℕ} (f : (u : V) → (Fin k → G.neighborSet u) → ℝ) :
    avg (fun ρ : Choices G k => ∏ u, f u (ρ u)) = ∏ u, avg (f u) := by
  unfold avg
  rw [← Fintype.prod_sum, Fintype.card_pi, Nat.cast_prod, ← Finset.prod_div_distrib]

/-- **Independence over the `k` samples** of one vertex. -/
lemma avg_pow_samples {α : Type*} [Fintype α] (k : ℕ) (g : α → ℝ) :
    avg (fun σ : Fin k → α => ∏ i, g (σ i)) = avg g ^ k := by
  unfold avg
  rw [← Fintype.prod_sum, Fintype.card_pi, Nat.cast_prod]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, div_pow]

omit [DecidableEq V] in
/-- On an `r`-regular graph with `r > 0` every neighbour set is nonempty, so rounds exist. -/
lemma choices_nonempty_of_regular {r k : ℕ} (hreg : G.IsRegularOfDegree r) (hr : 0 < r) :
    Nonempty (Choices G k) := by
  have hd : ∀ v, 0 < G.degree v := fun v => by rw [hreg v]; exact hr
  exact ⟨fun v _ => (nonempty_neighborSet G hd v).some⟩

/-- A one-vertex observable has the same average in the full round as on its own samples. -/
lemma avg_choices_depends {k : ℕ} (u : V) (g : (Fin k → G.neighborSet u) → ℝ)
    (hne : Nonempty (Choices G k)) :
    avg (fun ρ : Choices G k => g (ρ u)) = avg g := by
  have hfib (w : V) : Nonempty (Fin k → G.neighborSet w) := Nonempty.map (fun ρ => ρ w) hne
  let f : (w : V) → (Fin k → G.neighborSet w) → ℝ :=
    fun w σ => if h : w = u then g (h ▸ σ) else 1
  have hprod (ρ : Choices G k) : (∏ w, f w (ρ w)) = g (ρ u) := by
    rw [Finset.prod_eq_single u (fun w _ hw => by simp [f, dif_neg hw]) (by simp)]
    simp [f]
  have hf : f u = g := by
    ext σ
    show (if h : u = u then g (h ▸ σ) else 1) = g σ
    rw [dif_pos rfl]
  rw [show avg (fun ρ : Choices G k => g (ρ u)) =
      avg (fun ρ : Choices G k => ∏ w, f w (ρ w)) by simp_rw [hprod]]
  rw [avg_choices_prod]
  rw [Finset.prod_eq_single u (fun w _ hw => ?_) (fun hu => by simp at hu)]
  · rw [hf]
  · haveI := hfib w
    have hfw : f w = fun _ => 1 := by
      ext σ
      simp [f, dif_neg hw]
    rw [hfw, avg_const]

/-- One neighbour of `u`, drawn uniformly, lies outside `A` with probability `1 - d_A(u) / r`. -/
lemma avg_neighbor_miss {r : ℕ} (hreg : G.IsRegularOfDegree r) (hr : 0 < r) (u : V)
    (A : Finset V) :
    avg (fun w : G.neighborSet u => if (w : V) ∈ A then (0 : ℝ) else 1) =
      1 - ((G.neighborFinset u ∩ A).card : ℝ) / r := by
  rw [avg_neighborSet G u (fun w => if w ∈ A then (0 : ℝ) else 1), hreg u]
  classical
  have hhit : ∑ w ∈ G.neighborFinset u, (if w ∈ A then (1 : ℝ) else 0) =
      ((G.neighborFinset u ∩ A).card : ℝ) := by
    simp
  have hone : ∑ w ∈ G.neighborFinset u, (1 : ℝ) = r := by
    rw [Finset.sum_const, G.card_neighborFinset_eq_degree, hreg u, nsmul_eq_mul, mul_one]
  have hpoint (w) (_ : w ∈ G.neighborFinset u) :
      (if w ∈ A then (0 : ℝ) else 1) = 1 - (if w ∈ A then 1 else 0) := by
    by_cases hw : w ∈ A <;> simp [hw]
  rw [Finset.sum_congr rfl hpoint, Finset.sum_sub_distrib, hone, hhit, sub_div,
    div_self (by exact_mod_cast hr.ne')]

/-- `d_A(u) / r ∈ [0, 1]`. -/
lemma neighbor_frac_mem {r : ℕ} (hreg : G.IsRegularOfDegree r) (hr : 0 < r) (u : V)
    (A : Finset V) :
    0 ≤ ((G.neighborFinset u ∩ A).card : ℝ) / r ∧
      ((G.neighborFinset u ∩ A).card : ℝ) / r ≤ 1 := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hle : (G.neighborFinset u ∩ A).card ≤ r := by
    rw [← hreg u, ← G.card_neighborFinset_eq_degree]
    exact Finset.card_le_card Finset.inter_subset_left
  constructor
  · positivity
  · rw [div_le_one hr0]
    exact_mod_cast hle

/-- `∑_u d_A(u) / r = |A|`. -/
lemma sum_neighbor_frac {r : ℕ} (hreg : G.IsRegularOfDegree r) (hr : 0 < r) (A : Finset V) :
    ∑ u, ((G.neighborFinset u ∩ A).card : ℝ) / r = A.card := by
  rw [← Finset.sum_div, ← Nat.cast_sum, sum_neighborCard_eq hreg, Nat.cast_mul,
    mul_div_cancel_left₀]
  exact_mod_cast hr.ne'

omit [Fintype V] [DecidableRel G.Adj] in
/-- The indicator that `u` is infected is `1` at the source and otherwise depends only on the
samples of `u`: it equals `1` exactly when one of those samples lands in `A`. -/
lemma bips_infect_indicator {k : ℕ} {v u : V} (huv : u ≠ v) (A : Finset V)
    (σ : Fin k → G.neighborSet u) :
    (if u = v ∨ ∃ i, (σ i : V) ∈ A then (1 : ℝ) else 0) =
      if ∃ i, (σ i : V) ∈ A then 1 else 0 := by
  by_cases h : ∃ i, (σ i : V) ∈ A <;> simp [h, huv]

omit [Fintype V] [DecidableRel G.Adj] in
/-- Hitting `A` with at least one of `k` samples is `1` minus the product of the misses. -/
lemma hit_eq_one_sub_prod {k : ℕ} (u : V) (A : Finset V) (σ : Fin k → G.neighborSet u) :
    (if ∃ i, (σ i : V) ∈ A then (1 : ℝ) else 0) =
      1 - ∏ i, if (σ i : V) ∈ A then 0 else 1 := by
  classical
  by_cases h : ∃ i, (σ i : V) ∈ A
  · obtain ⟨i, hi⟩ := h
    have hprod : (∏ j, if (σ j : V) ∈ A then (0 : ℝ) else 1) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (if_pos hi)
    rw [if_pos ⟨i, hi⟩, hprod, sub_zero]
  · rw [if_neg h]
    have hmiss : ∀ j, (σ j : V) ∉ A := by simpa using h
    have hprod : (∏ j, if (σ j : V) ∈ A then (0 : ℝ) else 1) = 1 := by
      refine Finset.prod_eq_one fun j _ => ?_
      simp [hmiss j]
    rw [hprod, sub_self]

/-- Probability that `u` belongs to `bipsStep v A`. It is `1` for the source and
`1 - (1 - d_A(u) / r) ^ k` otherwise. -/
lemma bips_infect_prob {r k : ℕ} (hreg : G.IsRegularOfDegree r) (hr : 0 < r) (v u : V)
    (A : Finset V) :
    avg (fun ρ : Choices G k => if u ∈ bipsStep v A ρ then (1 : ℝ) else 0) =
      if u = v then 1
      else 1 - (1 - ((G.neighborFinset u ∩ A).card : ℝ) / r) ^ k := by
  have hne := choices_nonempty_of_regular hreg hr (k := k)
  classical
  by_cases huv : u = v
  · subst huv
    have hind (ρ : Choices G k) : (if u ∈ bipsStep u A ρ then (1 : ℝ) else 0) = 1 := by
      simp [bipsStep]
    simp_rw [hind]
    haveI := hne
    exact avg_const 1
  · simp only [huv, ite_false]
    have hind (ρ : Choices G k) :
        (if u ∈ bipsStep v A ρ then (1 : ℝ) else 0) =
          if ∃ i, (ρ u i : V) ∈ A then 1 else 0 := by
      simp only [mem_bipsStep, huv, false_or]
    simp_rw [hind]
    have hdep := avg_choices_depends u
      (fun σ : Fin k → G.neighborSet u => if ∃ i, (σ i : V) ∈ A then (1 : ℝ) else 0) hne
    rw [show avg (fun ρ : Choices G k => if ∃ i, (ρ u i : V) ∈ A then (1 : ℝ) else 0) =
        avg (fun σ : Fin k → G.neighborSet u => if ∃ i, (σ i : V) ∈ A then (1 : ℝ) else 0)
        from hdep]
    have hσ (σ : Fin k → G.neighborSet u) :
        (if ∃ i, (σ i : V) ∈ A then (1 : ℝ) else 0) =
          1 - ∏ i, if (σ i : V) ∈ A then 0 else 1 :=
      hit_eq_one_sub_prod u A σ
    haveI : Nonempty (Fin k → G.neighborSet u) := Nonempty.map (fun ρ => ρ u) hne
    simp_rw [hσ]
    rw [avg_sub (fun _ : Fin k → G.neighborSet u => (1 : ℝ))
      (fun σ : Fin k → G.neighborSet u => ∏ i, if (σ i : V) ∈ A then (0 : ℝ) else 1)]
    rw [avg_const]
    have hpow := avg_pow_samples k (fun w : G.neighborSet u => if (w : V) ∈ A then (0 : ℝ) else 1)
    rw [show avg (fun σ : Fin k → G.neighborSet u => ∏ i, if (σ i : V) ∈ A then (0 : ℝ) else 1) =
        (avg (fun w : G.neighborSet u => if (w : V) ∈ A then (0 : ℝ) else 1)) ^ k from hpow]
    rw [avg_neighbor_miss hreg hr u A]

omit [DecidableRel G.Adj] in
/-- `|bipsStep v A ρ| = ∑_u 1_{u ∈ bipsStep v A ρ}`. -/
lemma bipsStep_card_eq_sum {k : ℕ} (v : V) (A : Finset V) (ρ : Choices G k) :
    ((bipsStep v A ρ).card : ℝ) =
      ∑ u, if u ∈ bipsStep v A ρ then (1 : ℝ) else 0 := by
  classical
  rw [Finset.card_eq_sum_ite (Finset.subset_univ _), Nat.cast_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  split_ifs <;> simp

/-- `E|A'| = ∑_u P(u ∈ A')`, with no regularity hypothesis. -/
lemma bips_expected_card {k : ℕ} (v : V) (A : Finset V) :
    avg (fun ρ : Choices G k => ((bipsStep v A ρ).card : ℝ)) =
      ∑ u, avg (fun ρ : Choices G k => if u ∈ bipsStep v A ρ then (1 : ℝ) else 0) := by
  simp_rw [bipsStep_card_eq_sum, avg_sum]

/-- The uniform average on an empty type is zero. -/
lemma avg_eq_zero_of_isEmpty {α : Type*} [Fintype α] [IsEmpty α] (f : α → ℝ) : avg f = 0 := by
  unfold avg
  rw [Finset.univ_eq_empty, Finset.sum_empty, Fintype.card_eq_zero, Nat.cast_zero, div_zero]

/-- `E(e^{-φ B}) = 1 - (1 - e^{-φ}) P(B)` for an event `B` on a nonempty finite space. -/
lemma avg_exp_bernoulli {α : Type*} [Fintype α] [Nonempty α] (φ : ℝ) (p : α → Prop)
    [DecidablePred p] :
    avg (fun a => Real.exp (-φ * if p a then (1 : ℝ) else 0)) =
      1 - (1 - Real.exp (-φ)) * avg (fun a => if p a then 1 else 0) := by
  have hfun (a : α) : Real.exp (-φ * if p a then (1 : ℝ) else 0) =
      1 - (1 - Real.exp (-φ)) * (if p a then 1 else 0) := by
    by_cases hp : p a <;> simp [hp]
  simp_rw [hfun, avg_sub, avg_const_mul, avg_const]

end Epidemics
