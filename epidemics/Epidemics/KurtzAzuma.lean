import Epidemics.KurtzAzumaAux

/-! # A maximal Azuma–Hoeffding inequality along i.i.d. uniform rounds (CRN-2)

The martingale concentration behind Kurtz's law of large numbers (`Epidemics.Kurtz`), in the
finite-probability layer of `Dynamics`: a process `X_{j+1} = step X_j ρ_j` driven by i.i.d.
uniform rounds `ρ_j : R` (expectations by `Dynamics.expList`), and increments `D (X_j) ρ_j` with
zero conditional mean, `avg (D y) = 0` for every state `y`, and bounded by `c`. Their partial sums
`M_k = incrementSum step D x (l.take k)` form a martingale, and

  `P(∃ k ≤ n, M_k ≥ λ) ≤ exp(-λ² / (2 n c²))`

(K. Azuma, *Weighted sums of certain dependent random variables*, Tôhoku Math. J. 19, 1967;
W. Hoeffding, J. Amer. Statist. Assoc. 58, 1963, Theorem 2 for the independent case), in the
maximal form obtained from Ville's (Doob's) maximal inequality for the exponential supermartingale
`exp(θ M_k - k θ² c² / 2)`.

The state type `σ` is arbitrary (not necessarily finite), so this covers every martingale with
respect to the rounds: take for `σ` the histories `List R`. Mathlib's Azuma–Hoeffding inequality
(`ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF`) is measure-theoretic and not
maximal, and `Dynamics.Concentration` only treats sums of independent coordinates, hence this
statement.
-/

namespace Epidemics.Kurtz

open Dynamics

variable {σ R : Type*} [Fintype R]

/-- The sum `∑_{j < |l|} D (X_j) (l_j)` of the increments `D` along the rounds `l`, for the process
`X_0 = x`, `X_{j+1} = step X_j l_j`. When every `avg (D y)` vanishes,
`k ↦ incrementSum step D x (l.take k)` is a martingale along i.i.d. uniform rounds `l`. -/
noncomputable def incrementSum (step : σ → R → σ) (D : σ → R → ℝ) (x : σ) (l : List R) : ℝ :=
  match l with
  | [] => 0
  | a :: l => D x a + incrementSum step D (step x a) l

omit [Fintype R] in
/-- `incrementSum` of the affine increments `θ D - b` (the exponent of the exponential
supermartingale). -/
lemma incrementSum_mul_sub (step : σ → R → σ) (D : σ → R → ℝ) (θ b : ℝ) (x : σ) (l : List R) :
    incrementSum step (fun y a ↦ θ * D y a - b) x l
      = θ * incrementSum step D x l - l.length * b := by
  induction l generalizing x with
  | nil => simp [incrementSum]
  | cons a l ih =>
    simp only [incrementSum, ih, List.length_cons]
    push_cast
    ring

/-- **Maximal Azuma–Hoeffding inequality** (Azuma 1967; Hoeffding 1963, Theorem 2, for independent
summands). If the increments have zero mean over a uniform round, `avg (D y) = 0`, and are bounded,
`|D y a| ≤ c`, then over `n` i.i.d. uniform rounds the martingale
`M_k = incrementSum step D x (l.take k)` reaches `λ ≥ 0` at some step `k ≤ n` with probability at
most `exp(-λ² / (2 n c²))`. -/
theorem expList_azuma (step : σ → R → σ) (D : σ → R → ℝ) {c : ℝ}
    (hmean : ∀ y, avg (D y) = 0) (hbound : ∀ y a, |D y a| ≤ c) (x : σ) (n : ℕ) {lam : ℝ}
    (hlam : 0 ≤ lam) :
    expList R n (fun l ↦ if ∃ k ≤ n, lam ≤ incrementSum step D x (l.take k) then 1 else 0)
      ≤ Real.exp (-(lam ^ 2 / (2 * n * c ^ 2))) := by
  rcases isEmpty_or_nonempty R with hR | hR
  · cases n with
    | zero =>
      simp only [expList_zero, CharP.cast_eq_zero, mul_zero, zero_mul, div_zero, neg_zero,
        Real.exp_zero]
      split_ifs <;> norm_num
    | succ n =>
      rw [expList_succ]
      simp only [avg, Finset.univ_eq_empty, Finset.sum_empty, zero_div]
      positivity
  by_cases hnc : (n : ℝ) * c ^ 2 = 0
  · have h0 : lam ^ 2 / (2 * n * c ^ 2) = 0 := by rw [mul_assoc, hnc, mul_zero, div_zero]
    rw [h0, neg_zero, Real.exp_zero]
    exact expList_le_one fun l ↦ by split_ifs <;> norm_num
  have hK : 0 < (n : ℝ) * c ^ 2 :=
    lt_of_le_of_ne (by positivity) (Ne.symm hnc)
  obtain ⟨K, hKdef⟩ : ∃ K, K = (n : ℝ) * c ^ 2 := ⟨_, rfl⟩
  rw [← hKdef] at hK
  have h2K : 2 * (n : ℝ) * c ^ 2 = 2 * K := by rw [hKdef]; ring
  rw [h2K]
  have hθ : 0 ≤ lam / K := div_nonneg hlam hK.le
  have hE (y : σ) :
      avg (fun a ↦ Real.exp (lam / K * D y a - (lam / K) ^ 2 * c ^ 2 / 2)) ≤ 1 := by
    have h := avg_exp_mul_le (hmean y) (hbound y) (lam / K)
    have hsplit (a : R) : Real.exp (lam / K * D y a - (lam / K) ^ 2 * c ^ 2 / 2)
        = Real.exp (-((lam / K) ^ 2 * c ^ 2 / 2)) * Real.exp (lam / K * D y a) := by
      rw [← Real.exp_add]
      ring_nf
    simp_rw [hsplit]
    rw [avg_const_mul]
    calc Real.exp (-((lam / K) ^ 2 * c ^ 2 / 2)) * avg (fun a ↦ Real.exp (lam / K * D y a))
        ≤ Real.exp (-((lam / K) ^ 2 * c ^ 2 / 2)) * Real.exp ((lam / K) ^ 2 * c ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hV := expList_ville step (fun y a ↦ lam / K * D y a - (lam / K) ^ 2 * c ^ 2 / 2)
    (incrementSum step fun y a ↦ lam / K * D y a - (lam / K) ^ 2 * c ^ 2 / 2)
    (fun _ ↦ rfl) (fun _ _ _ ↦ rfl) hE n x (Real.exp_pos (lam ^ 2 / (2 * K)))
  calc _ ≤ expList R n (fun l ↦ if ∃ k ≤ n, Real.exp (lam ^ 2 / (2 * K))
          ≤ Real.exp (incrementSum step (fun y a ↦ lam / K * D y a - (lam / K) ^ 2 * c ^ 2 / 2)
            x (l.take k)) then 1 else 0) := by
        refine expList_le_expList fun l ↦ ite_one_zero_le_of_imp fun ⟨k, hk, hle⟩ ↦ ⟨k, hk, ?_⟩
        rw [Real.exp_le_exp, incrementSum_mul_sub]
        have hm : ((l.take k).length : ℝ) ≤ n := by
          exact_mod_cast (List.length_take_le k l).trans hk
        have h1 : lam / K * lam ≤ lam / K * incrementSum step D x (l.take k) :=
          mul_le_mul_of_nonneg_left hle hθ
        have h2 : ((l.take k).length : ℝ) * ((lam / K) ^ 2 * c ^ 2 / 2)
            ≤ n * ((lam / K) ^ 2 * c ^ 2 / 2) :=
          mul_le_mul_of_nonneg_right hm (by positivity)
        have h3 : (n : ℝ) * ((lam / K) ^ 2 * c ^ 2 / 2) = lam ^ 2 / (2 * K) := by
          rw [hKdef]
          field_simp
        have h4 : lam / K * lam = 2 * (lam ^ 2 / (2 * K)) := by
          field_simp
        linarith
    _ ≤ 1 / Real.exp (lam ^ 2 / (2 * K)) := hV
    _ = Real.exp (-(lam ^ 2 / (2 * K))) := by rw [Real.exp_neg, one_div]

end Epidemics.Kurtz
