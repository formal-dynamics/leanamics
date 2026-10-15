import Dynamics.Uniform

/-!
# A maximal Azuma–Hoeffding inequality along i.i.d. uniform rounds

Martingale concentration in the finite-probability layer: a process `X_{j+1} = step X_j ρ_j`
driven by i.i.d. uniform rounds `ρ_j : R` (expectations by `expList`), and increments
`D (X_j) ρ_j` with zero conditional mean, `avg (D y) = 0` for every state `y`, and bounded by `c`.
Their partial sums `M_k = incrementSum step D x (l.take k)` form a martingale, and

  `P(∃ k ≤ n, M_k ≥ λ) ≤ exp(-λ² / (2 n c²))`

(K. Azuma, *Weighted sums of certain dependent random variables*, Tôhoku Math. J. 19, 1967;
W. Hoeffding, J. Amer. Statist. Assoc. 58, 1963, Theorem 2 for the independent case), in the
maximal form obtained from Ville's (Doob's) maximal inequality for the exponential supermartingale
`exp(θ M_k - k θ² c² / 2)`.

* `incrementSum`: the partial sums, linear and monotone in the increments (`incrementSum_add`,
  `incrementSum_sub`, `incrementSum_const_mul`, `incrementSum_mono`), with `incrementSum_mul_sub`,
  `incrementSum_neg`, `incrementSum_telescope` (increments `φ (step y a) - φ y - ψ y` telescope)
  and `incrementSum_take` (the sum of a state function along the first `k` rounds);
* `avg_exp_mul_le`: **Hoeffding's lemma** for a centred variable bounded by `c` under a uniform
  draw, `avg (exp (θ f)) ≤ exp (θ² c² / 2)` (convexity of `exp`, then
  `Real.cosh_le_exp_half_sq`);
* `expList_ville`: **Ville's maximal inequality** for a multiplicative process
  `exp (M x l)` with `M x (a :: l) = E x a + M (step x a) l` and `avg (exp (E y ·)) ≤ 1` (a
  nonnegative supermartingale started at `1`): it reaches `μ > 0` within `n` rounds with
  probability at most `1 / μ`. Proved by induction on `n`, peeling off the first round;
* `expList_azuma`: the maximal Azuma–Hoeffding inequality.

The state type `σ` is arbitrary (not necessarily finite), so this covers every martingale with
respect to the rounds: take for `σ` the histories `List R`.

**Why not Mathlib.** Mathlib's Azuma–Hoeffding inequality
(`ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF`) is measure-theoretic (a
filtration, conditional sub-Gaussian MGFs) and bounds `P(M_n ≥ λ)` at the final time only, not
`P(∃ k ≤ n, M_k ≥ λ)`; its Hoeffding lemma (`hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`)
is stated for integrals. Using them would need a bridge from `avg`/`expList` to measures on the
path space, which this library avoids. `Dynamics.Concentration` and `Dynamics.Chernoff` only
treat sums of independent coordinates (with Hoeffding's lemma for Bernoulli variables,
`one_sub_add_mul_exp_le`), hence the elementary proofs here.
-/

namespace Dynamics

open Real

/-- An indicator is monotone in its event. -/
lemma ite_one_zero_le_of_imp {P Q : Prop} [Decidable P] [Decidable Q] (h : P → Q) :
    (if P then (1 : ℝ) else 0) ≤ if Q then 1 else 0 := by
  by_cases hP : P
  · rw [if_pos hP, if_pos (h hP)]
  · rw [if_neg hP]
    split_ifs <;> norm_num

/-! ### Sums of increments along the rounds -/

section IncrementSum

variable {σ R : Type*}

/-- The sum `∑_{j < |l|} D (X_j) (l_j)` of the increments `D` along the rounds `l`, for the process
`X_0 = x`, `X_{j+1} = step X_j l_j`. When every `avg (D y)` vanishes,
`k ↦ incrementSum step D x (l.take k)` is a martingale along i.i.d. uniform rounds `l`. -/
noncomputable def incrementSum (step : σ → R → σ) (D : σ → R → ℝ) (x : σ) (l : List R) : ℝ :=
  match l with
  | [] => 0
  | a :: l => D x a + incrementSum step D (step x a) l

@[simp] lemma incrementSum_nil (step : σ → R → σ) (D : σ → R → ℝ) (x : σ) :
    incrementSum step D x [] = 0 := rfl

@[simp] lemma incrementSum_cons (step : σ → R → σ) (D : σ → R → ℝ) (x : σ) (a : R) (l : List R) :
    incrementSum step D x (a :: l) = D x a + incrementSum step D (step x a) l := rfl

/-- Sums of increments are additive in the increments. -/
lemma incrementSum_add (step : σ → R → σ) (D E : σ → R → ℝ) (x : σ) (l : List R) :
    incrementSum step (fun y a => D y a + E y a) x l
      = incrementSum step D x l + incrementSum step E x l := by
  induction l generalizing x with
  | nil => simp
  | cons a l ih => simp only [incrementSum_cons, ih]; ring

/-- Sums of differences of increments. -/
lemma incrementSum_sub (step : σ → R → σ) (D E : σ → R → ℝ) (x : σ) (l : List R) :
    incrementSum step (fun y a => D y a - E y a) x l
      = incrementSum step D x l - incrementSum step E x l := by
  induction l generalizing x with
  | nil => simp
  | cons a l ih => simp only [incrementSum_cons, ih]; ring

/-- Scaling the increments scales their sum. -/
lemma incrementSum_const_mul (step : σ → R → σ) (c : ℝ) (D : σ → R → ℝ) (x : σ) (l : List R) :
    incrementSum step (fun y a => c * D y a) x l = c * incrementSum step D x l := by
  induction l generalizing x with
  | nil => simp
  | cons a l ih => simp only [incrementSum_cons, ih]; ring

/-- Larger increments have a larger sum. -/
lemma incrementSum_mono (step : σ → R → σ) {D E : σ → R → ℝ} (h : ∀ y a, D y a ≤ E y a)
    (x : σ) (l : List R) : incrementSum step D x l ≤ incrementSum step E x l := by
  induction l generalizing x with
  | nil => simp
  | cons a l ih => simp only [incrementSum_cons]; exact add_le_add (h x a) (ih _)

@[simp] lemma incrementSum_zero (step : σ → R → σ) (x : σ) (l : List R) :
    incrementSum step (fun _ _ => 0) x l = 0 := by
  induction l generalizing x with
  | nil => simp
  | cons a l ih => simp [ih]

/-- Nonnegative increments have a nonnegative sum. -/
lemma incrementSum_nonneg (step : σ → R → σ) {D : σ → R → ℝ} (h : ∀ y a, 0 ≤ D y a) (x : σ)
    (l : List R) : 0 ≤ incrementSum step D x l := by
  simpa using incrementSum_mono step (D := fun _ _ => 0) h x l

/-- `incrementSum` of the affine increments `θ D - b` (the exponent of the exponential
supermartingale). -/
lemma incrementSum_mul_sub (step : σ → R → σ) (D : σ → R → ℝ) (θ b : ℝ) (x : σ) (l : List R) :
    incrementSum step (fun y a => θ * D y a - b) x l
      = θ * incrementSum step D x l - l.length * b := by
  induction l generalizing x with
  | nil => simp [incrementSum]
  | cons a l ih =>
    simp only [incrementSum, ih, List.length_cons]
    push_cast
    ring

/-- Negated increments. -/
lemma incrementSum_neg (step : σ → R → σ) (D : σ → R → ℝ) (x : σ) (l : List R) :
    incrementSum step (fun y a => -D y a) x l = -incrementSum step D x l := by
  induction l generalizing x with
  | nil => simp [incrementSum]
  | cons a l ih =>
    simp only [incrementSum, ih]
    ring

/-- Increments of the form `φ (step y a) - φ y - ψ y` telescope. -/
lemma incrementSum_telescope (step : σ → R → σ) (φ ψ : σ → ℝ) (x : σ) (l : List R) :
    incrementSum step (fun y a => φ (step y a) - φ y - ψ y) x l
      = φ (l.foldl step x) - φ x - incrementSum step (fun y _ => ψ y) x l := by
  induction l generalizing x with
  | nil => simp [incrementSum]
  | cons a l ih =>
    simp only [incrementSum, ih, List.foldl_cons]
    ring

/-- The sum of a state function along the first `k` rounds. -/
lemma incrementSum_take (step : σ → R → σ) (ψ : σ → ℝ) (x : σ) (l : List R) (k : ℕ)
    (hk : k ≤ l.length) :
    incrementSum step (fun y _ => ψ y) x (l.take k)
      = ∑ j ∈ Finset.range k, ψ ((l.take j).foldl step x) := by
  induction l generalizing x k with
  | nil =>
    simp only [List.length_nil, Nat.le_zero] at hk
    subst hk
    simp
  | cons a l ih =>
    cases k with
    | zero => simp
    | succ k =>
      rw [List.take_succ_cons, Finset.sum_range_succ']
      simp only [incrementSum, List.take_succ_cons, List.foldl_cons, List.take_zero,
        List.foldl_nil]
      rw [ih (step x a) k (by simpa using hk)]
      ring

end IncrementSum

/-! ### Hoeffding's lemma, Ville's inequality and Azuma–Hoeffding -/

variable {σ R : Type*} [Fintype R]

/-- **Hoeffding's lemma** (Hoeffding 1963, (4.16)) for a uniform draw: if `f` has mean zero and
`|f| ≤ c`, then `avg (exp (θ f)) ≤ exp (θ² c² / 2)`. -/
lemma avg_exp_mul_le {f : R → ℝ} {c : ℝ} (hmean : avg f = 0) (hb : ∀ a, |f a| ≤ c) (θ : ℝ) :
    avg (fun a => exp (θ * f a)) ≤ exp (θ ^ 2 * c ^ 2 / 2) := by
  rcases isEmpty_or_nonempty R with hR | hR
  · simp only [avg, Finset.univ_eq_empty, Finset.sum_empty, zero_div]
    positivity
  have hc : 0 ≤ c := (abs_nonneg _).trans (hb (Classical.arbitrary R))
  rcases hc.eq_or_lt with rfl | hc
  · have h0 (a : R) : f a = 0 := abs_nonpos_iff.mp (hb a)
    simp [h0, avg_const]
  -- convexity of `exp` on the segment `[-θc, θc]`
  have key (a : R) : exp (θ * f a)
      ≤ (exp (-(θ * c)) + exp (θ * c)) / 2 + (exp (θ * c) - exp (-(θ * c))) / (2 * c) * f a := by
    have hfa := abs_le.mp (hb a)
    have h1 : 0 ≤ (c - f a) / (2 * c) := div_nonneg (by linarith) (by positivity)
    have h2 : 0 ≤ (c + f a) / (2 * c) := div_nonneg (by linarith) (by positivity)
    have h12 : (c - f a) / (2 * c) + (c + f a) / (2 * c) = 1 := by field_simp; ring
    have hconv := convexOn_exp.2 (Set.mem_univ (-(θ * c))) (Set.mem_univ (θ * c)) h1 h2 h12
    simp only [smul_eq_mul] at hconv
    have hl : (c - f a) / (2 * c) * -(θ * c) + (c + f a) / (2 * c) * (θ * c) = θ * f a := by
      field_simp
      ring
    have hr : (c - f a) / (2 * c) * exp (-(θ * c)) + (c + f a) / (2 * c) * exp (θ * c)
        = (exp (-(θ * c)) + exp (θ * c)) / 2
          + (exp (θ * c) - exp (-(θ * c))) / (2 * c) * f a := by
      field_simp
      ring
    rw [hl, hr] at hconv
    exact hconv
  calc avg (fun a => exp (θ * f a))
      ≤ avg (fun a => (exp (-(θ * c)) + exp (θ * c)) / 2
          + (exp (θ * c) - exp (-(θ * c))) / (2 * c) * f a) := avg_le_avg key
    _ = cosh (θ * c) := by
        rw [avg_add, avg_const, avg_const_mul, hmean, mul_zero, add_zero, cosh_eq, add_comm]
    _ ≤ exp ((θ * c) ^ 2 / 2) := cosh_le_exp_half_sq _
    _ = exp (θ ^ 2 * c ^ 2 / 2) := by ring_nf

/-- **Ville's maximal inequality** along i.i.d. uniform rounds (finite horizon). Let
`M x (a :: l) = E x a + M (step x a) l`, `M x [] = 0`, with `avg (exp (E y ·)) ≤ 1` for every
`y`, so that `k ↦ exp (M x (l.take k))` is a nonnegative supermartingale started at `1`. Then it
reaches `μ > 0` at some step `k ≤ n` with probability at most `1 / μ`. -/
lemma expList_ville (step : σ → R → σ) (E : σ → R → ℝ) (M : σ → List R → ℝ)
    (hM0 : ∀ x, M x [] = 0) (hM : ∀ x a l, M x (a :: l) = E x a + M (step x a) l)
    (hE : ∀ y, avg (fun a => exp (E y a)) ≤ 1) (n : ℕ) :
    ∀ (x : σ) {μ : ℝ}, 0 < μ →
      expList R n (fun l => if ∃ k ≤ n, μ ≤ exp (M x (l.take k)) then 1 else 0) ≤ 1 / μ := by
  induction n with
  | zero =>
    intro x μ hμ
    simp only [expList_zero]
    split_ifs with h
    · obtain ⟨k, -, hk⟩ := h
      rw [List.take_nil, hM0, exp_zero] at hk
      rw [le_div_iff₀ hμ]
      linarith
    · positivity
  | succ n ih =>
    intro x μ hμ
    rcases le_or_gt μ 1 with hμ1 | hμ1
    · calc _ ≤ (1 : ℝ) := expList_le_one fun l => by split_ifs <;> norm_num
        _ ≤ 1 / μ := by rw [le_div_iff₀ hμ]; linarith
    rw [expList_succ]
    have hpt (a : R) : expList R n (fun l =>
          if ∃ k ≤ n + 1, μ ≤ exp (M x ((a :: l).take k)) then (1 : ℝ) else 0)
        ≤ exp (E x a) / μ := by
      have hμ' : 0 < μ / exp (E x a) := by positivity
      calc _ ≤ expList R n (fun l =>
              if ∃ k ≤ n, μ / exp (E x a) ≤ exp (M (step x a) (l.take k)) then (1 : ℝ) else 0) :=
            expList_le_expList fun l => ite_one_zero_le_of_imp fun ⟨k, hk, hle⟩ => by
              rcases k with _ | k
              · rw [List.take_zero, hM0, exp_zero] at hle
                linarith
              · refine ⟨k, by omega, ?_⟩
                rw [List.take_succ_cons, hM, exp_add] at hle
                rw [div_le_iff₀ (exp_pos _)]
                linarith
        _ ≤ 1 / (μ / exp (E x a)) := ih (step x a) hμ'
        _ = exp (E x a) / μ := by rw [one_div_div]
    calc avg (fun a => expList R n (fun l =>
            if ∃ k ≤ n + 1, μ ≤ exp (M x ((a :: l).take k)) then (1 : ℝ) else 0))
        ≤ avg (fun a => exp (E x a) / μ) := avg_le_avg hpt
      _ = avg (fun a => exp (E x a)) / μ := by
          simp only [div_eq_mul_inv, mul_comm _ μ⁻¹, avg_const_mul]
      _ ≤ 1 / μ := div_le_div_of_nonneg_right (hE x) hμ.le

/-- **Maximal Azuma–Hoeffding inequality** (Azuma 1967; Hoeffding 1963, Theorem 2, for independent
summands). If the increments have zero mean over a uniform round, `avg (D y) = 0`, and are bounded,
`|D y a| ≤ c`, then over `n` i.i.d. uniform rounds the martingale
`M_k = incrementSum step D x (l.take k)` reaches `λ ≥ 0` at some step `k ≤ n` with probability at
most `exp(-λ² / (2 n c²))`. -/
theorem expList_azuma (step : σ → R → σ) (D : σ → R → ℝ) {c : ℝ}
    (hmean : ∀ y, avg (D y) = 0) (hbound : ∀ y a, |D y a| ≤ c) (x : σ) (n : ℕ) {lam : ℝ}
    (hlam : 0 ≤ lam) :
    expList R n (fun l => if ∃ k ≤ n, lam ≤ incrementSum step D x (l.take k) then 1 else 0)
      ≤ exp (-(lam ^ 2 / (2 * n * c ^ 2))) := by
  rcases isEmpty_or_nonempty R with hR | hR
  · cases n with
    | zero =>
      simp only [expList_zero, CharP.cast_eq_zero, mul_zero, zero_mul, div_zero, neg_zero,
        exp_zero]
      split_ifs <;> norm_num
    | succ n =>
      rw [expList_succ]
      simp only [avg, Finset.univ_eq_empty, Finset.sum_empty, zero_div]
      positivity
  by_cases hnc : (n : ℝ) * c ^ 2 = 0
  · have h0 : lam ^ 2 / (2 * n * c ^ 2) = 0 := by rw [mul_assoc, hnc, mul_zero, div_zero]
    rw [h0, neg_zero, exp_zero]
    exact expList_le_one fun l => by split_ifs <;> norm_num
  have hK : 0 < (n : ℝ) * c ^ 2 :=
    lt_of_le_of_ne (by positivity) (Ne.symm hnc)
  obtain ⟨K, hKdef⟩ : ∃ K, K = (n : ℝ) * c ^ 2 := ⟨_, rfl⟩
  rw [← hKdef] at hK
  have h2K : 2 * (n : ℝ) * c ^ 2 = 2 * K := by rw [hKdef]; ring
  rw [h2K]
  have hθ : 0 ≤ lam / K := div_nonneg hlam hK.le
  have hE (y : σ) :
      avg (fun a => exp (lam / K * D y a - (lam / K) ^ 2 * c ^ 2 / 2)) ≤ 1 := by
    have h := avg_exp_mul_le (hmean y) (hbound y) (lam / K)
    have hsplit (a : R) : exp (lam / K * D y a - (lam / K) ^ 2 * c ^ 2 / 2)
        = exp (-((lam / K) ^ 2 * c ^ 2 / 2)) * exp (lam / K * D y a) := by
      rw [← exp_add]
      ring_nf
    simp_rw [hsplit]
    rw [avg_const_mul]
    calc exp (-((lam / K) ^ 2 * c ^ 2 / 2)) * avg (fun a => exp (lam / K * D y a))
        ≤ exp (-((lam / K) ^ 2 * c ^ 2 / 2)) * exp ((lam / K) ^ 2 * c ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left h (exp_pos _).le
      _ = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]
  have hV := expList_ville step (fun y a => lam / K * D y a - (lam / K) ^ 2 * c ^ 2 / 2)
    (incrementSum step fun y a => lam / K * D y a - (lam / K) ^ 2 * c ^ 2 / 2)
    (fun _ => rfl) (fun _ _ _ => rfl) hE n x (exp_pos (lam ^ 2 / (2 * K)))
  calc _ ≤ expList R n (fun l => if ∃ k ≤ n, exp (lam ^ 2 / (2 * K))
          ≤ exp (incrementSum step (fun y a => lam / K * D y a - (lam / K) ^ 2 * c ^ 2 / 2)
            x (l.take k)) then 1 else 0) := by
        refine expList_le_expList fun l => ite_one_zero_le_of_imp fun ⟨k, hk, hle⟩ => ⟨k, hk, ?_⟩
        rw [exp_le_exp, incrementSum_mul_sub]
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
    _ ≤ 1 / exp (lam ^ 2 / (2 * K)) := hV
    _ = exp (-(lam ^ 2 / (2 * K))) := by rw [exp_neg, one_div]

end Dynamics
