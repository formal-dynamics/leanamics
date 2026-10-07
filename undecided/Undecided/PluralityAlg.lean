import Undecided.PluralityRound

/-! # Algebra of the expected counts (UND-3)

Identities and inequalities between the counts of a configuration (`cnt`, `und`, `oth`) and
the expected counts after one round (`mu`, `muU`, `muS`), with `c = c_m`, `q` undecided,
`S = oth x m = ∑_{j ≠ m} cⱼ`:

* `cnt_mu_sub`: `cᵢ µ_m - µᵢ c_m = cᵢ c_m (c_m - cᵢ)/n`, the drift of the ratio `cᵢ/c_m`
  (the expected growth rates `(cᵢ + 2q)/n` of the paper's (3) favour larger communities);
  `oth_mu_sub_ge`: summed over `j ≠ m`, at least `(1 - θ) c² S / n` when every `cⱼ ≤ θ c`;
* `mu_add_two_muU`: `µ_m + 2µ_q = n + (n - c - 2q)²/n + 2W/n` with
  `W = c(n - q) - ∑ⱼ cⱼ² = ∑_{j ≠ m} cⱼ(c - cⱼ)` (`W_eq`), and `W ≥ (1 - θ) c S` (`W_ge`): this is
  the paper's Lemma 1 (plurality drift) in the form used here;
* `muS_le`, `muU_le`: the bounds behind the final contraction of `4S + q`.
-/

namespace Undecided.Plurality
open Finset Dynamics Real

variable {n k : ℕ}

lemma cnt_add_und_le (x : Config n k) (i : Fin k) : cnt x i + und x ≤ n := by
  have h := und_add_sum x
  have := single_le_sum (fun j _ => cnt_nonneg x j) (mem_univ i)
  linarith

lemma oth_add_und_le (x : Config n k) (m : Fin k) : oth x m + und x ≤ n := by
  unfold oth
  linarith [cnt_nonneg x m]

lemma cnt_le_oth (x : Config n k) {m j : Fin k} (hj : j ≠ m) : cnt x j ≤ oth x m := by
  rw [oth_eq_sum]
  exact single_le_sum (fun j _ => cnt_nonneg x j) (mem_erase.mpr ⟨hj, mem_univ j⟩)

lemma mu_nonneg (x : Config n k) (i : Fin k) : 0 ≤ mu x i := by
  unfold mu
  have := cnt_nonneg x i
  have := und_nonneg x
  positivity

lemma mu_le_n (x : Config n k) (i : Fin k) (hn : (0 : ℝ) < n) : mu x i ≤ n := by
  unfold mu
  rw [div_le_iff₀ hn]
  have h1 := cnt_add_und_le x i
  have := cnt_nonneg x i
  have := und_nonneg x
  nlinarith

lemma mu_le_two_cnt (x : Config n k) (i : Fin k) (hn : (0 : ℝ) < n) : mu x i ≤ 2 * cnt x i := by
  unfold mu
  rw [div_le_iff₀ hn]
  have h1 := cnt_add_und_le x i
  have := cnt_nonneg x i
  have := und_nonneg x
  nlinarith

/-- A smaller community has a smaller expected size. -/
lemma mu_le_mu (x : Config n k) {i j : Fin k} (h : cnt x i ≤ cnt x j) : mu x i ≤ mu x j := by
  unfold mu
  have := cnt_nonneg x i
  have := und_nonneg x
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  apply div_le_div_of_nonneg_right _ hn
  nlinarith

lemma muU_le_n (x : Config n k) (hn : (0 : ℝ) < n) : muU x ≤ n := by
  unfold muU
  rw [div_le_iff₀ hn]
  have h0 : 0 ≤ ∑ j, cnt x j := sum_nonneg fun j _ => cnt_nonneg x j
  have h1 : und x ≤ n := by linarith [und_add_sum x]
  have := und_nonneg x
  have : 0 ≤ ∑ i, cnt x i ^ 2 := sum_nonneg fun i _ => sq_nonneg _
  nlinarith

/-- The drift of the ratio `cᵢ / c_m`: `cᵢ µ_m - µᵢ c_m = cᵢ c_m (c_m - cᵢ)/n`. -/
lemma cnt_mu_sub (x : Config n k) (i m : Fin k) :
    cnt x i * mu x m - mu x i * cnt x m = cnt x i * cnt x m * (cnt x m - cnt x i) / n := by
  unfold mu
  ring

lemma oth_mu_sub (x : Config n k) (m : Fin k) :
    oth x m * mu x m - muS x m * cnt x m =
      ∑ j ∈ univ.erase m, cnt x j * cnt x m * (cnt x m - cnt x j) / n := by
  rw [oth_eq_sum, muS_eq_sum, sum_mul, sum_mul, ← sum_sub_distrib]
  exact sum_congr rfl fun j _ => cnt_mu_sub x j m

/-- Summed over the other colours, the drift is at least `(1 - θ) c² S / n` when every other
community has at most `θ c` nodes. -/
lemma oth_mu_sub_ge (x : Config n k) (m : Fin k) {θ : ℝ}
    (hθ : ∀ j, j ≠ m → cnt x j ≤ θ * cnt x m) :
    (1 - θ) * cnt x m ^ 2 * oth x m / n ≤ oth x m * mu x m - muS x m * cnt x m := by
  rw [oth_mu_sub, oth_eq_sum, mul_sum, sum_div]
  refine sum_le_sum fun j hj => ?_
  have hj' := (mem_erase.mp hj).1
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  apply div_le_div_of_nonneg_right _ hn
  have h1 := hθ j hj'
  have h2 := cnt_nonneg x j
  have h3 := cnt_nonneg x m
  have : cnt x j * cnt x m * ((1 - θ) * cnt x m) ≤ cnt x j * cnt x m * (cnt x m - cnt x j) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  nlinarith

/-- `µ_S ≤ S(S + 2q)/n`. -/
lemma muS_le (x : Config n k) (m : Fin k) :
    muS x m ≤ oth x m * (oth x m + 2 * und x) / n := by
  rw [muS_eq_sum]
  unfold mu
  rw [← sum_div]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  apply div_le_div_of_nonneg_right _ hn
  rw [oth_eq_sum, sum_mul]
  refine sum_le_sum fun j hj => ?_
  have hj' := (mem_erase.mp hj).1
  have := cnt_le_oth x hj'
  rw [oth_eq_sum] at this
  have := cnt_nonneg x j
  have := und_nonneg x
  nlinarith

lemma muS_le_n (x : Config n k) (m : Fin k) (hn : (0 : ℝ) < n) : muS x m ≤ n := by
  refine (muS_le x m).trans ?_
  rw [div_le_iff₀ hn]
  have := oth_add_und_le x m
  have := oth_nonneg x m
  have := und_nonneg x
  nlinarith

lemma sum_sq_eq (x : Config n k) (m : Fin k) :
    ∑ j, cnt x j ^ 2 = cnt x m ^ 2 + ∑ j ∈ univ.erase m, cnt x j ^ 2 :=
  (add_sum_erase _ _ (mem_univ m)).symm

/-- `µ_q ≤ (q² + 2cS + S²)/n`. -/
lemma muU_le (x : Config n k) (m : Fin k) :
    muU x ≤ (und x ^ 2 + 2 * cnt x m * oth x m + oth x m ^ 2) / n := by
  unfold muU
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  apply div_le_div_of_nonneg_right _ hn
  rw [sum_sq_eq x m]
  have : 0 ≤ ∑ j ∈ univ.erase m, cnt x j ^ 2 := sum_nonneg fun j _ => sq_nonneg _
  have e : (n : ℝ) - und x = cnt x m + oth x m := by unfold oth; ring
  rw [e]
  nlinarith

/-- The paper's Lemma 1 in the form used here:
`µ_m + 2µ_q = n + (n - c - 2q)²/n + 2(c(n - q) - ∑ⱼ cⱼ²)/n`. -/
lemma mu_add_two_muU (x : Config n k) (m : Fin k) (hn : (0 : ℝ) < n) :
    mu x m + 2 * muU x = n + (n - cnt x m - 2 * und x) ^ 2 / n +
      2 * (cnt x m * (n - und x) - ∑ j, cnt x j ^ 2) / n := by
  unfold mu muU
  field_simp
  ring

/-- `W = c(n - q) - ∑ⱼ cⱼ² = ∑_{j ≠ m} cⱼ(c - cⱼ)`. -/
lemma W_eq (x : Config n k) (m : Fin k) :
    cnt x m * (n - und x) - ∑ j, cnt x j ^ 2 =
      ∑ j ∈ univ.erase m, cnt x j * (cnt x m - cnt x j) := by
  have e : (n : ℝ) - und x = cnt x m + ∑ j ∈ univ.erase m, cnt x j := by
    rw [← oth_eq_sum]; unfold oth; ring
  rw [e, sum_sq_eq x m, mul_add, mul_sum]
  have : ∑ j ∈ univ.erase m, cnt x j * (cnt x m - cnt x j) =
      ∑ j ∈ univ.erase m, cnt x m * cnt x j - ∑ j ∈ univ.erase m, cnt x j ^ 2 := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun j _ => by ring
  rw [this]
  ring

/-- `W ≥ (1 - θ) c S` when every other community has at most `θ c` nodes. -/
lemma W_ge (x : Config n k) (m : Fin k) {θ : ℝ} (hθ : ∀ j, j ≠ m → cnt x j ≤ θ * cnt x m) :
    (1 - θ) * cnt x m * oth x m ≤ cnt x m * (n - und x) - ∑ j, cnt x j ^ 2 := by
  rw [W_eq, oth_eq_sum, mul_sum]
  refine sum_le_sum fun j hj => ?_
  have h1 := hθ j (mem_erase.mp hj).1
  have h2 := cnt_nonneg x j
  nlinarith

end Undecided.Plurality
