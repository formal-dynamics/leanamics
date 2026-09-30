import Plurality.Model

/-!
# The next expected coloring (Lemma 2.1)

A node recolors itself using three independent uniform samples, so the
probability that it adopts color `j` under a rule `f` is a polynomial in the
color fractions `x_h = c_h / n`:
`∑_{a,b,c} x_a x_b x_c 𝟙[f a b c = j]` (`avg_adopt`). For 3-majority this is
`x_j² + x_j (1 - ∑_h x_h²)` (`avg_adopt_maj3`), and summing over the `n`
independent nodes gives the paper's Lemma 2.1 (`expected_count`):
`𝔼[C_{j,t+1} | C_t = c] = c_j (1 + (n c_j - ∑_h c_h²)/n²)`.

The per-node `{0,1}` decomposition `count_stepWith_eq_sum` is the shape the
concentration bounds (Chernoff, Hoeffding, Bernstein) consume.
-/

namespace Plurality

open Finset Dynamics
open ThreeMajority (Tgt3 tgt3_nonempty)

variable {n k : ℕ}

/-- The fraction `x_j = c_j / n` of nodes of color `j`. -/
noncomputable def frac (x : Config n k) (j : Fin k) : ℝ := (count x j : ℝ) / n

lemma frac_nonneg (x : Config n k) (j : Fin k) : 0 ≤ frac x j := by
  unfold frac; positivity

lemma frac_le_one (x : Config n k) (j : Fin k) : frac x j ≤ 1 := by
  unfold frac
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [div_le_one (by exact_mod_cast hn)]
    exact_mod_cast count_le x j

lemma sum_frac (hn : 1 ≤ n) (x : Config n k) : ∑ j, frac x j = 1 := by
  unfold frac
  rw [← sum_div, sum_count_real, div_self]
  exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn)

/-- The color fraction is the probability that a uniform sample has that color. -/
lemma avg_color_indicator (x : Config n k) (j : Fin k) :
    avg (fun v : Fin n => if x v = j then (1 : ℝ) else 0) = frac x j := by
  rw [avg_indicator]
  simp [frac, count]

/-- The indicator that a node whose three samples are `s` adopts color `j`
under rule `f`. -/
def adopt (f : Fin k → Fin k → Fin k → Fin k) (x : Config n k) (j : Fin k)
    (s : Fin n × Fin n × Fin n) : ℝ :=
  if f (x s.1) (x s.2.1) (x s.2.2) = j then 1 else 0

lemma adopt_zero_one (f : Fin k → Fin k → Fin k → Fin k) (x : Config n k) (j : Fin k)
    (s : Fin n × Fin n × Fin n) : adopt f x j s = 0 ∨ adopt f x j s = 1 := by
  unfold adopt; split_ifs <;> simp

/-- The new count of color `j` is a sum of independent per-node indicators. -/
lemma count_stepWith_eq_sum (f : Fin k → Fin k → Fin k → Fin k) (x : Config n k)
    (r : Tgt3 n) (j : Fin k) :
    (count (stepWith f x r) j : ℝ) = ∑ v, adopt f x j (r v) := by
  unfold count adopt
  rw [card_filter]
  push_cast
  rfl

/-- **Three independent samples.** The average of a function of the three
sampled colors is its expectation under three independent draws from the
color fractions. -/
lemma avg_color_triple (x : Config n k) (g : Fin k → Fin k → Fin k → ℝ) :
    avg (fun s : Fin n × Fin n × Fin n => g (x s.1) (x s.2.1) (x s.2.2))
      = ∑ a, ∑ b, ∑ c, frac x a * frac x b * frac x c * g a b c := by
  have h1 (G : Fin k → ℝ) : ∑ v, G (x v) = ∑ a, (count x a : ℝ) * G a := by
    simpa using sum_comp_eq_sum_count x G
  have hsum : ∑ s : Fin n × Fin n × Fin n, g (x s.1) (x s.2.1) (x s.2.2)
      = ∑ a, (count x a : ℝ) * ∑ b, (count x b : ℝ) * ∑ c, (count x c : ℝ) * g a b c := by
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    calc ∑ s1, ∑ s2, ∑ s3, g (x s1) (x s2) (x s3)
        = ∑ s1, ∑ s2, ∑ c, (count x c : ℝ) * g (x s1) (x s2) c :=
          sum_congr rfl fun s1 _ => sum_congr rfl fun s2 _ => h1 (g (x s1) (x s2))
      _ = ∑ s1, ∑ b, (count x b : ℝ) * ∑ c, (count x c : ℝ) * g (x s1) b c :=
          sum_congr rfl fun s1 _ => h1 (fun b => ∑ c, (count x c : ℝ) * g (x s1) b c)
      _ = ∑ a, (count x a : ℝ) * ∑ b, (count x b : ℝ) * ∑ c, (count x c : ℝ) * g a b c :=
          h1 (fun a => ∑ b, (count x b : ℝ) * ∑ c, (count x c : ℝ) * g a b c)
  unfold avg
  rw [hsum]
  simp only [Fintype.card_prod, Fintype.card_fin, frac]
  push_cast
  rw [sum_div]
  refine sum_congr rfl fun a _ => ?_
  rw [mul_sum, sum_div]
  refine sum_congr rfl fun b _ => ?_
  rw [mul_sum, mul_sum, sum_div]
  refine sum_congr rfl fun c _ => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp

/-- The probability that a node adopts color `j` under rule `f`. -/
lemma avg_adopt (f : Fin k → Fin k → Fin k → Fin k) (x : Config n k) (j : Fin k) :
    avg (adopt f x j)
      = ∑ a, ∑ b, ∑ c, frac x a * frac x b * frac x c * (if f a b c = j then 1 else 0) :=
  avg_color_triple x (fun a b c => if f a b c = j then 1 else 0)

/-- The expected new count of color `j` under rule `f` is `n` times the adoption
probability. -/
lemma expected_count_stepWith (hn : 1 ≤ n) (f : Fin k → Fin k → Fin k → Fin k)
    (x : Config n k) (j : Fin k) :
    avg (fun r : Tgt3 n => (count (stepWith f x r) j : ℝ)) = n * avg (adopt f x j) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  simp_rw [count_stepWith_eq_sum]
  rw [avg_sum]
  simp_rw [show ∀ v : Fin n, avg (fun r : Tgt3 n => adopt f x j (r v)) = avg (adopt f x j)
    from fun v => avg_eval n v (adopt f x j)]
  simp

/-- `∑_c w_c · (if b = c then u else v) = w_b u + (1 - w_b) v` for weights summing to `1`. -/
lemma sum_weight_ite {w : Fin k → ℝ} (hw : ∑ c, w c = 1) (b : Fin k) (u v : ℝ) :
    ∑ c, w c * (if b = c then u else v) = w b * u + (1 - w b) * v := by
  have h (c : Fin k) : w c * (if b = c then u else v)
      = w c * v + (if b = c then w c * (u - v) else 0) := by
    split_ifs <;> ring
  simp_rw [h]
  rw [sum_add_distrib, ← sum_mul, hw, sum_ite_eq]
  simp only [mem_univ, if_true]
  ring

/-- **The 3-majority adoption polynomial.** For weights `w` summing to one,
`∑_{a,b,c} w_a w_b w_c 𝟙[maj3 a b c = j] = w_j² + w_j (1 - ∑_h w_h²)`. -/
lemma sum_triple_maj3 {w : Fin k → ℝ} (hw : ∑ c, w c = 1) (j : Fin k) :
    ∑ a, ∑ b, ∑ c, w a * w b * w c * (if maj3 a b c = j then 1 else 0)
      = w j ^ 2 + w j * (1 - ∑ h, w h ^ 2) := by
  have hc (a b : Fin k) : ∑ c, w a * w b * w c * (if maj3 a b c = j then (1 : ℝ) else 0)
      = w a * w b * (w b * (if b = j then 1 else 0) + (1 - w b) * (if a = j then 1 else 0)) := by
    have : ∀ c, w a * w b * w c * (if maj3 a b c = j then (1 : ℝ) else 0)
        = w a * w b * (w c * (if b = c then (if b = j then 1 else 0)
            else (if a = j then 1 else 0))) := by
      intro c
      unfold maj3
      split_ifs <;> simp_all
    simp_rw [this, ← mul_sum]
    rw [sum_weight_ite hw]
  simp_rw [hc]
  have hb (a : Fin k) : ∑ b, w a * w b * (w b * (if b = j then (1 : ℝ) else 0)
        + (1 - w b) * (if a = j then 1 else 0))
      = w a * (w j ^ 2 + (if a = j then 1 else 0) * (1 - ∑ h, w h ^ 2)) := by
    have : ∀ b, w a * w b * (w b * (if b = j then (1 : ℝ) else 0)
          + (1 - w b) * (if a = j then 1 else 0))
        = w a * ((if b = j then w b ^ 2 else 0)
          + (if a = j then 1 else 0) * (w b - w b ^ 2)) := by
      intro b
      split_ifs <;> ring
    simp_rw [this, ← mul_sum, sum_add_distrib, sum_ite_eq', ← mul_sum, sum_sub_distrib, hw]
    simp
  simp_rw [hb]
  have : ∀ a, w a * (w j ^ 2 + (if a = j then (1 : ℝ) else 0) * (1 - ∑ h, w h ^ 2))
      = w a * w j ^ 2 + (if a = j then w a * (1 - ∑ h, w h ^ 2) else 0) := by
    intro a
    split_ifs <;> ring
  simp_rw [this, sum_add_distrib, ← sum_mul, hw, sum_ite_eq']
  simp

/-- The probability that a node adopts color `j` under 3-majority is
`x_j² + x_j (1 - ∑_h x_h²)`. -/
lemma avg_adopt_maj3 (hn : 1 ≤ n) (x : Config n k) (j : Fin k) :
    avg (adopt maj3 x j) = frac x j ^ 2 + frac x j * (1 - ∑ h, frac x h ^ 2) := by
  rw [avg_adopt]
  exact sum_triple_maj3 (sum_frac hn x) j

/-- **Lemma 2.1 (next expected coloring).** For every coloring and every
color `j`, `𝔼[C_{j,t+1} | C_t = c] = c_j (1 + (n c_j - ∑_h c_h²) / n²)`. -/
theorem expected_count (hn : 1 ≤ n) (x : Config n k) (j : Fin k) :
    avg (fun r : Tgt3 n => (count (step x r) j : ℝ))
      = count x j * (1 + (n * count x j - ∑ h, (count x h : ℝ) ^ 2) / n ^ 2) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn)
  change avg (fun r : Tgt3 n => (count (stepWith maj3 x r) j : ℝ)) = _
  rw [expected_count_stepWith hn, avg_adopt_maj3 hn]
  simp only [frac, div_pow, ← sum_div]
  field_simp
  ring

end Plurality
