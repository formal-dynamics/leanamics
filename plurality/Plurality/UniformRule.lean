import Plurality.ClearMajority

/-!
# Theorem 4.8 (b): a solver with the clear-majority property is uniform

Let `f` have the clear-majority property and let `r, g, b` be distinct colors
with `δ_r ≤ 1` (`r` is returned on at most one of the six orderings of
`(r, g, b)`). Start from `23n/60` nodes of color `r`, `n/3` of color `g` and
`17n/60` of color `b`: `r` is the unique plurality color with bias `n/20`.

**One round.** With only `r, g, b` present and `x = x_r`, a node adopts `r`
only if it sees `r` at least twice, or sees `r, g, b` in an order on which
`f` returns `r` (clear majority rules out everything else), so
`p(r) ≤ 3x² - 2x³ + δ_r x_r x_g x_b ≤ x (3x - 2x² + (1-x)²/4)`. For
`x ≤ 2/5` this is at most `0.97 x` (`expected_count_le`), and Hoeffding's
inequality bounds the probability of jumping above `2n/5`
(`jump_prob_le`).

**Many rounds.** The *frozen* chain (`frozenStep`) stops as soon as `r` has
more than `2n/5` nodes. On it, `Φ = C_r 𝟙[C_r ≤ 2n/5]` contracts by `0.97`
in **every** state (`frozen_potential_le`), and it is stopped within `T`
rounds with probability at most `T e^{-9n/31250}` (`frozen_stop_le`). The
real and frozen chains agree until the frozen chain stops
(`foldl_frozen_eq`). Hence `r` survives `T₀ = O(log n)` rounds with
probability at most `1/4` (`alive_le`), and so it is never the consensus color
with probability more than `1/4`: `f` is not an `(n/20, 1/4)`-solver
(`not_solver_of_nonuniform`).

`theorem_4_8_b`: an `(n/20, 1/4)`-solver with the clear-majority property has
the uniform property. The paper's proof of Lemma 4.10 is a sketch covering
`δ_r = 1` with `(δ_g, δ_b) ∈ {(3,2), (4,1)}`; the argument here covers every
triple with some `δ ≤ 1`, which is every non-uniform triple.
-/

namespace Plurality

open Finset Real Dynamics
open ThreeMajority (Tgt3 tgt3_nonempty)

variable {n k : ℕ}

/-! ### Three colors present -/

/-- Every node supports `r`, `g` or `b`. -/
def Supp3 (r g b : Fin k) (y : Config n k) : Prop := ∀ v, y v = r ∨ y v = g ∨ y v = b

lemma Supp3.stepWith {f : Rule k} (hf : Conservative f) {r g b : Fin k} {y : Config n k}
    (hy : Supp3 r g b y) (t : Tgt3 n) : Supp3 r g b (stepWith f y t) := fun v => by
  change f (y (t v).1) (y (t v).2.1) (y (t v).2.2) = r
    ∨ f (y (t v).1) (y (t v).2.1) (y (t v).2.2) = g
    ∨ f (y (t v).1) (y (t v).2.1) (y (t v).2.2) = b
  rcases hf (y (t v).1) (y (t v).2.1) (y (t v).2.2) with h | h | h <;> rw [h] <;> exact hy _

lemma Supp3.count_eq_zero {r g b : Fin k} {y : Config n k} (hy : Supp3 r g b y) {c : Fin k}
    (hr : c ≠ r) (hg : c ≠ g) (hb : c ≠ b) : count y c = 0 := by
  unfold count
  rw [card_eq_zero, filter_eq_empty_iff]
  intro v _ hv
  rcases hy v with h | h | h
  · exact hr (hv.symm.trans h)
  · exact hg (hv.symm.trans h)
  · exact hb (hv.symm.trans h)

lemma sum_eq_three {r g b : Fin k} (hrg : r ≠ g) (hgb : g ≠ b) (hrb : r ≠ b) {F : Fin k → ℝ}
    (hF : ∀ c, c ≠ r → c ≠ g → c ≠ b → F c = 0) : ∑ c, F c = F r + F g + F b := by
  rw [← sum_subset (subset_univ {r, g, b}) fun c _ hc => by
    simp only [mem_insert, mem_singleton, not_or] at hc
    exact hF c hc.1 hc.2.1 hc.2.2]
  rw [sum_insert (by simp [hrg, hrb]), sum_insert (by simp [hgb]), sum_singleton]
  ring

/-! ### One round -/

/-- **Pointwise bound on adopting `r`.** For colors `a, b', c` among `r, g, b`,
`f` returns `r` only if `r` appears at least twice or `(a, b', c)` is an
ordering of `(r, g, b)` on which `f` returns `r`. -/
lemma adopt_r_le {f : Rule k} (hcm : ClearMajority f) {r g b : Fin k}
    (hrg : r ≠ g) (hgb : g ≠ b) (hrb : r ≠ b) {a b' c : Fin k}
    (ha : a = r ∨ a = g ∨ a = b) (hb' : b' = r ∨ b' = g ∨ b' = b) (hc : c = r ∨ c = g ∨ c = b) :
    let e : Fin k → ℝ := fun z => if z = r then 1 else 0
    let i : Fin k → Fin k → ℝ := fun z z' => if z = z' then 1 else 0
    let d : Fin k → Fin k → Fin k → ℝ := fun u v w => if f u v w = r then 1 else 0
    d a b' c ≤ (e a * e b' + e a * e c + e b' * e c - 2 * (e a * e b' * e c))
      + (i a r * i b' g * i c b * d r g b + i a r * i b' b * i c g * d r b g
        + i a g * i b' r * i c b * d g r b + i a g * i b' b * i c r * d g b r
        + i a b * i b' r * i c g * d b r g + i a b * i b' g * i c r * d b g r) := by
  intro e i d
  have h1 (u v : Fin k) : f u u v = u := (hcm u v).1
  have h2 (u v : Fin k) : f u v u = u := (hcm u v).2.1
  have h3 (u v : Fin k) : f v u u = u := (hcm u v).2.2
  rcases ha with rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl <;>
    simp [e, i, d, h1, h2, h3, hrg, hgb, hrb, hrg.symm, hgb.symm, hrb.symm] <;> norm_num

/-- **Adoption probability of `r`** with only `r, g, b` present:
`p(r) ≤ 3x² - 2x³ + δ_r x_r x_g x_b`. -/
theorem avg_adopt_r_le (hn : 1 ≤ n) {f : Rule k} (hcm : ClearMajority f)
    {r g b : Fin k} (hrg : r ≠ g) (hgb : g ≠ b) (hrb : r ≠ b) {y : Config n k}
    (hy : Supp3 r g b y) :
    avg (adopt f y r) ≤ 3 * frac y r ^ 2 - 2 * frac y r ^ 3
      + deltaCount f r g b r * (frac y r * frac y g * frac y b) := by
  rw [avg_adopt]
  set w := frac y with hw
  have hw0 : ∀ c, c ≠ r → c ≠ g → c ≠ b → w c = 0 := fun c h1 h2 h3 => by
    simp [hw, frac, hy.count_eq_zero h1 h2 h3]
  have hsum : ∑ c, w c = 1 := sum_frac hn y
  have hwnn : ∀ c, 0 ≤ w c := frac_nonneg y
  set e : Fin k → ℝ := fun z => if z = r then 1 else 0
  set i : Fin k → Fin k → ℝ := fun z z' => if z = z' then 1 else 0
  set d : Fin k → Fin k → Fin k → ℝ := fun u v w => if f u v w = r then 1 else 0
  -- the pointwise bound, weighted
  have hpt : ∀ a b' c, w a * w b' * w c * (if f a b' c = r then (1 : ℝ) else 0)
      ≤ w a * w b' * w c * ((e a * e b' + e a * e c + e b' * e c - 2 * (e a * e b' * e c))
      + (i a r * i b' g * i c b * d r g b + i a r * i b' b * i c g * d r b g
        + i a g * i b' r * i c b * d g r b + i a g * i b' b * i c r * d g b r
        + i a b * i b' r * i c g * d b r g + i a b * i b' g * i c r * d b g r)) := by
    intro a b' c
    have supp (z : Fin k) : w z = 0 ∨ (z = r ∨ z = g ∨ z = b) := by
      by_cases h1 : z = r
      · exact Or.inr (Or.inl h1)
      by_cases h2 : z = g
      · exact Or.inr (Or.inr (Or.inl h2))
      by_cases h3 : z = b
      · exact Or.inr (Or.inr (Or.inr h3))
      exact Or.inl (hw0 z h1 h2 h3)
    rcases supp a with h | ha
    · simp [h]
    rcases supp b' with h | hb'
    · simp [h]
    rcases supp c with h | hc
    · simp [h]
    exact mul_le_mul_of_nonneg_left (adopt_r_le hcm hrg hgb hrb ha hb' hc)
      (by have := hwnn a; have := hwnn b'; have := hwnn c; positivity)
  refine (sum_le_sum fun a _ => sum_le_sum fun b' _ => sum_le_sum fun c _ => hpt a b' c).trans
    (le_of_eq ?_)
  -- evaluate every term by factorization
  have F (P Q R : Fin k → ℝ) (κ : ℝ) :
      ∑ a, ∑ b', ∑ c, w a * w b' * w c * (P a * Q b' * R c * κ)
        = (∑ a, w a * P a) * (∑ b', w b' * Q b') * (∑ c, w c * R c) * κ := by
    rw [← sum_triple_factor]
    simp only [sum_mul]
    exact sum_congr rfl fun a _ => sum_congr rfl fun b' _ => sum_congr rfl fun c _ => by ring
  have hone : ∑ a, w a * (fun _ : Fin k => (1 : ℝ)) a = 1 := by simp [hsum]
  have hind (z : Fin k) : ∑ a, w a * i a z = w z := sum_weight_ind w z
  have he : ∑ a, w a * e a = w r := sum_weight_ind w r
  -- split the big sum into its eleven pieces
  have split : ∀ a b' c, w a * w b' * w c * ((e a * e b' + e a * e c + e b' * e c
      - 2 * (e a * e b' * e c))
      + (i a r * i b' g * i c b * d r g b + i a r * i b' b * i c g * d r b g
        + i a g * i b' r * i c b * d g r b + i a g * i b' b * i c r * d g b r
        + i a b * i b' r * i c g * d b r g + i a b * i b' g * i c r * d b g r))
      = w a * w b' * w c * (e a * e b' * 1 * 1) + w a * w b' * w c * (e a * 1 * e c * 1)
        + w a * w b' * w c * (1 * e b' * e c * 1) + w a * w b' * w c * (e a * e b' * e c * (-2))
        + w a * w b' * w c * (i a r * i b' g * i c b * d r g b)
        + w a * w b' * w c * (i a r * i b' b * i c g * d r b g)
        + w a * w b' * w c * (i a g * i b' r * i c b * d g r b)
        + w a * w b' * w c * (i a g * i b' b * i c r * d g b r)
        + w a * w b' * w c * (i a b * i b' r * i c g * d b r g)
        + w a * w b' * w c * (i a b * i b' g * i c r * d b g r) := fun a b' c => by ring
  simp_rw [split, sum_add_distrib]
  rw [F e e (fun _ => 1) 1, F e (fun _ => 1) e 1, F (fun _ => 1) e e 1, F e e e (-2),
    F (i · r) (i · g) (i · b) _, F (i · r) (i · b) (i · g) _, F (i · g) (i · r) (i · b) _,
    F (i · g) (i · b) (i · r) _, F (i · b) (i · r) (i · g) _, F (i · b) (i · g) (i · r) _]
  simp only [he, hind, hone]
  simp only [deltaCount, d]
  push_cast
  ring

/-- `3x² - 2x³ + x(1-x)²/4 ≤ 0.97 x` for `0 ≤ x ≤ 2/5`. -/
lemma poly_le (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 2 / 5) :
    3 * x ^ 2 - 2 * x ^ 3 + x * (1 - x) ^ 2 / 4 ≤ 97 / 100 * x := by
  have : 0 ≤ (2 / 5 - x) * (72 / 70 - x) := mul_nonneg (by linarith) (by linarith)
  nlinarith [mul_nonneg h0 this]

/-- **Contraction in expectation.** With only `r, g, b` present, `δ_r ≤ 1` and
at most `2n/5` nodes of color `r`, the expected number of `r` nodes after one
round is at most `0.97` times the current one. -/
theorem expected_count_le (hn : 1 ≤ n) {f : Rule k} (hf : Conservative f)
    (hcm : ClearMajority f) {r g b : Fin k} (hrg : r ≠ g) (hgb : g ≠ b) (hrb : r ≠ b)
    (hδ : deltaCount f r g b r ≤ 1) {y : Config n k} (hy : Supp3 r g b y)
    (hlow : (count y r : ℝ) ≤ 2 * n / 5) :
    (n : ℝ) * avg (adopt f y r) ≤ 97 / 100 * count y r := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hp := avg_adopt_r_le hn hcm hrg hgb hrb hy
  set x := frac y r with hx
  have hx0 : 0 ≤ x := frac_nonneg y r
  have hxg : 0 ≤ frac y g := frac_nonneg y g
  have hxb : 0 ≤ frac y b := frac_nonneg y b
  have hsum : x + frac y g + frac y b = 1 := by
    have := sum_frac hn y
    rwa [sum_eq_three hrg hgb hrb fun c h1 h2 h3 => by
      simp [frac, hy.count_eq_zero h1 h2 h3]] at this
  have hx4 : x ≤ 2 / 5 := by
    rw [hx, frac, div_le_iff₀ hn0]; linarith
  have hδ' : (deltaCount f r g b r : ℝ) ≤ 1 := by exact_mod_cast hδ
  -- `x_g x_b ≤ ((1 - x)/2)²`
  have hgb' : frac y g * frac y b ≤ (1 - x) ^ 2 / 4 := by
    nlinarith [sq_nonneg (frac y g - frac y b)]
  have hprod : (deltaCount f r g b r : ℝ) * (x * frac y g * frac y b) ≤ x * (1 - x) ^ 2 / 4 := by
    have h0 : 0 ≤ x * frac y g * frac y b := by positivity
    calc (deltaCount f r g b r : ℝ) * (x * frac y g * frac y b) ≤ 1 * (x * frac y g * frac y b) :=
          mul_le_mul_of_nonneg_right hδ' h0
      _ = x * (frac y g * frac y b) := by ring
      _ ≤ x * ((1 - x) ^ 2 / 4) := mul_le_mul_of_nonneg_left hgb' hx0
      _ = x * (1 - x) ^ 2 / 4 := by ring
  have := poly_le x hx0 hx4
  have hcount : (n : ℝ) * x = count y r := by rw [hx, frac]; field_simp
  have : avg (adopt f y r) ≤ 97 / 100 * x := by linarith
  nlinarith

/-- **No jump above `2n/5`.** From at most `2n/5` nodes of color `r`, one
round ends with more than `2n/5` of them with probability at most
`exp(-9n/31250)`. -/
theorem jump_prob_le (hn : 1 ≤ n) {f : Rule k} (hf : Conservative f) (hcm : ClearMajority f)
    {r g b : Fin k} (hrg : r ≠ g) (hgb : g ≠ b) (hrb : r ≠ b) (hδ : deltaCount f r g b r ≤ 1)
    {y : Config n k} (hy : Supp3 r g b y) (hlow : (count y r : ℝ) ≤ 2 * n / 5) :
    avg (fun t : Tgt3 n => if 2 * (n : ℝ) / 5 < count (stepWith f y t) r then (1 : ℝ) else 0)
      ≤ exp (-(9 * n / 31250)) := by
  haveI : Nonempty (Fin n × Fin n × Fin n) := ⟨(⟨0, hn⟩, ⟨0, hn⟩, ⟨0, hn⟩)⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hE := expected_count_le hn hf hcm hrg hgb hrb hδ hy hlow
  have hsum : ∑ _v : Fin n, avg (adopt f y r) = n * avg (adopt f y r) := by
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hH := avg_hoeffding (fun (_ : Fin n) t => adopt f y r t)
    (fun _ t => adopt_zero_one f y r t) (lam := 3 * n / 250) (by positivity)
  rw [hsum] at hH
  refine le_trans (avg_le_avg fun t => ?_) (hH.trans (le_of_eq ?_))
  · have hc := count_stepWith_eq_sum f y t r
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exfalso; apply h2; rw [← hc]; linarith
    · norm_num
    · exact le_rfl
  · congr 1
    field_simp
    ring

/-! ### The frozen chain -/

/-- `r` has at most `2n/5` nodes. -/
def LowR (r : Fin k) (y : Config n k) : Prop := (count y r : ℝ) ≤ 2 * n / 5

open Classical in
/-- One round of the chain that stops once `r` has more than `2n/5` nodes. -/
noncomputable def frozenStep (f : Rule k) (r : Fin k) (y : Config n k) (t : Tgt3 n) :
    Config n k :=
  if LowR r y then stepWith f y t else y

open Classical in
/-- The potential `Φ = C_r 𝟙[C_r ≤ 2n/5]`. -/
noncomputable def potential (r : Fin k) (y : Config n k) : ℝ :=
  if LowR r y then (count y r : ℝ) else 0

lemma potential_nonneg (r : Fin k) (y : Config n k) : 0 ≤ potential r y := by
  unfold potential; split_ifs <;> positivity

lemma Supp3.frozen {f : Rule k} (hf : Conservative f) {r g b : Fin k} {y : Config n k}
    (hy : Supp3 r g b y) (t : Tgt3 n) : Supp3 r g b (frozenStep f r y t) := by
  unfold Plurality.frozenStep; split_ifs
  · exact hy.stepWith hf t
  · exact hy

/-- **`Φ` contracts in every state of the frozen chain.** -/
theorem frozen_potential_le (hn : 1 ≤ n) {f : Rule k} (hf : Conservative f)
    (hcm : ClearMajority f) {r g b : Fin k} (hrg : r ≠ g) (hgb : g ≠ b) (hrb : r ≠ b)
    (hδ : deltaCount f r g b r ≤ 1) :
    ∀ (T : ℕ) (y : Config n k), Supp3 r g b y →
      expList (Tgt3 n) T (fun l => potential r (l.foldl (frozenStep f r) y))
        ≤ (97 / 100) ^ T * potential r y := by
  haveI := tgt3_nonempty hn
  intro T
  induction T with
  | zero => intro y _; simp
  | succ T ih =>
    intro y hy
    rw [expList_succ]
    have hstep : avg (fun t => potential r (frozenStep f r y t)) ≤ 97 / 100 * potential r y := by
      by_cases hlow : LowR r y
      · have hpot : potential r y = count y r := by simp [potential, hlow]
        rw [hpot]
        calc avg (fun t => potential r (frozenStep f r y t))
            ≤ avg (fun t : Tgt3 n => (count (stepWith f y t) r : ℝ)) := avg_le_avg fun t => by
              have hfz : frozenStep f r y t = stepWith f y t := by
                simp [Plurality.frozenStep, hlow]
              rw [hfz]
              unfold potential
              split_ifs
              · exact le_refl _
              · positivity
          _ = n * avg (adopt f y r) := expected_count_stepWith hn f y r
          _ ≤ 97 / 100 * count y r := expected_count_le hn hf hcm hrg hgb hrb hδ hy hlow
      · have : ∀ t, potential r (frozenStep f r y t) = 0 := fun t => by
          simp [Plurality.frozenStep, hlow, potential]
        simp_rw [this]
        rw [avg_const]
        have : potential r y = 0 := by simp [potential, hlow]
        rw [this]; norm_num
    calc avg (fun t => expList (Tgt3 n) T
          (fun l => potential r ((t :: l).foldl (frozenStep f r) y)))
        ≤ avg (fun t => (97 / 100) ^ T * potential r (frozenStep f r y t)) :=
          avg_le_avg fun t => ih _ (hy.frozen hf t)
      _ = (97 / 100) ^ T * avg (fun t => potential r (frozenStep f r y t)) := avg_const_mul _ _
      _ ≤ (97 / 100) ^ T * (97 / 100 * potential r y) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = (97 / 100) ^ (T + 1) * potential r y := by ring

/-- **The frozen chain rarely stops.** -/
theorem frozen_stop_le (hn : 1 ≤ n) {f : Rule k} (hf : Conservative f) (hcm : ClearMajority f)
    {r g b : Fin k} (hrg : r ≠ g) (hgb : g ≠ b) (hrb : r ≠ b) (hδ : deltaCount f r g b r ≤ 1)
    (T : ℕ) {y : Config n k} (hy : Supp3 r g b y) (hlow : LowR r y) :
    expList (Tgt3 n) T (fun l => by
        classical exact if l.foldl (frozenStep f r) y ∈ {z | Supp3 r g b z ∧ LowR r z}
          then (0 : ℝ) else 1)
      ≤ T * exp (-(9 * n / 31250)) := by
  classical
  haveI := tgt3_nonempty hn
  have key : ∀ t < T, ∀ z ∈ {z : Config n k | Supp3 r g b z ∧ LowR r z},
      avg (fun u => if frozenStep f r z u ∈ {z : Config n k | Supp3 r g b z ∧ LowR r z}
        then (0 : ℝ) else 1) ≤ exp (-(9 * n / 31250)) := by
    intro t _ z hz
    refine le_trans (avg_le_avg fun u => ?_) (jump_prob_le hn hf hcm hrg hgb hrb hδ hz.1 hz.2)
    have hsupp := hz.1.stepWith hf u
    have hfz : frozenStep f r z u = stepWith f z u := by simp [Plurality.frozenStep, hz.2]
    rw [hfz]
    simp only [Set.mem_setOf_eq, LowR]
    split_ifs with h1 h2 h2
    · norm_num
    · norm_num
    · exact le_rfl
    · exfalso; push Not at h2; exact h1 ⟨hsupp, h2⟩
  convert expList_escape (frozenStep f r) (exp_pos _).le T
    (fun _ => {z : Config n k | Supp3 r g b z ∧ LowR r z}) y ⟨hy, hlow⟩
    (fun t ht z hz => by convert key t ht z hz using 3; split_ifs <;> rfl) using 3
  split_ifs <;> rfl

lemma foldl_frozen_high {f : Rule k} {r : Fin k} {y : Config n k} (hy : ¬ LowR r y) :
    ∀ l : List (Tgt3 n), l.foldl (frozenStep f r) y = y := by
  intro l
  induction l with
  | nil => rfl
  | cons t l ih =>
    rw [List.foldl_cons]
    have : frozenStep f r y t = y := by simp [Plurality.frozenStep, hy]
    rw [this, ih]

/-- **Coupling.** If the frozen chain has not stopped, it agrees with the real one. -/
lemma foldl_frozen_eq {f : Rule k} {r : Fin k} :
    ∀ (l : List (Tgt3 n)) (y : Config n k), LowR r (l.foldl (frozenStep f r) y) →
      l.foldl (frozenStep f r) y = runWith f y l := by
  intro l
  induction l with
  | nil => intro y _; rfl
  | cons t l ih =>
    intro y hlow
    by_cases hy : LowR r y
    · have : frozenStep f r y t = stepWith f y t := by simp [Plurality.frozenStep, hy]
      rw [List.foldl_cons, this] at hlow ⊢
      exact ih _ hlow
    · rw [List.foldl_cons, show frozenStep f r y t = y by simp [Plurality.frozenStep, hy],
        foldl_frozen_high hy] at hlow
      exact absurd hlow hy

lemma Supp3.foldl_frozen {f : Rule k} (hf : Conservative f) {r g b : Fin k} :
    ∀ (l : List (Tgt3 n)) {y : Config n k}, Supp3 r g b y →
      Supp3 r g b (l.foldl (Plurality.frozenStep f r) y) := by
  intro l
  induction l with
  | nil => intro y hy; exact hy
  | cons t l ih => intro y hy; exact ih (hy.frozen hf t)

/-- **`r` dies out.** After `T` rounds, `r` still has a node with probability at
most `0.97^T C_r + T e^{-9n/31250}`. -/
theorem alive_le (hn : 1 ≤ n) {f : Rule k} (hf : Conservative f) (hcm : ClearMajority f)
    {r g b : Fin k} (hrg : r ≠ g) (hgb : g ≠ b) (hrb : r ≠ b) (hδ : deltaCount f r g b r ≤ 1)
    (T : ℕ) {y : Config n k} (hy : Supp3 r g b y) (hlow : LowR r y) :
    expList (Tgt3 n) T (fun l => if 1 ≤ count (runWith f y l) r then (1 : ℝ) else 0)
      ≤ (97 / 100) ^ T * count y r + T * exp (-(9 * n / 31250)) := by
  classical
  have hpt (l : List (Tgt3 n)) : (if 1 ≤ count (runWith f y l) r then (1 : ℝ) else 0)
      ≤ potential r (l.foldl (frozenStep f r) y)
        + (if l.foldl (frozenStep f r) y ∈ {z | Supp3 r g b z ∧ LowR r z} then (0 : ℝ) else 1) := by
    have hi : (0 : ℝ) ≤ if l.foldl (frozenStep f r) y ∈ {z | Supp3 r g b z ∧ LowR r z}
        then (0 : ℝ) else 1 := by split <;> norm_num
    by_cases hz : LowR r (l.foldl (frozenStep f r) y)
    · have hpot : potential r (l.foldl (frozenStep f r) y)
          = count (runWith f y l) r := by
        simp only [potential, hz, ↓reduceIte]
        rw [foldl_frozen_eq l y hz]
      have hmem : l.foldl (frozenStep f r) y ∈ {z | Supp3 r g b z ∧ LowR r z} :=
        ⟨Supp3.foldl_frozen hf l hy, hz⟩
      rw [hpot, if_pos hmem, add_zero]
      split_ifs with h
      · have : (1 : ℝ) ≤ count (runWith f y l) r := by exact_mod_cast h
        linarith
      · linarith [Nat.cast_nonneg (α := ℝ) (count (runWith f y l) r)]
    · have : l.foldl (frozenStep f r) y ∉ {z | Supp3 r g b z ∧ LowR r z} := fun h => hz h.2
      rw [if_neg this]
      have := potential_nonneg r (l.foldl (frozenStep f r) y)
      split_ifs <;> linarith
  have hpot : potential r y = count y r := by simp [potential, hlow]
  calc _ ≤ expList (Tgt3 n) T (fun l => potential r (l.foldl (frozenStep f r) y)
        + (if l.foldl (frozenStep f r) y ∈ {z | Supp3 r g b z ∧ LowR r z} then (0 : ℝ) else 1)) :=
        expList_le_expList hpt
    _ = expList (Tgt3 n) T (fun l => potential r (l.foldl (frozenStep f r) y))
        + expList (Tgt3 n) T (fun l =>
          if l.foldl (frozenStep f r) y ∈ {z | Supp3 r g b z ∧ LowR r z} then (0 : ℝ) else 1) :=
        expList_add _ _ _
    _ ≤ (97 / 100) ^ T * potential r y + T * exp (-(9 * n / 31250)) := by
        gcongr
        · exact frozen_potential_le hn hf hcm hrg hgb hrb hδ T y hy
        · convert frozen_stop_le hn hf hcm hrg hgb hrb hδ T hy hlow using 3
    _ = (97 / 100) ^ T * count y r + T * exp (-(9 * n / 31250)) := by rw [hpot]

/-! ### The counterexample -/

/-- The number `T₀ = ⌈log (8n) / log (100/97)⌉` of rounds after which `r` has died
out with probability at least `3/4`. -/
noncomputable def extinctRounds (n : ℕ) : ℕ :=
  ⌈Real.log ((8 * n : ℕ) : ℝ) / Real.log (100 / 97)⌉₊

lemma extinct_numerics (hL : 20 ≤ Real.log n) :
    (97 / 100 : ℝ) ^ extinctRounds n * n ≤ 1 / 8 ∧
      (extinctRounds n : ℝ) * exp (-(9 * n / 31250)) ≤ 1 / 8 := by
  have hn : 1 ≤ n := one_le_of_log_pos (by linarith)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set L := Real.log n with hLdef
  constructor
  · have h := le_pow_ceil (n := 8 * n) (by omega) (show (1 : ℝ) < 100 / 97 by norm_num)
    have e : ⌈Real.log ((8 * n : ℕ) : ℝ) / Real.log (100 / 97)⌉₊ = extinctRounds n := rfl
    rw [e] at h
    push_cast at h
    have hp : (97 / 100 : ℝ) ^ extinctRounds n = ((100 / 97 : ℝ) ^ extinctRounds n)⁻¹ := by
      rw [← inv_pow]; norm_num
    rw [hp, ← div_eq_inv_mul, div_le_iff₀ (by positivity)]
    linarith
  · have hlq : 3 / 100 ≤ Real.log (100 / 97) := by
      have := sub_one_div_le_log (show (0 : ℝ) < 100 / 97 by norm_num)
      norm_num at this ⊢; linarith
    have hlog8 : Real.log ((8 * n : ℕ) : ℝ) = Real.log 8 + L := by
      push_cast; rw [Real.log_mul (by norm_num) hn0.ne']
    have h8 : Real.log 8 ≤ 7 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8 by norm_num); linarith
    have h80 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ Real.log ((8 * n : ℕ) : ℝ) / Real.log (100 / 97) by
      rw [hlog8]; exact div_nonneg (by linarith) (by linarith))
    have hT : (extinctRounds n : ℝ) ≤ 50 * L := by
      have hdiv : Real.log ((8 * n : ℕ) : ℝ) / Real.log (100 / 97) ≤ (7 + L) / (3 / 100) := by
        rw [hlog8]
        calc (Real.log 8 + L) / Real.log (100 / 97) ≤ (7 + L) / Real.log (100 / 97) :=
              div_le_div_of_nonneg_right (by linarith) (by linarith)
          _ ≤ (7 + L) / (3 / 100) := div_le_div_of_nonneg_left (by linarith) (by norm_num) hlq
      have : (extinctRounds n : ℝ) < (7 + L) / (3 / 100) + 1 := by
        unfold extinctRounds; linarith
      linarith
    -- `e^{9n/31250} ≥ e^{2.5 L} ≥ 21780 L`
    have h1 := mul_le_exp (show (20 : ℝ) ≤ L by linarith)
    have hnL : exp L = n := by rw [hLdef, exp_log hn0]
    have h2 := mul_le_exp (show (20 : ℝ) ≤ 5 / 2 * L by linarith)
    have h3 : exp (5 / 2 * L) ≤ exp (9 * n / 31250) := exp_le_exp.mpr (by linarith)
    rw [exp_neg, ← div_eq_mul_inv, div_le_iff₀ (exp_pos _)]
    nlinarith

/-- The coloring with nodes `< a₁` colored `r`, nodes in `[a₁, a₂)` colored `g`
and the others `b`. -/
def threeColor (n : ℕ) (r g b : Fin k) (a₁ a₂ : ℕ) : Config n k :=
  fun v => if (v : ℕ) < a₁ then r else if (v : ℕ) < a₂ then g else b

/-- **A non-uniform triple defeats the rule.** If `f` has the clear-majority
property and `δ_r ≤ 1` for distinct `r, g, b`, then from `23n/60` nodes of
color `r`, `n/3` of `g` and `17n/60` of `b` (bias `n/20`), consensus on `r`
has probability at most `1/4` at every time. Hence `f` is not an
`(n/20, 1/4)`-solver (for `60 ∣ n`, `log n ≥ 20`). -/
theorem not_solver_of_nonuniform (h60 : 60 ∣ n) (hL : 20 ≤ Real.log n) {f : Rule k}
    (hf : Conservative f) (hcm : ClearMajority f) {r g b : Fin k}
    (hrg : r ≠ g) (hgb : g ≠ b) (hrb : r ≠ b) (hδ : deltaCount f r g b r ≤ 1) :
    ¬ Solver f n (n / 20) (1 / 4) := by
  intro hS
  have hn : 1 ≤ n := one_le_of_log_pos (by linarith)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨q, hq⟩ := h60
  have hq0 : 0 < q := by omega
  have hnq : (n : ℝ) = 60 * q := by exact_mod_cast hq
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq0
  set x := threeColor n r g b (23 * q) (43 * q) with hx
  have hsupp : Supp3 r g b x := fun v => by
    simp only [hx, threeColor]; split_ifs <;> simp
  -- the counts
  have hcr : count x r = 23 * q := by
    unfold count
    have : (univ.filter fun v : Fin n => x v = r)
        = univ.filter fun v : Fin n => (v : ℕ) < 23 * q := by
      ext v; simp only [hx, threeColor, mem_filter, mem_univ, true_and]
      split_ifs with h1 h2 <;> simp [h1, hrg.symm, hrb.symm]
    rw [this, Fin.card_filter_val_lt]; omega
  have hcb : count x b = 17 * q := by
    unfold count
    have : (univ.filter fun v : Fin n => x v = b)
        = univ.filter fun v : Fin n => ¬ (v : ℕ) < 43 * q := by
      ext v; simp only [hx, threeColor, mem_filter, mem_univ, true_and]
      split_ifs with h1 h2 <;> simp [hrb, hgb] <;> omega
    rw [this]
    have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
      (fun v : Fin n => (v : ℕ) < 43 * q)
    rw [Fin.card_filter_val_lt] at h
    simp only [card_univ, Fintype.card_fin] at h
    omega
  have hcg : (count x g : ℝ) = 20 * q := by
    have := sum_count_real x
    rw [sum_eq_three hrg hgb hrb fun c h1 h2 h3 => by
      simp [hsupp.count_eq_zero h1 h2 h3]] at this
    rw [hcr, hcb] at this; push_cast at this; linarith
  -- `r` is the unique plurality color with bias `n/20`
  obtain ⟨hM, hs⟩ := le_bias_of_gap (c := count x) (m := r) (g := 3 * q) (by linarith)
    (by rw [hcr]; push_cast; linarith) fun j hj => by
      rw [hcr]; push_cast
      by_cases hjg : j = g
      · rw [hjg, hcg]; linarith
      by_cases hjb : j = b
      · rw [hjb, hcb]; push_cast; linarith
      rw [hsupp.count_eq_zero hj hjg hjb]; push_cast; linarith
  obtain ⟨T, hT⟩ := hS x r hM (by rw [hnq]; linarith) (1 / 4) (by norm_num)
  -- consensus on `r` needs `r` alive after `T₀` rounds, which is unlikely
  have hlow : LowR r x := by
    change ((count x r : ℕ) : ℝ) ≤ 2 * n / 5
    rw [hcr, hnq]; push_cast; linarith
  have h1 := mono_le_alive hn hf x r T (extinctRounds n)
  have h2 := alive_le hn hf hcm hrg hgb hrb hδ (extinctRounds n) hsupp hlow
  obtain ⟨h3, h4⟩ := extinct_numerics hL
  have hcr' : (count x r : ℝ) ≤ n := by exact_mod_cast count_le x r
  have h5 : (97 / 100 : ℝ) ^ extinctRounds n * count x r ≤ 1 / 8 :=
    le_trans (mul_le_mul_of_nonneg_left hcr' (by positivity)) h3
  linarith

/-- **Theorem 4.8 (b).** If `f` has the clear-majority property and is an
`(n/20, 1/4)`-solver (for `60 ∣ n` and `log n ≥ 20`), then `f` has the uniform
property. -/
theorem theorem_4_8_b (h60 : 60 ∣ n) (hL : 20 ≤ Real.log n) {f : Rule k} (hf : Conservative f)
    (hcm : ClearMajority f) (hS : Solver f n (n / 20) (1 / 4)) : UniformRule f := by
  intro r g b hrg hgb hrb
  have hsum := deltaCount_sum hf hrg hgb hrb
  by_contra hne
  -- some color of the triple has `δ ≤ 1`
  by_cases hr : deltaCount f r g b r ≤ 1
  · exact not_solver_of_nonuniform h60 hL hf hcm hrg hgb hrb hr hS
  by_cases hg : deltaCount f r g b g ≤ 1
  · rw [← deltaCount_swap12] at hg
    exact not_solver_of_nonuniform h60 hL hf hcm hrg.symm hrb hgb hg hS
  · have hb : deltaCount f r g b b ≤ 1 := by omega
    rw [← deltaCount_swap13] at hb
    exact not_solver_of_nonuniform h60 hL hf hcm hgb.symm hrg.symm hrb.symm hb hS

end Plurality
