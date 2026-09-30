import Plurality.Rules

/-!
# Theorem 4.8 (a): a solver must follow the clear majority

Consider two colors `r ≠ b` and only these two colors present, with fractions
`x` and `y = 1 - x`. Under a 3-input rule `f`, a node adopts `r` with
probability `x³ + Δ_r x² y + (3 - Δ_b) x y²`, where `Δ_r = majCount f r b` and
`Δ_b = majCount f b r`. Hence

  `p(x) - x = x y (x (Δ_r - 2) + y (2 - Δ_b))`.

If `Δ_r ≤ 2 ≤ Δ_b` this is `≤ 0` in **every** state, so the number of red nodes
is a supermartingale, its expectation never exceeds its initial value, and from
`5n/8` red nodes (bias `n/4`) the probability that all nodes are red at any time
is at most `5/8` (`not_solver_of_drift`). No optional stopping is needed.

`theorem_4_8_a`: a `(n/4, 1/4)`-solver has, for every pair of colors, either
`Δ_r = Δ_b = 3` (it follows the clear majority on that pair) or
`Δ_r, Δ_b ≤ 1`.

**The remaining case.** The paper's proof also claims the case
`Δ_r, Δ_b ≤ 1`, but it only checks the supermartingale inequality when red is
the majority. In this case `p(x) - x > 0` when red is the minority: the process
is pulled towards an interior point `x* = (2 - Δ_b)/(4 - Δ_r - Δ_b)`, and which
color eventually wins depends on how the process leaves that point, which is
not addressed. That case is left open here.
-/

namespace Plurality

open Finset Real Dynamics
open ThreeMajority (Tgt3 tgt3_nonempty)

variable {n k : ℕ}

lemma majCount_le (f : Rule k) (r b : Fin k) : majCount f r b ≤ 3 := by
  unfold majCount; split_ifs <;> omega

/-- The coloring with the first `a` nodes colored `r` and the others `b`. -/
def twoColor (n : ℕ) (r b : Fin k) (a : ℕ) : Config n k := fun v => if (v : ℕ) < a then r else b

lemma count_twoColor_left {r b : Fin k} (hrb : r ≠ b) {a : ℕ} (ha : a ≤ n) :
    count (twoColor n r b a) r = a := by
  unfold count twoColor
  have : (univ.filter fun v : Fin n => (if (v : ℕ) < a then r else b) = r)
      = univ.filter fun v : Fin n => (v : ℕ) < a := by
    ext v; by_cases h : (v : ℕ) < a <;> simp [h, hrb.symm]
  rw [this, Fin.card_filter_val_lt]
  omega

lemma count_twoColor_right {r b : Fin k} (hrb : r ≠ b) {a : ℕ} (ha : a ≤ n) :
    count (twoColor n r b a) b = n - a := by
  have h1 := count_twoColor_left (n := n) hrb ha
  unfold count twoColor at *
  have : (univ.filter fun v : Fin n => (if (v : ℕ) < a then r else b) = b)
      = univ.filter fun v : Fin n => ¬ (if (v : ℕ) < a then r else b) = r := by
    ext v; by_cases h : (v : ℕ) < a <;> simp [hrb, hrb.symm]
  rw [this]
  have := card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
    (fun v : Fin n => (if (v : ℕ) < a then r else b) = r)
  simp only [card_univ, Fintype.card_fin] at this
  omega

/-- Every node supports `r` or `b`. -/
def Supp2 (r b : Fin k) (y : Config n k) : Prop := ∀ v, y v = r ∨ y v = b

lemma Supp2.stepWith {f : Rule k} (hf : Conservative f) {r b : Fin k} {y : Config n k}
    (hy : Supp2 r b y) (t : Tgt3 n) : Supp2 r b (stepWith f y t) := fun v => by
  change f (y (t v).1) (y (t v).2.1) (y (t v).2.2) = r
    ∨ f (y (t v).1) (y (t v).2.1) (y (t v).2.2) = b
  rcases hf (y (t v).1) (y (t v).2.1) (y (t v).2.2) with h | h | h <;> rw [h] <;> exact hy _

lemma Supp2.count_eq_zero {r b : Fin k} {y : Config n k} (hy : Supp2 r b y) {c : Fin k}
    (hr : c ≠ r) (hb : c ≠ b) : count y c = 0 := by
  unfold count
  rw [card_eq_zero, filter_eq_empty_iff]
  intro v _ hv
  rcases hy v with h | h
  · exact hr (hv.symm.trans h)
  · exact hb (hv.symm.trans h)

lemma sum_eq_two {r b : Fin k} (hrb : r ≠ b) {F : Fin k → ℝ}
    (hF : ∀ c, c ≠ r → c ≠ b → F c = 0) : ∑ c, F c = F r + F b :=
  sum_eq_add r b hrb (fun c _ h => hF c h.1 h.2) (by simp) (by simp)

lemma ite_comp {f : Rule k} {r b u v w : Fin k} (hrb : r ≠ b) (h : f u v w = r ∨ f u v w = b) :
    (if f u v w = r then (1 : ℝ) else 0) = 1 - (if f u v w = b then 1 else 0) := by
  rcases h with h | h <;> simp [h, hrb, hrb.symm]

/-- **The red drift.** With only `r` and `b` present and `Δ_r ≤ 2 ≤ Δ_b`, the
expected number of red nodes does not increase in one round. -/
theorem expected_red_le (hn : 1 ≤ n) {f : Rule k} (hf : Conservative f) {r b : Fin k}
    (hrb : r ≠ b) (hr : majCount f r b ≤ 2) (hb : 2 ≤ majCount f b r) {y : Config n k}
    (hy : Supp2 r b y) :
    avg (fun t : Tgt3 n => (count (stepWith f y t) r : ℝ)) ≤ count y r := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [expected_count_stepWith hn, avg_adopt]
  set w := frac y with hw
  have hw0 : ∀ c, c ≠ r → c ≠ b → w c = 0 := fun c h1 h2 => by
    simp [hw, frac, hy.count_eq_zero h1 h2]
  have hsum : w r + w b = 1 := by
    have := sum_frac hn y
    rwa [sum_eq_two hrb hw0] at this
  have hwr : 0 ≤ w r := frac_nonneg y r
  have hwb : 0 ≤ w b := frac_nonneg y b
  set g : Fin k → Fin k → Fin k → ℝ := fun a b' c => if f a b' c = r then 1 else 0 with hg
  -- expand the triple sum over the two colors present
  have h3 : ∀ a b', ∑ c, w a * w b' * w c * g a b' c
      = w a * w b' * w r * g a b' r + w a * w b' * w b * g a b' b := fun a b' =>
    sum_eq_two hrb fun c h1 h2 => by rw [hw0 c h1 h2]; ring
  rw [sum_congr rfl fun a _ => sum_congr rfl fun b' _ => h3 a b']
  have h2 : ∀ a, ∑ b', (w a * w b' * w r * g a b' r + w a * w b' * w b * g a b' b)
      = (w a * w r * w r * g a r r + w a * w r * w b * g a r b)
        + (w a * w b * w r * g a b r + w a * w b * w b * g a b b) := fun a =>
    sum_eq_two hrb fun c h1 h2 => by rw [hw0 c h1 h2]; ring
  rw [sum_congr rfl fun a _ => h2 a, sum_eq_two hrb fun c h1 h2 => by rw [hw0 c h1 h2]; ring]
  -- the eight colour patterns
  have grrr : g r r r = 1 := by
    simp only [hg]; rcases hf r r r with h | h | h <;> simp [h]
  have gbbb : g b b b = 0 := by
    simp only [hg]; rcases hf b b b with h | h | h <;> simp [h, hrb.symm]
  have hmem (u v w' : Fin k) (hu : u = r ∨ u = b) (hv : v = r ∨ v = b) (hw' : w' = r ∨ w' = b) :
      f u v w' = r ∨ f u v w' = b := by
    rcases hf u v w' with h | h | h <;> rw [h] <;> assumption
  have hΔr : (majCount f r b : ℝ) = g r r b + g r b r + g b r r := by
    simp only [majCount, hg]; push_cast; ring
  have hΔb : (majCount f b r : ℝ)
      = (1 - g b b r) + (1 - g b r b) + (1 - g r b b) := by
    simp only [majCount, hg]
    rw [ite_comp hrb (hmem b b r (Or.inr rfl) (Or.inr rfl) (Or.inl rfl)),
      ite_comp hrb (hmem b r b (Or.inr rfl) (Or.inl rfl) (Or.inr rfl)),
      ite_comp hrb (hmem r b b (Or.inl rfl) (Or.inr rfl) (Or.inr rfl))]
    push_cast; ring
  have hr' : (majCount f r b : ℝ) ≤ 2 := by exact_mod_cast hr
  have hb' : (2 : ℝ) ≤ majCount f b r := by exact_mod_cast hb
  -- `p - x = x² y (Δ_r - 2) + x y² (2 - Δ_b) ≤ 0`
  have hkey : w r * w r * w r * g r r r + w r * w r * w b * g r r b
      + (w r * w b * w r * g r b r + w r * w b * w b * g r b b)
      + (w b * w r * w r * g b r r + w b * w r * w b * g b r b
      + (w b * w b * w r * g b b r + w b * w b * w b * g b b b))
      = w r - (w r ^ 2 * w b * (2 - majCount f r b) + w r * w b ^ 2 * (majCount f b r - 2)) := by
    rw [grrr, gbbb, hΔr, hΔb]
    have : w b = 1 - w r := by linarith
    rw [this]
    ring
  rw [hkey]
  have h1 : 0 ≤ w r ^ 2 * w b * (2 - majCount f r b) := by
    apply mul_nonneg (by positivity); linarith
  have h2 : 0 ≤ w r * w b ^ 2 * (majCount f b r - 2) := by
    apply mul_nonneg (by positivity); linarith
  have : (n : ℝ) * w r = count y r := by
    rw [hw, frac]; field_simp
  nlinarith

/-- **The red count is a supermartingale**: its expectation after `T` rounds is
at most its initial value. -/
theorem expected_red_le_iter (hn : 1 ≤ n) {f : Rule k} (hf : Conservative f) {r b : Fin k}
    (hrb : r ≠ b) (hr : majCount f r b ≤ 2) (hb : 2 ≤ majCount f b r) :
    ∀ (T : ℕ) (y : Config n k), Supp2 r b y →
      expList (Tgt3 n) T (fun l => (count (runWith f y l) r : ℝ)) ≤ count y r := by
  intro T
  induction T with
  | zero => intro y _; simp
  | succ T ih =>
    intro y hy
    rw [expList_succ]
    calc avg (fun t => expList (Tgt3 n) T (fun l => (count (runWith f y (t :: l)) r : ℝ)))
        ≤ avg (fun t : Tgt3 n => (count (stepWith f y t) r : ℝ)) :=
          avg_le_avg fun t => ih _ (hy.stepWith hf t)
      _ ≤ count y r := expected_red_le hn hf hrb hr hb hy

/-- **If `Δ_r ≤ 2 ≤ Δ_b`, the rule is not an `(n/4, 1/4)`-solver.** From `5n/8`
red and `3n/8` blue nodes, all nodes are red at time `T` with probability at
most `5/8`, for every `T`. -/
theorem not_solver_of_drift (h8 : 8 ∣ n) (hn : 1 ≤ n) {f : Rule k} (hf : Conservative f)
    {r b : Fin k} (hrb : r ≠ b) (hr : majCount f r b ≤ 2) (hb : 2 ≤ majCount f b r) :
    ¬ Solver f n (n / 4) (1 / 4) := by
  intro hS
  haveI := tgt3_nonempty hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨q, hq⟩ := h8
  have ha : 5 * q ≤ n := by omega
  set x := twoColor n r b (5 * q) with hx
  have hcr : count x r = 5 * q := count_twoColor_left hrb ha
  have hcb : count x b = 3 * q := by rw [hx, count_twoColor_right hrb ha]; omega
  have hsupp : Supp2 r b x := fun v => by
    simp only [hx, twoColor]; split_ifs <;> simp
  have hqpos : (0 : ℝ) < q := by
    have : 0 < q := by omega
    exact_mod_cast this
  have hnq : (n : ℝ) = 8 * q := by exact_mod_cast hq
  -- `r` is the unique plurality color with bias at least `n/4`
  obtain ⟨hM, hs⟩ := le_bias_of_gap (c := count x) (m := r) (g := 2 * q) (by linarith)
    (by rw [hcr]; push_cast; linarith) fun j hj => by
      by_cases hjb : j = b
      · rw [hjb, hcb, hcr]; push_cast; linarith
      · rw [hsupp.count_eq_zero hj hjb, hcr]; push_cast; linarith
  obtain ⟨T, hT⟩ := hS x r hM (by rw [hnq]; linarith) (1 / 16) (by norm_num)
  -- `P(all red) ≤ 𝔼[red]/n ≤ 5/8`
  have hle : expList (Tgt3 n) T (fun l => if Mono (runWith f x l) r then (1 : ℝ) else 0)
      ≤ expList (Tgt3 n) T (fun l => (1 / (n : ℝ)) * (count (runWith f x l) r : ℝ)) := by
    refine expList_le_expList fun l => ?_
    split_ifs with hm
    · rw [(mono_iff_count _ _).mp hm]; field_simp; rfl
    · positivity
  rw [expList_const_mul] at hle
  have hE := expected_red_le_iter hn hf hrb hr hb T x hsupp
  rw [hcr] at hE
  have : (1 / (n : ℝ)) * expList (Tgt3 n) T (fun l => (count (runWith f x l) r : ℝ)) ≤ 5 / 8 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hn0]
    push_cast at hE
    linarith
  linarith

/-- **Theorem 4.8 (a), proved cases.** If `f` is an `(n/4, 1/4)`-solver (with
`8 ∣ n`), then for every pair of distinct colors either `f` follows the clear
majority on that pair (`Δ_r = Δ_b = 3`) or `Δ_r, Δ_b ≤ 1`. The paper claims
that the second alternative is also impossible; see the module docstring. -/
theorem theorem_4_8_a (h8 : 8 ∣ n) (hn : 1 ≤ n) {f : Rule k} (hf : Conservative f)
    (hS : Solver f n (n / 4) (1 / 4)) {r b : Fin k} (hrb : r ≠ b) :
    (majCount f r b = 3 ∧ majCount f b r = 3) ∨ (majCount f r b ≤ 1 ∧ majCount f b r ≤ 1) := by
  have h1 := majCount_le f r b
  have h2 := majCount_le f b r
  by_contra hne
  by_cases hA : majCount f r b ≤ 2 ∧ 2 ≤ majCount f b r
  · exact not_solver_of_drift h8 hn hf hrb hA.1 hA.2 hS
  · exact not_solver_of_drift h8 hn hf hrb.symm (by omega) (by omega) hS

end Plurality
