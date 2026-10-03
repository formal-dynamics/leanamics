import Median.Defs
import Dynamics.Concentration

/-! # The binary median dynamics: one round as a sum of independent coordinates

With two values, the median rule keeps a node's value unless both sampled nodes
hold the other one; a node holding `true` ends `true` unless both samples are
`false`, and vice versa. The number of `true` nodes after one round is therefore
a sum over the nodes of independent `{0,1}` coordinates, one per node, each
depending only on that node's own pair of samples. This file develops the
corresponding bookkeeping:

* `med3` on `Bool` is `max` / `min` of the two sampled values;
* the counts as real sums (`ones`, `falsesR`, `gapR`);
* the exact one-round expectations: with `a` `true` nodes, `m` `false` nodes and
  gap `g = a - m`, `𝔼[ones'] = a + a m g / n²` and `𝔼[m'] = m - a m g / n²`
  (the `p ↦ 3p² - 2p³` map, with `p = a/n`);
* Hoeffding and Bernstein tails for the two counts (`Dynamics.Concentration`),
  and Markov's inequality `P[m' ≥ 1] ≤ 𝔼[m']`.
-/

namespace Median

open Finset Real Dynamics

/-! ### The median of three Bools -/

/-- A `true` node takes the maximum of its two samples. -/
lemma med3_true (b c : Bool) : med3 (true : Bool) b c = max b c := by
  unfold med3; cases b <;> cases c <;> simp

/-- A `false` node takes the minimum of its two samples. -/
lemma med3_false (b c : Bool) : med3 (false : Bool) b c = min b c := by
  unfold med3; cases b <;> cases c <;> simp

/-! ### Counts as real sums -/

variable {n : ℕ}

/-- Number of `false` nodes, as a real. -/
def falsesR (x : Config n Bool) : ℝ := (n : ℝ) - (ones x : ℝ)

/-- The gap `ones - falses`, as a real. -/
def gapR (x : Config n Bool) : ℝ := (ones x : ℝ) - falsesR x

lemma ones_le (x : Config n Bool) : ones x ≤ n := by
  have := card_le_card (filter_subset (fun v => x v = true) univ)
  simpa [ones] using this

lemma falsesR_nonneg (x : Config n Bool) : 0 ≤ falsesR x := by
  have := ones_le x
  simp [falsesR]
  omega

lemma gapR_le (x : Config n Bool) : gapR x ≤ n := by
  have h := ones_le x
  simp only [gapR, falsesR]
  have : (ones x : ℝ) ≤ n := by exact_mod_cast h
  linarith

/-- The cast of the natural difference `n - ones x`. -/
lemma cast_nat_sub (x : Config n Bool) : ((n - ones x : ℕ) : ℝ) = falsesR x :=
  Nat.cast_sub (ones_le x)

lemma sum_ite_true_false (x : Config n Bool) :
    (∑ v, (if x v = true then (1 : ℝ) else 0)) + ∑ v, (if x v = false then (1 : ℝ) else 0)
      = (n : ℝ) := by
  have h : ∀ v : Fin n, (if x v = true then (1 : ℝ) else 0)
      + (if x v = false then 1 else 0) = 1 := by
    intro v; cases x v <;> simp
  calc (∑ v, (if x v = true then (1 : ℝ) else 0)) + ∑ v, (if x v = false then (1 : ℝ) else 0)
      = ∑ v, ((if x v = true then (1 : ℝ) else 0) + (if x v = false then 1 else 0)) :=
        (Finset.sum_add_distrib).symm
    _ = ∑ v, (1 : ℝ) := Finset.sum_congr rfl fun v _ => h v
    _ = (n : ℝ) := by simp

lemma ones_eq_sum (x : Config n Bool) :
    (ones x : ℝ) = ∑ v, (if x v = true then (1 : ℝ) else 0) :=
  Finset.natCast_card_filter _ univ

lemma falsesR_eq_sum (x : Config n Bool) :
    falsesR x = ∑ v, (if x v = false then (1 : ℝ) else 0) := by
  have h1 := ones_eq_sum x
  have h2 := sum_ite_true_false x
  simp only [falsesR]
  linarith

/-- Only the all-`true` configuration has no `false` node. -/
lemma eq_true_iff_falsesR_zero {x : Config n Bool} : x = (fun _ => true) ↔ falsesR x = 0 := by
  constructor
  · intro h
    simp [falsesR, h, ones]
  · intro h
    funext v
    by_cases hv : x v = true
    · exact hv
    · exfalso
      have hvf : x v = false := by
        rcases Bool.eq_false_or_eq_true (x v) with h | h
        · exact absurd h hv
        · exact h
      have h1 : (1 : ℝ) ≤ ∑ w, (if x w = false then (1 : ℝ) else 0) := by
        calc (1 : ℝ) = (if x v = false then (1 : ℝ) else 0) := by simp [hvf]
          _ ≤ ∑ w, (if x w = false then (1 : ℝ) else 0) :=
              Finset.single_le_sum (f := fun w => (if x w = false then (1 : ℝ) else 0))
                (fun w _ => by split <;> norm_num) (mem_univ v)
      rw [falsesR_eq_sum] at h
      linarith

/-! ### One round as a sum of independent coordinates -/

/-- The `{0,1}` coordinate of node `v`: whether `v` holds `true` after one round. -/
def coord (x : Config n Bool) (v : Fin n) (p : Fin n × Fin n) : ℝ :=
  if med3 (x v) (x p.1) (x p.2) = true then 1 else 0

/-- The complementary coordinate: whether `v` holds `false` after one round. -/
def fcoord (x : Config n Bool) (v : Fin n) (p : Fin n × Fin n) : ℝ := 1 - coord x v p

lemma coord_zero_one (x : Config n Bool) (v : Fin n) (p : Fin n × Fin n) :
    coord x v p = 0 ∨ coord x v p = 1 := by
  unfold coord
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

lemma fcoord_zero_one (x : Config n Bool) (v : Fin n) (p : Fin n × Fin n) :
    fcoord x v p = 0 ∨ fcoord x v p = 1 := by
  unfold fcoord
  rcases coord_zero_one x v p with h | h <;> simp [h]

lemma coord_nonneg (x : Config n Bool) (v : Fin n) (p : Fin n × Fin n) : 0 ≤ coord x v p := by
  rcases coord_zero_one x v p with h | h <;> simp [h]

lemma fcoord_nonneg (x : Config n Bool) (v : Fin n) (p : Fin n × Fin n) : 0 ≤ fcoord x v p := by
  rcases fcoord_zero_one x v p with h | h <;> simp [h]

lemma fcoord_le_one (x : Config n Bool) (v : Fin n) (p : Fin n × Fin n) : fcoord x v p ≤ 1 := by
  unfold fcoord; linarith [coord_nonneg x v p]

/-- The number of `true` nodes after a round is the sum of the coordinates. -/
lemma ones_step_sum (x : Config n Bool) (r : Round n) :
    (ones (step x r) : ℝ) = ∑ v, coord x v (r v) := by
  rw [ones_eq_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [coord, step]

/-- The number of `false` nodes after a round is the sum of the complementary
coordinates. -/
lemma falses_step_sum (x : Config n Bool) (r : Round n) :
    falsesR (step x r) = ∑ v, fcoord x v (r v) := by
  have h1 := ones_step_sum x r
  simp only [falsesR, fcoord]
  rw [sum_sub_distrib]
  have hcard : ∑ v : Fin n, (1 : ℝ) = n := by simp
  rw [hcard]
  linarith

/-! ### Per-node expectations -/

lemma avg_false_ind (x : Config n Bool) :
    avg (fun u : Fin n => (if x u = false then (1 : ℝ) else 0)) = falsesR x / n := by
  rw [avg_indicator]
  have h : ((univ.filter fun u => x u = false).card : ℝ) = falsesR x := by
    rw [Finset.natCast_card_filter]
    exact (falsesR_eq_sum x).symm
  rw [h]
  simp

lemma avg_true_ind (x : Config n Bool) :
    avg (fun u : Fin n => (if x u = true then (1 : ℝ) else 0)) = (ones x : ℝ) / n := by
  unfold avg
  rw [ones_eq_sum]
  simp

/-- A `true` node stays `true` unless both samples are `false`. -/
lemma avg_coord_of_true (x : Config n Bool) [NeZero n] {v : Fin n} (hv : x v = true) :
    avg (coord x v) = 1 - (falsesR x / n) ^ 2 := by
  have hpt : ∀ p : Fin n × Fin n,
      coord x v p
        = 1 - (if x p.1 = false then (1 : ℝ) else 0) * (if x p.2 = false then 1 else 0) := by
    intro p
    simp only [coord, hv, med3_true]
    cases hb : x p.1 <;> cases hc : x p.2 <;> simp
  have hfun : coord x v
      = fun p : Fin n × Fin n =>
        1 - (if x p.1 = false then (1 : ℝ) else 0) * (if x p.2 = false then 1 else 0) :=
    funext hpt
  rw [hfun, avg_sub, avg_const]
  have havg : avg (fun p : Fin n × Fin n =>
      (if x p.1 = false then (1 : ℝ) else 0) * (if x p.2 = false then 1 else 0))
      = avg (fun u : Fin n => (if x u = false then (1 : ℝ) else 0))
        * avg (fun u : Fin n => (if x u = false then (1 : ℝ) else 0)) :=
    avg_mul_prod (fun u : Fin n => (if x u = false then (1 : ℝ) else 0))
      (fun u : Fin n => (if x u = false then (1 : ℝ) else 0))
  rw [havg, avg_false_ind]
  ring

/-- A `false` node turns `true` only if both samples are `true`. -/
lemma avg_coord_of_false (x : Config n Bool) [NeZero n] {v : Fin n} (hv : x v = false) :
    avg (coord x v) = ((ones x : ℝ) / n) ^ 2 := by
  have hpt : ∀ p : Fin n × Fin n,
      coord x v p = (if x p.1 = true then (1 : ℝ) else 0) * (if x p.2 = true then 1 else 0) := by
    intro p
    simp only [coord, hv, med3_false]
    cases hb : x p.1 <;> cases hc : x p.2 <;> simp
  have hfun : coord x v
      = fun p : Fin n × Fin n =>
        (if x p.1 = true then (1 : ℝ) else 0) * (if x p.2 = true then 1 else 0) :=
    funext hpt
  rw [hfun]
  have havg : avg (fun p : Fin n × Fin n =>
      (if x p.1 = true then (1 : ℝ) else 0) * (if x p.2 = true then 1 else 0))
      = avg (fun u : Fin n => (if x u = true then (1 : ℝ) else 0))
        * avg (fun u : Fin n => (if x u = true then (1 : ℝ) else 0)) :=
    avg_mul_prod (fun u : Fin n => (if x u = true then (1 : ℝ) else 0))
      (fun u : Fin n => (if x u = true then (1 : ℝ) else 0))
  rw [havg, avg_true_ind]
  ring

/-- The expected number of `true` nodes after one round. -/
lemma sum_avg_coord (x : Config n Bool) [NeZero n] :
    ∑ v, avg (coord x v)
      = (ones x : ℝ) + (ones x : ℝ) * falsesR x * gapR x / n ^ 2 := by
  have hper : ∀ v : Fin n, avg (coord x v)
      = (if x v = true then (1 : ℝ) else 0) * (1 - (falsesR x / n) ^ 2)
        + (if x v = false then (1 : ℝ) else 0) * ((ones x : ℝ) / n) ^ 2 := by
    intro v
    by_cases hb : x v = true
    · rw [avg_coord_of_true x hb]
      simp [hb]
    · have hb' : x v = false := by
        rcases Bool.eq_false_or_eq_true (x v) with h | h
        · exact absurd h hb
        · exact h
      rw [avg_coord_of_false x hb']
      simp [hb']
  simp only [hper]
  rw [sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
    ← ones_eq_sum x, ← falsesR_eq_sum x]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  simp only [gapR, falsesR]
  field_simp
  ring

/-- The expected number of `false` nodes after one round. -/
lemma sum_avg_fcoord (x : Config n Bool) [NeZero n] :
    ∑ v, avg (fcoord x v)
      = falsesR x - (ones x : ℝ) * falsesR x * gapR x / n ^ 2 := by
  have hper : ∀ v : Fin n, avg (fcoord x v) = 1 - avg (coord x v) := by
    intro v
    unfold fcoord
    rw [avg_sub, avg_const]
  have hsum : ∑ v, avg (fcoord x v) = ∑ v, (1 - avg (coord x v)) :=
    Finset.sum_congr rfl fun v _ => hper v
  rw [hsum, sum_sub_distrib]
  have hcard : ∑ v : Fin n, (1 : ℝ) = n := by simp
  rw [hcard, sum_avg_coord x]
  simp only [gapR, falsesR]
  ring

/-! ### Expectation bounds -/

lemma falses_plus_ones (x : Config n Bool) : (ones x : ℝ) + falsesR x = n := by
  simp [falsesR]

lemma gapR_eq (x : Config n Bool) : gapR x = (ones x : ℝ) - falsesR x := rfl

/-- Multiplying both sides of a `≤` by a positive factor preserves it. -/
lemma le_of_mul_le_mul_right' {p q d : ℝ} (hd : 0 < d) (h : p * d ≤ q * d) : p ≤ q := by
  by_contra hc
  push Not at hc
  have := mul_lt_mul_of_pos_right hc hd
  linarith

/-- The product of the two counts is `(n² - gap²)/4`. -/
lemma ones_mul_falses (x : Config n Bool) [NeZero n] :
    (ones x : ℝ) * falsesR x = ((n : ℝ) ^ 2 - gapR x ^ 2) / 4 := by
  have e1 : (ones x : ℝ) + falsesR x = n := falses_plus_ones x
  have e2 : (ones x : ℝ) - falsesR x = gapR x := gapR_eq x
  rw [← e1, ← e2]
  ring

/-- The expected number of `false` nodes after one round is at most `3m²/n`. -/
lemma expfalses_le (x : Config n Bool) [NeZero n] :
    ∑ v, avg (fcoord x v) ≤ 3 * falsesR x ^ 2 / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne n))
  have hn2 : (0 : ℝ) < n ^ 2 := by positivity
  have hm0 : 0 ≤ falsesR x := falsesR_nonneg x
  have ha : (ones x : ℝ) = n - falsesR x := by
    have := falses_plus_ones x
    linarith
  have hg : gapR x = n - 2 * falsesR x := by
    have h1 := falses_plus_ones x
    have h2 := gapR_eq x
    linarith
  rw [sum_avg_fcoord]
  refine le_of_mul_le_mul_right' hn2 ?_
  have hl : (falsesR x - (ones x : ℝ) * falsesR x * gapR x / n ^ 2) * n ^ 2
      = falsesR x * n ^ 2 - (ones x : ℝ) * falsesR x * gapR x := by
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
    field_simp

  have hr : (3 * falsesR x ^ 2 / n) * n ^ 2 = 3 * falsesR x ^ 2 * n := by
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
    field_simp

  rw [hl, hr, ha, hg]
  have hring : (3 * falsesR x ^ 2 * n - (falsesR x * n ^ 2
      - (n - falsesR x) * falsesR x * (n - 2 * falsesR x))) = 2 * falsesR x ^ 3 := by
    ring
  have h2 : (0 : ℝ) ≤ falsesR x ^ 3 := pow_nonneg hm0 3
  linarith

/-- Below `n/4` false nodes, the expected number of `false` nodes drops by a
factor `3/4`: `𝔼[m'] ≤ (3/4) m`. -/
lemma expfalses_le_three_fourth (x : Config n Bool) [NeZero n]
    (hm : falsesR x ≤ n / 4) : ∑ v, avg (fcoord x v) ≤ 3 / 4 * falsesR x := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne n))
  have hm0 : 0 ≤ falsesR x := falsesR_nonneg x
  have h4 : 4 * falsesR x ≤ n := by linarith
  refine (expfalses_le x).trans ?_
  refine le_of_mul_le_mul_right' hn0 ?_
  have hl : (3 * falsesR x ^ 2 / n) * n = 3 * falsesR x ^ 2 := by
    field_simp

  rw [hl]
  have hring : 3 * falsesR x * n - 3 * falsesR x ^ 2 * 4
      = 3 * falsesR x * (n - 4 * falsesR x) := by
    ring
  have hpos : (0 : ℝ) ≤ 3 * falsesR x * (n - 4 * falsesR x) :=
    mul_nonneg (mul_nonneg (by norm_num) hm0) (sub_nonneg.mpr h4)
  nlinarith [hring, hpos]

/-- Below `n/4` false nodes, `𝔼[m'] ≤ (5/8) m`. -/
lemma expfalses_le_five_eighth (x : Config n Bool) [NeZero n]
    (hm : falsesR x ≤ n / 4) : ∑ v, avg (fcoord x v) ≤ 5 / 8 * falsesR x := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  have hn2 : (0 : ℝ) < n ^ 2 := by positivity
  have hm0 : 0 ≤ falsesR x := falsesR_nonneg x
  have ha : (ones x : ℝ) = n - falsesR x := by
    have := falses_plus_ones x
    linarith
  have hg : gapR x = n - 2 * falsesR x := by
    have h1 := falses_plus_ones x
    have h2 := gapR_eq x
    linarith
  have h4 : 4 * falsesR x ≤ n := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne n))
    linarith
  rw [sum_avg_fcoord]
  refine le_of_mul_le_mul_right' hn2 ?_
  have hl : (falsesR x - (ones x : ℝ) * falsesR x * gapR x / n ^ 2) * n ^ 2
      = falsesR x * n ^ 2 - (ones x : ℝ) * falsesR x * gapR x := by
    field_simp

  rw [hl, ha, hg]
  have hring : 8 * (n - falsesR x) * (n - 2 * falsesR x) - 3 * n * n
      = (n - 4 * falsesR x) * (5 * n - 4 * falsesR x) := by
    ring
  have h5 : 4 * falsesR x ≤ 5 * n := by linarith
  have hpos : (0 : ℝ) ≤ (n - 4 * falsesR x) * (5 * n - 4 * falsesR x) :=
    mul_nonneg (sub_nonneg.mpr h4) (sub_nonneg.mpr h5)
  have hprod : (0 : ℝ) ≤ falsesR x * ((n - 4 * falsesR x) * (5 * n - 4 * falsesR x)) :=
    mul_nonneg hm0 hpos
  nlinarith [hring, hpos, hprod]

/-- While the gap is at most `n/2`, the expected number of `true` nodes after one
round satisfies `n/2 + (11/16) g ≤ 𝔼[ones']`. -/
lemma expones_ge (x : Config n Bool) [NeZero n]
    (hg0 : 0 ≤ gapR x) (hg : gapR x ≤ n / 2) :
    n / 2 + 11 / 16 * gapR x ≤ ∑ v, avg (coord x v) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  have hn2 : (0 : ℝ) < n ^ 2 := by positivity
  have h4 : 4 * gapR x ^ 2 ≤ n ^ 2 := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne n))
    nlinarith [hg0, hg]
  have ha2 : (ones x : ℝ) = ((n : ℝ) + gapR x) / 2 := by
    have e1 := falses_plus_ones x
    have e2 := gapR_eq x
    linarith
  have ham4 := ones_mul_falses x
  rw [sum_avg_coord]
  refine le_of_mul_le_mul_right' hn2 ?_
  have hr : ((ones x : ℝ) + (ones x : ℝ) * falsesR x * gapR x / n ^ 2) * n ^ 2
      = (ones x : ℝ) * n ^ 2 + (ones x : ℝ) * falsesR x * gapR x := by
    field_simp

  rw [hr, ham4, ha2]
  have hpos : (0 : ℝ) ≤ gapR x * (n ^ 2 - 4 * gapR x ^ 2) :=
    mul_nonneg hg0 (sub_nonneg.mpr h4)
  have hring : (((n : ℝ) + gapR x) / 2) * n ^ 2 + gapR x * (((n : ℝ) ^ 2 - gapR x ^ 2) / 4)
      - (n / 2 + 11 / 16 * gapR x) * n ^ 2 = gapR x * (n ^ 2 - 4 * gapR x ^ 2) / 16 := by
    field_simp
    ring
  nlinarith [hring, hpos]

/-! ### Concentration for one round -/

/-- **Hoeffding's inequality, lower tail**: for independent `{0,1}` coordinates,
`P(X + λ ≤ 𝔼X) ≤ exp(-2λ²/n)`. -/
lemma avg_hoeffding_lower {n : ℕ} {γ : Type*} [Fintype γ] [Nonempty γ]
    (Y : Fin n → γ → ℝ) (hY : ∀ i x, Y i x = 0 ∨ Y i x = 1) {lam : ℝ} (hlam : 0 ≤ lam) :
    avg (fun ω : Fin n → γ =>
        if ∑ i, Y i (ω i) + lam ≤ ∑ i, avg (Y i) then (1 : ℝ) else 0)
      ≤ exp (-(2 * lam ^ 2 / n)) := by
  have hYc : ∀ i x, (1 - Y i x) = 0 ∨ (1 - Y i x) = 1 := by
    intro i y
    rcases hY i y with h | h <;> simp [h]
  have hB := avg_hoeffding (Y := fun i y => 1 - Y i y) hYc hlam
  have hsum : ∀ ω : Fin n → γ, ∑ i, (1 - Y i (ω i)) = (n : ℝ) - ∑ i, Y i (ω i) := by
    intro ω
    rw [sum_sub_distrib]
    simp
  have hsumavg : ∑ i, avg (fun y => 1 - Y i y) = (n : ℝ) - ∑ i, avg (Y i) := by
    have havg1 : ∀ i, avg (fun y => 1 - Y i y) = 1 - avg (Y i) := by
      intro i
      rw [avg_sub, avg_const]
    simp only [havg1]
    rw [sum_sub_distrib]
    simp
  have hcond : ∀ ω : Fin n → γ,
      ((∑ i, avg (fun y => 1 - Y i y)) + lam ≤ ∑ i, (1 - Y i (ω i)))
        ↔ (∑ i, Y i (ω i) + lam ≤ ∑ i, avg (Y i)) := by
    intro ω
    rw [hsumavg, hsum ω]
    constructor <;> intro h <;> linarith
  have heq : (fun ω : Fin n → γ =>
        if (∑ i, avg (fun y => 1 - Y i y)) + lam ≤ ∑ i, (1 - Y i (ω i)) then (1 : ℝ) else 0)
      = fun ω : Fin n → γ =>
        if ∑ i, Y i (ω i) + lam ≤ ∑ i, avg (Y i) then (1 : ℝ) else 0 := by
    funext ω
    simp only [hcond ω]
  rwa [heq] at hB

/-- Probability that one round produces at most `𝔼 - lam` `true` nodes. -/
lemma ones_tail_lower (x : Config n Bool) [NeZero n] {lam : ℝ} (hlam : 0 ≤ lam) :
    avg (fun r : Round n =>
        if (ones (step x r) : ℝ) + lam ≤ ∑ v, avg (coord x v) then (1 : ℝ) else 0)
      ≤ exp (-(2 * lam ^ 2 / n)) := by
  have hev : (fun r : Round n =>
        if (ones (step x r) : ℝ) + lam ≤ ∑ v, avg (coord x v) then (1 : ℝ) else 0)
      = fun ω : Fin n → Fin n × Fin n =>
        if ∑ v, coord x v (ω v) + lam ≤ ∑ v, avg (coord x v) then (1 : ℝ) else 0 := by
    funext r
    simp only [ones_step_sum]
  rw [hev]
  exact avg_hoeffding_lower (coord x) (coord_zero_one x) hlam

/-- Probability that one round produces at least `𝔼 + lam` `false` nodes. -/
lemma falses_tail_upper (x : Config n Bool) [NeZero n] {lam : ℝ} (hlam : 0 ≤ lam) :
    avg (fun r : Round n =>
        if ∑ v, avg (fcoord x v) + lam ≤ falsesR (step x r) then (1 : ℝ) else 0)
      ≤ exp (-(2 * lam ^ 2 / n)) := by
  have hev : (fun r : Round n =>
        if ∑ v, avg (fcoord x v) + lam ≤ falsesR (step x r) then (1 : ℝ) else 0)
      = fun ω : Fin n → Fin n × Fin n =>
        if (∑ v, avg (fcoord x v)) + lam ≤ ∑ v, fcoord x v (ω v) then (1 : ℝ) else 0 := by
    funext r
    simp only [falses_step_sum]
  rw [hev]
  exact avg_hoeffding (fcoord x) (fcoord_zero_one x) hlam

/-- The variance of a `{0,1}`-valued coordinate is at most its mean. -/
lemma variance_fcoord_le (x : Config n Bool) [NeZero n] (v : Fin n) :
    variance (fcoord x v) ≤ avg (fcoord x v) := by
  have h1 : variance (fcoord x v) ≤ avg (fun p => fcoord x v p ^ 2) :=
    variance_le_avg_sq _
  have h2 : avg (fun p : Fin n × Fin n => fcoord x v p ^ 2) = avg (fcoord x v) := by
    have hfun : (fun p : Fin n × Fin n => fcoord x v p ^ 2) = fcoord x v := by
      funext p
      rcases fcoord_zero_one x v p with h | h <;> simp [h]
    rw [hfun]
  rw [h2] at h1
  exact h1

/-- Bernstein's bound for the number of `false` nodes after one round. -/
lemma falses_tail_bernstein (x : Config n Bool) [NeZero n] {lam σ2 : ℝ}
    (hlam : 0 ≤ lam) (hσ0 : 0 < σ2) (hvar : ∑ v, variance (fcoord x v) ≤ σ2) :
    avg (fun r : Round n =>
        if ∑ v, avg (fcoord x v) + lam ≤ falsesR (step x r) then (1 : ℝ) else 0)
      ≤ exp (-(lam ^ 2 / (2 * σ2 * (1 + lam / (3 * σ2))))) := by
  have hev : (fun r : Round n =>
        if ∑ v, avg (fcoord x v) + lam ≤ falsesR (step x r) then (1 : ℝ) else 0)
      = fun ω : Fin n → Fin n × Fin n =>
        if (∑ v, avg (fcoord x v)) + lam ≤ ∑ v, fcoord x v (ω v) then (1 : ℝ) else 0 := by
    funext r
    simp only [falses_step_sum]
  rw [hev]
  have hYb : ∀ v p, fcoord x v p - avg (fcoord x v) ≤ 1 := by
    intro v p
    have h0 : 0 ≤ avg (fcoord x v) := avg_nonneg fun p => fcoord_nonneg x v p
    have h1 := fcoord_le_one x v p
    linarith
  have hB := avg_bernstein (fcoord x) (by norm_num : (0 : ℝ) < 1) hYb hvar hσ0 hlam
  rw [show 1 + 1 * lam / (3 * σ2) = 1 + lam / (3 * σ2) from by ring] at hB
  exact hB

/-- **Markov's inequality**: the probability of a `false` node after one round is
at most the expected number of `false` nodes. -/
lemma falses_tail_markov (x : Config n Bool) [NeZero n] :
    avg (fun r : Round n => if 1 ≤ falsesR (step x r) then (1 : ℝ) else 0)
      ≤ ∑ v, avg (fcoord x v) := by
  have hle : ∀ r : Round n,
      (if 1 ≤ falsesR (step x r) then (1 : ℝ) else 0) ≤ ∑ v, fcoord x v (r v) := by
    intro r
    by_cases h : 1 ≤ falsesR (step x r)
    · rw [if_pos h]
      rw [falses_step_sum] at h
      exact h
    · rw [if_neg h]
      exact sum_nonneg fun v _ => fcoord_nonneg x v (r v)
  calc avg (fun r : Round n => if 1 ≤ falsesR (step x r) then (1 : ℝ) else 0)
      ≤ avg (fun r : Round n => ∑ v, fcoord x v (r v)) := avg_le_avg hle
    _ = ∑ v : Fin n, avg (fun r : Round n => fcoord x v (r v)) := avg_sum univ _
    _ = ∑ v : Fin n, avg (fcoord x v) := by
        refine Finset.sum_congr rfl fun v _ => avg_eval n v _

end Median
