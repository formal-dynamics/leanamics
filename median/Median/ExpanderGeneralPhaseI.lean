import Median.ExpanderGeneralLoss
import Median.ExpanderGeneralHitting

/-! # Phase I: a small imbalance grows until the minority is a small fraction

The paper's Lemma 2 and Corollary 2 (Cooper, Elsässer and Radzik, ICALP 2014,
arXiv:1404.7479, Section 4). Throughout, `n = |V|`, `A = majority a x`, `B = minority a x`,
`ν = (A − B)/n` (`imbalance`) and `η = α n / √(A B)` (`phaseEta`). The common hypotheses of
the one-round lemmas are those of the proof of Lemma 2: `0 < c ≤ 1/2`, `0 < α ≤ c^{3/2}/36`,
the mixing hypothesis `MixingProp G d α c`, and `c n ≤ B ≤ A`.

* `expected_gain_ge`: `𝔼 Δ_{BA} ≥ (A² B / n²)(1 − 2η)` (the paper's (hjre21)-(be56sw)).
* `expected_loss_le`: `𝔼 Δ_{AB} ≤ (A B² / n²)(1 + 15η)` (the paper's (eq-upperOnDAB)).
* `gain_tail`: `P(Δ_{BA} ≤ (A² B / n²)(1 − 3η)) ≤ e^{−α² c n / 6}` (the paper's (eq-fger)).
* `loss_tail`: `P(Δ_{AB} ≥ (A B² / n²)(1 + 17η)) ≤ e^{−α² c² n / 2}` (the paper's (eq-fger2)).
* `phaseI_step`: with probability at least `1 − e^{−α² c n / 6} − e^{−α² c² n / 2}`, the new
  imbalance is at least `ν + ν (1 − ν²)/2 − 12 α / √(1 − ν²)` (the paper's (ncnwd-Appx)).
* `growth_small`, `growth_large`: the deterministic consequences `ν' ≥ (5/4) ν` for
  `120 α ≤ ν ≤ 1/2`, and `1 − ν' ≤ (3/4)(1 − ν)` for `1/2 ≤ ν ≤ 1 − 2c`.
* `phaseI`: the paper's Lemma 2, with `K = 120` and an explicit number of rounds: if
  `ν₀ ≥ 120 α`, then within `phaseIRounds ν₀ c` rounds the minority drops to at most `c n`,
  except with probability `phaseIRounds ν₀ c · (e^{−α² c n / 6} + e^{−α² c² n / 2})`.
* `phaseI_expander`: the paper's Corollary 2, `phaseI` for a graph with `λ_G ≤ α`.

The flows are sums of independent indicators over the vertices (`gainCount_eq_sum`,
`lossCount_eq_sum`), with expectations `∑_{v ∈ B} (1 − p_v)²` and `∑_{v ∈ A} p_v²` for
`p_v = d_v^B / d` (`avg_gainCount`, `avg_lossCount`). The combinatorial core of
`expected_loss_le` is `sum_sq_nbCount_le` (`Median.ExpanderGeneralLoss`), and the induction over
the rounds of `phaseI` is `phaseI_of_step` (`Median.ExpanderGeneralHitting`).
-/

namespace Median.ExpanderGeneral
open Finset Dynamics Real

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### The two flows as sums of independent indicators -/

omit [DecidableEq V] in
/-- `Δ_{BA}` as a sum of indicators. -/
lemma gainCount_eq_sum (a : Bool) (x y : V → Bool) :
    (gainCount a x y : ℝ) = ∑ v, if x v ≠ a then 1 - neInd a (y v) else 0 := by
  unfold gainCount
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases hx : x v = a <;> by_cases hy : y v = a <;> simp [hx, hy, neInd]

omit [DecidableEq V] in
/-- `Δ_{AB}` as a sum of indicators. -/
lemma lossCount_eq_sum (a : Bool) (x y : V → Bool) :
    (lossCount a x y : ℝ) = ∑ v, if x v = a then neInd a (y v) else 0 := by
  unfold lossCount
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases hx : x v = a <;> by_cases hy : y v = a <;> simp [hx, hy, neInd]

/-- A vertex of `B` converts to `a` with probability `(1 − p)²`, where `p` is the probability
that one sample differs from `a`. -/
lemma avg_gain_pair {β : Type*} [Fintype β] [Nonempty β] (a xv : Bool) (g : β → Bool) {p : ℝ}
    (hp : avg (fun i => neInd a (g i)) = p) :
    avg (fun q : β × β => if xv ≠ a then 1 - neInd a (med3 xv (g q.1) (g q.2)) else 0)
      = if xv ≠ a then (1 - p) ^ 2 else 0 := by
  by_cases h : xv = a
  · simp [h, avg_const]
  · simp only [ne_eq, h, not_false_eq_true, if_true]
    rw [avg_sub, avg_const, avg_pair a xv g hp, if_neg h]
    ring

/-- A vertex of `A` converts away from `a` with probability `p²`. -/
lemma avg_loss_pair {β : Type*} [Fintype β] [Nonempty β] (a xv : Bool) (g : β → Bool) {p : ℝ}
    (hp : avg (fun i => neInd a (g i)) = p) :
    avg (fun q : β × β => if xv = a then neInd a (med3 xv (g q.1) (g q.2)) else 0)
      = if xv = a then p ^ 2 else 0 := by
  by_cases h : xv = a
  · simp only [h, if_true]
    rw [avg_pair a a g hp, if_pos rfl]
    ring
  · simp [h, avg_const]

variable {G} in
/-- **Expected gain**: `𝔼 Δ_{BA} = ∑_{v ∈ B} (1 − p_v)²` with `p_v = d_v^B / d`. -/
lemma avg_gainCount {d : ℕ} (hd : 0 < d) (hreg : G.IsRegularOfDegree d) (a : Bool)
    (x : V → Bool) :
    avg (fun r : GraphRound G => (gainCount a x (graphStep G x r) : ℝ))
      = ∑ v ∈ univ.filter (fun v => x v ≠ a), (1 - (nbCount G a x v : ℝ) / d) ^ 2 := by
  have hdeg : ∀ v, 0 < G.degree v := fun v => by rw [hreg v]; exact hd
  have := neighborRound_nonempty G hdeg
  simp_rw [gainCount_eq_sum, avg_sum]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hp : avg (fun r : NeighborRound G => neInd a (x (r v))) = (nbCount G a x v : ℝ) / d := by
    rw [avg_neighborRound_eval G hdeg v (fun u => neInd a (x u)), avg_neighbor_neInd hreg]
  exact avg_gain_pair a (x v) (fun r : NeighborRound G => x (r v)) hp

variable {G} in
/-- **Expected loss**: `𝔼 Δ_{AB} = ∑_{v ∈ A} p_v²` with `p_v = d_v^B / d`. -/
lemma avg_lossCount {d : ℕ} (hd : 0 < d) (hreg : G.IsRegularOfDegree d) (a : Bool)
    (x : V → Bool) :
    avg (fun r : GraphRound G => (lossCount a x (graphStep G x r) : ℝ))
      = ∑ v ∈ univ.filter (fun v => x v = a), ((nbCount G a x v : ℝ) / d) ^ 2 := by
  have hdeg : ∀ v, 0 < G.degree v := fun v => by rw [hreg v]; exact hd
  have := neighborRound_nonempty G hdeg
  simp_rw [lossCount_eq_sum, avg_sum]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hp : avg (fun r : NeighborRound G => neInd a (x (r v))) = (nbCount G a x v : ℝ) / d := by
    rw [avg_neighborRound_eval G hdeg v (fun u => neInd a (x u)), avg_neighbor_neInd hreg]
  exact avg_loss_pair a (x v) (fun r : NeighborRound G => x (r v)) hp

/-! ### The parameter `η` -/

omit [DecidableEq V] in
/-- The bounds `2α ≤ η ≤ c/25` on `η = α n / √(A B)` (the paper's (hjcbw671)), for `n > 0`. -/
lemma phaseEta_bounds {c α : ℝ} (hc0 : 0 < c) (hc : c ≤ 1 / 2) (hα0 : 0 < α)
    (hα : α ≤ c * √c / 36) {a : Bool} {x : V → Bool} (hn : 0 < (Fintype.card V : ℝ))
    (hB : c * Fintype.card V ≤ minority a x) (hBA : minority a x ≤ majority a x) :
    0 < phaseEta α a x ∧ 2 * α ≤ phaseEta α a x ∧ phaseEta α a x ≤ c / 25 := by
  have hsum : (majority a x : ℝ) + minority a x = Fintype.card V := by
    exact_mod_cast majority_add_minority a x
  have hBA' : (minority a x : ℝ) ≤ majority a x := by exact_mod_cast hBA
  have hB0 : 0 < (minority a x : ℝ) := lt_of_lt_of_le (mul_pos hc0 hn) hB
  have hAB : 0 < (majority a x : ℝ) * minority a x := mul_pos (by linarith) hB0
  set s := √((majority a x : ℝ) * minority a x) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hAB
  have hss : s * s = (majority a x : ℝ) * minority a x := Real.mul_self_sqrt hAB.le
  have hsc : √c * √c = c := Real.mul_self_sqrt hc0.le
  have hsc0 : 0 ≤ √c := Real.sqrt_nonneg c
  have heta : phaseEta α a x = α * Fintype.card V / s := rfl
  refine ⟨by rw [heta]; exact div_pos (mul_pos hα0 hn) hs0, ?_, ?_⟩
  · rw [heta, le_div_iff₀ hs0]
    have h2s : 2 * s ≤ Fintype.card V := by
      nlinarith [sq_nonneg ((majority a x : ℝ) - minority a x)]
    nlinarith
  · rw [heta, div_le_iff₀ hs0]
    have hα2 : α * α ≤ c * c * c / 1296 := by
      have := mul_le_mul hα hα hα0.le (by positivity)
      nlinarith
    have hA2 : (Fintype.card V : ℝ) ≤ 2 * majority a x := by linarith
    have hABc : c * (Fintype.card V : ℝ) * Fintype.card V ≤ 2 * (s * s) := by
      rw [hss]
      nlinarith
    have hsq : (α * Fintype.card V) * (α * Fintype.card V) ≤ (c / 25 * s) * (c / 25 * s) := by
      have h1 : α * α * ((Fintype.card V : ℝ) * Fintype.card V)
          ≤ c * c * c / 1296 * ((Fintype.card V : ℝ) * Fintype.card V) :=
        mul_le_mul_of_nonneg_right hα2 (by positivity)
      have h2 : c * c * (c * (Fintype.card V : ℝ) * Fintype.card V) ≤ c * c * (2 * (s * s)) :=
        mul_le_mul_of_nonneg_left hABc (by positivity)
      nlinarith
    exact (mul_self_le_mul_self_iff (mul_nonneg hα0.le hn.le) (by positivity)).mpr hsq

/-! ### One round: expectations of the two flows -/

variable {G} in
/-- The core of (hjre21)-(be56sw): `∑_{v ∈ B} (1 − p_v)² ≥ (A² B / n²)(1 − 2η)`, by
Cauchy-Schwarz and the mixing hypothesis for the pair `(A, B)`. -/
lemma sum_gain_ge {d : ℕ} (hd : 0 < d) (hreg : G.IsRegularOfDegree d) {c α : ℝ}
    (hc0 : 0 < c) (hc : c ≤ 1 / 2) (hα0 : 0 < α) (hα : α ≤ c * √c / 36)
    (hmix : MixingProp G d α c) (a : Bool) (x : V → Bool)
    (hB : c * Fintype.card V ≤ minority a x) (hBA : minority a x ≤ majority a x) :
    (majority a x : ℝ) ^ 2 * minority a x / (Fintype.card V : ℝ) ^ 2 * (1 - 2 * phaseEta α a x)
      ≤ ∑ v ∈ univ.filter (fun v => x v ≠ a), (1 - (nbCount G a x v : ℝ) / d) ^ 2 := by
  have hQ0 : 0 ≤ ∑ v ∈ univ.filter (fun v => x v ≠ a), (1 - (nbCount G a x v : ℝ) / d) ^ 2 :=
    Finset.sum_nonneg fun v _ => sq_nonneg _
  rcases (Nat.cast_nonneg (α := ℝ) (Fintype.card V)).eq_or_lt with hn | hn
  · rw [← hn]
    simpa using hQ0
  obtain ⟨hη0, -, hηc⟩ := phaseEta_bounds hc0 hc hα0 hα hn hB hBA
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hsum : (majority a x : ℝ) + minority a x = Fintype.card V := by
    exact_mod_cast majority_add_minority a x
  have hBA' : (minority a x : ℝ) ≤ majority a x := by exact_mod_cast hBA
  have hB0 : 0 < (minority a x : ℝ) := lt_of_lt_of_le (mul_pos hc0 hn) hB
  have hAB : 0 < (majority a x : ℝ) * minority a x := mul_pos (by linarith) hB0
  set Bs := univ.filter (fun v => x v ≠ a) with hBs
  set As := univ.filter (fun v => x v = a) with hAs
  have hBcard : (Bs.card : ℝ) = minority a x := rfl
  have hAcard : (As.card : ℝ) = majority a x := rfl
  set y := ∑ v ∈ Bs, (1 - (nbCount G a x v : ℝ) / d) with hydef
  -- `y = E(B, A) / d = E(A, B) / d`
  have hy : y * d = edgeCount G As Bs := by
    rw [edgeCount_comm, hydef, Finset.sum_mul]
    unfold edgeCount
    push_cast
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [hAs, card_inter_majority hreg]
    field_simp
  -- the mixing hypothesis for `X = A`, `Y = B`
  have hdisj : Disjoint As Bs := Finset.disjoint_filter.mpr fun v _ h1 h2 => h2 h1
  have hsc1 : c * √c ≤ 1 := by
    have : √c ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
    nlinarith [Real.sqrt_nonneg c]
  have hAbig : 2 / 3 * α * (c * √c) * Fintype.card V ≤ As.card := by
    rw [hAcard]
    have h1 : α ≤ 1 / 36 := by linarith
    have h2 : α * (c * √c) ≤ 1 / 36 := by
      nlinarith [mul_nonneg hc0.le (Real.sqrt_nonneg c)]
    nlinarith
  have hmixAB := hmix As Bs hdisj (by rw [hBcard]; exact hB) hAbig
  rw [hAcard, hBcard] at hmixAB
  have hE := (abs_le.mp hmixAB).1
  -- `α √(A B) = (A B / n) η`
  set s := √((majority a x : ℝ) * minority a x) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hAB
  have hss : s * s = (majority a x : ℝ) * minority a x := Real.mul_self_sqrt hAB.le
  have hηs : phaseEta α a x * s = α * Fintype.card V := by
    show α * Fintype.card V / s * s = _
    field_simp
  have hαs : (majority a x : ℝ) * minority a x / Fintype.card V * phaseEta α a x = α * s := by
    rw [← hss, div_mul_eq_mul_div, div_eq_iff hn.ne']
    linear_combination s * hηs
  -- `y ≥ (A B / n)(1 − η) ≥ 0`
  have hyl : (majority a x : ℝ) * minority a x / Fintype.card V * (1 - phaseEta α a x) ≤ y := by
    have h1 : (d : ℝ) * majority a x * minority a x / Fintype.card V
        = d * ((majority a x : ℝ) * minority a x / Fintype.card V) := by ring
    have h2 : (majority a x : ℝ) * minority a x / Fintype.card V * (1 - phaseEta α a x)
        = (majority a x : ℝ) * minority a x / Fintype.card V - α * s := by
      rw [mul_sub, mul_one, hαs]
    rw [h2, ← mul_le_mul_iff_of_pos_left hd']
    nlinarith
  have hyl0 : 0 ≤ (majority a x : ℝ) * minority a x / Fintype.card V * (1 - phaseEta α a x) :=
    mul_nonneg (div_nonneg hAB.le hn.le) (by linarith)
  have hCS : y ^ 2 ≤ Bs.card * ∑ v ∈ Bs, (1 - (nbCount G a x v : ℝ) / d) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [hBcard] at hCS
  calc (majority a x : ℝ) ^ 2 * minority a x / (Fintype.card V : ℝ) ^ 2
        * (1 - 2 * phaseEta α a x)
      ≤ (majority a x : ℝ) ^ 2 * minority a x / (Fintype.card V : ℝ) ^ 2
        * (1 - phaseEta α a x) ^ 2 :=
        mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (phaseEta α a x)]) (by positivity)
    _ = ((majority a x : ℝ) * minority a x / Fintype.card V * (1 - phaseEta α a x)) ^ 2
          / minority a x := by
        field_simp
    _ ≤ y ^ 2 / minority a x :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ hyl0 hyl 2) hB0.le
    _ ≤ ∑ v ∈ Bs, (1 - (nbCount G a x v : ℝ) / d) ^ 2 := by
        rw [div_le_iff₀ hB0]
        linarith

/-- **Expected gain of the majority** (the paper's (hjre21)-(be56sw) in the proof of Lemma 2):
`𝔼 Δ_{BA} = ∑_{v ∈ B} (d_v^A / d)² ≥ E(A, B)² / (B d²) ≥ (A² B / n²)(1 − 2η)`. -/
theorem expected_gain_ge {d : ℕ} (hd : 0 < d) (hreg : G.IsRegularOfDegree d) {c α : ℝ}
    (hc0 : 0 < c) (hc : c ≤ 1 / 2) (hα0 : 0 < α) (hα : α ≤ c * √c / 36)
    (hmix : MixingProp G d α c) (a : Bool) (x : V → Bool)
    (hB : c * Fintype.card V ≤ minority a x) (hBA : minority a x ≤ majority a x) :
    (majority a x : ℝ) ^ 2 * minority a x / (Fintype.card V : ℝ) ^ 2
        * (1 - 2 * phaseEta α a x)
      ≤ avg (fun r : GraphRound G => (gainCount a x (graphStep G x r) : ℝ)) := by
  rw [avg_gainCount hd hreg]
  exact sum_gain_ge hd hreg hc0 hc hα0 hα hmix a x hB hBA

/-- **Expected loss of the majority** (the paper's (eq-upperOnDAB) in the proof of Lemma 2):
`𝔼 Δ_{AB} = ∑_{v ∈ A} (d_v^B / d)² ≤ (A B² / n²)(1 + 15η)`. -/
theorem expected_loss_le {d : ℕ} (hd : 0 < d) (hreg : G.IsRegularOfDegree d) {c α : ℝ}
    (hc0 : 0 < c) (hc : c ≤ 1 / 2) (hα0 : 0 < α) (hα : α ≤ c * √c / 36)
    (hmix : MixingProp G d α c) (a : Bool) (x : V → Bool)
    (hB : c * Fintype.card V ≤ minority a x) (hBA : minority a x ≤ majority a x) :
    avg (fun r : GraphRound G => (lossCount a x (graphStep G x r) : ℝ))
      ≤ (majority a x : ℝ) * (minority a x : ℝ) ^ 2 / (Fintype.card V : ℝ) ^ 2
        * (1 + 15 * phaseEta α a x) := by
  rw [avg_lossCount hd hreg]
  exact sum_sq_nbCount_le hd hreg hc0 hc hα0 hα hmix a x hB hBA

/-! ### One round: concentration -/

omit [Fintype V] [DecidableEq V] in
/-- An indicator has average at most `1`. -/
lemma avg_indicator_le_one {R : Type*} [Fintype R] [Nonempty R] (P : R → Prop)
    [DecidablePred P] : avg (fun r => if P r then (1 : ℝ) else 0) ≤ 1 := by
  calc avg (fun r => if P r then (1 : ℝ) else 0) ≤ avg (fun _ : R => (1 : ℝ)) :=
        avg_le_avg fun r => by split_ifs <;> norm_num
    _ = 1 := avg_const 1

/-- **Lower tail of the gain** (the paper's (eq-fger)):
`P(Δ_{BA} ≤ (A² B / n²)(1 − 3η)) ≤ e^{−α² c n / 6}`. -/
theorem gain_tail {d : ℕ} (hd : 0 < d) (hreg : G.IsRegularOfDegree d) {c α : ℝ}
    (hc0 : 0 < c) (hc : c ≤ 1 / 2) (hα0 : 0 < α) (hα : α ≤ c * √c / 36)
    (hmix : MixingProp G d α c) (a : Bool) (x : V → Bool)
    (hB : c * Fintype.card V ≤ minority a x) (hBA : minority a x ≤ majority a x) :
    avg (fun r : GraphRound G =>
        if (gainCount a x (graphStep G x r) : ℝ)
            ≤ (majority a x : ℝ) ^ 2 * minority a x / (Fintype.card V : ℝ) ^ 2
              * (1 - 3 * phaseEta α a x) then (1 : ℝ) else 0)
      ≤ exp (-(α ^ 2 * c * Fintype.card V / 6)) := by
  have hdeg : ∀ v, 0 < G.degree v := fun v => by rw [hreg v]; exact hd
  have := neighborRound_nonempty G hdeg
  rcases (Nat.cast_nonneg (α := ℝ) (Fintype.card V)).eq_or_lt with hn | hn
  · rw [← hn, mul_zero, zero_div, neg_zero, exp_zero]
    exact avg_indicator_le_one _
  obtain ⟨hη0, h2α, hηc⟩ := phaseEta_bounds hc0 hc hα0 hα hn hB hBA
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  rw [← avg_equiv (roundEquiv hreg)]
  set Y : V → Fin d × Fin d → ℝ := fun v q => if x v ≠ a then
    1 - neInd a (med3 (x v) (x (nbrEquiv hreg v q.1)) (x (nbrEquiv hreg v q.2))) else 0 with hYdef
  have hY : ∀ v q, Y v q = 0 ∨ Y v q = 1 := fun v q => by
    simp only [hYdef, neInd]
    split_ifs <;> simp
  have hsum (ω : V → Fin d × Fin d) :
      (gainCount a x (graphStep G x (roundEquiv hreg ω)) : ℝ) = ∑ v, Y v (ω v) := by
    rw [gainCount_eq_sum]
    rfl
  have hv (v : V) :
      avg (Y v) = if x v ≠ a then (1 - (nbCount G a x v : ℝ) / d) ^ 2 else 0 := by
    have hp : avg (fun i : Fin d => neInd a (x (nbrEquiv hreg v i)))
        = (nbCount G a x v : ℝ) / d := by
      rw [avg_equiv (nbrEquiv hreg v) (fun u : G.neighborSet v => neInd a (x u)),
        avg_neighbor_neInd hreg]
    exact avg_gain_pair a (x v) (fun i : Fin d => x (nbrEquiv hreg v i)) hp
  set K := (majority a x : ℝ) ^ 2 * minority a x / (Fintype.card V : ℝ) ^ 2 with hK
  have hμ : K * (1 - 2 * phaseEta α a x) ≤ ∑ v, avg (Y v) := by
    simp_rw [hv]
    rw [← Finset.sum_filter]
    exact sum_gain_ge hd hreg hc0 hc hα0 hα hmix a x hB hBA
  have key := avg_chernoff_lower Y hY hη0 (by linarith) hμ
  simp_rw [hsum]
  have hK0 : 0 ≤ K := by positivity
  have hincl : K * (1 - 3 * phaseEta α a x)
      ≤ (1 - phaseEta α a x) * (K * (1 - 2 * phaseEta α a x)) := by
    nlinarith [mul_nonneg hK0 (sq_nonneg (phaseEta α a x))]
  refine le_trans (avg_le_avg fun ω => ?_) (key.trans ?_)
  · by_cases h1 : ∑ v, Y v (ω v) ≤ K * (1 - 3 * phaseEta α a x)
    · rw [if_pos h1, if_pos (h1.trans hincl)]
    · rw [if_neg h1]
      split_ifs <;> norm_num
  · rw [exp_le_exp, neg_le_neg_iff]
    have hsum' : (majority a x : ℝ) + minority a x = Fintype.card V := by
      exact_mod_cast majority_add_minority a x
    have hBA' : (minority a x : ℝ) ≤ majority a x := by exact_mod_cast hBA
    have hA2 : (Fintype.card V : ℝ) ^ 2 / 4 ≤ (majority a x : ℝ) ^ 2 := by nlinarith
    have hKc : c * Fintype.card V / 4 ≤ K := by
      rw [hK, le_div_iff₀ (by positivity)]
      have := mul_le_mul hA2 hB (by positivity) (by positivity)
      nlinarith
    have hμ8 : c * Fintype.card V / 8 ≤ K * (1 - 2 * phaseEta α a x) := by nlinarith
    have hη2 : 4 * α ^ 2 ≤ phaseEta α a x ^ 2 := by nlinarith
    have := mul_le_mul hη2 hμ8 (by positivity) (sq_nonneg _)
    nlinarith [mul_pos (mul_pos (pow_pos hα0 2) hc0) hn]

/-- **Upper tail of the loss** (the paper's (eq-fger2)):
`P(Δ_{AB} ≥ (A B² / n²)(1 + 17η)) ≤ e^{−α² c² n / 2}`. -/
theorem loss_tail {d : ℕ} (hd : 0 < d) (hreg : G.IsRegularOfDegree d) {c α : ℝ}
    (hc0 : 0 < c) (hc : c ≤ 1 / 2) (hα0 : 0 < α) (hα : α ≤ c * √c / 36)
    (hmix : MixingProp G d α c) (a : Bool) (x : V → Bool)
    (hB : c * Fintype.card V ≤ minority a x) (hBA : minority a x ≤ majority a x) :
    avg (fun r : GraphRound G =>
        if (majority a x : ℝ) * (minority a x : ℝ) ^ 2 / (Fintype.card V : ℝ) ^ 2
              * (1 + 17 * phaseEta α a x)
            ≤ (lossCount a x (graphStep G x r) : ℝ) then (1 : ℝ) else 0)
      ≤ exp (-(α ^ 2 * c ^ 2 * Fintype.card V / 2)) := by
  have hdeg : ∀ v, 0 < G.degree v := fun v => by rw [hreg v]; exact hd
  have := neighborRound_nonempty G hdeg
  rcases (Nat.cast_nonneg (α := ℝ) (Fintype.card V)).eq_or_lt with hn | hn
  · rw [← hn, mul_zero, zero_div, neg_zero, exp_zero]
    exact avg_indicator_le_one _
  obtain ⟨hη0, h2α, hηc⟩ := phaseEta_bounds hc0 hc hα0 hα hn hB hBA
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  rw [← avg_equiv (roundEquiv hreg)]
  set Y : V → Fin d × Fin d → ℝ := fun v q => if x v = a then
    neInd a (med3 (x v) (x (nbrEquiv hreg v q.1)) (x (nbrEquiv hreg v q.2))) else 0 with hYdef
  have hY : ∀ v q, Y v q = 0 ∨ Y v q = 1 := fun v q => by
    simp only [hYdef, neInd]
    split_ifs <;> simp
  have hsum (ω : V → Fin d × Fin d) :
      (lossCount a x (graphStep G x (roundEquiv hreg ω)) : ℝ) = ∑ v, Y v (ω v) := by
    rw [lossCount_eq_sum]
    rfl
  have hv (v : V) : avg (Y v) = if x v = a then ((nbCount G a x v : ℝ) / d) ^ 2 else 0 := by
    have hp : avg (fun i : Fin d => neInd a (x (nbrEquiv hreg v i)))
        = (nbCount G a x v : ℝ) / d := by
      rw [avg_equiv (nbrEquiv hreg v) (fun u : G.neighborSet v => neInd a (x u)),
        avg_neighbor_neInd hreg]
    exact avg_loss_pair a (x v) (fun i : Fin d => x (nbrEquiv hreg v i)) hp
  set K := (majority a x : ℝ) * (minority a x : ℝ) ^ 2 / (Fintype.card V : ℝ) ^ 2 with hK
  have hμ : ∑ v, avg (Y v) ≤ K * (1 + 15 * phaseEta α a x) := by
    simp_rw [hv]
    rw [← Finset.sum_filter]
    exact sum_sq_nbCount_le hd hreg hc0 hc hα0 hα hmix a x hB hBA
  have key := avg_chernoff_upper Y hY hη0 hμ
  simp_rw [hsum]
  have hK0 : 0 ≤ K := by positivity
  have hincl : (1 + phaseEta α a x) * (K * (1 + 15 * phaseEta α a x))
      ≤ K * (1 + 17 * phaseEta α a x) := by
    have : 15 * phaseEta α a x ^ 2 ≤ phaseEta α a x := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this hK0]
  refine le_trans (avg_le_avg fun ω => ?_) (key.trans ?_)
  · by_cases h1 : K * (1 + 17 * phaseEta α a x) ≤ ∑ v, Y v (ω v)
    · rw [if_pos h1, if_pos (hincl.trans h1)]
    · rw [if_neg h1]
      split_ifs <;> norm_num
  · rw [exp_le_exp, neg_le_neg_iff, le_div_iff₀ (by linarith)]
    have hsum' : (majority a x : ℝ) + minority a x = Fintype.card V := by
      exact_mod_cast majority_add_minority a x
    have hBA' : (minority a x : ℝ) ≤ majority a x := by exact_mod_cast hBA
    have hB2 : c ^ 2 * (Fintype.card V : ℝ) ^ 2 ≤ (minority a x : ℝ) ^ 2 := by
      have := mul_le_mul hB hB (by positivity) (by positivity)
      nlinarith
    have hKc : c ^ 2 * Fintype.card V / 2 ≤ K := by
      rw [hK, le_div_iff₀ (by positivity)]
      have := mul_le_mul (show (Fintype.card V : ℝ) / 2 ≤ majority a x by linarith) hB2
        (by positivity) (by positivity)
      nlinarith
    have hμ2 : c ^ 2 * Fintype.card V / 2 ≤ K * (1 + 15 * phaseEta α a x) := by nlinarith
    have hη2 : 4 * α ^ 2 ≤ phaseEta α a x ^ 2 := by nlinarith
    have := mul_le_mul hη2 hμ2 (by positivity) (sq_nonneg _)
    nlinarith [mul_pos (mul_pos (pow_pos hα0 2) (pow_pos hc0 2)) hn]

/-- The algebra of (bchwc): if `Δ_{BA} > (A² B / n²)(1 − 3η)` and `Δ_{AB} < (A B² / n²)(1 + 17η)`
with `B ≤ A`, `A + B = n`, then `ν' = ν + 2 (Δ_{BA} − Δ_{AB}) / n` is at least
`ν + ν (1 − ν²)/2 − 6η`, written with `ν = (A − B)/n` and `1 − ν² = 4 A B / n²`. -/
lemma phaseI_step_algebra {A B N η g l : ℝ} (hN : 0 < N) (hsum : A + B = N) (hBA : B ≤ A)
    (hB0 : 0 ≤ B) (hη0 : 0 ≤ η) (hg : A ^ 2 * B / N ^ 2 * (1 - 3 * η) < g)
    (hl : l < A * B ^ 2 / N ^ 2 * (1 + 17 * η)) :
    (A - B) / N + (A - B) / N * (4 * (A * B) / N ^ 2) / 2 - 6 * η
      ≤ (A - B) / N + 2 * (g - l) / N := by
  have hN2 : 0 < N ^ 2 := by positivity
  rw [div_mul_eq_mul_div, div_lt_iff₀ hN2] at hg
  rw [div_mul_eq_mul_div, lt_div_iff₀ hN2] at hl
  have hAB : 0 ≤ A * B := mul_nonneg (by linarith) hB0
  have e1 := mul_le_mul_of_nonneg_left (show 3 * A + 17 * B ≤ 10 * N by linarith)
    (mul_nonneg hη0 hAB)
  have e2 := mul_le_mul_of_nonneg_left
    (show 4 * (A * B) ≤ N ^ 2 by nlinarith [sq_nonneg (A - B)]) (mul_nonneg hη0 hN.le)
  have e3 : 0 ≤ η * N ^ 3 := by positivity
  have hkey : A * B * (A - B) - 3 * η * N ^ 3 ≤ (g - l) * N ^ 2 := by
    nlinarith only [hg, hl, e1, e2, e3]
  have hfrac : (A - B) / N * (4 * (A * B) / N ^ 2) / 2 - 6 * η - 2 * (g - l) / N
      = 2 * (A * B * (A - B) - 3 * η * N ^ 3 - (g - l) * N ^ 2) / N ^ 3 := by
    field_simp
    ring
  have : 2 * (A * B * (A - B) - 3 * η * N ^ 3 - (g - l) * N ^ 2) / N ^ 3 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  linarith

/-- **One round of Phase I** (the paper's (bchwc) and (ncnwd-Appx)): with probability at least
`1 − e^{−α² c n / 6} − e^{−α² c² n / 2}`, the new imbalance `ν'` satisfies
`ν' ≥ ν + ν (1 − ν²)/2 − 12 α / √(1 − ν²)`. -/
theorem phaseI_step {d : ℕ} (hd : 0 < d) (hreg : G.IsRegularOfDegree d) {c α : ℝ}
    (hc0 : 0 < c) (hc : c ≤ 1 / 2) (hα0 : 0 < α) (hα : α ≤ c * √c / 36)
    (hmix : MixingProp G d α c) (a : Bool) (x : V → Bool)
    (hB : c * Fintype.card V ≤ minority a x) (hBA : minority a x ≤ majority a x) :
    1 - exp (-(α ^ 2 * c * Fintype.card V / 6)) - exp (-(α ^ 2 * c ^ 2 * Fintype.card V / 2))
      ≤ avg (fun r : GraphRound G =>
          if imbalance a x + imbalance a x * (1 - imbalance a x ^ 2) / 2
                - 12 * α / √(1 - imbalance a x ^ 2)
              ≤ imbalance a (graphStep G x r) then (1 : ℝ) else 0) := by
  have hdeg : ∀ v, 0 < G.degree v := fun v => by rw [hreg v]; exact hd
  have := neighborRound_nonempty G hdeg
  have he1 := exp_pos (-(α ^ 2 * c * Fintype.card V / 6))
  have he2 := exp_pos (-(α ^ 2 * c ^ 2 * Fintype.card V / 2))
  rcases (Nat.cast_nonneg (α := ℝ) (Fintype.card V)).eq_or_lt with hn | hn
  · -- no vertices: the imbalance is `0` and the bound holds in every round
    have h0 : ∀ y : V → Bool, imbalance a y = 0 := fun y => by simp [imbalance, ← hn]
    have hpt : ∀ r : GraphRound G, (if imbalance a x + imbalance a x * (1 - imbalance a x ^ 2) / 2
        - 12 * α / √(1 - imbalance a x ^ 2) ≤ imbalance a (graphStep G x r) then (1 : ℝ) else 0)
          = 1 := fun r => by
      rw [if_pos]
      simp only [h0]
      norm_num
      linarith
    simp_rw [hpt, avg_const]
    linarith
  obtain ⟨hη0, -, hηc⟩ := phaseEta_bounds hc0 hc hα0 hα hn hB hBA
  have hsum : (majority a x : ℝ) + minority a x = Fintype.card V := by
    exact_mod_cast majority_add_minority a x
  have hBA' : (minority a x : ℝ) ≤ majority a x := by exact_mod_cast hBA
  have hB0 : 0 < (minority a x : ℝ) := lt_of_lt_of_le (mul_pos hc0 hn) hB
  have hAB : 0 < (majority a x : ℝ) * minority a x := mul_pos (by linarith) hB0
  set g₀ := (majority a x : ℝ) ^ 2 * minority a x / (Fintype.card V : ℝ) ^ 2
    * (1 - 3 * phaseEta α a x) with hg₀
  set l₀ := (majority a x : ℝ) * (minority a x : ℝ) ^ 2 / (Fintype.card V : ℝ) ^ 2
    * (1 + 17 * phaseEta α a x) with hl₀
  have hgt := gain_tail G hd hreg hc0 hc hα0 hα hmix a x hB hBA
  have hlt := loss_tail G hd hreg hc0 hc hα0 hα hmix a x hB hBA
  -- `√(1 − ν²) = 2 √(A B) / n`
  set s := √((majority a x : ℝ) * minority a x) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hAB
  have hss : s * s = (majority a x : ℝ) * minority a x := Real.mul_self_sqrt hAB.le
  have hν : imbalance a x = ((majority a x : ℝ) - minority a x) / Fintype.card V := rfl
  have h1ν : 1 - imbalance a x ^ 2
      = 4 * ((majority a x : ℝ) * minority a x) / (Fintype.card V : ℝ) ^ 2 := by
    rw [hν]
    field_simp
    nlinarith
  have hsqrt : √(1 - imbalance a x ^ 2) = 2 * s / Fintype.card V := by
    rw [h1ν, ← hss, show 4 * (s * s) / (Fintype.card V : ℝ) ^ 2
      = (2 * s / Fintype.card V) ^ 2 by field_simp; ring]
    exact Real.sqrt_sq (by positivity)
  have h12 : 12 * α / √(1 - imbalance a x ^ 2) = 6 * phaseEta α a x := by
    rw [hsqrt]
    show _ = 6 * (α * Fintype.card V / s)
    field_simp
    ring
  -- on the good event, the bound holds
  have hgood : ∀ r : GraphRound G, g₀ < gainCount a x (graphStep G x r) →
      (lossCount a x (graphStep G x r) : ℝ) < l₀ →
      imbalance a x + imbalance a x * (1 - imbalance a x ^ 2) / 2
        - 12 * α / √(1 - imbalance a x ^ 2) ≤ imbalance a (graphStep G x r) := by
    intro r hg hl
    set y := graphStep G x r with hy
    have hy1 : (minority a y : ℝ) + gainCount a x y = minority a x + lossCount a x y := by
      exact_mod_cast minority_add_gainCount a x y
    have hy2 : (majority a y : ℝ) + minority a y = Fintype.card V := by
      exact_mod_cast majority_add_minority a y
    have hν' : imbalance a y = imbalance a x
        + 2 * ((gainCount a x y : ℝ) - lossCount a x y) / Fintype.card V := by
      rw [hν, ← add_div, imbalance, div_left_inj' hn.ne']
      linarith
    rw [hν', h12, h1ν, hν]
    exact phaseI_step_algebra hn hsum hBA' hB0.le hη0.le hg hl
  have hpt (r : GraphRound G) :
      1 - (if (gainCount a x (graphStep G x r) : ℝ) ≤ g₀ then (1 : ℝ) else 0)
        - (if l₀ ≤ (lossCount a x (graphStep G x r) : ℝ) then (1 : ℝ) else 0)
        ≤ if imbalance a x + imbalance a x * (1 - imbalance a x ^ 2) / 2
            - 12 * α / √(1 - imbalance a x ^ 2) ≤ imbalance a (graphStep G x r)
          then (1 : ℝ) else 0 := by
    by_cases hg : (gainCount a x (graphStep G x r) : ℝ) ≤ g₀
    · rw [if_pos hg]
      split_ifs <;> norm_num
    · by_cases hl : l₀ ≤ (lossCount a x (graphStep G x r) : ℝ)
      · rw [if_pos hl]
        split_ifs <;> norm_num
      · rw [if_neg hg, if_neg hl, if_pos (hgood r (not_le.mp hg) (not_le.mp hl))]
        norm_num
  calc 1 - exp (-(α ^ 2 * c * Fintype.card V / 6)) - exp (-(α ^ 2 * c ^ 2 * Fintype.card V / 2))
      ≤ 1 - avg (fun r : GraphRound G =>
          if (gainCount a x (graphStep G x r) : ℝ) ≤ g₀ then (1 : ℝ) else 0)
        - avg (fun r : GraphRound G =>
          if l₀ ≤ (lossCount a x (graphStep G x r) : ℝ) then (1 : ℝ) else 0) := by
        linarith
    _ = avg (fun r : GraphRound G =>
          1 - (if (gainCount a x (graphStep G x r) : ℝ) ≤ g₀ then (1 : ℝ) else 0)
            - (if l₀ ≤ (lossCount a x (graphStep G x r) : ℝ) then (1 : ℝ) else 0)) := by
        rw [avg_sub, avg_sub, avg_const]
    _ ≤ _ := avg_le_avg hpt

/-! ### The deterministic recursion -/

/-- While `120 α ≤ ν ≤ 1/2`, the recursion (ncnwd-Appx) gives `ν' ≥ (5/4) ν`. -/
theorem growth_small {α ν ν' : ℝ} (hα : 0 ≤ α) (h1 : 120 * α ≤ ν) (h2 : ν ≤ 1 / 2)
    (h : ν + ν * (1 - ν ^ 2) / 2 - 12 * α / √(1 - ν ^ 2) ≤ ν') : 5 / 4 * ν ≤ ν' := by
  have hν0 : 0 ≤ ν := by linarith
  have hs : 4 / 5 ≤ √(1 - ν ^ 2) := by
    rw [show (4 / 5 : ℝ) = √((4 / 5) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hpos : 0 < √(1 - ν ^ 2) := by linarith
  have h3 : 12 * α / √(1 - ν ^ 2) ≤ 15 * α := by
    rw [div_le_iff₀ hpos]
    nlinarith
  have h4 : 3 / 8 * ν ≤ ν * (1 - ν ^ 2) / 2 := by nlinarith
  linarith

/-- While `1/2 ≤ ν ≤ 1 − 2c` and `α ≤ c^{3/2}/36`, the recursion (ncnwd-Appx) gives
`δ' ≤ (3/4) δ` for `δ = 1 − ν` (the paper's (ncnwd-Appx334x)). -/
theorem growth_large {c α ν ν' : ℝ} (hc : 0 < c) (hα0 : 0 ≤ α) (hα : α ≤ c * √c / 36)
    (h1 : 1 / 2 ≤ ν) (h2 : ν ≤ 1 - 2 * c)
    (h : ν + ν * (1 - ν ^ 2) / 2 - 12 * α / √(1 - ν ^ 2) ≤ ν') :
    1 - ν' ≤ 3 / 4 * (1 - ν) := by
  have hsc : 0 ≤ √c := Real.sqrt_nonneg c
  have h3 : √3 * √c ≤ √(1 - ν ^ 2) := by
    rw [← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have h43 : 4 / 3 ≤ √3 := by
    rw [show (4 / 3 : ℝ) = √((4 / 3) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hcpos : 0 < √c := Real.sqrt_pos.mpr hc
  have hpos : 0 < √(1 - ν ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have h5 : 48 * α ≤ c * √(1 - ν ^ 2) := by nlinarith
  have h6 : 12 * α / √(1 - ν ^ 2) ≤ c / 4 := by
    rw [div_le_iff₀ hpos]
    linarith
  have h7 : 3 / 8 * (1 - ν) ≤ ν * (1 - ν ^ 2) / 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 - ν by linarith) (show 0 ≤ ν * (1 + ν) - 3 / 4 by nlinarith)]
  linarith

/-! ### Lemma 2 and Corollary 2 -/

omit [DecidableEq V] in
/-- A minority of at least `c n` means an imbalance of at most `1 − 2c`. -/
lemma imbalance_le_of_le_minority {c : ℝ} (hc : c ≤ 1 / 2) {a : Bool} {x : V → Bool}
    (hB : c * Fintype.card V ≤ minority a x) : imbalance a x ≤ 1 - 2 * c := by
  have hsum : (majority a x : ℝ) + minority a x = Fintype.card V := by
    exact_mod_cast majority_add_minority a x
  unfold imbalance
  rcases (Nat.cast_nonneg (α := ℝ) (Fintype.card V)).eq_or_lt with hn | hn
  · rw [← hn, div_zero]
    linarith
  · rw [div_le_iff₀ hn]
    linarith


/-- **Lemma 2** (Phase I, with `K = 120`): on a `d`-regular graph satisfying the mixing
hypothesis `MixingProp G d α c` with `0 < c ≤ 1/2` and `0 < α ≤ c^{3/2}/36`, if the initial
imbalance is `ν₀ ≥ 120 α`, then within `T₁ = phaseIRounds ν₀ c` rounds the minority drops to at
most `c n` (at some time `t ≤ T₁`), except with probability at most
`T₁ (e^{−α² c n / 6} + e^{−α² c² n / 2})`. -/
theorem phaseI {d : ℕ} (hd : 0 < d) (hreg : G.IsRegularOfDegree d) {c α : ℝ}
    (hc0 : 0 < c) (hc : c ≤ 1 / 2) (hα0 : 0 < α) (hα : α ≤ c * √c / 36)
    (hmix : MixingProp G d α c) (a : Bool) (x : V → Bool) (hν : 120 * α ≤ imbalance a x) :
    1 - (phaseIRounds (imbalance a x) c : ℝ)
        * (exp (-(α ^ 2 * c * Fintype.card V / 6)) + exp (-(α ^ 2 * c ^ 2 * Fintype.card V / 2)))
      ≤ expList (GraphRound G) (phaseIRounds (imbalance a x) c)
          (fun l => if ∃ t ≤ phaseIRounds (imbalance a x) c,
              (minority a (graphRun G x (l.take t)) : ℝ) ≤ c * Fintype.card V
            then (1 : ℝ) else 0) := by
  refine phaseI_of_step hd hreg hc0 hα0 (add_nonneg (exp_pos _).le (exp_pos _).le) a ?_ x hν
  intro y hB hBA
  have hle : imbalance a y ≤ 1 - 2 * c := imbalance_le_of_le_minority hc hB
  rw [← sub_sub]
  refine (phaseI_step G hd hreg hc0 hc hα0 hα hmix a y hB hBA).trans (avg_le_avg fun r => ?_)
  by_cases h1 : imbalance a y + imbalance a y * (1 - imbalance a y ^ 2) / 2
      - 12 * α / √(1 - imbalance a y ^ 2) ≤ imbalance a (graphStep G y r)
  · rw [if_pos h1, if_pos ⟨fun h120 hhalf => growth_small hα0.le h120 hhalf h1,
      fun hhalf => growth_large hc0 hα0.le hα hhalf hle h1⟩]
  · rw [if_neg h1]
    split_ifs <;> norm_num

/-- **Corollary 2** (Phase I on expanders): `phaseI` for a `d`-regular graph with `λ_G ≤ α`,
through the expander mixing lemma (`mixingProp_of_lambdaG`). -/
theorem phaseI_expander {d : ℕ} (hd : 0 < d) (hreg : G.IsRegularOfDegree d) {c α : ℝ}
    (hc0 : 0 < c) (hc : c ≤ 1 / 2) (hα0 : 0 < α) (hα : α ≤ c * √c / 36)
    (hlam : lambdaG G d ≤ α) (a : Bool) (x : V → Bool) (hν : 120 * α ≤ imbalance a x) :
    1 - (phaseIRounds (imbalance a x) c : ℝ)
        * (exp (-(α ^ 2 * c * Fintype.card V / 6)) + exp (-(α ^ 2 * c ^ 2 * Fintype.card V / 2)))
      ≤ expList (GraphRound G) (phaseIRounds (imbalance a x) c)
          (fun l => if ∃ t ≤ phaseIRounds (imbalance a x) c,
              (minority a (graphRun G x (l.take t)) : ℝ) ≤ c * Fintype.card V
            then (1 : ℝ) else 0) :=
  phaseI G hd hreg hc0 hc hα0 hα (mixingProp_of_lambdaG G hreg hlam c) a x hν

end Median.ExpanderGeneral
