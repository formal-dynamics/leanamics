import ThreeMajority.ManyOpinionsBreaking
import ThreeMajority.ManyOpinionsDropping
import ThreeMajority.AnyStartMain

/-!
# 3-Majority with many colours reaches consensus (BCNPT16, Theorem 3.1; roadmap MAJ-12 (a))

Theorem 3.1 of Becchetti, Clementi, Natale, Pasquale, Trevisan, *Stabilizing consensus with many
opinions*, SODA 2016, arXiv:1508.06782 (BCNPT16 below): from any configuration with
`k ≤ n^{1/3 − ε}` colours, 3-Majority reaches consensus within
`O((k² √(log n) + k log n)(k + log n))` rounds w.h.p. The proof has two steps.

* `phase_colour_dies`: from `j ≥ 2` colours, one colour dies within
  `O(j² √(log n) + j log n)` rounds with probability at least `1/5` (symmetry breaking,
  Lemma 3.3, then dropping, Lemmas 3.4 and 3.5, composed at the hitting time by
  `hitProb_mul_le_event`). The paper says `1/4`, the product of the probabilities `1/2` of
  Lemmas 3.3 and 3.5, ignoring the failure probability of Lemma 3.4.
* `consensus_of_phases`: if every phase of `L` rounds removes a colour with probability at
  least `p`, then after `M` phases consensus fails with probability at most
  `(1 − p/2)^M 2^k` (the potential `2^{#colours}`).

`consensus_many_opinions` is Theorem 3.1 under the condition `C k³ log n ≤ n`, and
`bcnpt16Phase2_of_pos` is Theorem 3.1 as stated in the paper: it proves the hypothesis
`Bcnpt16Phase2 ε` of roadmap MAJ-6 (b), for every `ε > 0`, without changing it. Hence
`threeMaj_anyStart_consensus_unconditional`: Theorem 4 of Berenbrink, Clementi, Elsässer, Kling,
Mallmann-Trenn, Natale (PODC 2017) without hypothesis.
-/

namespace ThreeMajority

open Finset Dynamics

/-- From a state where the symmetry is broken for `j` colours (`BrokenSymmetry j`), fewer than
`j` colours remain after the two dropping stages (`t₃` rounds of Lemma 3.4, then `t₄` rounds of
Lemma 3.5) with probability at least `2/5`. The two stages are hypotheses here. -/
lemma two_fifths_le_event_of_broken {n : ℕ} [NeZero n] {j t₃ t₄ : ℕ} {C₃ : ℝ}
    (hst1 : ∀ (x : Fin n → Fin n) (a : Fin n), numColours x ≤ j →
      (colourCount x a : ℝ) ≤ n / j - 16 * √(j * n * Real.log n) →
      expList (Tgt3 n) t₃
        (fun l => if C₃ * j ^ 2 * Real.log n < colourCount (runCol x l) a then 1 else 0) ≤ 1 / n)
    (hst2 : ∀ (x : Fin n → Fin n) (a : Fin n), numColours x ≤ j →
      (colourCount x a : ℝ) ≤ n / (2 * j) →
      1 / 2 ≤ expList (Tgt3 n) t₄ (fun l => if colourCount (runCol x l) a = 0 then 1 else 0))
    (hthr : C₃ * j ^ 2 * Real.log n ≤ n / (2 * j)) (hn5 : (5 : ℝ) ≤ n)
    (b : Fin n → Fin n) (hb : BrokenSymmetry j b) :
    (2 : ℝ) / 5 ≤ (Kernel.ofStep (stepCol (n := n) (σ := Fin n))).event
      (fun y => numColours y < j) (t₃ + t₄) b := by
  rw [event_ofStep_stepCol]
  rcases hb with hb | ⟨hbj, a, ha0, hathr⟩
  · have h1 : (fun l => if numColours (runCol b l) < j then (1 : ℝ) else 0) = fun _ => 1 :=
      funext fun l => if_pos ((numColours_runCol_le b l).trans_lt hb)
    rw [h1, expList_const]
    norm_num
  · have hst := hst1 b a hbj hathr
    -- a phase-2 start: at most `C₃ j² log n ≤ n/(2j)` agents of colour `a`
    have hinner (l₁ : List (Tgt3 n)) :
        (1 / 2 : ℝ) * (1 - if C₃ * j ^ 2 * Real.log n < colourCount (runCol b l₁) a then 1 else 0)
          ≤ expList (Tgt3 n) t₄
            (fun l₂ => if colourCount (runCol (runCol b l₁) l₂) a = 0 then 1 else 0) := by
      split_ifs with hbig
      · simp only [sub_self, mul_zero]
        exact expList_nonneg fun _ => by split_ifs <;> norm_num
      · push Not at hbig
        have := hst2 (runCol b l₁) a ((numColours_runCol_le b l₁).trans hbj) (hbig.trans hthr)
        linarith
    have hn1 : 1 / (n : ℝ) ≤ 1 / 5 := one_div_le_one_div_of_le (by norm_num) hn5
    calc (2 : ℝ) / 5 ≤ 1 / 2 * (1 - 1 / n) := by linarith
      _ ≤ 1 / 2 * (1 - expList (Tgt3 n) t₃
            (fun l => if C₃ * j ^ 2 * Real.log n < colourCount (runCol b l) a then 1 else 0)) := by
          gcongr
      _ = expList (Tgt3 n) t₃ (fun l₁ => (1 / 2 : ℝ) *
            (1 - if C₃ * j ^ 2 * Real.log n < colourCount (runCol b l₁) a then 1 else 0)) := by
          have h : (fun l₁ => (1 / 2 : ℝ) *
              (1 - if C₃ * j ^ 2 * Real.log n < colourCount (runCol b l₁) a then 1 else 0)) =
              fun l₁ => 1 / 2 + (-(1 / 2) : ℝ) *
                (if C₃ * j ^ 2 * Real.log n < colourCount (runCol b l₁) a then 1 else 0) :=
            funext fun l₁ => by ring
          rw [h, expList_add, expList_const, expList_const_mul]
          ring
      _ ≤ expList (Tgt3 n) t₃ (fun l₁ => expList (Tgt3 n) t₄
            (fun l₂ => if colourCount (runCol (runCol b l₁) l₂) a = 0 then 1 else 0)) :=
          expList_le_expList hinner
      _ = expList (Tgt3 n) (t₃ + t₄)
            (fun l => if colourCount (runCol b l) a = 0 then 1 else 0) := by
          rw [expList_append]
          simp only [runCol_append]
      _ ≤ expList (Tgt3 n) (t₃ + t₄) (fun l => if numColours (runCol b l) < j then 1 else 0) :=
          expList_le_expList fun l => by
            split_ifs with h1 h2
            · exact le_rfl
            · exact absurd ((numColours_runCol_lt_of_dead b l ha0 h1).trans_le hbj) h2
            · norm_num
            · exact le_rfl

/-- **One phase** (BCNPT16, proof of Theorem 3.1): there is `C` such that, from every
configuration `c` with `j ≥ 2` colours and `C j³ log n ≤ n`, after any
`t ≥ C (j² √(log n) + j log n)` rounds fewer than `j` colours remain with probability at least
`1/5`. -/
theorem phase_colour_dies :
    ∃ C : ℝ, ∀ (n : ℕ) (c : Fin n → Fin n), 2 ≤ numColours c →
      C * (numColours c : ℝ) ^ 3 * Real.log n ≤ n →
      ∀ t : ℕ, C * ((numColours c : ℝ) ^ 2 * √(Real.log n) + numColours c * Real.log n) ≤ t →
        1 / 5 ≤ expList (Tgt3 n) t
          (fun l => if numColours (runCol c l) < numColours c then 1 else 0) := by
  obtain ⟨C₂, hC₂⟩ := symmetry_breaking
  obtain ⟨C₃, hC₃⟩ := dropping_stage1
  obtain ⟨C₄, hC₄⟩ := dropping_stage2
  refine ⟨2 * (|C₂| + |C₃| + |C₄|) + 3, fun n c hc2 hcond t ht => ?_⟩
  have hkn : numColours c ≤ n := by
    simpa [numColours] using card_image_le (s := (univ : Finset (Fin n))) (f := c)
  haveI : NeZero n := ⟨by omega⟩
  have hhit := hC₂ n c hc2
  generalize hj : numColours c = j at hc2 hcond ht hhit ⊢
  -- arithmetic facts
  have a₂ := abs_nonneg C₂
  have a₃ := abs_nonneg C₃
  have a₄ := abs_nonneg C₄
  have hL : 0.6931471803 ≤ Real.log n :=
    Real.log_two_gt_d9.le.trans (Real.log_le_log (by norm_num) (by exact_mod_cast (by omega)))
  have hL0 : 0 ≤ Real.log n := by linarith
  have hsq : 0 ≤ √(Real.log n) := Real.sqrt_nonneg _
  have hj2 : (2 : ℝ) ≤ j := by exact_mod_cast hc2
  have hj0 : (0 : ℝ) < j := by linarith
  have hj8 : (8 : ℝ) ≤ (j : ℝ) ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hj2 3
    norm_num at this
    linarith
  have hX : 5 ≤ (j : ℝ) ^ 3 * Real.log n := by nlinarith
  have hX0 : 0 ≤ (j : ℝ) ^ 3 * Real.log n := by linarith
  have hcond' (D : ℝ) (hD : D ≤ 2 * (|C₂| + |C₃| + |C₄|) + 3) :
      D * (j : ℝ) ^ 3 * Real.log n ≤ n := by
    calc D * (j : ℝ) ^ 3 * Real.log n = D * ((j : ℝ) ^ 3 * Real.log n) := by ring
      _ ≤ (2 * (|C₂| + |C₃| + |C₄|) + 3) * ((j : ℝ) ^ 3 * Real.log n) :=
          mul_le_mul_of_nonneg_right hD hX0
      _ = _ := by ring
      _ ≤ n := hcond
  have hn5 : (5 : ℝ) ≤ n := by have := hcond' 1 (by linarith); linarith
  have hQ : 1 ≤ (j : ℝ) * Real.log n := by nlinarith
  have hjj : (j : ℝ) * Real.log n ≤ (j : ℝ) ^ 3 * Real.log n := by
    have : (j : ℝ) ≤ (j : ℝ) ^ 3 := by nlinarith
    exact mul_le_mul_of_nonneg_right this hL0
  -- the three stage lengths
  obtain ⟨t₁, ht₁⟩ : ∃ t₁ : ℕ, t₁ = ⌈|C₂| * (j : ℝ) ^ 2 * √(Real.log n)⌉₊ := ⟨_, rfl⟩
  obtain ⟨t₃, ht₃⟩ : ∃ t₃ : ℕ, t₃ = ⌈|C₃| * j * Real.log n⌉₊ := ⟨_, rfl⟩
  obtain ⟨t₄, ht₄⟩ : ∃ t₄ : ℕ, t₄ = ⌈|C₄| * j * Real.log n⌉₊ := ⟨_, rfl⟩
  have ht₁le : (t₁ : ℝ) ≤ |C₂| * (j : ℝ) ^ 2 * √(Real.log n) + 1 :=
    ht₁ ▸ (Nat.ceil_lt_add_one (by positivity)).le
  have ht₃le : (t₃ : ℝ) ≤ |C₃| * j * Real.log n + 1 :=
    ht₃ ▸ (Nat.ceil_lt_add_one (by positivity)).le
  have ht₄le : (t₄ : ℝ) ≤ |C₄| * j * Real.log n + 1 :=
    ht₄ ▸ (Nat.ceil_lt_add_one (by positivity)).le
  have ht₁ge : C₂ * (j : ℝ) ^ 2 * √(Real.log n) ≤ t₁ := by
    refine le_trans ?_ (ht₁ ▸ Nat.le_ceil _)
    have : 0 ≤ (j : ℝ) ^ 2 * √(Real.log n) := by positivity
    have := mul_le_mul_of_nonneg_right (le_abs_self C₂) this
    linarith [show C₂ * (j : ℝ) ^ 2 * √(Real.log n) = C₂ * ((j : ℝ) ^ 2 * √(Real.log n)) by ring,
      show |C₂| * (j : ℝ) ^ 2 * √(Real.log n) = |C₂| * ((j : ℝ) ^ 2 * √(Real.log n)) by ring]
  have ht₃ge : C₃ * j * Real.log n ≤ t₃ := by
    refine le_trans ?_ (ht₃ ▸ Nat.le_ceil _)
    have : 0 ≤ (j : ℝ) * Real.log n := by positivity
    have := mul_le_mul_of_nonneg_right (le_abs_self C₃) this
    linarith [show C₃ * j * Real.log n = C₃ * (j * Real.log n) by ring,
      show |C₃| * j * Real.log n = |C₃| * (j * Real.log n) by ring]
  have ht₄ge : C₄ * j * Real.log n ≤ t₄ := by
    refine le_trans ?_ (ht₄ ▸ Nat.le_ceil _)
    have : 0 ≤ (j : ℝ) * Real.log n := by positivity
    have := mul_le_mul_of_nonneg_right (le_abs_self C₄) this
    linarith [show C₄ * j * Real.log n = C₄ * (j * Real.log n) by ring,
      show |C₄| * j * Real.log n = |C₄| * (j * Real.log n) by ring]
  have ht₃n : t₃ ≤ n := by
    have h1 := hcond' (|C₃| + 1) (by linarith)
    have h2 : |C₃| * ((j : ℝ) * Real.log n) ≤ |C₃| * ((j : ℝ) ^ 3 * Real.log n) :=
      mul_le_mul_of_nonneg_left hjj a₃
    have : (t₃ : ℝ) ≤ n := by nlinarith
    exact_mod_cast this
  have hthr : C₃ * j ^ 2 * Real.log n ≤ n / (2 * j) := by
    rw [le_div_iff₀ (by positivity)]
    have h1 := hcond' (2 * |C₃|) (by linarith)
    have h2 : C₃ * ((j : ℝ) ^ 3 * Real.log n) ≤ |C₃| * ((j : ℝ) ^ 3 * Real.log n) :=
      mul_le_mul_of_nonneg_right (le_abs_self C₃) hX0
    nlinarith
  have htime : t₁ + (t₃ + t₄) ≤ t := by
    have hP : 0 ≤ (j : ℝ) ^ 2 * √(Real.log n) := by positivity
    have e1 : |C₂| * ((j : ℝ) ^ 2 * √(Real.log n)) ≤
        (2 * (|C₂| + |C₃| + |C₄|) + 3) * ((j : ℝ) ^ 2 * √(Real.log n)) :=
      mul_le_mul_of_nonneg_right (by linarith) hP
    have e2 : (|C₃| + |C₄| + 3) * ((j : ℝ) * Real.log n) ≤
        (2 * (|C₂| + |C₃| + |C₄|) + 3) * ((j : ℝ) * Real.log n) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have : ((t₁ + (t₃ + t₄) : ℕ) : ℝ) ≤ t := by
      push_cast
      nlinarith
    exact_mod_cast this
  -- the two dropping stages from a broken-symmetry state, and the composition
  have hB : ∀ b, BrokenSymmetry j b → (2 : ℝ) / 5 ≤
      (Kernel.ofStep (stepCol (n := n) (σ := Fin n))).event
        (fun y => numColours y < j) (t₃ + t₄) b :=
    two_fifths_le_event_of_broken (C₃ := C₃)
      (fun x a hx hxa =>
        hC₃ n j x a hc2 (hcond' C₃ (by linarith [le_abs_self C₃])) hx hxa t₃ ht₃ge ht₃n)
      (fun x a hx hxa =>
        hC₄ n j x a hc2 (hcond' C₄ (by linarith [le_abs_self C₄])) hx hxa t₄ ht₄ge) hthr hn5
  have habs : ∀ y, numColours y < j →
      (Kernel.ofStep (stepCol (n := n) (σ := Fin n)) y).prob (fun y => numColours y < j) = 1 :=
    fun y hy => prob_ofStep_numColours_lt j y hy
  have hcomp := hitProb_mul_le_event _ habs hB t₁ c
  have hh := hhit (hcond' C₂ (by linarith [le_abs_self C₂])) t₁ ht₁ge
  have hmono := Kernel.event_monotone _ habs c htime
  simp only at hmono
  have hfin : (1 : ℝ) / 5 ≤ (Kernel.ofStep (stepCol (n := n) (σ := Fin n))).event
      (fun y => numColours y < j) t c := by
    have := mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 2 / 5)
    linarith
  rw [event_ofStep_stepCol] at hfin
  exact hfin

/-- **Amplification over phases** (BCNPT16, proof of Theorem 3.1): if from every configuration
with between `2` and `k` colours a phase of `L` rounds removes a colour with probability at least
`p ≤ 1`, then from a configuration `c` with at most `k` colours, consensus fails after `M` phases
with probability at most `(1 − p/2)^M 2^k`. -/
theorem consensus_of_phases {n : ℕ} (L k M : ℕ) {p : ℝ} (hp : p ≤ 1)
    (hphase : ∀ x : Fin n → Fin n, 2 ≤ numColours x → numColours x ≤ k →
      p ≤ expList (Tgt3 n) L (fun l => if numColours (runCol x l) < numColours x then 1 else 0))
    (c : Fin n → Fin n) (hc : numColours c ≤ k) :
    expList (Tgt3 n) (M * L) (fun l => if numColours (runCol c l) ≤ 1 then 0 else 1) ≤
      (1 - p / 2) ^ M * 2 ^ k := by
  -- the potential `V = 2^{#colours}` off consensus
  obtain ⟨V, hV⟩ : ∃ V : (Fin n → Fin n) → ℝ,
      V = fun y => if numColours y ≤ 1 then 0 else 2 ^ numColours y := ⟨_, rfl⟩
  have hq : 0 ≤ 1 - p / 2 := by linarith
  have hmono (y : Fin n → Fin n) (l : List (Tgt3 n)) :
      numColours (runCol y l) ≤ numColours y := by
    have := numColours_runCol_append_le y [] l
    simpa only [runCol_nil, List.nil_append] using this
  have hV0 (y : Fin n → Fin n) : 0 ≤ V y := by
    rw [hV]
    dsimp only
    split_ifs <;> positivity
  -- one phase multiplies the expected potential by at most `1 - p/2`
  have hone (x : Fin n → Fin n) (hxk : numColours x ≤ k) :
      expList (Tgt3 n) L (fun l => V (runCol x l)) ≤ (1 - p / 2) * V x := by
    by_cases hx : numColours x ≤ 1
    · have h0 : (fun l => V (runCol x l)) = fun _ => 0 :=
        funext fun l => by rw [hV]; exact if_pos ((hmono x l).trans hx)
      rw [h0]
      calc expList (Tgt3 n) L (fun _ => (0 : ℝ)) = 0 := Dynamics.expList_zero_fun L
        _ ≤ (1 - p / 2) * V x := mul_nonneg hq (hV0 x)
    · push Not at hx
      have hxn : numColours x ≤ n := by
        simpa [numColours] using card_image_le (s := (univ : Finset (Fin n))) (f := x)
      haveI : NeZero n := ⟨by omega⟩
      obtain ⟨K, hK⟩ : ∃ K, K = numColours x := ⟨_, rfl⟩
      rw [← hK] at hx
      obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
      have hpt (l : List (Tgt3 n)) : V (runCol x l) ≤
          2 ^ (K' + 1) + (-2 ^ K') * (if numColours (runCol x l) < numColours x then 1 else 0) := by
        have hle := hmono x l
        have h4 : (0 : ℝ) ≤ 2 ^ K' := by positivity
        have h5 : (2 : ℝ) ^ (K' + 1) = 2 * 2 ^ K' := by rw [pow_succ]; ring
        rw [hV]
        dsimp only
        split_ifs with h1 h2 h2
        · linarith
        · linarith
        · have h3 : (2 : ℝ) ^ numColours (runCol x l) ≤ 2 ^ K' :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          linarith
        · have h3 : (2 : ℝ) ^ numColours (runCol x l) ≤ 2 ^ (K' + 1) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          linarith
      have hVx : V x = 2 ^ (K' + 1) := by
        rw [hV]
        dsimp only
        rw [if_neg (by omega), ← hK]
      calc expList (Tgt3 n) L (fun l => V (runCol x l))
          ≤ expList (Tgt3 n) L (fun l => 2 ^ (K' + 1) +
              (-2 ^ K') * (if numColours (runCol x l) < numColours x then 1 else 0)) :=
            expList_le_expList hpt
        _ = 2 ^ (K' + 1) + (-2 ^ K') * expList (Tgt3 n) L
              (fun l => if numColours (runCol x l) < numColours x then 1 else 0) := by
            rw [expList_add, expList_const, expList_const_mul]
        _ ≤ 2 ^ (K' + 1) + (-2 ^ K') * p := by
            have : (0 : ℝ) ≤ 2 ^ K' := by positivity
            nlinarith [hphase x (by omega) hxk]
        _ = (1 - p / 2) * V x := by rw [hVx, pow_succ]; ring
  -- `m` phases multiply it by at most `(1 - p/2)^m`
  have hall (m : ℕ) : ∀ x : Fin n → Fin n, numColours x ≤ k →
      expList (Tgt3 n) (m * L) (fun l => V (runCol x l)) ≤ (1 - p / 2) ^ m * V x := by
    induction m with
    | zero => intro x _; simp
    | succ m ih =>
      intro x hxk
      rw [show (m + 1) * L = L + m * L by ring, expList_append]
      calc expList (Tgt3 n) L (fun l₁ => expList (Tgt3 n) (m * L)
            (fun l₂ => V (runCol x (l₁ ++ l₂))))
          ≤ expList (Tgt3 n) L (fun l₁ => (1 - p / 2) ^ m * V (runCol x l₁)) :=
            expList_le_expList fun l₁ => by
              simp_rw [runCol_append]
              exact ih _ ((hmono x l₁).trans hxk)
        _ = (1 - p / 2) ^ m * expList (Tgt3 n) L (fun l₁ => V (runCol x l₁)) :=
            expList_const_mul _ _ _
        _ ≤ (1 - p / 2) ^ m * ((1 - p / 2) * V x) := by gcongr; exact hone x hxk
        _ = (1 - p / 2) ^ (m + 1) * V x := by ring
  have hVc : V c ≤ 2 ^ k := by
    rw [hV]
    dsimp only
    split_ifs
    · positivity
    · exact pow_le_pow_right₀ (by norm_num) hc
  calc expList (Tgt3 n) (M * L) (fun l => if numColours (runCol c l) ≤ 1 then 0 else 1)
      ≤ expList (Tgt3 n) (M * L) (fun l => V (runCol c l)) := by
        refine expList_le_expList fun l => ?_
        rw [hV]
        dsimp only
        split_ifs
        · exact le_rfl
        · exact one_le_pow₀ (by norm_num)
    _ ≤ (1 - p / 2) ^ M * V c := hall M c hc
    _ ≤ (1 - p / 2) ^ M * 2 ^ k := by gcongr

/-- Consensus is absorbing, so missing it at time `T` implies missing it at every earlier
time `T₀ ≤ T`. -/
lemma expList_not_consensus_le {n : ℕ} [NeZero n] {σ : Type*} [DecidableEq σ] (c : Fin n → σ)
    {T₀ T : ℕ} (h : T₀ ≤ T) :
    expList (Tgt3 n) T (fun l => if numColours (runCol c l) ≤ 1 then 0 else 1) ≤
      expList (Tgt3 n) T₀ (fun l => if numColours (runCol c l) ≤ 1 then 0 else 1) := by
  obtain ⟨T', rfl⟩ := Nat.exists_eq_add_of_le h
  rw [expList_append]
  refine expList_le_expList fun l₁ => ?_
  calc expList (Tgt3 n) T'
        (fun l₂ => if numColours (runCol c (l₁ ++ l₂)) ≤ 1 then (0 : ℝ) else 1)
      ≤ expList (Tgt3 n) T'
        (fun _ => if numColours (runCol c l₁) ≤ 1 then (0 : ℝ) else 1) :=
        expList_le_expList fun l₂ => by
          have := numColours_runCol_append_le c l₁ l₂
          split_ifs <;> first | (exfalso; omega) | norm_num
    _ = _ := expList_const T' _

/-- The number of phases: with `M = 10 (k + ⌈log n⌉)`, `(9/10)^M 2^k ≤ 1/n` (since
`(9/10)^10 ≤ e^{-1}` and `2 ≤ e`). -/
lemma nine_tenths_pow_mul_two_pow_le {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    ((9 : ℝ) / 10) ^ (10 * (k + ⌈Real.log n⌉₊)) * 2 ^ k ≤ 1 / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h10 : ((9 : ℝ) / 10) ^ 10 ≤ Real.exp (-1) := by
    rw [Real.exp_neg, le_inv_comm₀ (by positivity) (Real.exp_pos 1)]
    refine Real.exp_one_lt_d9.le.trans ?_
    norm_num
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hL : Real.log n ≤ (⌈Real.log n⌉₊ : ℝ) := Nat.le_ceil _
  calc ((9 : ℝ) / 10) ^ (10 * (k + ⌈Real.log n⌉₊)) * 2 ^ k
      = (((9 : ℝ) / 10) ^ 10) ^ (k + ⌈Real.log n⌉₊) * 2 ^ k := by rw [pow_mul]
    _ ≤ (Real.exp (-1)) ^ (k + ⌈Real.log n⌉₊) * (Real.exp 1) ^ k := by gcongr
    _ = Real.exp (-(⌈Real.log n⌉₊ : ℝ)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
        push_cast
        ring_nf
    _ ≤ Real.exp (-Real.log n) := Real.exp_le_exp.mpr (by linarith)
    _ = 1 / n := by rw [Real.exp_neg, Real.exp_log hn0, one_div]

/-- **Theorem 3.1** (BCNPT16), under the condition `C k³ log n ≤ n` on the number `k` of colours:
there is `C` such that from every configuration `c` with `k` colours and `C k³ log n ≤ n`,
3-Majority has reached consensus after any `T ≥ C (k² √(log n) + k log n)(k + log n)` rounds with
probability at least `1 − 1/n`. -/
theorem consensus_many_opinions :
    ∃ C : ℝ, ∀ (n : ℕ) (c : Fin n → Fin n), C * (numColours c : ℝ) ^ 3 * Real.log n ≤ n →
      ∀ T : ℕ, C * (((numColours c : ℝ) ^ 2 * √(Real.log n) + numColours c * Real.log n) *
          (numColours c + Real.log n)) ≤ T →
        expList (Tgt3 n) T (fun l => if numColours (runCol c l) ≤ 1 then 0 else 1) ≤ 1 / n := by
  obtain ⟨C₁, hC₁⟩ := phase_colour_dies
  refine ⟨15 * (|C₁| + 1), fun n c hcond T hT => ?_⟩
  by_cases hk : numColours c ≤ 1
  · have h0 : (fun l => if numColours (runCol c l) ≤ 1 then (0 : ℝ) else 1) = fun _ => 0 := by
      funext l
      have := numColours_runCol_append_le c [] l
      simp only [runCol_nil, List.nil_append] at this
      rw [if_pos (this.trans hk)]
    rw [h0]
    calc expList (Tgt3 n) T (fun _ => (0 : ℝ)) = 0 := Dynamics.expList_zero_fun T
      _ ≤ 1 / n := by positivity
  push Not at hk
  -- `n ≥ 2`, since there are at least two colours
  have hkn : numColours c ≤ n := by
    simpa [numColours] using card_image_le (s := (univ : Finset (Fin n))) (f := c)
  haveI : NeZero n := ⟨by omega⟩
  have hn1 : 1 ≤ n := by omega
  obtain ⟨k, hkdef⟩ : ∃ k, k = numColours c := ⟨_, rfl⟩
  rw [← hkdef] at hcond hT hk
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log n := ⟨_, rfl⟩
  rw [← hLdef] at hcond hT
  have hL : 0.6931471803 ≤ L := by
    rw [hLdef]
    refine Real.log_two_gt_d9.le.trans (Real.log_le_log (by norm_num) ?_)
    exact_mod_cast (by omega : 2 ≤ n)
  have hL0 : 0 ≤ L := by linarith
  have hC₁0 : 0 ≤ |C₁| := abs_nonneg C₁
  have hsqrt0 : 0 ≤ √L := Real.sqrt_nonneg L
  -- the phase length `P` and the number of phases `M`
  obtain ⟨P, hP⟩ : ∃ P : ℕ, P = ⌈|C₁| * ((k : ℝ) ^ 2 * √L + k * L)⌉₊ := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = 10 * (k + ⌈L⌉₊) := ⟨_, rfl⟩
  have hphase : ∀ x : Fin n → Fin n, 2 ≤ numColours x → numColours x ≤ k →
      1 / 5 ≤ expList (Tgt3 n) P
        (fun l => if numColours (runCol x l) < numColours x then 1 else 0) := by
    intro x hx2 hxk
    have hxk' : (numColours x : ℝ) ≤ k := by exact_mod_cast hxk
    have hx0 : (0 : ℝ) ≤ numColours x := Nat.cast_nonneg _
    refine hC₁ n x hx2 ?_ P ?_
    · rw [← hLdef]
      calc C₁ * (numColours x : ℝ) ^ 3 * L ≤ |C₁| * (numColours x : ℝ) ^ 3 * L := by
            have := le_abs_self C₁
            have : 0 ≤ (numColours x : ℝ) ^ 3 * L := by positivity
            nlinarith
        _ ≤ 15 * (|C₁| + 1) * (k : ℝ) ^ 3 * L := by gcongr; linarith
        _ ≤ n := hcond
    · rw [← hLdef]
      calc C₁ * ((numColours x : ℝ) ^ 2 * √L + numColours x * L)
          ≤ |C₁| * ((numColours x : ℝ) ^ 2 * √L + numColours x * L) := by
            have := le_abs_self C₁
            have : 0 ≤ (numColours x : ℝ) ^ 2 * √L + numColours x * L := by positivity
            nlinarith
        _ ≤ |C₁| * ((k : ℝ) ^ 2 * √L + k * L) := by gcongr
        _ ≤ P := hP ▸ Nat.le_ceil _
  have hamp := consensus_of_phases P k M (p := 1 / 5) (by norm_num) hphase c hkdef.ge
  -- `M P ≤ T`
  have hPle : (P : ℝ) ≤ (|C₁| + 1) * ((k : ℝ) ^ 2 * √L + k * L) := by
    have h1 : (P : ℝ) ≤ |C₁| * ((k : ℝ) ^ 2 * √L + k * L) + 1 :=
      hP ▸ (Nat.ceil_lt_add_one (by positivity)).le
    have h2 : 1 ≤ (k : ℝ) ^ 2 * √L + k * L := by nlinarith
    nlinarith
  have hMle : (M : ℝ) ≤ 15 * (k + L) := by
    have h1 : (⌈L⌉₊ : ℝ) ≤ L + 1 := (Nat.ceil_lt_add_one hL0).le
    rw [hM]
    push_cast
    linarith
  have hMP : M * P ≤ T := by
    have h0 : (0 : ℝ) ≤ (k : ℝ) ^ 2 * √L + k * L := by positivity
    have : ((M * P : ℕ) : ℝ) ≤ T := by
      push_cast
      calc (M : ℝ) * P ≤ (15 * (k + L)) * ((|C₁| + 1) * ((k : ℝ) ^ 2 * √L + k * L)) :=
            mul_le_mul hMle hPle (Nat.cast_nonneg _) (by positivity)
        _ = 15 * (|C₁| + 1) * (((k : ℝ) ^ 2 * √L + k * L) * (k + L)) := by ring
        _ ≤ T := hT
    exact_mod_cast this
  calc expList (Tgt3 n) T (fun l => if numColours (runCol c l) ≤ 1 then 0 else 1)
      ≤ expList (Tgt3 n) (M * P) (fun l => if numColours (runCol c l) ≤ 1 then 0 else 1) :=
        expList_not_consensus_le c hMP
    _ ≤ (1 - 1 / 5 / 2) ^ M * 2 ^ k := hamp
    _ = ((9 : ℝ) / 10) ^ (10 * (k + ⌈Real.log n⌉₊)) * 2 ^ k := by rw [hM, hLdef]; norm_num
    _ ≤ 1 / n := nine_tenths_pow_mul_two_pow_le hn1 k

/-- The hypothesis `Bcnpt16Phase2` of `threeMaj_anyStart_consensus` (roadmap MAJ-6 (b)), unfolded.
(Pinned, so that its definition is frozen together with `bcnpt16Phase2_of_pos`.) -/
theorem bcnpt16Phase2_iff (ε : ℝ) :
    Bcnpt16Phase2 ε ↔ ∃ C N : ℝ, ∀ n : ℕ, N ≤ n → ∀ c : Fin n → Fin n,
      (numColours c : ℝ) ≤ (n : ℝ) ^ (1 / 3 - ε) →
      ∀ T : ℕ, C * (((numColours c : ℝ) ^ 2 * √(Real.log n) + numColours c * Real.log n) *
          (numColours c + Real.log n)) ≤ T →
        expList (Tgt3 n) T (fun l => if numColours (runCol c l) ≤ 1 then 0 else 1) ≤ 1 / n :=
  Iff.rfl

/-- **Theorem 3.1** (BCNPT16, the adversary-free case), as stated in the paper: for every
`ε > 0`, from any configuration with `k ≤ n^{1/3 − ε}` colours, 3-Majority reaches consensus
within `O((k² √(log n) + k log n)(k + log n))` rounds with probability at least `1 − 1/n`. This is
the hypothesis `Bcnpt16Phase2 ε` of `threeMaj_anyStart_consensus` (roadmap MAJ-6 (b)). -/
theorem bcnpt16Phase2_of_pos {ε : ℝ} (hε : 0 < ε) : Bcnpt16Phase2 ε := by
  obtain ⟨C, hC⟩ := consensus_many_opinions
  -- eventually `|C| log n ≤ n^{3ε}`
  have hev : ∀ᶠ y : ℝ in Filter.atTop, |C| * Real.log y ≤ y ^ (3 * ε) := by
    have h1 := eventually_log_rpow_le_rpow 1 (s := 3 * ε / 2) (by positivity)
    have h2 := (tendsto_rpow_atTop (show 0 < 3 * ε / 2 by positivity)).eventually_ge_atTop |C|
    filter_upwards [h1, h2, Filter.eventually_ge_atTop 1] with y hy1 hy2 hy3
    rw [Real.rpow_one] at hy1
    calc |C| * Real.log y ≤ y ^ (3 * ε / 2) * y ^ (3 * ε / 2) :=
          mul_le_mul hy2 hy1 (Real.log_nonneg hy3) (by positivity)
      _ = y ^ (3 * ε) := by rw [← Real.rpow_add (by linarith)]; ring_nf
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  refine ⟨C, max N 1, fun n hn c hk T hT => hC n c ?_ T hT⟩
  have hn1 : (1 : ℝ) ≤ n := le_of_max_le_right hn
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hL : 0 ≤ Real.log n := Real.log_nonneg hn1
  -- `k³ ≤ n^{1 − 3ε}`
  have hk3 : (numColours c : ℝ) ^ 3 ≤ (n : ℝ) ^ (1 - 3 * ε) := by
    calc (numColours c : ℝ) ^ 3 ≤ ((n : ℝ) ^ (1 / 3 - ε)) ^ 3 := by gcongr
      _ = (n : ℝ) ^ (1 - 3 * ε) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hn0]
          ring_nf
  have hnpos : (0 : ℝ) < n := by linarith
  calc C * (numColours c : ℝ) ^ 3 * Real.log n
      ≤ |C| * (numColours c : ℝ) ^ 3 * Real.log n := by
        gcongr
        exact le_abs_self C
    _ ≤ |C| * (n : ℝ) ^ (1 - 3 * ε) * Real.log n := by gcongr
    _ = (n : ℝ) ^ (1 - 3 * ε) * (|C| * Real.log n) := by ring
    _ ≤ (n : ℝ) ^ (1 - 3 * ε) * (n : ℝ) ^ (3 * ε) := by
        gcongr
        exact hN n (le_of_max_le_left hn)
    _ = n := by
        rw [← Real.rpow_add hnpos]
        simp

/-- **Theorem 4** of Berenbrink, Clementi, Elsässer, Kling, Mallmann-Trenn, Natale (PODC 2017),
without hypothesis: from any configuration of colours in `[n]`, 3-Majority reaches consensus within
any `T ≥ C n^{3/4} log^{7/8} n` rounds with probability at least `1 − 2/n`, for `n ≥ N`
(`threeMaj_anyStart_consensus` with its Phase 2 hypothesis discharged by Theorem 3.1 of BCNPT16
for `ε = 1/24`). -/
theorem threeMaj_anyStart_consensus_unconditional :
    ∃ C N : ℝ, ∀ n : ℕ, N ≤ n → ∀ c : Fin n → Fin n, ∀ T : ℕ,
      C * (n : ℝ) ^ ((3 : ℝ) / 4) * Real.log n ^ ((7 : ℝ) / 8) ≤ T →
        expList (Tgt3 n) T (fun l => if numColours (runCol c l) ≤ 1 then 0 else 1) ≤ 2 / n :=
  threeMaj_anyStart_consensus (bcnpt16Phase2_of_pos (by norm_num))

end ThreeMajority
