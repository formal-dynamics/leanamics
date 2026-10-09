import ThreeMajority.AnyStartComparison
import Dynamics.Rounds
import Dynamics.Bridge

/-!
# 3-Majority is at least as fast as Voter (BCEKMN17, Lemma 2)

Both processes are anonymous consensus processes (Definition 1), with the process functions
`alpha3M` and `alphaVoter`, defined here as the law of the colour adopted by one agent: the
image of one uniform sample triple under `majColour c`, resp. of one uniform sample under `c`.

* `alphaVoter_weight`, `alpha3M_weight`: Equations (1) and (2), `α^V_a(c) = x_a` and
  `α^{3M}_a(c) = x_a (1 + x_a − ‖x‖₂²)` with `x = c/n`.
* `apply_ofStep_stepCol`, `apply_ofStep_voterStep`: one uniformly random round of the
  round-based processes `stepCol` and `voterStep` is one step of the AC-processes `alpha3M` and
  `alphaVoter` (the agents' samples are independent).
* `dominates_alpha3M_alphaVoter`: the inequality proved in Lemma 2, `c ⪰ c'` implies
  `α^{3M}(c) ⪰ α^V(c')`.
* `voter_le_threeMaj`: Lemma 2, started from the same configuration, 3-Majority has at most `κ`
  colours at time `T` with at least the probability that Voter has.
-/

namespace ThreeMajority

open Finset Dynamics

variable {n : ℕ} [NeZero n] {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The process function of 3-Majority (BCEKMN17, Section 2.2): the law of `majColour c s` for
a uniform sample triple `s`. -/
noncomputable def alpha3M (c : Fin n → σ) : Distribution σ :=
  (Distribution.uniform (Fin n × Fin n × Fin n)).map (majColour c)

/-- The process function of Voter (BCEKMN17, Section 2.2): the law of `c u` for a uniform
agent `u`. -/
noncomputable def alphaVoter (c : Fin n → σ) : Distribution σ :=
  (Distribution.uniform (Fin n)).map c

omit [NeZero n] [Fintype σ] in
/-- The 3-Majority indicator: `[maj = a] = [x₂ = a][x₃ = a] + [x₁ = a] - [x₂ = x₃][x₁ = a]`. -/
lemma ite_majority_eq (x₁ x₂ x₃ a : σ) :
    (if (if x₂ = x₃ then x₂ else x₁) = a then (1 : ℝ) else 0) =
      (if x₂ = a then 1 else 0) * (if x₃ = a then 1 else 0) + (if x₁ = a then 1 else 0) -
        (if x₂ = x₃ then 1 else 0) * (if x₁ = a then 1 else 0) := by
  by_cases h23 : x₂ = x₃
  · subst h23
    by_cases h2 : x₂ = a <;> simp [h2]
  · by_cases h2 : x₂ = a
    · subst h2
      by_cases h1 : x₁ = x₂ <;> simp [h23, Ne.symm h23, h1]
    · by_cases h1 : x₁ = a <;> by_cases h3 : x₃ = a <;> simp [h23, h1, h2, h3]

omit [NeZero n] [Fintype σ] [DecidableEq σ] in
lemma sum3_mul_left (f g : Fin n → ℝ) :
    ∑ _x : Fin n, ∑ y : Fin n, ∑ z : Fin n, f y * g z = n * ((∑ y, f y) * ∑ z, g z) := by
  simp_rw [← mul_sum, ← sum_mul]
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

omit [NeZero n] [Fintype σ] [DecidableEq σ] in
lemma sum3_first (f : Fin n → ℝ) :
    ∑ x : Fin n, ∑ _y : Fin n, ∑ _z : Fin n, f x = n ^ 2 * ∑ x, f x := by
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_sum]
  ring

omit [NeZero n] [Fintype σ] [DecidableEq σ] in
lemma sum3_mul_right (E : Fin n → Fin n → ℝ) (f : Fin n → ℝ) :
    ∑ x : Fin n, ∑ y : Fin n, ∑ z : Fin n, E y z * f x = (∑ x, f x) * ∑ y, ∑ z, E y z := by
  simp_rw [← sum_mul]
  rw [← mul_sum]
  ring

omit [NeZero n] in
/-- The number of ordered pairs of agents of equal colour is `∑_b c_b²`. -/
lemma sum_sq_colourCount (c : Fin n → σ) :
    ∑ b, (colourCount c b : ℝ) ^ 2 = ∑ u, ∑ v, if c u = c v then (1 : ℝ) else 0 := by
  have h (u : Fin n) : (∑ v, if c u = c v then (1 : ℝ) else 0) = colourCount c (c u) := by
    simp [colourCount, eq_comm]
  simp_rw [h]
  rw [← sum_fiberwise univ c]
  refine sum_congr rfl fun b _ => ?_
  rw [sum_congr rfl fun u hu => by rw [(mem_filter.mp hu).2], sum_const, nsmul_eq_mul, sq]
  rfl

omit [NeZero n] in
/-- The number of sample triples whose 3-Majority colour is `a`. -/
lemma card_majColour_eq (c : Fin n → σ) (a : σ) :
    ((univ.filter fun s : Fin n × Fin n × Fin n => majColour c s = a).card : ℝ) =
      n * (colourCount c a : ℝ) ^ 2 + (n : ℝ) ^ 2 * colourCount c a -
        colourCount c a * ∑ b, (colourCount c b : ℝ) ^ 2 := by
  have hm : (colourCount c a : ℝ) = ∑ v, if c v = a then (1 : ℝ) else 0 := by
    simp [colourCount]
  rw [natCast_card_filter, sum_sq_colourCount]
  simp only [majColour, ite_majority_eq, sum_add_distrib, sum_sub_distrib,
    Fintype.sum_prod_type, sum3_first, sum3_mul_right, ← hm]
  rw [sum3_mul_left (fun v => if c v = a then (1 : ℝ) else 0)
    (fun v => if c v = a then (1 : ℝ) else 0), ← hm]
  ring
omit [NeZero n] [Fintype σ] in
/-- Drawing every coordinate independently from `(p i).map g` is applying `g` coordinatewise
to independent draws from the `p i`. -/
lemma independent_map_expect {ι α β : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    [Fintype β] (p : ι → Distribution α) (g : α → β) (f : (ι → β) → ℝ) :
    (Distribution.independent fun i => (p i).map g).expect f =
      (Distribution.independent p).expect (fun x => f (fun i => g (x i))) := by
  classical
  simp only [Distribution.expect, Distribution.independent, Distribution.map]
  simp_rw [Fintype.prod_sum, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_eq_single (fun i => g (x i))]
  · exact congrArg (· * _) (prod_congr rfl fun i _ => if_pos rfl)
  · intro y _ hy
    obtain ⟨i, hi⟩ : ∃ i, g (x i) ≠ y i := by
      by_contra h
      push Not at h
      exact hy (funext fun i => (h i).symm)
    rw [prod_eq_zero (mem_univ i) (if_neg hi), zero_mul]
  · simp

omit [NeZero n] in
/-- The weight of a pushed-forward uniform law is a normalized fibre count. -/
lemma uniform_map_weight {β : Type*} [Fintype β] [Nonempty β] (g : β → σ) (a : σ) :
    ((Distribution.uniform β).map g).weight a =
      ((univ.filter fun b => g b = a).card : ℝ) / Fintype.card β := by
  classical
  simp only [Distribution.map, Distribution.uniform]
  rw [← sum_filter, sum_const, nsmul_eq_mul, div_eq_mul_inv]

/-- **Equation (1)** (BCEKMN17): `α^V_a(c) = c_a / n`. -/
theorem alphaVoter_weight (c : Fin n → σ) (a : σ) :
    (alphaVoter c).weight a = (colourCount c a : ℝ) / n := by
  rw [alphaVoter, uniform_map_weight, Fintype.card_fin, colourCount]

/-- **Equation (2)** (BCEKMN17): with `x = c/n`, `α^{3M}_a(c) = x_a (1 + x_a − ‖x‖₂²)`. -/
theorem alpha3M_weight (c : Fin n → σ) (a : σ) :
    (alpha3M c).weight a = (colourCount c a : ℝ) / n *
      (1 + (colourCount c a : ℝ) / n - ∑ b, ((colourCount c b : ℝ) / n) ^ 2) := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [alpha3M, uniform_map_weight, card_majColour_eq]
  simp only [Fintype.card_prod, Fintype.card_fin, div_pow, ← sum_div]
  push_cast
  field_simp
  ring

/-- One uniformly random round of `stepCol` is one step of the AC-process `alpha3M`
(3-Majority is an AC-process, BCEKMN17, Section 2.2). -/
theorem apply_ofStep_stepCol (f : (Fin n → σ) → ℝ) (c : Fin n → σ) :
    (Kernel.ofStep (stepCol (n := n) (σ := σ))).apply f c = (acKernel alpha3M).apply f c := by
  rw [Kernel.apply_ofStep]
  simp only [Kernel.apply, acKernel, alpha3M, independent_map_expect,
    Distribution.independent_uniform_expect]
  rfl

omit [DecidableEq σ] in
/-- One uniformly random round of `voterStep` is one step of the AC-process `alphaVoter`
(Voter is an AC-process, BCEKMN17, Section 2.2). -/
theorem apply_ofStep_voterStep (f : (Fin n → σ) → ℝ) (c : Fin n → σ) :
    (Kernel.ofStep (voterStep (n := n) (σ := σ))).apply f c =
      (acKernel alphaVoter).apply f c := by
  rw [Kernel.apply_ofStep]
  simp only [Kernel.apply, acKernel, alphaVoter, independent_map_expect,
    Distribution.independent_uniform_expect]
  rfl

omit [NeZero n] [Fintype σ] [DecidableEq σ] in
/-- Among the sets of a given size, one of maximal `x`-sum is a top set: its entries are at
least the entries outside it (exchange argument). -/
lemma exists_top_set {ι : Type*} [Finite ι] (x : ι → ℝ) (S₁ : Finset ι) :
    ∃ S₂ : Finset ι, S₂.card = S₁.card ∧ ∑ i ∈ S₁, x i ≤ ∑ i ∈ S₂, x i ∧
      ∀ i ∈ S₂, ∀ j ∉ S₂, x j ≤ x i := by
  classical
  have := Fintype.ofFinite ι
  have h₁ : S₁ ∈ powersetCard S₁.card (univ : Finset ι) :=
    mem_powersetCard.mpr ⟨subset_univ _, rfl⟩
  obtain ⟨S₂, hmem, hmax⟩ :=
    (powersetCard S₁.card univ).exists_max_image (fun S => ∑ i ∈ S, x i) ⟨S₁, h₁⟩
  have hcard := (mem_powersetCard.mp hmem).2
  refine ⟨S₂, hcard, hmax S₁ h₁, fun i hi j hj => ?_⟩
  by_contra hlt
  have hj' : j ∉ S₂.erase i := fun h => hj (mem_of_mem_erase h)
  have hT : insert j (S₂.erase i) ∈ powersetCard S₁.card univ := by
    refine mem_powersetCard.mpr ⟨subset_univ _, ?_⟩
    rw [card_insert_of_notMem hj', card_erase_of_mem hi, ← hcard]
    exact Nat.sub_add_cancel (card_pos.mpr ⟨i, hi⟩)
  have h := hmax _ hT
  rw [sum_insert hj', ← add_sum_erase _ _ hi] at h
  linarith

omit [NeZero n] in
/-- The colour fractions of a configuration sum to one. -/
lemma sum_colourCount_div (c : Fin n → σ) (hn : (n : ℝ) ≠ 0) :
    ∑ b, (colourCount c b : ℝ) / n = 1 := by
  rw [← sum_div, div_eq_one_iff_eq hn]
  simp only [colourCount]
  rw [← Nat.cast_sum, ← card_eq_sum_card_fiberwise (fun v _ => mem_univ (c v))]
  simp

/-- The key inequality of Lemma 2: on a top set `S` of a probability vector `x`,
`‖x‖₂² ∑_S x ≤ ∑_S x²`. -/
lemma sq_norm_mul_sum_le {ι : Type*} [Fintype ι] (x : ι → ℝ)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∑ i, x i = 1) (S : Finset ι)
    (htop : ∀ i ∈ S, ∀ j ∉ S, x j ≤ x i) :
    (∑ j, x j ^ 2) * ∑ i ∈ S, x i ≤ ∑ i ∈ S, x i ^ 2 := by
  classical
  have hrow (i : ι) : ∑ j, x i * x j * (x i - x j) = x i ^ 2 - x i * ∑ j, x j ^ 2 :=
    calc ∑ j, x i * x j * (x i - x j) = ∑ j, (x i ^ 2 * x j - x i * x j ^ 2) :=
          sum_congr rfl fun j _ => by ring
      _ = x i ^ 2 * ∑ j, x j - x i * ∑ j, x j ^ 2 := by rw [sum_sub_distrib, mul_sum, mul_sum]
      _ = x i ^ 2 - x i * ∑ j, x j ^ 2 := by rw [hx1, mul_one]
  -- the pairs inside `S` cancel, the pairs `(i ∈ S, j ∉ S)` are nonnegative
  have hanti : ∑ i ∈ S, ∑ j ∈ S, x i * x j * (x i - x j) = 0 := by
    have h := sum_comm (s := S) (t := S) (f := fun i j => x i * x j * (x i - x j))
    have h2 : ∑ j ∈ S, ∑ i ∈ S, x i * x j * (x i - x j) =
        -∑ j ∈ S, ∑ i ∈ S, x j * x i * (x j - x i) := by
      rw [← sum_neg_distrib]
      refine sum_congr rfl fun _ _ => ?_
      rw [← sum_neg_distrib]
      exact sum_congr rfl fun _ _ => by ring
    linarith
  have hout : 0 ≤ ∑ i ∈ S, ∑ j ∈ Sᶜ, x i * x j * (x i - x j) :=
    sum_nonneg fun i hi => sum_nonneg fun j hj =>
      mul_nonneg (mul_nonneg (hx0 i) (hx0 j))
        (sub_nonneg.mpr (htop i hi j (mem_compl.mp hj)))
  have htot : ∑ i ∈ S, ∑ j, x i * x j * (x i - x j) =
      ∑ i ∈ S, x i ^ 2 - (∑ j, x j ^ 2) * ∑ i ∈ S, x i := by
    rw [sum_congr rfl fun i _ => hrow i, sum_sub_distrib, ← sum_mul, mul_comm]
  have hsplit : ∑ i ∈ S, ∑ j, x i * x j * (x i - x j) =
      ∑ i ∈ S, ∑ j ∈ S, x i * x j * (x i - x j) +
        ∑ i ∈ S, ∑ j ∈ Sᶜ, x i * x j * (x i - x j) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun i _ => (sum_add_sum_compl S _).symm
  linarith

omit [NeZero n] [Fintype σ] [DecidableEq σ] in
/-- Two kernels with the same one-step operator have the same iterates. -/
lemma iterate_eq_of_apply_eq {α : Type*} [Fintype α] {K K' : Kernel α}
    (h : ∀ f a, K.apply f a = K'.apply f a) (T : ℕ) (f : α → ℝ) :
    K.iterate T f = K'.iterate T f := by
  induction T with
  | zero => rfl
  | succ T ih =>
    funext a
    rw [Kernel.iterate_succ, Kernel.iterate_succ, ih, h]

/-- The inequality of the proof of **Lemma 2** (BCEKMN17): 3-Majority dominates Voter,
`c ⪰ c'` implies `α^{3M}(c) ⪰ α^V(c')`. -/
theorem dominates_alpha3M_alphaVoter :
    Dominates (alpha3M (n := n) (σ := σ)) alphaVoter := by
  intro c c' hc
  refine ⟨by rw [(alpha3M c).sum_one, (alphaVoter c').sum_one], fun S => ?_⟩
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  obtain ⟨x, hx⟩ : ∃ x : σ → ℝ, x = fun b => (colourCount c b : ℝ) / n := ⟨_, rfl⟩
  have hx0 (b : σ) : 0 ≤ x b := by rw [hx]; positivity
  have hx1 : ∑ b, x b = 1 := by rw [hx]; exact sum_colourCount_div c hn.ne'
  have hw (b : σ) : (alpha3M c).weight b = x b * (1 + x b - ∑ a, x a ^ 2) := by
    rw [alpha3M_weight, hx]
  obtain ⟨S₁, hS₁, hsum₁⟩ := hc.2 S
  obtain ⟨S₂, hS₂, hsum₂, htop⟩ := exists_top_set x S₁
  refine ⟨S₂, hS₂.trans hS₁, ?_⟩
  have hkey := sq_norm_mul_sum_le x hx0 hx1 S₂ htop
  calc ∑ b ∈ S, (alphaVoter c').weight b = (∑ b ∈ S, countVec c' b) / n := by
        simp only [alphaVoter_weight, countVec, sum_div]
    _ ≤ (∑ b ∈ S₁, countVec c b) / n := div_le_div_of_nonneg_right hsum₁ hn.le
    _ = ∑ b ∈ S₁, x b := by simp only [hx, countVec, sum_div]
    _ ≤ ∑ b ∈ S₂, x b := hsum₂
    _ ≤ ∑ b ∈ S₂, (alpha3M c).weight b := by
        simp only [hw, mul_add, mul_sub, mul_one, sum_add_distrib, sum_sub_distrib, ← sum_mul,
          ← sq]
        linarith


omit [Fintype σ] in
/-- **Lemma 2** (BCEKMN17): started from the same configuration `c`, after `T` rounds
3-Majority has at most `κ` colours with at least the probability that Voter has. Since neither
process creates colours, this is `T^κ_{3M}(c) ≤st T^κ_V(c)`. -/
theorem voter_le_threeMaj [Finite σ] (c : Fin n → σ) (κ T : ℕ) :
    expList (Fin n → Fin n) T (fun l => if numColours (voterRun c l) ≤ κ then 1 else 0) ≤
      expList (Tgt3 n) T (fun l => if numColours (runCol c l) ≤ κ then 1 else 0) := by
  have := Fintype.ofFinite σ
  -- both sides are events of the AC-processes (`apply_ofStep_voterStep`, `apply_ofStep_stepCol`)
  have hV : expList (Fin n → Fin n) T
      (fun l => if numColours (voterRun c l) ≤ κ then 1 else 0) =
        (acKernel alphaVoter).event (fun x => numColours x ≤ κ) T c := by
    rw [Kernel.event_eq_iterate, ← iterate_eq_of_apply_eq apply_ofStep_voterStep,
      Kernel.iterate_ofStep]
    simp only [voterRun_eq_foldl]
  have h3 : expList (Tgt3 n) T (fun l => if numColours (runCol c l) ≤ κ then 1 else 0) =
      (acKernel alpha3M).event (fun x => numColours x ≤ κ) T c := by
    rw [Kernel.event_eq_iterate, ← iterate_eq_of_apply_eq apply_ofStep_stepCol,
      Kernel.iterate_ofStep]
    simp only [runCol_eq_foldl]
  rw [hV, h3]
  exact ac_numColours _ _ dominates_alpha3M_alphaVoter c κ T

end ThreeMajority
