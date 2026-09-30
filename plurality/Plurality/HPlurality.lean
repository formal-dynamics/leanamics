import Plurality.Lower

/-!
# The lower bound for `h`-plurality (Section 4.3)

In the **`h`-plurality** dynamics every node samples `h` nodes uniformly at
random (with repetition, possibly itself) and adopts the most frequent color
among them, breaking ties uniformly at random.

**Tie-breaking.** Each node also draws a uniform ordering `σ` of its `h` sample
positions, and adopts the color of the tied position of smallest `σ`-rank
(`hplur`). All tied colors appear equally often, so this picks each tied color
with the same probability, as the paper requires.

* **Lemma 4.11** (`lemma_4_11`, `lemma_4_11_paper`): if color `j` has at most
  `a ≤ 2n/k` nodes, it has at least `a (1 + 2h²/k)` nodes after one round with
  probability at most `exp(-2 (a h²/k)² / n)`. A node adopts `j` only if it
  sees `j` at least twice (probability at most `(h²/2)(c_j/n)²`), or exactly
  once, in which case all `h` sampled colors are distinct and `j` must be at
  the position ranked first (probability `c_j/n`).
* **Theorem 4.12** (`theorem_4_12`, `theorem_4_12_log`): from a coloring with
  at most `(3/2)(n/k)` nodes per color, the process is not monochromatic after
  `T ≤ (k/(2h²)) log (4/3)` rounds, except with probability
  `k T exp(-2 n h⁴/k⁴)`.

The paper states Lemma 4.11 with the factor `1 + h²/k` but proves
`1 + 2h²/k`, which is also what Theorem 4.12 uses.
-/

namespace Plurality

open Finset Real Dynamics

variable {n k h : ℕ}

/-! ### Two finite-probability facts -/

/-- Fubini for uniform averages over a product. -/
lemma avg_prod_iter {β δ : Type*} [Fintype β] [Fintype δ] (F : β → δ → ℝ) :
    avg (fun p : β × δ => F p.1 p.2) = avg (fun d => avg (fun b => F b d)) := by
  unfold avg
  rw [Fintype.sum_prod_type, Fintype.card_prod, sum_comm, ← sum_div, div_div]
  push_cast
  ring_nf

/-- **Two distinct coordinates are independent.** -/
lemma avg_eval_two {γ : Type*} [Fintype γ] [Nonempty γ] (m : ℕ) {i i' : Fin m} (hii : i ≠ i')
    (G H : γ → ℝ) :
    avg (fun x : Fin m → γ => G (x i) * H (x i')) = avg G * avg H := by
  let F : Fin m → γ → ℝ := fun l => if l = i then G else if l = i' then H else fun _ => 1
  have hF (x : Fin m → γ) : G (x i) * H (x i') = ∏ l, F l (x l) := by
    rw [prod_eq_mul_of_mem i i' (mem_univ _) (mem_univ _) hii]
    · simp [F, hii.symm]
    · intro l _ hl
      simp [F, hl.1, hl.2]
  simp_rw [hF]
  rw [avg_prod_pi m F, prod_eq_mul_of_mem i i' (mem_univ _) (mem_univ _) hii]
  · simp [F, hii.symm]
  · intro l _ hl
    simp [F, hl.1, hl.2, avg_const]

/-! ### The model -/

/-- The randomness of one node in one round: `h` samples and an ordering of the
sample positions used to break ties. -/
abbrev HSample (n h : ℕ) := (Fin h → Fin n) × Equiv.Perm (Fin h)

/-- One round of `h`-plurality: the randomness of every node. -/
abbrev HRound (n h : ℕ) := Fin n → HSample n h

/-- How often the color at position `i` appears among the sampled colors `cs`. -/
def mult (cs : Fin h → Fin k) (i : Fin h) : ℕ := (univ.filter fun i' => cs i' = cs i).card

lemma one_le_mult (cs : Fin h → Fin k) (i : Fin h) : 1 ≤ mult cs i :=
  card_pos.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, rfl⟩⟩

lemma exists_top [NeZero h] (cs : Fin h → Fin k) : ∃ i, ∀ i', mult cs i' ≤ mult cs i := by
  obtain ⟨i, _, hi⟩ := exists_max_image univ (mult cs) univ_nonempty
  exact ⟨i, fun i' => hi i' (mem_univ _)⟩

/-- The ranks of the positions whose color is most frequent. -/
def topRanks (cs : Fin h → Fin k) (σ : Equiv.Perm (Fin h)) : Finset (Fin h) :=
  (univ.filter fun i => ∀ i', mult cs i' ≤ mult cs i).image σ

lemma topRanks_nonempty [NeZero h] (cs : Fin h → Fin k) (σ : Equiv.Perm (Fin h)) :
    (topRanks cs σ).Nonempty := by
  obtain ⟨i, hi⟩ := exists_top cs
  exact ⟨σ i, mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩, rfl⟩⟩

/-- The winning position: among the positions with a most frequent color, the
one ranked first by `σ`. -/
def winnerPos [NeZero h] (cs : Fin h → Fin k) (σ : Equiv.Perm (Fin h)) : Fin h :=
  σ.symm ((topRanks cs σ).min' (topRanks_nonempty cs σ))

/-- The **plurality color** of the sampled colors `cs`, ties broken by `σ`. -/
def hplur [NeZero h] (cs : Fin h → Fin k) (σ : Equiv.Perm (Fin h)) : Fin k :=
  cs (winnerPos cs σ)

/-- One round of `h`-plurality. -/
def hstep [NeZero h] (x : Config n k) (R : HRound n h) : Config n k :=
  fun v => hplur (fun i => x ((R v).1 i)) (R v).2

/-- The coloring after a list of rounds of `h`-plurality. -/
def hrun [NeZero h] (x : Config n k) (l : List (HRound n h)) : Config n k := l.foldl hstep x

lemma winnerPos_top [NeZero h] (cs : Fin h → Fin k) (σ : Equiv.Perm (Fin h)) (i' : Fin h) :
    mult cs i' ≤ mult cs (winnerPos cs σ) := by
  have hmem := min'_mem (topRanks cs σ) (topRanks_nonempty cs σ)
  obtain ⟨i, hi, he⟩ := mem_image.mp hmem
  have : winnerPos cs σ = i := by rw [winnerPos, ← he, Equiv.symm_apply_apply]
  rw [this]
  exact (mem_filter.mp hi).2 i'

/-- **Seen exactly once.** If `j` appears at exactly one sample position and
wins, then all sampled colors are distinct and `j` is at the position ranked
first. -/
lemma hplur_first [NeZero h] {cs : Fin h → Fin k} {σ : Equiv.Perm (Fin h)} {j : Fin k}
    (hj : hplur cs σ = j) (h1 : (univ.filter fun i => cs i = j).card = 1) :
    cs (σ.symm 0) = j := by
  have hw : mult cs (winnerPos cs σ) = 1 := by
    rw [mult, show cs (winnerPos cs σ) = j from hj, h1]
  -- every position is top, so the first rank is a top rank
  have hall : ∀ i, ∀ i', mult cs i' ≤ mult cs i := fun i i' => by
    have := winnerPos_top cs σ i'
    have := one_le_mult cs i
    omega
  have h0 : (0 : Fin h) ∈ topRanks cs σ :=
    mem_image.mpr ⟨σ.symm 0, mem_filter.mpr ⟨mem_univ _, hall _⟩, by simp⟩
  have hmin : (topRanks cs σ).min' (topRanks_nonempty cs σ) = 0 :=
    le_antisymm (min'_le _ _ h0) (Fin.zero_le _)
  rw [← hj, hplur, winnerPos, hmin]

/-! ### One node -/

variable [NeZero h]

/-- The indicator that a node with randomness `t` adopts `j`. -/
def hadopt (x : Config n k) (j : Fin k) (t : HSample n h) : ℝ :=
  if hplur (fun i => x (t.1 i)) t.2 = j then 1 else 0

lemma hadopt_zero_one (x : Config n k) (j : Fin k) (t : HSample n h) :
    hadopt x j t = 0 ∨ hadopt x j t = 1 := by
  unfold hadopt; split_ifs <;> simp

lemma count_hstep_eq_sum (x : Config n k) (R : HRound n h) (j : Fin k) :
    (count (hstep x R) j : ℝ) = ∑ v, hadopt x j (R v) := by
  unfold count hadopt
  rw [card_filter]
  push_cast
  rfl

/-- The number of sample positions showing color `j`. -/
def seen (x : Config n k) (j : Fin k) (s : Fin h → Fin n) : ℕ :=
  (univ.filter fun i => x (s i) = j).card

omit [NeZero h] in
/-- `N(N-1) = ∑_{i ≠ i'} 𝟙ᵢ 𝟙ᵢ'` for the number `N` of positions showing `j`. -/
lemma seen_mul_pred (x : Config n k) (j : Fin k) (s : Fin h → Fin n) :
    (seen x j s : ℝ) * ((seen x j s : ℝ) - 1)
      = ∑ i, ∑ i' ∈ univ.erase i,
          (if x (s i) = j then (1 : ℝ) else 0) * (if x (s i') = j then (1 : ℝ) else 0) := by
  set e : Fin h → ℝ := fun i => if x (s i) = j then 1 else 0 with he
  have hN : (seen x j s : ℝ) = ∑ i, e i := by
    unfold seen; rw [card_filter]; push_cast; rfl
  have he2 (i : Fin h) : e i * e i = e i := by simp only [he]; split_ifs <;> norm_num
  have hrow (i : Fin h) : ∑ i' ∈ univ.erase i, e i * e i' = e i * (∑ i', e i') - e i := by
    rw [← mul_sum, ← add_sum_erase univ e (mem_univ i), mul_add, he2]
    ring
  have hR : (∑ i, ∑ i' ∈ univ.erase i,
      (if x (s i) = j then (1 : ℝ) else 0) * (if x (s i') = j then (1 : ℝ) else 0))
      = ∑ i, ∑ i' ∈ univ.erase i, e i * e i' := rfl
  rw [hR, sum_congr rfl fun i _ => hrow i, sum_sub_distrib, ← sum_mul, ← hN]
  ring

/-- **Adoption probability** (proof of Lemma 4.11): a node adopts `j` with
probability at most `x_j + (h²/2) x_j²`, where `x_j = c_j/n`. -/
lemma avg_hadopt_le (hn : 1 ≤ n) (x : Config n k) (j : Fin k) :
    avg (hadopt (h := h) x j) ≤ frac x j + (h : ℝ) ^ 2 / 2 * frac x j ^ 2 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  -- pointwise: `𝟙[adopt j] ≤ 𝟙[first position shows j] + N(N-1)/2`
  have hpt (t : HSample n h) : hadopt x j t
      ≤ (if x (t.1 (t.2.symm 0)) = j then (1 : ℝ) else 0)
        + (seen x j t.1 : ℝ) * ((seen x j t.1 : ℝ) - 1) / 2 := by
    have hq : (0 : ℝ) ≤ (seen x j t.1 : ℝ) * ((seen x j t.1 : ℝ) - 1) / 2 := by
      rcases Nat.eq_zero_or_pos (seen x j t.1) with h0 | h0
      · simp [h0]
      · have : (1 : ℝ) ≤ seen x j t.1 := by exact_mod_cast h0
        have : 0 ≤ (seen x j t.1 : ℝ) - 1 := by linarith
        positivity
    unfold hadopt
    split_ifs with hw hf
    · linarith
    · -- `j` wins without being at the first rank: it is seen at least twice
      have hpos : 1 ≤ seen x j t.1 := card_pos.mpr ⟨winnerPos _ t.2,
        mem_filter.mpr ⟨mem_univ _, hw⟩⟩
      have h2 : 2 ≤ seen x j t.1 := by
        by_contra hlt
        exact hf (hplur_first hw (by unfold seen at hpos hlt; omega))
      have : (2 : ℝ) ≤ seen x j t.1 := by exact_mod_cast h2
      nlinarith
    · linarith
    · linarith
  calc avg (hadopt (h := h) x j)
      ≤ avg (fun t : HSample n h => (if x (t.1 (t.2.symm 0)) = j then (1 : ℝ) else 0)
          + (seen x j t.1 : ℝ) * ((seen x j t.1 : ℝ) - 1) / 2) := avg_le_avg hpt
    _ = avg (fun t : HSample n h => if x (t.1 (t.2.symm 0)) = j then (1 : ℝ) else 0)
          + avg (fun s : Fin h → Fin n => (seen x j s : ℝ) * ((seen x j s : ℝ) - 1) / 2) := by
        rw [avg_add, avg_fst_mul (fun s : Fin h → Fin n =>
          (seen x j s : ℝ) * ((seen x j s : ℝ) - 1) / 2)]
    _ ≤ frac x j + (h : ℝ) ^ 2 / 2 * frac x j ^ 2 := by
        -- the first position shows `j` with probability `x_j`
        have h1 : avg (fun t : HSample n h => if x (t.1 (t.2.symm 0)) = j then (1 : ℝ) else 0)
            = frac x j := by
          rw [avg_prod_iter (fun (s : Fin h → Fin n) (σ : Equiv.Perm (Fin h)) =>
            if x (s (σ.symm 0)) = j then (1 : ℝ) else 0)]
          have (σ : Equiv.Perm (Fin h)) : avg (fun s : Fin h → Fin n =>
              if x (s (σ.symm 0)) = j then (1 : ℝ) else 0) = frac x j := by
            rw [avg_eval h (σ.symm 0) (fun v => if x v = j then (1 : ℝ) else 0)]
            exact avg_color_indicator x j
          simp_rw [this]
          exact avg_const _
        -- `𝔼[N(N-1)] = h(h-1) x_j²`
        have hNN : avg (fun s : Fin h → Fin n => (seen x j s : ℝ) * ((seen x j s : ℝ) - 1))
            = h * (h - 1) * frac x j ^ 2 := by
          simp_rw [seen_mul_pred]
          rw [avg_sum]
          have hrow (i : Fin h) : avg (fun s : Fin h → Fin n => ∑ i' ∈ univ.erase i,
              (if x (s i) = j then (1 : ℝ) else 0) * (if x (s i') = j then (1 : ℝ) else 0))
              = (h - 1) * frac x j ^ 2 := by
            rw [avg_sum]
            rw [sum_congr rfl fun i' hi' => by
              rw [avg_eval_two h (Ne.symm (mem_erase.mp hi').1)
                (fun v => if x v = j then (1 : ℝ) else 0)
                (fun v => if x v = j then (1 : ℝ) else 0), avg_color_indicator]]
            rw [sum_const, card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin,
              nsmul_eq_mul, Nat.cast_sub (NeZero.one_le), sq]
            push_cast
            ring
          simp_rw [hrow]
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
        have h2 : avg (fun s : Fin h → Fin n => (seen x j s : ℝ) * ((seen x j s : ℝ) - 1) / 2)
            ≤ (h : ℝ) ^ 2 / 2 * frac x j ^ 2 := by
          have e : (fun s : Fin h → Fin n => (seen x j s : ℝ) * ((seen x j s : ℝ) - 1) / 2)
              = fun s => (1 / 2) * ((seen x j s : ℝ) * ((seen x j s : ℝ) - 1)) :=
            funext fun s => by ring
          rw [e, avg_const_mul, hNN]
          have : 0 ≤ frac x j ^ 2 := sq_nonneg _
          have : (0 : ℝ) ≤ h := Nat.cast_nonneg _
          nlinarith
        linarith

/-! ### Lemma 4.11 -/

/-- **Lemma 4.11 (growth rate under `h`-plurality).** If color `j` has at most
`a ≤ 2n/k` nodes, then after one round it has at least `a (1 + 2h²/k)` nodes
with probability at most `exp(-2 (a h²/k)² / n)`. -/
theorem lemma_4_11 (hn : 1 ≤ n) (hk : 1 ≤ k) (x : Config n k) (j : Fin k) {a : ℝ}
    (hx : (count x j : ℝ) ≤ a) (ha : a ≤ 2 * n / k) :
    avg (fun R : HRound n h =>
        if a * (1 + 2 * h ^ 2 / k) ≤ count (hstep x R) j then (1 : ℝ) else 0)
      ≤ exp (-(2 * (a * h ^ 2 / k) ^ 2 / n)) := by
  haveI : Nonempty (HSample n h) := ⟨(fun _ => ⟨0, hn⟩, 1)⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  set c : ℝ := (count x j : ℝ) with hc
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  have ha0 : 0 ≤ a := le_trans hc0 hx
  have hh0 : (0 : ℝ) ≤ (h : ℝ) ^ 2 := sq_nonneg _
  -- `𝔼[C'_j] ≤ c + h² c²/(2n) ≤ a + a h²/k`
  have hμ : ∑ _v : Fin n, avg (hadopt (h := h) x j) ≤ a + a * h ^ 2 / k := by
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hp := avg_hadopt_le (h := h) hn x j
    have hf : frac x j = c / n := rfl
    calc (n : ℝ) * avg (hadopt (h := h) x j)
        ≤ n * (frac x j + (h : ℝ) ^ 2 / 2 * frac x j ^ 2) :=
          mul_le_mul_of_nonneg_left hp hn0.le
      _ = c + (h : ℝ) ^ 2 * c ^ 2 / (2 * n) := by rw [hf]; field_simp
      _ ≤ a + (h : ℝ) ^ 2 * a ^ 2 / (2 * n) := by
          have : c ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hc0 hx 2
          have : (h : ℝ) ^ 2 * c ^ 2 / (2 * n) ≤ (h : ℝ) ^ 2 * a ^ 2 / (2 * n) :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left this hh0) (by positivity)
          linarith
      _ ≤ a + a * h ^ 2 / k := by
          have hak : a * k ≤ 2 * n := by rwa [le_div_iff₀ hk0] at ha
          have : (h : ℝ) ^ 2 * a ^ 2 / (2 * n) ≤ a * h ^ 2 / k := by
            rw [div_le_div_iff₀ (by positivity) hk0]
            nlinarith [mul_le_mul_of_nonneg_left hak (mul_nonneg ha0 hh0)]
          linarith
  have hH := avg_hoeffding (fun (_ : Fin n) t => hadopt (h := h) x j t)
    (fun _ t => hadopt_zero_one x j t) (lam := a * h ^ 2 / k) (by positivity)
  refine le_trans (avg_le_avg fun R => ?_) hH
  have hC := count_hstep_eq_sum x R j
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exfalso
    apply h2
    rw [← hC]
    have : a * (1 + 2 * h ^ 2 / k) = a + a * h ^ 2 / k + a * h ^ 2 / k := by ring
    linarith
  · norm_num
  · exact le_rfl

omit [NeZero h] in
/-- For `a ≥ n/k`, the bound of Lemma 4.11 is at most `exp(-2 n h⁴ / k⁴)`. -/
lemma exp_bound_le (hn : 1 ≤ n) (hk : 1 ≤ k) {a : ℝ} (ha : (n : ℝ) / k ≤ a) :
    exp (-(2 * (a * h ^ 2 / k) ^ 2 / n)) ≤ exp (-(2 * n * (h : ℝ) ^ 4 / (k : ℝ) ^ 4)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  apply exp_le_exp.mpr
  rw [neg_le_neg_iff]
  have h1 : ((n : ℝ) / k) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (by positivity) ha 2
  have e1 : 2 * (a * h ^ 2 / k) ^ 2 / n = 2 * a ^ 2 * (h : ℝ) ^ 4 / ((k : ℝ) ^ 2 * n) := by
    field_simp
  have e2 : 2 * n * (h : ℝ) ^ 4 / (k : ℝ) ^ 4
      = 2 * ((n : ℝ) / k) ^ 2 * (h : ℝ) ^ 4 / ((k : ℝ) ^ 2 * n) := by
    field_simp
  rw [e1, e2]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have : (0 : ℝ) ≤ (h : ℝ) ^ 4 := by positivity
  nlinarith

/-- **Lemma 4.11, as stated in the paper** (with the factor `1 + 2h²/k` that its
proof gives): if `n/k ≤ c_j ≤ 2n/k`, then
`P(C_{j,t+1} ≥ (1 + 2h²/k) c_j) ≤ exp(-2 n h⁴/k⁴)`. -/
theorem lemma_4_11_paper (hn : 1 ≤ n) (hk : 1 ≤ k) (x : Config n k) (j : Fin k)
    (h1 : (n : ℝ) / k ≤ count x j) (h2 : (count x j : ℝ) ≤ 2 * n / k) :
    avg (fun R : HRound n h =>
        if (count x j : ℝ) * (1 + 2 * h ^ 2 / k) ≤ count (hstep x R) j then (1 : ℝ) else 0)
      ≤ exp (-(2 * n * (h : ℝ) ^ 4 / (k : ℝ) ^ 4)) :=
  (lemma_4_11 hn hk x j le_rfl h2).trans (exp_bound_le hn hk h1)

/-! ### Theorem 4.12 -/

/-- The threshold of round `t`: `(3/2)(n/k)(1 + 2h²/k)^t`. -/
def hBalancedSet (n : ℕ) {k : ℕ} (h : ℕ) (j : Fin k) (t : ℕ) : Set (Config n k) :=
  {x | (count x j : ℝ) ≤ 3 / 2 * ((n : ℝ) / k) * (1 + 2 * (h : ℝ) ^ 2 / k) ^ t}

/-- **Theorem 4.12 (lower bound for `h`-plurality).** Let `k ≥ 3`. If every color
starts with at most `(3/2)(n/k)` nodes and `(3/2)(1 + 2h²/k)^T ≤ 2`, then the
coloring after `T` rounds of `h`-plurality is monochromatic with probability
at most `k T exp(-2 n h⁴/k⁴)`. -/
theorem theorem_4_12 (hn : 1 ≤ n) (hk : 3 ≤ k) (x : Config n k)
    (hx : ∀ j, (count x j : ℝ) ≤ 3 / 2 * ((n : ℝ) / k)) {T : ℕ}
    (hT : 3 / 2 * (1 + 2 * (h : ℝ) ^ 2 / k) ^ T ≤ 2) :
    expList (HRound n h) T (fun l => if Monochromatic (hrun x l) then (1 : ℝ) else 0)
      ≤ k * T * exp (-(2 * n * (h : ℝ) ^ 4 / (k : ℝ) ^ 4)) := by
  classical
  haveI : Nonempty (HSample n h) := ⟨(fun _ => ⟨0, hn⟩, 1)⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hk1 : 1 ≤ k := by omega
  set q : ℝ := 1 + 2 * (h : ℝ) ^ 2 / k with hq
  have hq1 : 1 ≤ q := by
    have : 0 ≤ 2 * (h : ℝ) ^ 2 / k := by positivity
    linarith
  set p : ℝ := exp (-(2 * n * (h : ℝ) ^ 4 / (k : ℝ) ^ 4))
  have hnk : (0 : ℝ) ≤ n / k := by positivity
  -- each color stays below its threshold
  have hcolor (j : Fin k) : expList (HRound n h) T (fun l =>
      if hrun x l ∈ hBalancedSet n h j T then (0 : ℝ) else 1) ≤ T * p := by
    refine expList_escape hstep (exp_pos _).le T (hBalancedSet n h j) x
      (by simpa [hBalancedSet] using hx j) fun t ht y hy => ?_
    set a : ℝ := 3 / 2 * ((n : ℝ) / k) * q ^ t with ha
    have hqt : 1 ≤ q ^ t := one_le_pow₀ hq1
    have ha1 : (n : ℝ) / k ≤ a := by
      rw [ha]; nlinarith [mul_le_mul_of_nonneg_left hqt hnk]
    have ha2 : a ≤ 2 * n / k := by
      have : q ^ t ≤ q ^ T := pow_le_pow_right₀ hq1 ht.le
      have : a ≤ 3 / 2 * q ^ T * (n / k) := by
        rw [ha]; nlinarith [mul_le_mul_of_nonneg_left this hnk]
      have : 3 / 2 * q ^ T * ((n : ℝ) / k) ≤ 2 * ((n : ℝ) / k) :=
        mul_le_mul_of_nonneg_right hT hnk
      have e : 2 * ((n : ℝ) / k) = 2 * n / k := by ring
      linarith
    have h411 := (lemma_4_11 (h := h) hn hk1 y j hy ha2).trans (exp_bound_le hn hk1 ha1)
    refine le_trans (avg_le_avg fun R => ?_) h411
    simp only [hBalancedSet, Set.mem_setOf_eq]
    split_ifs with h1 h2 h2
    · norm_num
    · norm_num
    · exact le_rfl
    · exfalso
      apply h1
      push Not at h2
      have e : 3 / 2 * ((n : ℝ) / k) * q ^ (t + 1) = a * q := by rw [ha, pow_succ]; ring
      rw [e]
      exact h2.le
  -- a monochromatic coloring has a color above its threshold
  have hpt (l : List (HRound n h)) : (if Monochromatic (hrun x l) then (1 : ℝ) else 0)
      ≤ ∑ j, (if hrun x l ∈ hBalancedSet n h j T then (0 : ℝ) else 1) := by
    split_ifs with hm
    · obtain ⟨j, hj⟩ := hm
      have hcn : (count (hrun x l) j : ℝ) = n := by exact_mod_cast (mono_iff_count _ _).mp hj
      have hnot : hrun x l ∉ hBalancedSet n h j T := by
        simp only [hBalancedSet, Set.mem_setOf_eq, hcn, not_le]
        have h3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
        have : 3 / 2 * ((n : ℝ) / k) * q ^ T ≤ 2 * ((n : ℝ) / k) := by
          nlinarith [mul_le_mul_of_nonneg_right hT hnk]
        have : 2 * ((n : ℝ) / k) < n := by
          rw [mul_div_assoc', div_lt_iff₀ hk0]; nlinarith
        linarith
      calc (1 : ℝ) = if hrun x l ∈ hBalancedSet n h j T then 0 else 1 := by rw [if_neg hnot]
        _ ≤ _ := single_le_sum (f := fun j => if hrun x l ∈ hBalancedSet n h j T then (0 : ℝ)
            else 1) (fun j _ => by split <;> norm_num) (mem_univ j)
    · exact sum_nonneg fun j _ => by split <;> norm_num
  calc _ ≤ expList (HRound n h) T
        (fun l => ∑ j, (if hrun x l ∈ hBalancedSet n h j T then (0 : ℝ) else 1)) :=
        expList_le_expList hpt
    _ = ∑ j, expList (HRound n h) T
        (fun l => if hrun x l ∈ hBalancedSet n h j T then (0 : ℝ) else 1) := expList_sum _ _ _
    _ ≤ ∑ _j : Fin k, (T : ℝ) * p := sum_le_sum fun j _ => hcolor j
    _ = k * T * p := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- **Theorem 4.12, logarithmic form.** Under the hypotheses of `theorem_4_12`,
the coloring is still not monochromatic after `T ≤ (k/(2h²)) log (4/3)` rounds,
i.e. `Ω(k/h²)` rounds, except with probability `k T exp(-2 n h⁴/k⁴)`. -/
theorem theorem_4_12_log (hn : 1 ≤ n) (hk : 3 ≤ k) (x : Config n k)
    (hx : ∀ j, (count x j : ℝ) ≤ 3 / 2 * ((n : ℝ) / k)) {T : ℕ}
    (hT : (T : ℝ) ≤ k / (2 * (h : ℝ) ^ 2) * Real.log (4 / 3)) :
    expList (HRound n h) T (fun l => if Monochromatic (hrun x l) then (1 : ℝ) else 0)
      ≤ k * T * exp (-(2 * n * (h : ℝ) ^ 4 / (k : ℝ) ^ 4)) := by
  refine theorem_4_12 hn hk x hx ?_
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hh0 : (0 : ℝ) < (h : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ h := by exact_mod_cast NeZero.one_le
    positivity
  have h1 : (1 + 2 * (h : ℝ) ^ 2 / k) ^ T ≤ exp (2 * (h : ℝ) ^ 2 * T / k) := by
    calc (1 + 2 * (h : ℝ) ^ 2 / k) ^ T ≤ exp (2 * (h : ℝ) ^ 2 / k) ^ T :=
          pow_le_pow_left₀ (by positivity) (by linarith [add_one_le_exp (2 * (h : ℝ) ^ 2 / k)]) T
      _ = exp (2 * (h : ℝ) ^ 2 * T / k) := by rw [← exp_nat_mul]; ring_nf
  have h2 : exp (2 * (h : ℝ) ^ 2 * T / k) ≤ 4 / 3 := by
    rw [← exp_log (show (0 : ℝ) < 4 / 3 by norm_num)]
    apply exp_le_exp.mpr
    rw [div_le_iff₀ hk0]
    have := mul_le_mul_of_nonneg_left hT (show 0 ≤ 2 * (h : ℝ) ^ 2 by positivity)
    have e : 2 * (h : ℝ) ^ 2 * (k / (2 * (h : ℝ) ^ 2) * Real.log (4 / 3))
        = Real.log (4 / 3) * k := by
      have : (h : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne h)
      field_simp
    linarith
  linarith

end Plurality
