import Plurality.Saturation
import Dynamics.Phases

/-!
# The general upper bound (Theorem 3.8)

If `m` is the unique plurality color, `c_m ≥ n/λ` for some `λ ≥ 3` and the
bias is at least `Λ = 22 √(λ n log n)`, then 3-majority reaches consensus on
`m` within `O(λ log n)` rounds with high probability.

The proof runs the chain through nested phases and applies
`Dynamics.Kernel.nested_phases` (the paper's Lemma A.4) to `kernel maj3`.

* **Growth phases** `growthSet i`: either `c_m > 2n/3`, or `m` is the unique
  plurality color with `c_m ≥ n/λ` and bias at least `Λ (1 + 1/(6λ))^i`.
  Lemma 3.5 moves the chain from phase `i` to `i + 1`, applied to every
  other color that currently has a node (colors without nodes stay empty).
  Once `Λ (1 + 1/(6λ))^i > n` the second alternative is impossible, so the
  chain has `c_m > 2n/3`.
* **Saturation phases** `satSet j`: fewer than
  `max ((n/3)(17/18)^j, n^{1/4} log n)` nodes disagree with `m`. By Lemma 3.7
  this threshold shrinks by `17/18` per round down to `n^{1/4} log n`.
* **Consensus** `monoSet`: from below `n^{1/4} log n` dissenters, one round
  reaches consensus except with probability `n^{-1/5}` (Lemma 3.7).

## Differences from the paper

* The paper's saturation sets also require `s(c) ≥ n/3`, which Lemma 3.7
  does not show is preserved. Here the saturation sets only bound
  `n - c_m < n/3`, which already implies a unique plurality color and
  `s(c) ≥ n/3` (`of_dissent_lt`).
* The paper charges each growth round `1/n²`, but Lemma 3.5 bounds the
  failure against *one* competing color, so a round needs a union bound over
  all of them. Only colors that currently have a node matter (the others stay
  empty), and there are fewer than `n - c_m` of them, so a round fails with
  probability at most `1/n`. The final failure probability is therefore
  `O(λ log n / n)` instead of `O(λ log n / n²)`.
* The hypothesis `λ < √n` of the paper is not needed for the proof. It only
  makes the bias hypothesis satisfiable (`Λ ≤ n`) and the bound nontrivial.
* "Sufficiently large `n`" is `log n ≥ 40`, and `k ≥ 2` excludes the trivial
  single-color case.
-/

namespace Plurality

open Finset Real Dynamics
open ThreeMajority (Tgt3 tgt3_nonempty)

/-! ### The phases -/

/-- Growth phase `i`: `c_m > 2n/3`, or `m` is the unique plurality color with at
least `n/λ` nodes and bias at least `Λ (1 + 1/(6λ))^i`. -/
def growthSet (n : ℕ) {k : ℕ} (m : Fin k) (lam Λ : ℝ) (i : ℕ) : Set (Config n k) :=
  {x | 2 / 3 * (n : ℝ) < count x m ∨
    (argmaxSet (count x) = {m} ∧ (n : ℝ) / lam ≤ count x m ∧
      Λ * (1 + 1 / lam / 6) ^ i ≤ bias (count x))}

/-- Saturation phase `j`: fewer than `max ((n/3)(17/18)^j) (n^{1/4} log n)`
nodes disagree with `m`. -/
def satSet (n : ℕ) {k : ℕ} (m : Fin k) (j : ℕ) : Set (Config n k) :=
  {x | (n : ℝ) - count x m
    < max ((n : ℝ) / 3 * (17 / 18) ^ j) ((n : ℝ) ^ (1 / 4 : ℝ) * Real.log n)}

/-- Consensus on `m`. -/
def monoSet (n : ℕ) {k : ℕ} (m : Fin k) : Set (Config n k) := {x | Mono x m}

variable {n k : ℕ}

/-! ### Bookkeeping for one round -/

lemma prob_mono_set {α : Type*} [Fintype α] (p : Distribution α) {A B : Set α} (h : A ⊆ B) :
    p.prob (· ∈ A) ≤ p.prob (· ∈ B) := by
  classical
  unfold Distribution.prob
  refine p.expect_mono fun a => ?_
  by_cases ha : a ∈ A
  · simp [ha, h ha]
  · by_cases hb : a ∈ B <;> simp [ha, hb]

/-- One round of 3-majority lands in `A` with probability at least
`1 - 𝔼[bad]`, if every round that misses `A` is charged at least `1` by the
nonnegative `bad`. -/
lemma le_prob_step [NeZero n] (x : Config n k) (A : Set (Config n k)) (bad : Tgt3 n → ℝ)
    (h0 : ∀ r, 0 ≤ bad r) (h1 : ∀ r, step x r ∉ A → 1 ≤ bad r) :
    1 - avg bad ≤ ((kernel maj3) x).prob (· ∈ A) := by
  rw [kernel, Dynamics.Kernel.prob_ofStep]
  have e : 1 - avg bad = avg (fun r => 1 - bad r) := by rw [avg_sub, avg_const]
  rw [e]
  refine avg_le_avg fun r => ?_
  by_cases hr : stepWith maj3 x r ∈ A
  · simp only [hr, ↓reduceIte]
    linarith [h0 r]
  · have := h1 r hr
    simp only [hr, ↓reduceIte]
    linarith

lemma ite_one_zero_nonneg (P : Prop) [Decidable P] : (0 : ℝ) ≤ if P then 1 else 0 := by
  split <;> norm_num

/-! ### Counting facts -/

lemma count_add_count_le (x : Config n k) {j m : Fin k} (hj : j ≠ m) :
    count x j + count x m ≤ n := by
  have hs := sum_count x
  rw [← add_sum_erase univ _ (mem_univ m)] at hs
  have := single_le_sum (f := count x) (fun _ _ => Nat.zero_le _)
    (mem_erase.mpr ⟨hj, mem_univ j⟩)
  omega

/-- A color without nodes stays without nodes. -/
lemma count_step_eq_zero (x : Config n k) {j : Fin k} (hj : count x j = 0) (r : Tgt3 n) :
    count (step x r) j = 0 := by
  unfold count at *
  rw [card_eq_zero, filter_eq_empty_iff] at *
  intro v _ hv
  simp only [step, stepWith] at hv
  rcases maj3_mem (x (r v).1) (x (r v).2.1) (x (r v).2.2) with h | h | h <;>
    exact hj (mem_univ _) (h.symm.trans hv)

lemma argmaxSet_eq_of_lt {c : Fin k → ℕ} {m : Fin k} (h : ∀ j, j ≠ m → c j < c m) :
    argmaxSet c = {m} := by
  have hmax : maxc c = c m := by
    refine le_antisymm (Finset.sup_le fun j _ => ?_) (le_maxc c m)
    by_cases hj : j = m
    · rw [hj]
    · exact (h j hj).le
  ext j
  simp only [mem_argmaxSet, mem_singleton, hmax]
  constructor
  · intro hj
    by_contra hne
    exact (h j hne).ne hj
  · rintro rfl
    rfl

/-- If `m` leads every other color by at least `g > 0` (and has at least `g`
nodes), then `m` is the unique plurality color and the bias is at least `g`. -/
lemma le_bias_of_gap {c : Fin k → ℕ} {m : Fin k} {g : ℝ} (hg : 0 < g) (hgm : g ≤ c m)
    (h : ∀ j, j ≠ m → (c j : ℝ) + g ≤ c m) :
    argmaxSet c = {m} ∧ g ≤ bias c := by
  have hlt : ∀ j, j ≠ m → c j < c m := fun j hj => by
    have := h j hj
    exact_mod_cast (show (c j : ℝ) < c m by linarith)
  have hM := argmaxSet_eq_of_lt hlt
  refine ⟨hM, ?_⟩
  have hcm := argmaxSet_eq_singleton hM
  have hsec : (secondc c : ℝ) + g ≤ c m := by
    unfold secondc
    rcases (univ.filter fun h => c h ≠ maxc c).eq_empty_or_nonempty with he | hne
    · rw [he]
      simpa using hgm
    · obtain ⟨j, hj, hsup⟩ := exists_mem_eq_sup _ hne c
      rw [hsup]
      exact h j fun e => (mem_filter.mp hj).2 (e ▸ hcm)
  rw [bias_of_singleton hM]
  have hle := secondc_le_maxc c
  rw [Nat.cast_sub hle, ← hcm]
  linarith

/-- If fewer than a third of the nodes disagree with `m`, then `m` is the
unique plurality color and the bias is at least `n/3`. -/
lemma of_dissent_lt (x : Config n k) {m : Fin k} (hu : (n : ℝ) - count x m < n / 3) :
    argmaxSet (count x) = {m} ∧ (n : ℝ) / 3 ≤ bias (count x) := by
  have hM : argmaxSet (count x) = {m} := argmaxSet_eq_of_lt fun j hj => by
    have := count_add_count_le x hj
    have : ((count x j + count x m : ℕ) : ℝ) ≤ n := by exact_mod_cast this
    push_cast at this
    exact_mod_cast (show (count x j : ℝ) < count x m by linarith)
  refine ⟨hM, ?_⟩
  have := bias_ge_of_singleton x hM
  linarith

/-- `n^{1/4} log n ≤ n/3` for `log n ≥ 40`. -/
lemma quarter_log_le_third (hL : 40 ≤ Real.log n) :
    (n : ℝ) ^ (1 / 4 : ℝ) * Real.log n ≤ n / 3 := by
  have hn : 1 ≤ n := one_le_of_log_pos (by linarith)
  set L := Real.log n with hLdef
  have hq : (n : ℝ) ^ (1 / 4 : ℝ) = exp (L / 4) := by rw [rpow_eq_exp hn, ← hLdef]; ring_nf
  have hnexp : (n : ℝ) = exp (L / 4) * exp (3 * L / 4) := by
    rw [← exp_add, natCast_eq_exp hn, ← hLdef]; ring_nf
  have h := mul_le_exp (show (20 : ℝ) ≤ 3 * L / 4 by linarith)
  have h3 : 3 * L ≤ exp (3 * L / 4) := by nlinarith
  have := mul_le_mul_of_nonneg_left h3 (exp_pos (L / 4)).le
  rw [hq, hnexp]
  linarith

/-! ### Saturation phases -/

lemma satSet_sub (hL : 40 ≤ Real.log n) (m : Fin k) (j : ℕ) :
    satSet n m j ⊆ {x | (n : ℝ) - count x m < n / 3} := by
  intro x hx
  have hB := quarter_log_le_third hL
  have hpow : ((17 : ℝ) / 18) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have ha : (n : ℝ) / 3 * (17 / 18) ^ j ≤ n / 3 := by
    have : (0 : ℝ) ≤ n / 3 := by positivity
    nlinarith
  exact lt_of_lt_of_le hx (max_le ha hB)

lemma satSet_succ_sub (m : Fin k) (j : ℕ) : satSet n m (j + 1) ⊆ satSet n m j := by
  intro x hx
  simp only [satSet, Set.mem_setOf_eq] at hx ⊢
  refine lt_of_lt_of_le hx (max_le_max ?_ le_rfl)
  have : (0 : ℝ) ≤ n / 3 * (17 / 18) ^ j := by positivity
  rw [pow_succ]
  nlinarith

/-- **One saturation round.** From `satSet j`, the chain is in `satSet (j+1)`
after one round except with probability `1/n²` (Lemma 3.7). -/
theorem sat_step [NeZero n] (hL : 40 ≤ Real.log n) (m : Fin k) (j : ℕ) {x : Config n k}
    (hx : x ∈ satSet n m j) :
    1 - 1 / (n : ℝ) ^ 2 ≤ ((kernel maj3) x).prob (· ∈ satSet n m (j + 1)) := by
  set B := (n : ℝ) ^ (1 / 4 : ℝ) * Real.log n with hB
  have hu3 : (n : ℝ) - count x m < n / 3 := satSet_sub hL m j hx
  obtain ⟨hM, hs⟩ := of_dissent_lt x hu3
  have hx' : (n : ℝ) - count x m < max ((n : ℝ) / 3 * (17 / 18) ^ j) B := hx
  by_cases hbig : B ≤ (n : ℝ) - count x m
  · have h7 := lemma_3_7_i hL x hM hs hbig
    have hua : (n : ℝ) - count x m < (n : ℝ) / 3 * (17 / 18) ^ j := by
      rcases lt_max_iff.mp hx' with h | h
      · exact h
      · linarith
    refine le_trans (by linarith) (le_prob_step x _ _ (fun r => ite_one_zero_nonneg _)
      fun r hr => ?_)
    split_ifs with h
    · exact le_rfl
    · exfalso
      apply hr
      change (n : ℝ) - count (step x r) m < max ((n : ℝ) / 3 * (17 / 18) ^ (j + 1)) B
      refine lt_of_lt_of_le ?_ (le_max_left _ _)
      rw [pow_succ]
      push Not at h
      nlinarith
  · have h7 := (lemma_3_7_ii hL x hM (lt_of_not_ge hbig)).2
    refine le_trans (by linarith) (le_prob_step x _ _ (fun r => ite_one_zero_nonneg _)
      fun r hr => ?_)
    split_ifs with h
    · exact le_rfl
    · exfalso
      apply hr
      change (n : ℝ) - count (step x r) m < max ((n : ℝ) / 3 * (17 / 18) ^ (j + 1)) B
      push Not at h
      exact lt_of_lt_of_le h (le_max_right _ _)

/-- **The last round.** Below `n^{1/4} log n` dissenters, one round reaches
consensus except with probability `n^{-1/5}` (Lemma 3.7). -/
theorem mono_step [NeZero n] (hL : 40 ≤ Real.log n) (m : Fin k) {x : Config n k}
    (hx : (n : ℝ) - count x m < (n : ℝ) ^ (1 / 4 : ℝ) * Real.log n) :
    1 - (n : ℝ) ^ (-(1 / 5 : ℝ)) ≤ ((kernel maj3) x).prob (· ∈ monoSet n m) := by
  have hu3 : (n : ℝ) - count x m < n / 3 := lt_of_lt_of_le hx (quarter_log_le_third hL)
  obtain ⟨hM, _⟩ := of_dissent_lt x hu3
  have h7 := (lemma_3_7_ii hL x hM hx).1
  refine le_trans (by linarith) (le_prob_step x _ _ (fun r => ite_one_zero_nonneg _)
    fun r hr => ?_)
  split_ifs with h
  · exact le_rfl
  · exfalso
    apply hr
    change Mono (step x r) m
    rw [mono_iff_count]
    push Not at h
    have := count_le (step x r) m
    have : (n : ℝ) ≤ count (step x r) m := by linarith
    have : n ≤ count (step x r) m := by exact_mod_cast this
    omega

lemma mono_stay [NeZero n] (m : Fin k) {x : Config n k} (hx : x ∈ monoSet n m) :
    1 ≤ ((kernel maj3) x).prob (· ∈ monoSet n m) := by
  have h := le_prob_step x (monoSet n m) (fun _ => 0) (fun _ => le_rfl)
    fun r hr => absurd (stepWith_mono maj3_mem hx r) hr
  rwa [avg_const, sub_zero] at h

/-! ### Growth phases -/

lemma growthSet_succ_sub (m : Fin k) {lam Λ : ℝ} (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (i : ℕ) :
    growthSet n m lam Λ (i + 1) ⊆ growthSet n m lam Λ i := by
  rintro x (h | ⟨hM, hcm, hs⟩)
  · exact Or.inl h
  · refine Or.inr ⟨hM, hcm, le_trans ?_ hs⟩
    have hq : 1 ≤ 1 + 1 / lam / 6 := by
      have : 0 ≤ 1 / lam / 6 := by positivity
      linarith
    rw [pow_succ]
    have : 0 ≤ Λ * (1 + 1 / lam / 6) ^ i := by positivity
    nlinarith

/-- Once the target bias exceeds `n`, only the alternative `c_m > 2n/3` is left. -/
lemma growthSet_sub_of_lt (m : Fin k) {lam Λ : ℝ} {i : ℕ}
    (hi : (n : ℝ) < Λ * (1 + 1 / lam / 6) ^ i) :
    growthSet n m lam Λ i ⊆ satSet n m 0 := by
  rintro x (h | ⟨_, _, hs⟩)
  · change (n : ℝ) - count x m < max ((n : ℝ) / 3 * (17 / 18) ^ 0) _
    refine lt_of_lt_of_le ?_ (le_max_left _ _)
    simp only [pow_zero, mul_one]
    linarith
  · exfalso
    have h1 : bias (count x) ≤ n := (bias_le_maxc _).trans (maxc_le_of_sum (sum_count x))
    have h2 : (bias (count x) : ℝ) ≤ n := by exact_mod_cast h1
    linarith

lemma satSet_zero_sub (m : Fin k) (lam Λ : ℝ) (i : ℕ) (hL : 40 ≤ Real.log n) :
    satSet n m 0 ⊆ growthSet n m lam Λ i := by
  intro x hx
  left
  have := satSet_sub hL m 0 hx
  simp only [Set.mem_setOf_eq] at this
  linarith

/-- **One growth round** (Lemma 3.5 and a union bound over the colors that
have nodes). From growth phase `i`, the chain is in growth phase `i + 1` after
one round except with probability `1/n`. -/
theorem growth_step [NeZero n] (hL : 40 ≤ Real.log n) (hk : 2 ≤ k) (m : Fin k) {lam Λ : ℝ}
    (hlam : 3 ≤ lam) (hΛ : 22 * √(lam * n * Real.log n) ≤ Λ) (i : ℕ) {x : Config n k}
    (hx : x ∈ growthSet n m lam Λ i) :
    1 - 1 / (n : ℝ) ≤ ((kernel maj3) x).prob (· ∈ growthSet n m lam Λ (i + 1)) := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlam0 : 0 < lam := by linarith
  have hΛ0 : 0 ≤ Λ := le_trans (by positivity) hΛ
  have hq1 : 1 ≤ 1 + 1 / lam / 6 := by
    have : 0 ≤ 1 / lam / 6 := by positivity
    linarith
  have hnn : 1 / (n : ℝ) ^ 2 ≤ 1 / n := by
    apply one_div_le_one_div_of_le hn0
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  by_cases hbig : 2 / 3 * (n : ℝ) < count x m
  · -- the plurality already exceeds `2n/3`: Lemma 3.7 keeps it there
    have hx0 : x ∈ satSet n m 0 := by
      change (n : ℝ) - count x m < max ((n : ℝ) / 3 * (17 / 18) ^ 0) _
      refine lt_of_lt_of_le ?_ (le_max_left _ _)
      simp only [pow_zero, mul_one]
      linarith
    have h := sat_step hL m 0 hx0
    have hsub : satSet n m (0 + 1) ⊆ growthSet n m lam Λ (i + 1) := fun y hy =>
      satSet_zero_sub m lam Λ (i + 1) hL (satSet_succ_sub m 0 hy)
    exact le_trans (by linarith) (h.trans (prob_mono_set _ hsub))
  -- the growth regime of Lemma 3.5
  obtain ⟨hM, hcm, hs⟩ := hx.resolve_left hbig
  push Not at hbig
  have hcmax := argmaxSet_eq_singleton hM
  set s : ℝ := ((bias (count x) : ℕ) : ℝ) with hs_def
  set q : ℝ := 1 + 1 / lam / 6 with hq_def
  have hs1 : (1 : ℝ) ≤ s := by rw [hs_def]; exact_mod_cast bias_pos hn x hM
  have hΛs : 22 * √((1 / (1 / lam)) * n * Real.log n) ≤ bias (count x) := by
    rw [one_div_one_div]
    have : Λ ≤ Λ * q ^ i := le_mul_of_one_le_right hΛ0 (one_le_pow₀ hq1)
    linarith
  have h35 := lemma_3_5 hn x hM (lam := 1 / lam) (by positivity)
    (by rw [div_le_iff₀ hlam0]; linarith)
    (by rw [one_div_mul_eq_div]; exact hcm) hbig hΛs
  -- the competing colors that have nodes
  set S := (univ.erase m).filter (fun j => count x j ≠ 0) with hS
  have hSm : ∀ j ∈ S, j ≠ m := fun j hj => (mem_erase.mp (mem_filter.mp hj).1).1
  have hcard : S.card + 1 ≤ n := by
    have hsum := sum_count x
    rw [← add_sum_erase univ _ (mem_univ m)] at hsum
    have h1 : S.card ≤ ∑ j ∈ univ.erase m, count x j :=
      calc S.card = ∑ j ∈ S, 1 := card_eq_sum_ones S
        _ ≤ ∑ j ∈ S, count x j :=
            sum_le_sum fun j hj => Nat.one_le_iff_ne_zero.mpr (mem_filter.mp hj).2
        _ ≤ ∑ j ∈ univ.erase m, count x j := sum_le_sum_of_subset (filter_subset _ _)
    have h2 := maxc_pos hn x
    omega
  -- the color attaining the bias has nodes
  obtain ⟨ℓ, hℓm, hℓ⟩ := exists_add_bias_eq hk hcmax
  have hℓS : ℓ ∈ S := by
    refine mem_filter.mpr ⟨mem_erase.mpr ⟨hℓm, mem_univ ℓ⟩, fun h0 => ?_⟩
    -- otherwise every other color is empty and `c_m = n > 2n/3`
    have hall : ∀ h ∈ univ.erase m, count x h = 0 := fun h hh => by
      have := add_bias_le hcmax (mem_erase.mp hh).1
      omega
    have hsum := sum_count x
    rw [← add_sum_erase univ _ (mem_univ m), sum_eq_zero hall, add_zero] at hsum
    have : (count x m : ℝ) = n := by exact_mod_cast hsum
    linarith
  -- the failure events
  let E : Fin k → Tgt3 n → ℝ := fun j r =>
    if (count (step x r) m : ℝ) - count (step x r) j ≤ s * (1 + 1 / lam / 6) then 1 else 0
  let F : Tgt3 n → ℝ := fun r => if (count (step x r) m : ℝ) ≤ count x m then 1 else 0
  have hbad : avg (fun r => ∑ j ∈ S, E j r + F r) ≤ 1 / n := by
    rw [avg_add, avg_sum]
    have h1 : ∑ j ∈ S, avg (E j) ≤ S.card * (1 / (n : ℝ) ^ 2) := by
      rw [← nsmul_eq_mul, ← sum_const]
      exact sum_le_sum fun j hj => h35.1 j (hSm j hj)
    have h2 : ((S.card + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hcard
    push_cast at h2
    have h3 : (S.card : ℝ) * (1 / (n : ℝ) ^ 2) + 1 / (n : ℝ) ^ 2 ≤ 1 / n := by
      rw [← add_one_mul]
      calc ((S.card : ℝ) + 1) * (1 / (n : ℝ) ^ 2) ≤ n * (1 / (n : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = 1 / n := by field_simp
    linarith [h35.2]
  refine le_trans (by linarith) (le_prob_step x _ _
    (fun r => add_nonneg (sum_nonneg fun j _ => ite_one_zero_nonneg _) (ite_one_zero_nonneg _))
    fun r hr => ?_)
  by_contra hlt
  push Not at hlt
  have hEn : ∀ j ∈ S, ¬ ((count (step x r) m : ℝ) - count (step x r) j ≤ s * q) := by
    intro j hj he
    have h1 : E j r ≤ ∑ j ∈ S, E j r :=
      single_le_sum (f := fun j => E j r) (fun j _ => ite_one_zero_nonneg _) hj
    have h2 : E j r = 1 := if_pos he
    linarith [ite_one_zero_nonneg ((count (step x r) m : ℝ) ≤ count x m)]
  have hFn : ¬ ((count (step x r) m : ℝ) ≤ count x m) := by
    intro he
    have h2 : F r = 1 := if_pos he
    linarith [sum_nonneg fun j (_ : j ∈ S) => ite_one_zero_nonneg
      ((count (step x r) m : ℝ) - count (step x r) j ≤ s * (1 + 1 / lam / 6))]
  push Not at hFn
  apply hr
  -- the next coloring is in growth phase `i + 1`
  have hg0 : 0 < s * q := by positivity
  have hgm : s * q ≤ count (step x r) m := by
    have := hEn ℓ hℓS
    push Not at this
    have : (0 : ℝ) ≤ count (step x r) ℓ := Nat.cast_nonneg _
    linarith
  have hgap : ∀ j, j ≠ m → (count (step x r) j : ℝ) + s * q ≤ count (step x r) m := by
    intro j hj
    by_cases hjS : j ∈ S
    · have := hEn j hjS
      push Not at this
      linarith
    · have h0 : count x j = 0 := by
        by_contra h0
        exact hjS (mem_filter.mpr ⟨mem_erase.mpr ⟨hj, mem_univ j⟩, h0⟩)
      rw [count_step_eq_zero x h0 r]
      simpa using hgm
  obtain ⟨hM', hs'⟩ := le_bias_of_gap hg0 hgm hgap
  refine Or.inr ⟨hM', by linarith, ?_⟩
  rw [pow_succ]
  have : 0 ≤ q := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hs this]

/-! ### Theorem 3.8 -/

/-- The number `T₁` of growth phases: enough for `(1 + 1/(6λ))^{T₁} ≥ n`. -/
noncomputable def growthPhases (n : ℕ) (lam : ℝ) : ℕ :=
  ⌈Real.log n / Real.log (1 + 1 / lam / 6)⌉₊

/-- The number `T₂` of saturation phases: enough for `(18/17)^{T₂ - 1} ≥ n`. -/
noncomputable def satPhases (n : ℕ) : ℕ := ⌈Real.log n / Real.log (18 / 17)⌉₊ + 1

/-- The total number of phases, `T = T₁ + T₂ + 1`; the process runs for `10 T` rounds. -/
noncomputable def phases (n : ℕ) (lam : ℝ) : ℕ := growthPhases n lam + satPhases n + 1

/-- `n ≤ q ^ ⌈log n / log q⌉₊` for `q > 1`. -/
lemma le_pow_ceil (hn : 1 ≤ n) {q : ℝ} (hq : 1 < q) :
    (n : ℝ) ≤ q ^ ⌈Real.log n / Real.log q⌉₊ := by
  have hlq : 0 < Real.log q := Real.log_pos hq
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← Real.log_le_log_iff hn0 (by positivity), Real.log_pow]
  have := Nat.le_ceil (Real.log n / Real.log q)
  rwa [div_le_iff₀ hlq] at this

/-- `log q ≥ (q - 1)/q` for `q > 0`. -/
lemma sub_one_div_le_log {q : ℝ} (hq : 0 < q) : (q - 1) / q ≤ Real.log q := by
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hq)
  rw [Real.log_inv] at h
  have e : (q - 1) / q = 1 - q⁻¹ := by field_simp
  linarith

/-- **The number of phases is `O(λ log n)`**: `T ≤ 13 λ log n`. -/
theorem phases_le (hL : 40 ≤ Real.log n) {lam : ℝ} (hlam : 3 ≤ lam) :
    (phases n lam : ℝ) ≤ 13 * lam * Real.log n := by
  set L := Real.log n
  have hlam0 : 0 < lam := by linarith
  have hq : 0 < 1 + 1 / lam / 6 := by positivity
  have hlq : 1 / (6 * lam + 1) ≤ Real.log (1 + 1 / lam / 6) := by
    refine le_trans (le_of_eq ?_) (sub_one_div_le_log hq)
    field_simp
    ring
  have hl18 : 1 / 18 ≤ Real.log (18 / 17) := by
    refine le_trans (le_of_eq ?_) (sub_one_div_le_log (by norm_num : (0 : ℝ) < 18 / 17))
    norm_num
  have h1 : (growthPhases n lam : ℝ) ≤ (6 * lam + 1) * L + 1 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ L / Real.log (1 + 1 / lam / 6) by
      apply div_nonneg <;> linarith [lt_of_lt_of_le (by positivity) hlq])
    have hdiv : L / Real.log (1 + 1 / lam / 6) ≤ (6 * lam + 1) * L := by
      rw [div_le_iff₀ (lt_of_lt_of_le (by positivity) hlq)]
      have := mul_le_mul_of_nonneg_left hlq (show 0 ≤ (6 * lam + 1) * L by positivity)
      have e : (6 * lam + 1) * L * (1 / (6 * lam + 1)) = L := by field_simp
      linarith
    unfold growthPhases
    linarith
  have h2 : (satPhases n : ℝ) ≤ 18 * L + 2 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ L / Real.log (18 / 17) by
      apply div_nonneg <;> linarith)
    have hdiv : L / Real.log (18 / 17) ≤ 18 * L := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    unfold satPhases
    push_cast
    linarith
  unfold phases
  push_cast
  nlinarith

/-- **Theorem 3.8 (the general upper bound).** Let `λ ≥ 3`, `log n ≥ 40` and
`k ≥ 2`. If `m` is the unique plurality color of `x`, `c_m ≥ n/λ` and
`s(c) ≥ 22 √(λ n log n)`, then after `10 T` rounds, where
`T = phases n λ ≤ 13 λ log n` (`phases_le`), every node supports `m` with
probability at least `1 - 11 T / n`. -/
theorem theorem_3_8 (hL : 40 ≤ Real.log n) (hk : 2 ≤ k) {lam : ℝ} (hlam : 3 ≤ lam)
    (x : Config n k) {m : Fin k} (hM : argmaxSet (count x) = {m})
    (hcm : (n : ℝ) / lam ≤ count x m)
    (hs : 22 * √(lam * n * Real.log n) ≤ bias (count x)) :
    1 - 11 * (phases n lam : ℝ) / n
      ≤ expList (Tgt3 n) (10 * phases n lam)
          (fun l => if Mono (run x l) m then (1 : ℝ) else 0) := by
  have hn : 1 ≤ n := one_le_of_log_pos (by linarith)
  haveI : NeZero n := ⟨by omega⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlam0 : 0 < lam := by linarith
  set L := Real.log n with hLdef
  set Λ : ℝ := 22 * √(lam * n * L) with hΛdef
  set q : ℝ := 1 + 1 / lam / 6 with hqdef
  set B : ℝ := (n : ℝ) ^ (1 / 4 : ℝ) * L with hBdef
  set T1 := growthPhases n lam with hT1
  set T2 := satPhases n with hT2
  set ν : ℝ := (n : ℝ) ^ (-(1 / 5 : ℝ)) with hν
  have hq1 : 1 < q := by
    have : 0 < 1 / lam / 6 := by positivity
    linarith
  -- numerical facts
  have hΛ1 : 1 < Λ := by
    have h1 : 1 ≤ lam * n * L := by
      have := mul_le_mul (mul_le_mul hlam hn1 (by norm_num) hlam0.le) hL (by norm_num)
        (by positivity)
      linarith
    have : 1 ≤ √(lam * n * L) := Real.one_le_sqrt.mpr h1
    linarith
  have hT1pos : 1 ≤ T1 := by
    apply Nat.one_le_iff_ne_zero.mpr
    rw [hT1, growthPhases, Ne, Nat.ceil_eq_zero, not_le]
    exact div_pos (by linarith) (Real.log_pos hq1)
  have hT2pos : 1 ≤ T2 := by rw [hT2, satPhases]; omega
  have hgrow : (n : ℝ) < Λ * q ^ T1 := by
    have h1 : (n : ℝ) ≤ q ^ T1 := le_pow_ceil hn hq1
    have h2 : (0 : ℝ) < q ^ T1 := by positivity
    nlinarith [mul_lt_mul_of_pos_right hΛ1 h2]
  have hB1 : 1 ≤ (n : ℝ) ^ (1 / 4 : ℝ) := Real.one_le_rpow hn1 (by norm_num)
  have hsat : ∀ x : Config n k, x ∈ satSet n m (T2 - 1) → (n : ℝ) - count x m < B := by
    intro y hy
    have hpow := le_pow_ceil hn (show (1 : ℝ) < 18 / 17 by norm_num)
    have e : T2 - 1 = ⌈Real.log n / Real.log (18 / 17)⌉₊ := by rw [hT2, satPhases]; omega
    have hsmall : (n : ℝ) / 3 * (17 / 18) ^ (T2 - 1) ≤ B := by
      rw [e]
      set P : ℝ := (18 / 17) ^ ⌈Real.log n / Real.log (18 / 17)⌉₊ with hP
      have hp : (0 : ℝ) < P := by positivity
      have hinv : ((17 : ℝ) / 18) ^ ⌈Real.log n / Real.log (18 / 17)⌉₊ = P⁻¹ := by
        rw [hP, ← inv_pow]; norm_num
      have h1 : (n : ℝ) * P⁻¹ ≤ 1 := by rw [← div_eq_mul_inv, div_le_one hp]; exact hpow
      have h2 : (n : ℝ) / 3 * P⁻¹ = (n * P⁻¹) / 3 := by ring
      have h3 : 40 ≤ B := by rw [hBdef]; nlinarith
      rw [hinv, h2]
      linarith
    exact lt_of_lt_of_le hy (max_le hsmall le_rfl)
  have hνn : 1 / (n : ℝ) ≤ ν := by
    rw [hν, one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hν10 : ν ^ 10 = 1 / (n : ℝ) ^ 2 := by
    rw [hν, ← Real.rpow_mul_natCast hn0.le,
      show (-(1 / 5 : ℝ)) * ((10 : ℕ) : ℝ) = -((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg hn0.le, Real.rpow_natCast, one_div]
  have hnn : 1 / (n : ℝ) ^ 2 ≤ 1 / n := by
    apply one_div_le_one_div_of_le hn0
    nlinarith
  -- the phases
  let A : ℕ → Set (Config n k) := fun p =>
    if p ≤ T1 then growthSet n m lam Λ (p - 1)
    else if p ≤ T1 + T2 then satSet n m (p - T1 - 1) else monoSet n m
  have hA1 : ∀ p, p ≤ T1 → A p = growthSet n m lam Λ (p - 1) := fun p hp => if_pos hp
  have hA2 : ∀ p, T1 < p → p ≤ T1 + T2 → A p = satSet n m (p - T1 - 1) := fun p h1 h2 => by
    simp only [A]; rw [if_neg (by omega), if_pos h2]
  have hA3 : ∀ p, T1 + T2 < p → A p = monoSet n m := fun p h => by
    simp only [A]; rw [if_neg (by omega), if_neg (by omega)]
  have hΛ : 22 * √(lam * n * Real.log n) ≤ Λ := le_rfl
  have hx : x ∈ A 1 := by
    rw [hA1 1 hT1pos]
    exact Or.inr ⟨hM, hcm, by simpa using hs⟩
  have K := Dynamics.Kernel.nested_phases (kernel maj3) A (T := T1 + T2 + 1) (by omega) 10
    (ε := 1 / n) (ν := ν) (by positivity) (by positivity)
    (by
      intro i hi1 hiT
      by_cases h1 : i + 1 ≤ T1
      · rw [hA1 _ h1, hA1 _ (by omega), show i + 1 - 1 = (i - 1) + 1 by omega]
        exact growthSet_succ_sub m hlam0 (by linarith) _
      by_cases h2 : i ≤ T1
      · rw [hA2 _ (by omega) (by omega), hA1 _ h2, show i + 1 - T1 - 1 = 0 by omega]
        exact satSet_zero_sub m lam Λ _ hL
      by_cases h3 : i + 1 ≤ T1 + T2
      · rw [hA2 _ (by omega) h3, hA2 _ (by omega) (by omega),
          show i + 1 - T1 - 1 = (i - T1 - 1) + 1 by omega]
        exact satSet_succ_sub m _
      · rw [hA3 _ (by omega), hA2 _ (by omega) (by omega)]
        intro y hy
        have hu : (n : ℝ) - count y m = 0 := by
          have := (mono_iff_count y m).mp hy
          rw [this]; ring
        change (n : ℝ) - count y m < max _ _
        rw [hu]
        exact lt_of_lt_of_le (by positivity) (le_max_right _ _))
    (by
      intro i hi1 hiT a ha
      by_cases h1 : i ≤ T1
      · rw [hA1 _ h1] at ha ⊢
        have := growth_step hL hk m hlam hΛ (i - 1) ha
        exact this.trans (prob_mono_set _ (growthSet_succ_sub m hlam0 (by linarith) _))
      by_cases h2 : i ≤ T1 + T2
      · rw [hA2 _ (by omega) h2] at ha ⊢
        have := sat_step hL m _ ha
        exact le_trans (by linarith) (this.trans (prob_mono_set _ (satSet_succ_sub m _)))
      · rw [hA3 _ (by omega)] at ha ⊢
        have h0 : (0 : ℝ) ≤ 1 / n := by positivity
        linarith [mono_stay m ha])
    (by
      intro i hi1 hiT a ha
      by_cases h1 : i + 1 ≤ T1
      · rw [hA1 _ h1, show i + 1 - 1 = (i - 1) + 1 by omega]
        rw [hA1 _ (by omega)] at ha
        exact le_trans (by linarith) (growth_step hL hk m hlam hΛ (i - 1) ha)
      by_cases h2 : i ≤ T1
      · rw [hA2 _ (by omega) (by omega), show i + 1 - T1 - 1 = 0 by omega]
        rw [hA1 _ h2] at ha
        have := growth_step hL hk m hlam hΛ (i - 1) ha
        rw [show i - 1 + 1 = T1 by omega] at this
        exact le_trans (by linarith)
          (this.trans (prob_mono_set _ (growthSet_sub_of_lt m hgrow)))
      by_cases h3 : i + 1 ≤ T1 + T2
      · rw [hA2 _ (by omega) h3, show i + 1 - T1 - 1 = (i - T1 - 1) + 1 by omega]
        rw [hA2 _ (by omega) (by omega)] at ha
        exact le_trans (by linarith) (sat_step hL m _ ha)
      · rw [hA3 _ (by omega)]
        rw [hA2 _ (by omega) (by omega), show i - T1 - 1 = T2 - 1 by omega] at ha
        exact mono_step hL m (hsat a ha))
    x hx
  rw [hA3 _ (by omega)] at K
  have hev : (kernel maj3).event (· ∈ monoSet n m) (10 * (T1 + T2 + 1)) x
      = expList (Tgt3 n) (10 * phases n lam)
          (fun l => if Mono (run x l) m then (1 : ℝ) else 0) :=
    kernel_event maj3 (fun y => Mono y m) _ x
  rw [hev, hν10] at K
  refine le_trans ?_ K
  have hT : (0 : ℝ) ≤ ((T1 + T2 + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have e : ((T1 + T2 + 1 : ℕ) : ℝ) = phases n lam := rfl
  rw [e] at hT ⊢
  have : (phases n lam : ℝ) * (10 * (1 / n) + 1 / (n : ℝ) ^ 2)
      ≤ 11 * (phases n lam : ℝ) / n := by
    have h11 : 10 * (1 / (n : ℝ)) + 1 / (n : ℝ) ^ 2 ≤ 11 * (1 / n) := by linarith
    calc (phases n lam : ℝ) * (10 * (1 / n) + 1 / (n : ℝ) ^ 2)
        ≤ (phases n lam : ℝ) * (11 * (1 / n)) := mul_le_mul_of_nonneg_left h11 hT
      _ = 11 * (phases n lam : ℝ) / n := by ring
  push_cast at this ⊢
  linarith

/-- **Theorem 3.8, `O(λ log n)` form.** Under the hypotheses of `theorem_3_8`,
consensus on `m` holds after `10 T ≤ 130 λ log n` rounds with probability at
least `1 - 143 λ log n / n`. -/
theorem theorem_3_8_bigO (hL : 40 ≤ Real.log n) (hk : 2 ≤ k) {lam : ℝ} (hlam : 3 ≤ lam)
    (x : Config n k) {m : Fin k} (hM : argmaxSet (count x) = {m})
    (hcm : (n : ℝ) / lam ≤ count x m)
    (hs : 22 * √(lam * n * Real.log n) ≤ bias (count x)) :
    ((10 * phases n lam : ℕ) : ℝ) ≤ 130 * lam * Real.log n ∧
      1 - 143 * lam * Real.log n / n
        ≤ expList (Tgt3 n) (10 * phases n lam)
            (fun l => if Mono (run x l) m then (1 : ℝ) else 0) := by
  have hT := phases_le hL hlam
  have hn : 1 ≤ n := one_le_of_log_pos (by linarith)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨by push_cast; linarith, le_trans ?_ (theorem_3_8 hL hk hlam x hM hcm hs)⟩
  have : 11 * (phases n lam : ℝ) / n ≤ 143 * lam * Real.log n / n :=
    div_le_div_of_nonneg_right (by linarith) hn0.le
  linarith

end Plurality
