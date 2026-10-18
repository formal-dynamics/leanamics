import Dynamics.Binomial
import Moran.PushPull

/-! # The neutral Moran chain on mutant counts

Population genetics follows the number `k` of mutants in a population of constant size `n`. In
Moran's model (Moran 1958) the individual that reproduces and the one that dies are drawn
independently and uniformly from the whole population, possibly the same one. In the neutral
case the count goes up by one with probability `k(n-k)/n²` (a mutant reproduces and a resident
dies), down by one with the same probability, and stays otherwise (`moranCountKernel`). If the
two individuals must differ, the probabilities are `k(n-k)/(n(n-1))` (`pullCountKernel`). Both
are symmetric birth–death chains on `{0, …, n}` (`birthDeath`).

Death–Birth on the complete graph, the sequential pull voter `pullKernel ⊤` (a uniformly random
vertex adopts the type of a uniformly random neighbour, that is of another vertex), lumps to
`pullCountKernel` under the number of mutants (`pullKernel_top_lumps`): a `SimpleGraph` has no
self-loops, so the library's kernel is the convention without self-loops. Moran's model has the
same jump chain (`moranCountKernel_sameJumpChain`), the walk that moves up or down by one with
probability `1/2` each until it is absorbed at `0` or `n` (`pullCountKernel_jump`): the two
chains differ only by idle steps. Hence, for `n ≥ 2`, they have the same fixation probability
`k / n` (`pullCountKernel_fixation`, from `pull_fixation` through the lumping, and
`moranCountKernel_fixation`, through the jump chain).
-/

namespace Moran
open Dynamics Finset

/-! ### Symmetric birth–death chains on `{0, …, n}` -/

/-- The count one below `k` (`0` from `0`). -/
def countDown {n : ℕ} (k : Fin (n + 1)) : Fin (n + 1) :=
  ⟨k - 1, lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩

/-- The count one above `k` (`n` from `n`). -/
def countUp {n : ℕ} (k : Fin (n + 1)) : Fin (n + 1) :=
  ⟨min (k + 1) n, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- One move of a symmetric birth–death chain: down by one (`0`), stay (`1`) or up by one (`2`),
with probabilities `q`, `1 - 2q` and `q`. -/
noncomputable def moveDist (q : ℝ) (h0 : 0 ≤ q) (h1 : 2 * q ≤ 1) : Distribution (Fin 3) where
  weight := ![q, 1 - 2 * q, q]
  nonneg i := by
    fin_cases i
    · exact h0
    · simpa using h1
    · exact h0
  sum_one := by
    simp only [Fin.sum_univ_three, Matrix.cons_val]
    ring

/-- A **symmetric birth–death chain** on `{0, …, n}`: from `k`, the count goes down by one and up
by one with probability `q k` each, and stays otherwise. (The moves are clamped to `{0, …, n}`;
the chains below have `q = 0` at `0` and at `n`.) -/
noncomputable def birthDeath {n : ℕ} (q : Fin (n + 1) → ℝ) (h0 : ∀ k, 0 ≤ q k)
    (h1 : ∀ k, 2 * q k ≤ 1) : Kernel (Fin (n + 1)) := fun k =>
  (moveDist (q k) (h0 k) (h1 k)).map ![countDown k, k, countUp k]

section BirthDeath
variable {n : ℕ} {q : Fin (n + 1) → ℝ} {h0 : ∀ k, 0 ≤ q k} {h1 : ∀ k, 2 * q k ≤ 1}

/-- One step of a symmetric birth–death chain, on observables. -/
theorem birthDeath_expect (k : Fin (n + 1)) (g : Fin (n + 1) → ℝ) :
    (birthDeath q h0 h1 k).expect g =
      q k * g (countDown k) + (1 - 2 * q k) * g k + q k * g (countUp k) := by
  rw [birthDeath, Distribution.map_expect]
  simp only [Distribution.expect, moveDist, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

/-- The transition probabilities of a symmetric birth–death chain to the other states. -/
theorem birthDeath_weight_of_ne {k y : Fin (n + 1)} (hy : y ≠ k) :
    (birthDeath q h0 h1 k).weight y =
      q k * ((if countDown k = y then 1 else 0) + if countUp k = y then 1 else 0) := by
  rw [Distribution.weight_eq_expect_ite, birthDeath_expect, if_neg (Ne.symm hy)]
  ring

/-- A symmetric birth–death chain stays at a state where `q` vanishes. -/
theorem birthDeath_prob_self {k : Fin (n + 1)} (hk : q k = 0) :
    (birthDeath q h0 h1 k).prob (· = k) = 1 := by
  rw [Distribution.prob_eq_expect, birthDeath_expect, hk, if_pos rfl]
  ring

/-- Symmetric birth–death chains whose move probabilities are proportional have the same jump
chain. -/
theorem birthDeath_sameJumpChain {q' : Fin (n + 1) → ℝ} {h0' : ∀ k, 0 ≤ q' k}
    {h1' : ∀ k, 2 * q' k ≤ 1} {c : ℝ} (hc : 0 < c) (h : ∀ k, q k = c * q' k) :
    (birthDeath q h0 h1).SameJumpChain (birthDeath q' h0' h1') :=
  Kernel.sameJumpChain_of_weight fun k => ⟨c, hc, fun y hy => by
    rw [birthDeath_weight_of_ne hy, birthDeath_weight_of_ne hy, h]
    ring⟩

end BirthDeath

/-! ### Moran's chain on counts, with and without self-loops -/

lemma count_le (n : ℕ) (k : Fin (n + 1)) : (k : ℝ) ≤ n := by exact_mod_cast Fin.is_le k

lemma moran_q_nonneg (n : ℕ) (k : Fin (n + 1)) : 0 ≤ (k : ℝ) * (n - k) / n ^ 2 :=
  div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.2 (count_le n k))) (sq_nonneg _)

lemma moran_q_le (n : ℕ) (k : Fin (n + 1)) : 2 * ((k : ℝ) * (n - k) / n ^ 2) ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn' : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    rw [mul_div_assoc', div_le_one hn']
    nlinarith [sq_nonneg ((n : ℝ) - k), sq_nonneg (k : ℝ)]

lemma pull_q_nonneg (n : ℕ) (k : Fin (n + 1)) : 0 ≤ (k : ℝ) * (n - k) / (n * (n - 1)) := by
  refine div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.2 (count_le n k))) ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.2 (by exact_mod_cast hn))

lemma pull_q_le (n : ℕ) (k : Fin (n + 1)) : 2 * ((k : ℝ) * (n - k) / (n * (n - 1))) ≤ 1 := by
  rcases lt_or_ge n 2 with hn | hn
  · have h : (n : ℝ) * (n - 1) = 0 := by
      interval_cases n <;> norm_num
    rw [h, div_zero, mul_zero]
    exact zero_le_one
  · have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hd : (0 : ℝ) < n * (n - 1) := by nlinarith
    rw [mul_div_assoc', div_le_one hd]
    nlinarith [sq_nonneg ((n : ℝ) - 2 * k), count_le n k]

/-- **Moran's neutral chain on mutant counts** (Moran 1958). In a population of `n`, the
reproducing and the dying individual are drawn independently and uniformly (possibly the same
one): from `k` mutants the count goes up by one with probability `k(n-k)/n²`, down by one with the
same probability, and stays otherwise. -/
noncomputable def moranCountKernel (n : ℕ) : Kernel (Fin (n + 1)) :=
  birthDeath (fun k => (k : ℝ) * (n - k) / n ^ 2) (moran_q_nonneg n) (moran_q_le n)

/-- **The neutral Moran chain on mutant counts without self-loops.** The reproducing and the
dying individual are two distinct individuals drawn uniformly: from `k` mutants among `n` the
count goes up by one with probability `k(n-k)/(n(n-1))`, down by one with the same probability,
and stays otherwise. These are also the probabilities of Kirman's recruitment model with
`ε = δ = 0`. -/
noncomputable def pullCountKernel (n : ℕ) : Kernel (Fin (n + 1)) :=
  birthDeath (fun k => (k : ℝ) * (n - k) / (n * (n - 1))) (pull_q_nonneg n) (pull_q_le n)

/-- The walk on `{0, …, n}` that moves up or down by one with probability `1/2` each, absorbed at
`0` and at `n`. -/
noncomputable def absorbedWalk (n : ℕ) : Kernel (Fin (n + 1)) :=
  birthDeath (fun k => if (k : ℕ) = 0 ∨ (k : ℕ) = n then 0 else 1 / 2)
    (fun k => by split <;> norm_num) (fun k => by split <;> norm_num)

/-- **Moran's model and the chain without self-loops have the same jump chain.** From `k`
mutants, Moran's model moves with probability `2k(n-k)/n²`, a fraction `(n-1)/n` of the
probability `2k(n-k)/(n(n-1))` without self-loops, and once it moves it goes up or down by one
with the same probabilities. -/
theorem moranCountKernel_sameJumpChain (n : ℕ) :
    (moranCountKernel n).SameJumpChain (pullCountKernel n) := by
  rcases lt_or_ge n 2 with hn | hn
  · refine birthDeath_sameJumpChain one_pos fun k => ?_
    have hk := Fin.is_le k
    have h0 : (k : ℝ) * (n - k) = 0 := by
      interval_cases n <;> interval_cases (k : ℕ) <;> norm_num
    rw [h0, zero_div, zero_div, mul_zero]
  · have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    refine birthDeath_sameJumpChain (c := (n - 1) / n) (div_pos (by linarith) (by linarith))
      fun k => ?_
    have h1 : (n : ℝ) - 1 ≠ 0 := by linarith
    have h2 : (n : ℝ) ≠ 0 := by linarith
    field_simp

/-- The absorbed walk is its own jump chain. -/
theorem absorbedWalk_jump (n : ℕ) : (absorbedWalk n).jump = absorbedWalk n := by
  refine Kernel.jump_eq_self _ fun k => ?_
  rw [Distribution.weight_eq_expect_ite, absorbedWalk, birthDeath_expect, if_pos rfl]
  by_cases hk : (k : ℕ) = 0 ∨ (k : ℕ) = n
  · right
    rw [if_pos hk]
    ring
  · left
    rw [if_neg hk]
    have hd : countDown k ≠ k := by
      simp only [countDown, ne_eq, Fin.ext_iff]
      omega
    have hu : countUp k ≠ k := by
      have := Fin.is_le k
      simp only [countUp, ne_eq, Fin.ext_iff]
      omega
    rw [if_neg hd, if_neg hu]
    ring

/-- **The jump chain of the neutral Moran chain on counts** (without self-loops, hence also with
self-loops by `moranCountKernel_sameJumpChain`): until absorption at `0` or `n`, the count moves
up or down by one with probability `1/2` each. -/
theorem pullCountKernel_jump (n : ℕ) : (pullCountKernel n).jump = absorbedWalk n := by
  have h : (pullCountKernel n).SameJumpChain (absorbedWalk n) := by
    refine Kernel.sameJumpChain_of_weight fun k => ?_
    by_cases hk : (k : ℕ) = 0 ∨ (k : ℕ) = n
    · refine ⟨1, one_pos, fun y hy => ?_⟩
      have h0 : (k : ℝ) * (n - k) = 0 := by
        rcases hk with hk | hk <;> simp [hk]
      rw [pullCountKernel, absorbedWalk, birthDeath_weight_of_ne hy, birthDeath_weight_of_ne hy,
        if_pos hk, h0, zero_div]
      ring
    · have hle := Fin.is_le k
      have hk1 : 1 ≤ (k : ℕ) := Nat.pos_of_ne_zero fun h => hk (Or.inl h)
      have hkn' : (k : ℕ) < n := lt_of_le_of_ne hle fun h => hk (Or.inr h)
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
      have hkn : (k : ℝ) < n := by exact_mod_cast hkn'
      have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
      have hd : (0 : ℝ) < n * (n - 1) := by nlinarith
      refine ⟨2 * ((k : ℝ) * (n - k) / (n * (n - 1))), by positivity, fun y hy => ?_⟩
      rw [pullCountKernel, absorbedWalk, birthDeath_weight_of_ne hy, birthDeath_weight_of_ne hy,
        if_neg hk]
      ring
  rw [h, absorbedWalk_jump]

/-! ### Death–Birth on the complete graph lumps to the chain without self-loops -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of mutants, in `{0, …, |V|}`. -/
def mutantCount (s : Config V) : Fin (Fintype.card V + 1) := countFin fun v => s v = true

omit [DecidableEq V] in
lemma mutantCount_val (s : Config V) : (mutantCount s : ℕ) = mutants s := rfl

omit [DecidableEq V] in
/-- The number of residents is `|V|` minus the number of mutants. -/
lemma card_filter_false (s : Config V) :
    (univ.filter fun v => s v = false).card = Fintype.card V - mutants s := by
  have h := card_filter_add_card_filter_not (s := univ) (fun v => s v = true)
  rw [card_univ] at h
  simp only [Bool.not_eq_true] at h
  unfold mutants
  omega

omit [DecidableEq V] in
/-- A configuration with a resident has fewer than `|V|` mutants. -/
lemma mutants_lt_card {s : Config V} {u : V} (hu : s u = false) : mutants s < Fintype.card V := by
  rw [← card_univ]
  exact card_lt_card (filter_ssubset.2 ⟨u, mem_univ u, by simp [hu]⟩)

/-- On the complete graph, a vertex copies each other vertex with probability `1/(|V| - 1)`. -/
lemma target_top_of_ne {u w : V} (h : u ≠ w) :
    target (⊤ : SimpleGraph V) u w = ((Fintype.card V : ℝ) - 1)⁻¹ := by
  have h2 : 1 < Fintype.card V := Fintype.one_lt_card_iff.2 ⟨u, w, h⟩
  have hdeg : (⊤ : SimpleGraph V).degree u = Fintype.card V - 1 :=
    SimpleGraph.complete_graph_degree u
  unfold target
  rw [if_neg (by omega), if_pos ((SimpleGraph.top_adj u w).2 h), hdeg,
    Nat.cast_sub h2.le, Nat.cast_one]

/-- In one death–Birth step on the complete graph, the updating vertex has type `b` and the
copied vertex type `c ≠ b` with probability `#b · #c / (n(n-1))`. -/
lemma pullDist_top_prob [Nonempty V] (s : Config V) {b c : Bool} (hbc : b ≠ c) :
    (pullDist (⊤ : SimpleGraph V)).prob (fun p => s p.1 = b ∧ s p.2 = c) =
      ((univ.filter fun u => s u = b).card * (univ.filter fun w => s w = c).card : ℝ) /
        (Fintype.card V * (Fintype.card V - 1)) := by
  classical
  have hp (p : V × V) : pullWeight (⊤ : SimpleGraph V) p * (if s p.1 = b ∧ s p.2 = c then 1 else 0)
      = if s p.1 = b ∧ s p.2 = c then
          (Fintype.card V : ℝ)⁻¹ * ((Fintype.card V : ℝ) - 1)⁻¹ else 0 := by
    split_ifs with hs
    · have hne : p.1 ≠ p.2 := fun he => hbc (by rw [← hs.1, ← hs.2, he])
      rw [pullWeight, target_top_of_ne hne, mul_one]
    · rw [mul_zero]
  rw [Distribution.prob_eq_expect]
  simp only [Distribution.expect, pullDist]
  rw [sum_congr rfl fun p _ => hp p, ← sum_filter, sum_const, nsmul_eq_mul, ← univ_product_univ,
    filter_product (p := fun u => s u = b) (q := fun w => s w = c), card_product, Nat.cast_mul,
    div_eq_mul_inv, mul_inv]

/-- The number of mutants after the vertex `u` adopts the type of `w`. -/
lemma mutantCount_update (s : Config V) (u w : V) :
    mutantCount (Function.update s u (s w)) =
      if s u = false ∧ s w = true then countUp (mutantCount s)
      else if s u = true ∧ s w = false then countDown (mutantCount s) else mutantCount s := by
  cases hu : s u <;> cases hw : s w
  · have he : Function.update s u false = s := by rw [← hu, Function.update_eq_self]
    rw [he]
    simp
  · have hlt := mutants_lt_card hu
    simp only [and_self, if_true]
    refine Fin.ext ?_
    rw [mutantCount_val, mutants_update_gain s hu]
    simp only [countUp, mutantCount_val]
    omega
  · simp only [Bool.true_eq_false, false_and, and_self, if_false, if_true]
    refine Fin.ext ?_
    rw [mutantCount_val, mutants_update_loss s hu]
    rfl
  · have he : Function.update s u true = s := by rw [← hu, Function.update_eq_self]
    rw [he]
    simp

/-- **Death–Birth on the complete graph is the neutral Moran chain on counts without
self-loops.** Under the sequential pull voter on `K_n` (a uniformly random vertex adopts the type
of a uniformly random other vertex), the number of mutants goes up by one with probability
`k(n-k)/(n(n-1))` from `k` mutants, down by one with the same probability, and stays otherwise:
it is `pullCountKernel n`. -/
theorem pullKernel_top_lumps [Nonempty V] :
    Kernel.Lumps mutantCount (pullKernel (⊤ : SimpleGraph V))
      (pullCountKernel (Fintype.card V)) := by
  classical
  refine Kernel.lumps_iff_apply.2 fun g s => ?_
  have hdecomp (p : V × V) : g (mutantCount (Function.update s p.1 (s p.2))) =
      g (mutantCount s) +
        (g (countUp (mutantCount s)) - g (mutantCount s)) *
          (if s p.1 = false ∧ s p.2 = true then 1 else 0) +
        (g (countDown (mutantCount s)) - g (mutantCount s)) *
          (if s p.1 = true ∧ s p.2 = false then 1 else 0) := by
    rw [mutantCount_update]
    by_cases h1 : s p.1 = false ∧ s p.2 = true
    · have h2 : ¬ (s p.1 = true ∧ s p.2 = false) := by simp [h1.1]
      rw [if_pos h1, if_pos h1, if_neg h2]
      ring
    · by_cases h2 : s p.1 = true ∧ s p.2 = false
      · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2]
        ring
      · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]
        ring
  have hup := pullDist_top_prob s (b := false) (c := true) Bool.false_ne_true
  have hdown := pullDist_top_prob s (b := true) (c := false) (by decide)
  rw [card_filter_false] at hup hdown
  simp only [Kernel.apply, pullKernel, Distribution.map_expect]
  rw [pullCountKernel, birthDeath_expect]
  simp only [hdecomp]
  rw [Distribution.expect_add, Distribution.expect_add, Distribution.expect_const,
    Distribution.expect_mul, Distribution.expect_mul, ← Distribution.prob_eq_expect,
    ← Distribution.prob_eq_expect, hup, hdown, mutantCount_val,
    Nat.cast_sub (mutants_le_card s)]
  have hfilter : (univ.filter fun u => s u = true).card = mutants s := rfl
  rw [hfilter]
  ring

/-! ### Fixation on counts -/

omit [DecidableEq V] in
/-- All vertices are mutants iff there are `|V|` mutants. -/
lemma allMutant_eq_ite (s : Config V) :
    allMutant s = if mutantCount s = Fin.last (Fintype.card V) then 1 else 0 := by
  have h : s = (fun _ => true) ↔ mutantCount s = Fin.last (Fintype.card V) := by
    rw [Fin.ext_iff, Fin.val_last, mutantCount, countFin_val, ← card_univ, card_filter_eq_iff]
    simp [funext_iff]
  unfold allMutant
  by_cases hs : s = fun _ => true
  · rw [if_pos hs, if_pos (h.1 hs)]
  · rw [if_neg hs, if_neg fun h' => hs (h.2 h')]

/-- On the complete graph, the reproductive value under pull is `(|V| - 1)` times the number of
mutants. -/
lemma pullValue_top (s : Config V) :
    pullValue (⊤ : SimpleGraph V) s = ((Fintype.card V : ℝ) - 1) * mutants s := by
  classical
  unfold pullValue mutants
  rw [sum_congr rfl fun v _ => by rw [SimpleGraph.complete_graph_degree v], sum_const,
    nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos (Fintype.card V) with h | h
  · haveI : IsEmpty V := Fintype.card_eq_zero_iff.1 h
    simp
  · rw [Nat.cast_sub h, Nat.cast_one]
    ring

/-- Fixation of the count chain without self-loops, from the count of a configuration. -/
lemma pullCountKernel_fixation_count [Nontrivial V] (s : Config V) :
    ⨆ t, (pullCountKernel (Fintype.card V)).event (· = Fin.last (Fintype.card V)) t
        (mutantCount s) = (mutantCount s : ℝ) / Fintype.card V := by
  have h := pull_fixation (⊤ : SimpleGraph V) SimpleGraph.connected_top s
  unfold fixation at h
  simp only [funext allMutant_eq_ite] at h
  have hn : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast Fintype.one_lt_card
  have hall : mutants (fun _ : V => true) = Fintype.card V := mutants_true rfl
  rw [pullValue_top, pullValue_top, hall] at h
  calc ⨆ t, (pullCountKernel (Fintype.card V)).event (· = Fin.last (Fintype.card V)) t
        (mutantCount s)
      = ⨆ t, (pullKernel (⊤ : SimpleGraph V)).iterate t
          (fun x => if mutantCount x = Fin.last (Fintype.card V) then 1 else 0) s :=
        iSup_congr fun t => by
          rw [← (pullKernel_top_lumps (V := V)).event, Kernel.event_eq_iterate]
    _ = _ := by
        rw [h, mutantCount_val]
        have h1 : (Fintype.card V : ℝ) - 1 ≠ 0 := by linarith
        field_simp

/-- **Neutral fixation on counts, without self-loops.** The neutral Moran chain on counts without
self-loops, in a population of `n ≥ 2`, fixes the mutants from `k` copies with probability
`k / n`. Derived from death–Birth on the complete graph (`pull_fixation`) through the lumping
`pullKernel_top_lumps`. -/
theorem pullCountKernel_fixation {n : ℕ} (hn : 2 ≤ n) (k : Fin (n + 1)) :
    ⨆ t, (pullCountKernel n).event (· = Fin.last n) t k = k / n := by
  have key (m : ℕ) (hm : Fintype.card (Fin n) = m) (y : Fin (m + 1)) (s : Config (Fin n))
      (hs : (mutantCount s : ℕ) = y) :
      ⨆ t, (pullCountKernel m).event (· = Fin.last m) t y = y / m := by
    subst hm
    haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
    obtain rfl : mutantCount s = y := Fin.ext hs
    exact pullCountKernel_fixation_count s
  refine key n (Fintype.card_fin n) k (fun i => decide ((i : ℕ) < k)) ?_
  simp only [mutantCount, countFin_val, decide_eq_true_eq]
  rw [Fin.card_filter_val_lt]
  exact min_eq_right (Fin.is_le k)

/-- **Neutral fixation in Moran's model on counts** (Moran 1958). In a population of `n ≥ 2`,
Moran's chain fixes the mutants from `k` copies with probability `k / n`. It has the same jump
chain as the chain without self-loops (`moranCountKernel_sameJumpChain`), hence the same absorption
probabilities (`Dynamics.Kernel.SameJumpChain.iSup_event_eq`). -/
theorem moranCountKernel_fixation {n : ℕ} (hn : 2 ≤ n) (k : Fin (n + 1)) :
    ⨆ t, (moranCountKernel n).event (· = Fin.last n) t k = k / n := by
  have habs (K : Kernel (Fin (n + 1))) (hK : ∀ a, a = Fin.last n → (K a).prob (· = a) = 1) :
      ∀ a, a = Fin.last n → (K a).prob (· = Fin.last n) = 1 := fun a ha => by
    subst ha
    exact hK _ rfl
  rw [(moranCountKernel_sameJumpChain n).iSup_event_eq
      (habs _ fun a ha => birthDeath_prob_self (by rw [ha]; simp))
      (habs _ fun a ha => birthDeath_prob_self (by rw [ha]; simp)),
    pullCountKernel_fixation hn k]

end Moran
