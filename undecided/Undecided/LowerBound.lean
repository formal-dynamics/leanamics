import Undecided.LowerBoundFirst
import Undecided.LowerBoundDescent
import Undecided.LowerBoundPlateau
import Undecided.SequentialMartingale

/-! # The `Ω(md(c))` lower bound of the undecided-state dynamics (UND-3, SODA 2015, Theorem 8)

Becchetti, Clementi, Natale, Pasquale and Silvestri, *Plurality consensus in the gossip model*
(SODA 2015, arXiv:1407.2565), Theorem 8: let `c̄` be the initial configuration (without
undecided nodes, Section 2.1). If the number of colours is `k ≤ ε (n / log n)^{1/6}`, where
`ε > 0` is a sufficiently small constant, then the convergence time of the undecided-state
dynamics is `Ω(md(c̄))` w.h.p.

The proof composes Lemma 3 (the first round, `first_round`), Lemma 6 (the number of undecided
nodes descends to `n/2` while no colour exceeds `γ n / md(c̄)`, `descent`) and Lemma 7 (the
plateau: for `Ω(md(c̄))` more rounds no colour exceeds `2γ n / md(c̄)`, `plateau`).

"W.h.p." and `Ω(·)` are made explicit as everywhere in `undecided/`: one constant `C` with
`log n ≥ C`, `C k ≤ (n / log n)^{1/6}`, failure probability at most `C / n`, and every round
`T ≤ md(c̄) / C`. Two forms are stated:

* `lower_bound_whp`: at every such round `T`, w.h.p. every colour has at most `C n / md(c̄)`
  nodes (what the proof shows);
* `lower_bound_consensus`: the convergence time itself. If `C (T + 1) ≤ md(c̄)`, the probability
  that all nodes hold the same colour after `T` rounds is at most `C / n`. Since monochromatic
  configurations are absorbing (`step_const`), this is the probability of converging within
  `T` rounds.
-/

namespace Undecided.Plurality
open Finset Dynamics Real

/-! ### Assembly helpers -/

section Helpers
variable {n k : ℕ}

/-- The probability of being in `{z | P z}` after `T` rounds is one minus the probability of
missing it. -/
lemma prob_eq_one_sub_miss [NeZero n] (T : ℕ) (x : Config n k) (P : Config n k → Prop)
    [DecidablePred P] :
    expList (Fin n → Fin n) T (fun l => if P (l.foldl step x) then (1 : ℝ) else 0)
      = 1 - miss {z | P z} T x := by
  classical
  unfold miss
  rw [← Undecided.Sequential.expList_one_sub]
  congr 1
  funext l
  by_cases hl : P (l.foldl step x)
  · rw [if_pos hl, if_pos (show l.foldl step x ∈ {z | P z} from hl)]
    norm_num
  · rw [if_neg hl, if_neg (show l.foldl step x ∉ {z | P z} from hl)]
    norm_num

/-- Without undecided nodes, `c₁ · md(c) ≤ n` (from `md(c) ≤ R(c) = n / c₁`). -/
lemma maxCount_mul_md_le (x : Config n k) (hq : count x none = 0) (hn : 0 < n) :
    (maxCount x : ℝ) * md x ≤ n := by
  have hM : (0 : ℝ) < maxCount x := by exact_mod_cast maxCount_pos_of_und_zero x hq hn
  have h1 := md_le_ratioR x
  rw [ratioR_of_und_zero x hq, le_div_iff₀ hM] at h1
  linarith

/-- A configuration without undecided nodes has a plurality colour. -/
lemma exists_plurality (x : Config n k) (hq : count x none = 0) (hn : 0 < n) :
    ∃ m, ∀ i, count x (some i) ≤ count x (some m) := by
  have hk : (univ : Finset (Fin k)).Nonempty := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h
      have := count_none_add_sum x
      simp [hq] at this
      omega
    · exact ⟨⟨0, h⟩, mem_univ _⟩
  obtain ⟨m, -, hm⟩ := exists_mem_eq_sup univ hk fun i => count x (some i)
  exact ⟨m, fun i => (count_le_maxCount x i).trans (le_of_eq hm)⟩

lemma one_lt_of_log {C : ℝ} (hC : 0 < C) {n : ℕ} (hL : C ≤ Real.log n) : 1 < n := by
  by_contra h
  have : (n : ℝ) ≤ 1 := by exact_mod_cast not_lt.mp h
  have := Real.log_nonpos (Nat.cast_nonneg n) this
  linarith

lemma one_le_div_log {n : ℕ} (hn : 1 < n) : 1 ≤ (n : ℝ) / Real.log n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  rw [one_le_div hlog]
  linarith [Real.log_le_sub_one_of_pos hn0]

/-- Weakening the range of `k` to a larger exponent and a smaller constant. -/
lemma range_mono {C C' a b N k : ℝ} (hCC : C' ≤ C) (hk : 0 ≤ k) (hN : 1 ≤ N)
    (hab : a ≤ b) (h : C * k ≤ N ^ a) : C' * k ≤ N ^ b :=
  calc C' * k ≤ C * k := mul_le_mul_of_nonneg_right hCC hk
    _ ≤ N ^ a := h
    _ ≤ N ^ b := Real.rpow_le_rpow_of_exponent_le hN hab

end Helpers

/-- **Theorem 8 of [BCNPS15]** (the plateau form). There is `C > 0` such that, for every `n`
with `log n ≥ C`, every `k` with `C k ≤ (n / log n)^{1/6}`, every configuration `x` without
undecided nodes and every round `T` with `C T ≤ md(x)`, with probability at least `1 - C / n`
every colour has at most `C n / md(x)` nodes after `T` rounds. -/
theorem lower_bound_whp : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, C ≤ Real.log n →
    ∀ k : ℕ, C * k ≤ ((n : ℝ) / Real.log n) ^ ((1 : ℝ) / 6) →
    ∀ x : Config n k, count x none = 0 → ∀ T : ℕ, C * T ≤ md x →
      1 - C / n ≤ expList (Fin n → Fin n) T
        (fun l => if (maxCount (l.foldl step x) : ℝ) ≤ C * n / md x then (1 : ℝ) else 0) := by
  obtain ⟨C3, hC3, h3⟩ := first_round
  obtain ⟨γ, C6, hγ, hC6, h6⟩ := descent
  obtain ⟨C7, hC7, h7⟩ := plateau γ hγ
  refine ⟨C3 + C6 + C7 + 2 * γ + 1, by positivity, ?_⟩
  intro n hL k hk x hq T hT
  set C := C3 + C6 + C7 + 2 * γ + 1 with hCdef
  have hn1 : 1 < n := one_lt_of_log (by positivity) hL
  haveI : NeZero n := ⟨by omega⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hN := one_le_div_log hn1
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hk2 : C3 * k ≤ ((n : ℝ) / Real.log n) ^ ((1 : ℝ) / 2) :=
    range_mono (by linarith) hk0 hN (by norm_num) hk
  have hk4 : C7 * k ≤ ((n : ℝ) / Real.log n) ^ ((1 : ℝ) / 4) :=
    range_mono (by linarith) hk0 hN (by norm_num) hk
  have hk6 : C6 * k ≤ ((n : ℝ) / Real.log n) ^ ((1 : ℝ) / 6) :=
    range_mono (by linarith) hk0 hN le_rfl hk
  obtain ⟨m, hm⟩ := exists_plurality x hq (by omega)
  have hmd1 : 1 ≤ md x := one_le_md x ⟨m, by
    have := maxCount_pos_of_und_zero x hq (by omega)
    obtain ⟨j, -, hj⟩ := exists_mem_eq_sup (univ : Finset (Fin k)) ⟨m, mem_univ m⟩
      fun i => count x (some i)
    exact lt_of_lt_of_le (by rw [maxCount_def] at this; rwa [hj] at this) (hm j)⟩
  have hmd0 : 0 < md x := by linarith
  set S : Set (Config n k) := {z | (maxCount z : ℝ) ≤ C * n / md x} with hS
  have hsub {a : ℝ} (ha : a ≤ C) :
      {z : Config n k | (maxCount z : ℝ) ≤ a * n / md x} ⊆ S := fun z hz => by
    simp only [Set.mem_setOf_eq, hS] at hz ⊢
    exact hz.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ha hn0.le) hmd0.le)
  rw [prob_eq_one_sub_miss T x (fun z => (maxCount z : ℝ) ≤ C * n / md x)]
  suffices hmiss : miss S T x ≤ C / n by exact (by linarith : 1 - C / n ≤ 1 - miss S T x)
  rcases T with _ | T
  · -- after `0` rounds: `c₁ ≤ n / md(x) ≤ C n / md(x)`
    have hx : x ∈ S := by
      simp only [hS, Set.mem_setOf_eq]
      rw [le_div_iff₀ hmd0]
      have := maxCount_mul_md_le x hq (by omega)
      have hM : (0 : ℝ) ≤ maxCount x := Nat.cast_nonneg _
      nlinarith
    have : miss S 0 x = 0 := by
      unfold miss
      simp [hx]
    rw [this]
    positivity
  · push_cast at hT
    have hmdC : C ≤ md x := by nlinarith
    rw [add_comm T 1]
    set S3 : Set (Config n k) := {y | (n : ℝ) / (2 * ratioR x ^ 2) ≤ cnt y m ∧
          (maxCount y : ℝ) ≤ 2 * n / ratioR x ^ 2 ∧
          n * (1 - 2 / ratioLam x) ≤ und y ∧ und y ≤ n * (1 - 1 / (2 * ratioLam x))} with hS3
    have hstage : ∀ y ∈ S3, miss S T y ≤ (C6 + C7) / n := by
      intro y hy
      obtain ⟨-, hy2, hy3, hy4⟩ := hy
      obtain ⟨t, -, hall, hwin⟩ :=
        h6 n (by linarith) k hk6 x hq (by linarith) y hy2 hy3 hy4
      rcases le_or_gt T t with hTt | hTt
      · calc miss S T y ≤ miss {z | (maxCount z : ℝ) ≤ γ * n / md x} T y :=
              miss_mono (hsub (by linarith)) T y
          _ ≤ C6 / n := hall T hTt
          _ ≤ (C6 + C7) / n := by gcongr; linarith
      · obtain ⟨j, rfl⟩ : ∃ j, T = t + j := ⟨T - t, by omega⟩
        have hpl : ∀ z ∈ {z : Config n k | (maxCount z : ℝ) ≤ γ * n / md x ∧
            |und z - n / 2| ≤ 2 * γ ^ 2 * n / md x}, miss S j z ≤ C7 / n := by
          intro z hz
          obtain ⟨hz1, hz2⟩ := hz
          have hj : C7 * (j : ℝ) ≤ md x := by
            have : (j : ℝ) ≤ t + j + 1 := by
              have : (0 : ℝ) ≤ t := Nat.cast_nonneg t
              linarith
            have hT2 : C * ((t : ℝ) + j + 1) ≤ md x := by push_cast at hT; linarith
            have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
            have : C7 * (j : ℝ) ≤ C * j := mul_le_mul_of_nonneg_right (by linarith) hj0
            nlinarith
          calc miss S j z ≤ miss {z | (maxCount z : ℝ) ≤ 2 * γ * n / md x ∧
                |und z - n / 2| ≤ 2 * γ ^ 2 * n / md x} j z :=
                miss_mono (fun w hw => hsub (a := 2 * γ) (by linarith) hw.1) j z
            _ ≤ C7 / n :=
                h7 n (by linarith) k hk4 (md x) (by linarith) (md_le_card x) z hz2 hz1 j hj
        have := miss_comp (T₁ := t) (T₂ := j) (by positivity) hpl y
        calc miss S (t + j) y ≤ _ := this
          _ ≤ C6 / n + C7 / n := by linarith [hwin]
          _ = (C6 + C7) / n := by ring
    have h1 := miss_comp (T₁ := 1) (T₂ := T) (by positivity) hstage x
    have h3' := h3 n (by linarith) k hk2 x m hq hm
    calc miss S (1 + T) x ≤ miss S3 1 x + (C6 + C7) / n := h1
      _ ≤ C3 / n + (C6 + C7) / n := by linarith
      _ ≤ C / n := by
        rw [← add_div]
        exact div_le_div_of_nonneg_right (by linarith) hn0.le

/-- **Theorem 8 of [BCNPS15]** (the convergence time is `Ω(md(c̄))` w.h.p.). There is `C > 0`
such that, for every `n` with `log n ≥ C`, every `k` with `C k ≤ (n / log n)^{1/6}`, every
configuration `x` without undecided nodes and every round `T` with `C (T + 1) ≤ md(x)`, the
probability that all nodes hold the same colour after `T` rounds is at most `C / n`. -/
theorem lower_bound_consensus : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, C ≤ Real.log n →
    ∀ k : ℕ, C * k ≤ ((n : ℝ) / Real.log n) ^ ((1 : ℝ) / 6) →
    ∀ x : Config n k, count x none = 0 → ∀ T : ℕ, C * (T + 1) ≤ md x →
      expList (Fin n → Fin n) T
        (fun l => if ∃ i, l.foldl step x = fun _ => some i then (1 : ℝ) else 0) ≤ C / n := by
  obtain ⟨C, hC, h⟩ := lower_bound_whp
  refine ⟨2 * C, by positivity, ?_⟩
  intro n hL k hk x hq T hT
  have hn1 : 1 < n := one_lt_of_log (by positivity) hL
  haveI : NeZero n := ⟨by omega⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hk' : C * k ≤ ((n : ℝ) / Real.log n) ^ ((1 : ℝ) / 6) :=
    le_trans (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg k)) hk
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hT' : C * T ≤ md x := by nlinarith
  have hmd : 2 * C ≤ md x := by nlinarith
  have hmd0 : 0 < md x := by linarith
  have hw := h n (le_trans (by linarith) hL) k hk' x hq T hT'
  have hpt (l : List (Fin n → Fin n)) :
      (if ∃ i, l.foldl step x = fun _ => some i then (1 : ℝ) else 0) ≤
        1 - (if (maxCount (l.foldl step x) : ℝ) ≤ C * n / md x then (1 : ℝ) else 0) := by
    by_cases hc : ∃ i, l.foldl step x = fun _ => some i
    · obtain ⟨i, hi⟩ := hc
      have hcnt : count (l.foldl step x) (some i) = n := by
        rw [hi, count_def]
        simp
      have hge : (n : ℝ) ≤ maxCount (l.foldl step x) := by
        have := count_le_maxCount (l.foldl step x) i
        rw [hcnt] at this
        exact_mod_cast this
      have hlt : C * n / md x < maxCount (l.foldl step x) := by
        have : C * n / md x ≤ n / 2 := by
          rw [div_le_iff₀ hmd0]
          nlinarith
        linarith
      rw [if_pos ⟨i, hi⟩, if_neg (not_le.mpr hlt)]
      norm_num
    · rw [if_neg hc]
      split_ifs <;> norm_num
  calc expList (Fin n → Fin n) T
        (fun l => if ∃ i, l.foldl step x = fun _ => some i then (1 : ℝ) else 0)
      ≤ expList (Fin n → Fin n) T (fun l =>
          1 - (if (maxCount (l.foldl step x) : ℝ) ≤ C * n / md x then (1 : ℝ) else 0)) :=
        expList_le_expList hpt
    _ = 1 - expList (Fin n → Fin n) T (fun l =>
          if (maxCount (l.foldl step x) : ℝ) ≤ C * n / md x then (1 : ℝ) else 0) :=
        Undecided.Sequential.expList_one_sub T _
    _ ≤ C / n := by linarith
    _ ≤ 2 * C / n := div_le_div_of_nonneg_right (by linarith) hn0.le

end Undecided.Plurality
