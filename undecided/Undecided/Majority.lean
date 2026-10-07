import Undecided.MajoritySymm

/-! # The undecided-state dynamics: the majority phase (UND-1)

Becchetti, Clementi, Natale, Pasquale and Silvestri, *Plurality consensus in the gossip model*
(SODA 2015, arXiv:1407.2565), analyze the synchronous undecided-state dynamics on the complete
graph: in every round every node samples one node uniformly at random (with replacement,
possibly itself, which gives the paper's expectations (3)–(4)) and updates by Table 1
(`Undecided.step`). For two colours their Theorem 11 says: starting without undecided nodes,
if the majority colour has at least `1 + α` times as many supporters as the other one, all
nodes support it within `O(log n)` rounds w.h.p. (with two colours the monochromatic distance
is at most `2`).

The roadmap target UND-1 is the stronger form with an additive bias (Survey Thm 28; Clementi,
Ghaffari, Gualà, Natale, Pasquale and Scornavacca, *A tight analysis of the parallel
undecided-state dynamics with two colors*, MFCS 2018, arXiv:1707.05135, Theorem 3.2): from
**any** configuration, undecided nodes allowed, in which one opinion leads the other by
`Ω(√(n log n))`, all nodes hold the initial majority opinion within `O(log n)` rounds w.h.p.

"W.h.p." is made explicit: for one constant `C`, every `n` with `log n ≥ C` and every initial
configuration with bias at least `C √(n log n)`, all nodes hold the majority opinion after
`⌈C log n⌉` rounds with probability at least `1 - C / n`. Probabilities are expectations of
indicators over `T` i.i.d. uniform rounds (`Dynamics.expList`); the configuration after the
rounds `l` is `l.foldl step x`. The all-`a` configuration is absorbing (`step_of_mono`), so
holding it after `⌈C log n⌉` rounds is the same as reaching it within `⌈C log n⌉` rounds.

* `majority_whp`: the majority opinion is `a` (the paper's convention `c₁ ≥ c₂`).
* `majority_whp_abs`: either opinion leads; the initial majority opinion wins.
* `majority_whp_of_ratio`: the two-colour case of Theorem 11 of the SODA paper (no undecided
  nodes initially, `count a ≥ (1 + α) count b`).

The proofs take `C = 10⁴` (`majority_explicit`, failure at most `2/n`); the phases are in
`Undecided/MajorityStages.lean` and assembled in `Undecided/MajorityAssembly.lean`.
-/

namespace Undecided
open Finset Dynamics

/-- **UND-1: the majority phase of the binary undecided-state dynamics** (Survey Thm 28;
Clementi et al., MFCS 2018, Theorem 3.2; for a bias of order `n` and no undecided nodes, SODA
2015 Theorem 11 with `k = 2`). There is a constant `C > 0` such that, for every `n` with
`log n ≥ C` and every configuration `x` of `n` nodes in which the `a`-nodes outnumber the
`b`-nodes by at least `C √(n log n)`, all nodes hold `a` after `⌈C log n⌉` rounds with
probability at least `1 - C / n`. Covered initial configurations: all of them with that bias,
whatever the number of undecided nodes (none, or all nodes but the `a`- and `b`-nodes). -/
theorem majority_whp : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, C ≤ Real.log n →
    ∀ x : Config n, C * √(n * Real.log n) ≤ (count x .a : ℝ) - count x .b →
      1 - C / n ≤ expList (Fin n → Fin n) ⌈C * Real.log n⌉₊
        (fun l => if l.foldl step x = (fun _ => .a) then (1 : ℝ) else 0) := by
  refine ⟨10000, by norm_num, fun n hL x hx => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast one_le_of_log hL
  have := prob_a_ge hL x hx
  have : 2 / (n : ℝ) ≤ 10000 / n := div_le_div_of_nonneg_right (by norm_num) hn0.le
  linarith

/-- **UND-1, either opinion** (Survey Thm 28; Clementi et al., MFCS 2018, Theorem 3.2, without
naming the majority). There is a constant `C > 0` such that, for every `n` with `log n ≥ C` and
every configuration `x` of `n` nodes (any number of undecided nodes) in which the numbers of
`a`- and `b`-nodes differ by at least `C √(n log n)`, all nodes hold the initial majority
opinion (`a` if the `a`-nodes are more, `b` otherwise) after `⌈C log n⌉` rounds with
probability at least `1 - C / n`. -/
theorem majority_whp_abs : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, C ≤ Real.log n →
    ∀ x : Config n, C * √(n * Real.log n) ≤ |(count x .a : ℝ) - count x .b| →
      1 - C / n ≤ expList (Fin n → Fin n) ⌈C * Real.log n⌉₊
        (fun l => if l.foldl step x = (fun _ => if count x .b < count x .a then .a else .b)
          then (1 : ℝ) else 0) := by
  refine ⟨10000, by norm_num, fun n hL x hx => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast one_le_of_log hL
  have h2 : 2 / (n : ℝ) ≤ 10000 / n := div_le_div_of_nonneg_right (by norm_num) hn0.le
  by_cases hab : count x .b < count x .a
  · simp only [hab, if_true]
    have hpos : (0 : ℝ) < (count x .a : ℝ) - count x .b := by
      have : (count x .b : ℝ) < count x .a := by exact_mod_cast hab
      linarith
    rw [abs_of_pos hpos] at hx
    linarith [prob_a_ge hL x hx]
  · simp only [hab, if_false]
    have hle : (count x .a : ℝ) ≤ count x .b := by exact_mod_cast not_lt.mp hab
    rw [abs_of_nonpos (by linarith), neg_sub] at hx
    linarith [prob_b_ge hL x hx]

/-- **SODA 2015, Theorem 11 for two colours.** Let `α > 0`. There is a constant `C > 0`
(depending on `α`) such that, for every `n` with `log n ≥ C` and every configuration `x` of `n`
nodes without undecided nodes (`q⁽⁰⁾ = 0`, as in the paper) in which `count a ≥ (1 + α) count b`,
all nodes hold `a` after `⌈C log n⌉` rounds with probability at least `1 - C / n`. (For two
colours `md(c̄) ≤ 2`, so the paper's `O(md(c̄) log n)` is `O(log n)`, and its condition
`k = O((n / log n)^{1/3})` holds.) -/
theorem majority_whp_of_ratio {α : ℝ} (hα : 0 < α) : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
    C ≤ Real.log n → ∀ x : Config n, count x .u = 0 → (1 + α) * count x .b ≤ (count x .a : ℝ) →
      1 - C / n ≤ expList (Fin n → Fin n) ⌈C * Real.log n⌉₊
        (fun l => if l.foldl step x = (fun _ => .a) then (1 : ℝ) else 0) := by
  refine ⟨10000 + 30000 * (2 + α) / α, by positivity, fun n hL x hu hab => ?_⟩
  have hC : (10000 : ℝ) ≤ 10000 + 30000 * (2 + α) / α := by
    have : (0 : ℝ) ≤ 30000 * (2 + α) / α := by positivity
    linarith
  have hL' : (10000 : ℝ) ≤ Real.log n := le_trans hC hL
  have hn1 := one_le_of_log hL'
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  haveI : NeZero n := ⟨by omega⟩
  have hL0 : (0 : ℝ) ≤ Real.log n := by linarith
  -- the bias is at least `α n / (2 + α)`
  have hsum := count_add x
  rw [hu, Nat.cast_zero, add_zero] at hsum
  have hbias : α * n / (2 + α) ≤ (count x .a : ℝ) - count x .b := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  -- and `α n / (2 + α) ≥ 10⁴ √(n log n)` once `log n ≥ 3·10⁴ (2 + α)/α`
  have hαL : 30000 * (2 + α) ≤ α * Real.log n := by
    have : 30000 * (2 + α) / α ≤ Real.log n := by linarith
    rw [div_le_iff₀ hα] at this
    linarith
  have hcube := log_cube_le hn1
  have hkey : (10000 : ℝ) ^ 2 * (n * Real.log n) ≤ (α * n / (2 + α)) ^ 2 := by
    have h2 : (30000 * (2 + α)) ^ 2 ≤ (α * Real.log n) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hαL 2
    have h3 : α ^ 2 * (Real.log n ^ 3 / 6) ≤ α ^ 2 * n :=
      mul_le_mul_of_nonneg_left hcube (sq_nonneg α)
    have h4 : (30000 * (2 + α)) ^ 2 * Real.log n ≤ (α * Real.log n) ^ 2 * Real.log n :=
      mul_le_mul_of_nonneg_right h2 hL0
    have h5 : (10000 : ℝ) ^ 2 * Real.log n * (2 + α) ^ 2 ≤ α ^ 2 * n := by nlinarith
    rw [div_pow, le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h5 hn0.le]
  have hx : 10000 * √(n * Real.log n) ≤ (count x .a : ℝ) - count x .b := by
    have e : 10000 * √((n : ℝ) * Real.log n) = √((10000 : ℝ) ^ 2 * (n * Real.log n)) := by
      rw [Real.sqrt_mul' ((10000 : ℝ) ^ 2) (by positivity), Real.sqrt_sq (by norm_num)]
    rw [e]
    calc √((10000 : ℝ) ^ 2 * (n * Real.log n)) ≤ √((α * n / (2 + α)) ^ 2) :=
          Real.sqrt_le_sqrt hkey
      _ = α * n / (2 + α) := Real.sqrt_sq (by positivity)
      _ ≤ _ := hbias
  -- pad the rounds from `⌈10⁴ log n⌉` to `⌈C log n⌉` (all-`a` is absorbing)
  have h1 := prob_a_ge hL' x hx
  rw [prob_allA_eq] at h1 ⊢
  have hmono := missP_allA_antitone x
    (Nat.ceil_mono (mul_le_mul_of_nonneg_right hC hL0))
  have : 2 / (n : ℝ) ≤ (10000 + 30000 * (2 + α) / α) / n :=
    div_le_div_of_nonneg_right (by linarith) hn0.le
  linarith

end Undecided
