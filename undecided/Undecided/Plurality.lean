import Undecided.PluralityAssembly

/-! # The undecided-state dynamics with `k` colours: plurality consensus (UND-3)

Becchetti, Clementi, Natale, Pasquale and Silvestri, *Plurality consensus in the gossip model*
(SODA 2015, arXiv:1407.2565), Theorem 11: let `k = O((n / log n)^{1/3})` and let `c̄` be any
initial configuration (without undecided nodes, `q⁽⁰⁾ = 0`, Section 2.1) in which the plurality
colour `1` satisfies `c̄₁ ≥ (1 + α) c̄ᵢ` for every colour `i ≠ 1`, where `α > 0` is an arbitrarily
small constant. Then w.h.p., after at most `O(md(c̄) log n)` rounds, all nodes support the initial
plurality colour. Here `md(c̄) = ∑ᵢ (c̄ᵢ / c̄₁)² ∈ [1, k]` is the monochromatic distance
(`Undecided.Plurality.md`).

"W.h.p." and `O(·)` are made explicit as in UND-1: for every `α > 0` there is one constant `C`
such that, for every `n` with `log n ≥ C`, every number of colours `k` with
`C k ≤ (n / log n)^{1/3}` and every configuration `x` without undecided nodes in which colour `m`
beats every other colour by the factor `1 + α`, all nodes support `m` after
`⌈C · md(x) · log n⌉` rounds with probability at least `1 - C / n`. Probabilities are
expectations of indicators over `T` i.i.d. uniform rounds (`Dynamics.expList`); the
configuration after the rounds `l` is `l.foldl step x`. The monochromatic configurations are
absorbing (`step_const`), so holding consensus after `T` rounds is the same as reaching it
within `T` rounds.

**Range of `k`.** The stated range is the paper's exponent `1/3` with a sufficiently small
constant (`k ≤ (n / log n)^{1/3} / C`, `C` depending on `α`), not an arbitrary constant: see
the UND-3 section of `FORMALIZATION_DIFFERENCES.md`. In short, the proof of Theorem 11 invokes
Lemma 10, which assumes `k = O((n / log n)^{1/4})`; and the per-round high-probability bounds on the ratios
`Cᵢ / C₁` (Lemma 2) only close at `k ≍ (n / log n)^{1/3}` when the drift
`(c₁ + 2q) / (cᵢ + 2q)` of the ratio beats its one-round fluctuation, which holds for
`k ≤ ε(α) (n / log n)^{1/3}`. The stated range contains `k = O((n / log n)^{1/4})` with any
constant for large `n`.

**Proof** (`plurality_explicit`, with `C = 10⁵ ((1 + α)²/α)²` and failure probability at most
`6/n`): Bernstein per round (`PluralityConc`, `PluralityRound`), an invariant on the ratios with
slack `12√(ℓ c_m)` kept by every good round (`PluralitySteps`), the potential `Φ = µ_m`, which
grows by `1 + κ/(8000B)` per good round until `4S + q ≤ n/10` (`PluralityProgress`), and the final
contraction of `4S + q` (`PluralityStages`), assembled in `PluralityAssembly`.
-/

namespace Undecided.Plurality
open Finset Dynamics

/-- **UND-3: plurality consensus of the undecided-state dynamics** (SODA 2015, Theorem 11).
Let `α > 0`. There is a constant `C > 0` (depending on `α`) such that, for every `n` with
`log n ≥ C`, every number of colours `k` with `C k ≤ (n / log n)^{1/3}`, every configuration `x`
of `n` nodes with `k` colours and no undecided nodes, and every colour `m` such that
`(1 + α) cᵢ ≤ c_m` for all colours `i ≠ m`, all nodes support `m` after `⌈C · md(x) · log n⌉`
rounds with probability at least `1 - C / n`. -/
theorem plurality_whp {α : ℝ} (hα : 0 < α) : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, C ≤ Real.log n →
    ∀ k : ℕ, C * k ≤ ((n : ℝ) / Real.log n) ^ ((1 : ℝ) / 3) →
    ∀ (x : Config n k) (m : Fin k), count x none = 0 →
      (∀ i, i ≠ m → (1 + α) * count x (some i) ≤ (count x (some m) : ℝ)) →
      1 - C / n ≤ expList (Fin n → Fin n) ⌈C * md x * Real.log n⌉₊
        (fun l => if l.foldl step x = (fun _ => some m) then (1 : ℝ) else 0) := by
  refine ⟨100000 * ((1 + α) ^ 2 / α) ^ 2, by positivity, fun n hL k hk x m hq hb => ?_⟩
  have hC : (0 : ℝ) < 100000 * ((1 + α) ^ 2 / α) ^ 2 := by positivity
  have hL0 : 0 < Real.log n := hC.trans_le hL
  have hn1 : 1 < n := by
    by_contra h
    have : (n : ℝ) ≤ 1 := by exact_mod_cast not_lt.mp h
    have := Real.log_nonpos (Nat.cast_nonneg n) this
    linarith
  haveI : NeZero n := ⟨by omega⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hcube := cube_of_rpow (by positivity) hL0 hn0.le hk
  have hmiss := plurality_explicit hα x m hL hcube hq hb
  rw [prob_allM_eq]
  have : (6 : ℝ) / n ≤ 100000 * ((1 + α) ^ 2 / α) ^ 2 / n := by
    apply div_le_div_of_nonneg_right _ hn0.le
    have : (16 : ℝ) ≤ ((1 + α) ^ 2 / α) ^ 2 := by
      have h4 := K_ge_four hα
      nlinarith
    nlinarith
  linarith

end Undecided.Plurality
