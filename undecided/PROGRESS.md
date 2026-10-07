# UND-1 progress: majority phase of the binary undecided-state dynamics

Source: Becchetti, Clementi, Natale, Pasquale, Silvestri, *Plurality consensus in the gossip
model*, SODA 2015, arXiv:1407.2565. The additive
`√(n log n)` form is Survey Thm 28 = Clementi, Ghaffari, Gualà, Natale, Pasquale, Scornavacca,
*A tight analysis of the parallel undecided-state dynamics with two colors*, MFCS 2018,
arXiv:1707.05135, Theorem 3.2.

## Status

**Done.** Phase 1 (pinning) and phase 2 (proofs) complete. `lake build Undecided` is
warning-free, no `sorry`; the job gate (`gate.py`, check mode) reports `SPEC OK` / `GATE OK`;
`#print axioms` of the three pinned theorems and of `majority_explicit`: only `propext`,
`Classical.choice`, `Quot.sound` (also `python3 ../scripts/check_axioms.py`, 10 declarations).

## Pinned (PINNED.txt; frozen up to `:=`)

All in `undecided/Undecided/Majority.lean`, namespace `Undecided`, imported by `Undecided.lean`:

* `majority_whp`: `∃ C > 0, ∀ n, C ≤ log n → ∀ x : Config n,
  C √(n log n) ≤ count a - count b → 1 - C/n ≤ P(after ⌈C log n⌉ rounds all nodes hold a)`.
  Any number of undecided nodes is allowed initially. **Proved with `C = 10⁴`.**
* `majority_whp_abs`: same with `|count a - count b|`; the target is the initial majority
  opinion (`a` if `count b < count a`, else `b`). **Proved with `C = 10⁴`.**
* `majority_whp_of_ratio (hα : 0 < α)`: SODA 2015 Theorem 11 with `k = 2`: `count u = 0`
  initially and `(1 + α) count b ≤ count a` give all-`a` after `⌈C log n⌉` rounds w.p.
  `≥ 1 - C/n`. **Proved with `C = 10⁴ + 3·10⁴ (2 + α)/α`.**

Probability = `expList (Fin n → Fin n) T (fun l => if l.foldl step x = fun _ => o then 1 else 0)`.
No new definitions in the pinned statements; they use `Config`, `Op`, `count`, `step` (hence
`update`) from `Undecided/Basic.lean`, which were not modified (the gate does not freeze
definition bodies).

## Proved (files, lines, main lemmas)

| file | lines | contents |
| --- | --- | --- |
| `MajorityRound.lean` | 146 | `count_add`; a count after one round is a sum of independent per-node indicators: `avg_count_step`, Hoeffding tails `tail_upper`, `tail_lower`; `bad_round` (a round misses the good event w.p. ≤ `4 exp(-2Λ²/n)`); `four_exp_sqrt` (`= 4/n²` for `Λ = √(n log n)`) |
| `MajorityArith.lean` | 149 | real inequalities: `bias_next` (`s' > s(1+q/n) - 2Λ`), `undec_next` (`q' > n/3 - s²/(2n) - Λ`), `contract` (`E[12b'+q'] ≤ 5/6 (12b+q)` when `b+2q ≤ 2n/3`, `q ≤ n/3`), `first_det`, `growth_det`, `bridge_det`, `fin_expect`, `fin_det` |
| `MajorityStages.lean` | 391 | `missP B T x` (miss probability) with `missP_succ`, `missP_mono`, `missP_comp` (composition of stages, Markov property via `expList_append`), `missP_allA_antitone` (absorption); round lemmas; `growth_stage` (via `Dynamics.expList_escape`, moving targets), `bridge_stage`, `fin_stage` (expectation contraction + stay, induction) |
| `MajorityAssembly.lean` | 192 | `big_n` (`n ≥ 4·10⁶ log n`), `prob_allA_eq`, **`majority_explicit`**: `log n ≥ 10⁴`, bias `≥ 10⁴ √(n log n)` ⟹ `missP (allA n) ⌈10⁴ log n⌉ x ≤ 2/n` |
| `MajoritySymm.lean` | 90 | `swapOp`, `update_swap`, `step_swap`, `foldl_swap`, `count_swap`; `prob_a_ge`, `prob_b_ge` |
| `Majority.lean` | 140 | the three pinned theorems |

Reusable pieces: `bad_round`/`tail_upper`/`tail_lower` (Hoeffding for any count of a synchronous
`K_n` round), `missP_comp` (phase composition for round-based processes; could move to
`dynamics/`), the `fin_stage` pattern (expectation contraction on a set that is left with
probability `≤ p` per round gives `ρ^T f + T p`), `swapOp` symmetry.

## Proof route actually taken

Only Hoeffding at deviation `Λ = √(n log n)` (per-round failure `4/n²`), no Bernstein. With
`s = a - b`, `Ψ = 12b + q`, `T = (T₁ + 1) + 18 + T₃ = ⌈10⁴ log n⌉`:

1. **First round + growth** (`T₁ + 1` rounds, `T₁ = ⌈log n / log(201/200)⌉ ≤ 201 log n + 1`):
   targets `{s ≥ 402Λ}` then `growthSet n g = {s ≥ g ∧ (q ≥ n/100 ∨ s ≥ g + n/20)}` with
   `g = 400Λ` growing by `201/200` per round up to `7n/10` (if `s ≤ 4n/5` a good round leaves
   `q' ≥ n/100` by Clementi et al.'s (4); if `q ≥ n/100` the bias grows by `1.01`).
2. **Bridge** (18 rounds): while `s ≥ 2n/3`, `Ψ` shrinks by `9/10` per good round, from
   `Ψ ≤ 2n` to `2n (9/10)^18 ≤ n/3`, and `s` loses at most `2Λ` per round.
3. **Final** (`T₃ ≥ 12 log n` rounds): on `{Ψ ≤ n/3}`, `E Ψ' ≤ 5/6 Ψ` and the set is kept after
   a good round, so `P(not all-a) ≤ (5/6)^T₃ n/3 + T₃ p ≤ 1/(3n) + T₃ p` (`Ψ < 1` iff all-`a`).

Total failure `≤ T·4/n² + 1/(3n) ≤ 2/n`. The phases follow Clementi et al. (MFCS 2018) in spirit
(their `H4`/`H5`/`H7` → `H6` → consensus), with a different, linear potential in the last phase.

## Errors / pitfalls seen

* Multi-line `by classical exact` terms inside statements break at the line break (the term
  must be indented more than the tactic block): introduced `missOne B x` instead.
* In this Mathlib `add_le_add_right h c : c + a ≤ c + b` (adds on the left).
* `Real.sqrt_mul` rewrites the first `√(x*y)` it finds: give the factor explicitly
  (`Real.sqrt_mul' (10000 ^ 2)`).
* Sanity checks before proving: a simulation (n = 10⁵, bias `√(n log n)` and `2√(n log n)`,
  starts with q = 0, q = n/2, b = 0 with a tiny, a = 2b with the rest undecided) always reached
  all-`a` within ≈ 2 log n rounds; with undecided nodes allowed, a ratio-only hypothesis is false
  (a = 2, b = 1, rest undecided: majority wins only ≈ 80%), hence `count u = 0` in
  `majority_whp_of_ratio`.

## Deviations from the paper

1. **Additive bias, undecided nodes allowed (main pin `majority_whp`).** SODA 2015 proves the
   binary case only as Theorem 11 with `k = 2`, from configurations without undecided nodes
   (`q⁽⁰⁾ = 0`, Section 2.1) and with a multiplicative bias `c₁ ≥ (1+α) c₂` (a bias of order
   `n`). The task and roadmap ask for the stronger statement from a bias `C √(n log n)` with
   undecided nodes allowed initially. That is Survey Thm 28 / Clementi et al. (MFCS 2018)
   Theorem 3.2, for *any* configuration with `|s| ≥ γ √(n log n)`. The SODA form is pinned
   separately (`majority_whp_of_ratio`), with `q⁽⁰⁾ = 0` as in the paper.
2. **Explicit w.h.p.** "w.h.p." (`1 - n^{-Θ(1)}`) and `O(log n)` become one existential
   constant `C`: `log n ≥ C`, bias `≥ C √(n log n)`, `⌈C log n⌉` rounds, probability
   `≥ 1 - C/n`. Clementi et al. allow any constant `γ > 0` (with a γ-dependent exponent);
   we pin only the existence of a suitable constant (a large `γ`).
3. **"Within T rounds" is stated as "at round T".** These are equivalent because the all-`a`
   (resp. all-`b`) configuration is absorbing (`step_of_mono`).
4. **Majority named `a`.** `majority_whp` follows the paper's convention `c₁ ≥ c₂`.
   `majority_whp_abs` covers either opinion.
5. **Sampling model.** Uniform with replacement, possibly oneself (as in Basic.lean). This is
   the model behind the paper's expectations (3)–(4) (`µ_i = c_i (c_i + 2q)/n`) and Clementi
   et al.'s (1)–(3).
6. **Finite probability.** Probabilities are `expList` expectations over `T` i.i.d. uniform
   rounds (equivalently `(kernel n).event`, by `Kernel.event_ofStep`), not path-space events.
7. **`majority_whp_of_ratio`:** `C` depends on `α` (the paper's `O(·)` depends on `α`). The
   paper's condition `k = O((n/log n)^{1/3})` is vacuous for `k = 2`, and `md(c̄) ≤ 2`, so
   `O(md(c̄) log n) = O(log n)`.
8. **Proof route.** Not the SODA 2015 route (Lemmas 1, 2, 5, 9, 10, Theorem 11, built on the
   monochromatic distance and a multiplicative bias), which does not reach an additive
   `√(n log n)` bias. The proof follows the phase structure of Clementi et al. (MFCS 2018),
   simplified with large explicit constants (`C = 10⁴`): Hoeffding only, three phases, and
   the linear potential `12b + q` in the final phase.
