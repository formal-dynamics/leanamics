# Paper vs. formalization

This file compares

> L. Becchetti, A. Clementi, E. Natale, F. Pasquale, R. Silvestri, L. Trevisan,
> **Simple Dynamics for Plurality Consensus**

with its Lean formalization in this package. There are two versions of the
paper:

* **SPAA** — Proceedings of SPAA 2014, pp. 247–256. Numbering in this package
  and its blueprint follows this version.
* **v3** — the journal version, [arXiv:1310.2858v3](https://arxiv.org/abs/1310.2858)
  (July 2015). Its upper-bound section is rewritten with different lemmas;
  its lower-bound section adds full proofs of Theorem 4.2 and a new Section 4.4.

The formalization of Theorem 3.8 follows the SPAA proof, repaired where
needed. The v3 proof was checked and is not used (see Section 2).

## 1. Theorem 3.8: how the Lean proof differs from SPAA

| | SPAA | Lean |
| --- | --- | --- |
| Hypotheses | `3 ≤ λ < √n`, `c_m ≥ n/λ`, `s ≥ 22√(λ n log n)`, "sufficiently large `n`" | `λ ≥ 3`, same bounds on `c_m` and `s`, `log n ≥ 40`, `k ≥ 2` |
| Conclusion | consensus in `10T ≤ 100 λ log n` rounds w.p. `≥ 1 - 11T/n²` | consensus in `10T ≤ 130 λ log n` rounds w.p. `≥ 1 - 11T/n` |
| Saturation phases | `M = {m}`, `s ≥ n/3`, `n - c_m ≤ (2n/3)(17/18)^{i-1}` | `n - c_m < max((n/3)(17/18)^j, n^{1/4} log n)` |
| Growth phases | `c_m > 2n/3`, or `M = {m}`, `c_m ≥ n/λ`, `s ≥ Λ(1+1/(6λ))^{i-1}` | same, with `T₁` chosen so that `Λ(1+1/(6λ))^{T₁} > n` |
| Per-round failure in growth | `1/n²` | `1/n` (union bound over colors) |

Reasons:

1. **The saturation phases are not preserved as defined.** The SPAA sets require
   `s(c) ≥ n/3`, but Lemma 3.7 only controls `n - c_m`, so nothing shows that a
   round keeps `s(c) ≥ n/3`. The Lean sets drop that condition:
   `n - c_m < n/3` already implies that `m` is the unique plurality color with
   `s(c) ≥ n/3` (`of_dissent_lt`). The threshold uses `max` with
   `n^{1/4} log n` so that the regime of Lemma 3.7(ii) also moves the chain
   forward.
2. **A union bound is missing.** Lemma 3.5 bounds the failure against *one*
   competing color, but entering the next growth phase needs the bias to grow
   against *all* of them. Colors without nodes stay empty
   (`count_step_eq_zero`), and fewer than `n - c_m` colors have nodes, so a
   round fails with probability at most `n/n² = 1/n`. The union bound over
   `k` colors that the paper would need gives the same order when `k ≤ n`.
3. **`λ < √n` is not needed.** It only makes the hypothesis
   `s ≥ 22√(λ n log n)` satisfiable.
4. **`k ≥ 2`** is used to locate the color attaining the bias; `k = 1` is
   trivially in consensus.
5. **Lemma 3.7** has no proof in SPAA or v3. The Lean proof uses Lemma 3.6
   with `s c_m ≥ n²/9` (first regime) and `s ≥ n - 2(n - c_m)` (second
   regime), the closed-form Chernoff upper tail, and Markov's inequality.
6. **Lemma A.4** has no proof in SPAA (the journal version drops it). The
   Lean proof (`Dynamics.Kernel.nested_phases`) does not need the hypothesis
   `ε ≤ ν`.

## 2. The journal version (arXiv v3)

v3 replaces Lemmas 3.3–3.7 by three new lemmas ("from plurality to
majority", "from majority to almost all", "the last step") and proves the
theorem in three sentences, without Lemma A.4. It fixes the two issues above
in spirit (its phases switch on `c_1 ≥ 2n/3`, and its per-color failure
probability is `1/n³`), but it has its own problems, so the formalization
keeps the SPAA proof:

* **An intermediate inequality that needs a minor correction.** The proof of "from plurality to
  majority" uses `μ_1 - μ_j ≥ (c_1 - c_j)(1 + c_1/(3n))` for every `j ≠ 1`.
  This fails for colors with few nodes: for `c = (n/3 + s, n/3, n/3 - s, 0)`
  and `j = 4`, `μ_1 - μ_4 = c_1(1 + s/n - 2s²/n²)`, which is below
  `c_1(1 + 1/9)` whenever `s < n/9`. The lemma's conclusion (stated with
  `s(c)` instead of `c_1 - c_j`) is still true, because `μ` is increasing in
  `c_j` and so `μ_1 - μ_j ≥ μ_1 - μ_2`.
* **Inconsistent constants.** One constant `α` plays two roles: the Chernoff
  width that gives failure probability `1/n³`, and the constant in the bias
  hypothesis. The step `2α√(2c_1 log n)/(c_1 - c_j) ≤ √(c_1/n)/(12√λ)` needs
  the second to be `24√2` times the first. Theorem 3.8 is stated with
  `24√(2λ n log n)` while Corollaries 3.10–3.12 still use `22`.
* **Garbled steps** in "from majority to almost all" (the line ending
  `= (7/9) μ_{-1}/n` and the final `≤ (8/9) Σ μ_i`), and hypotheses such as
  `n - c_1 = ω(log n)` that are only asymptotic.

## 3. Lower bounds (Section 4)

| Paper | Lean | Difference |
| --- | --- | --- |
| Lemma 4.1 | `lemma_4_1` | stated for `c_j ≤ n/k + b` (covers every `a ≤ b` at once) |
| Theorem 4.2 | `theorem_4_2`, `theorem_4_2_log` | explicit: monochromatic at time `T` w.p. `≤ kT/n²` whenever `b(1+3/k)^T ≤ n/k`; `k ≥ 3` |
| Theorem 4.8 (a), Lemma 4.9 | `theorem_4_8_a` | proved except for rules with `Δ_r, Δ_b ≤ 1`; needs `8 ∣ n` |
| Theorem 4.8 (b), Lemma 4.10 | `theorem_4_8_b` | explicit `η = 1/20`; needs `60 ∣ n`, `log n ≥ 20` |
| Lemma 4.11 | `lemma_4_11`, `lemma_4_11_paper` | factor `1 + 2h²/k`; allows `c_j ≤ a` |
| Theorem 4.12 | `theorem_4_12`, `theorem_4_12_log` | explicit: monochromatic w.p. `≤ kT e^{-2nh⁴/k⁴}` for `T ≤ (k/(2h²)) log(4/3)`; `k ≥ 3` |

The issues found while formalizing, in both SPAA and v3 unless stated
otherwise:

* **Theorem 4.2: range of `k`.** Lemma 4.1 needs `b ≥ k√(n log n)`, so the
  thresholds must start at `b_0 = max((n/k)^{1-ε}, k√(n log n))`, and the
  number of rounds obtained is `(k/3) log(n/(k b_0))`. This is `Ω(k log n)`
  for `k ≤ n^{1/4-δ}` but degenerates as `k → (n/log n)^{1/4}`, where
  `n/k = k√(n log n)`. The formal statement is parametrized by `b`, so it
  holds for every `k`; only the `Ω(k log n)` reading needs the smaller range.
  v3's full proof also has the typo `(1 - 3/k)^T` for `(1 + 3/k)^T`, and
  chooses the thresholds `b` after seeing the trajectory; the union bound
  needs the fixed schedule `b_t = (1 + 3/k)^t b_0` used here
  (`Dynamics.expList_escape`).
* **Lemma 4.9 (clear majority): a gap.** The proof shows that the number of
  red nodes is a supermartingale, but checks `E[X_{t+1} | X_t] ≤ X_t` only when
  red is the majority. From formula (7),
  `p(r) - c_r/n = (c_r/n)(c_b/n)(x(Δ_r - 2) + y(2 - Δ_b))` with
  `x = c_r/n, y = c_b/n`. The Lean proof uses that when `Δ_r ≤ 2 ≤ Δ_b` this
  is `≤ 0` in *every* state, so no optional stopping is needed
  (`not_solver_of_drift`), and by swapping the roles of the two colors this
  covers every non-majority pair except `Δ_r, Δ_b ≤ 1`. In that case the drift
  is positive when red is the minority: the process is pulled to
  `x* = (2 - Δ_b)/(4 - Δ_r - Δ_b)`, and which color eventually wins depends on
  how it leaves that point. The paper's argument does not address this, and it
  is left open. Also `(1 - ε)n ≤ 5n/8` gives `ε ≥ 3/8`, not `5/8` (still
  `> 1/4`).
* **Lemma 4.10 (uniform property)** is a sketch in the paper: it treats
  `δ_r = 1` with `(δ_g, δ_b) ∈ {(3,2), (4,1)}` (missing `(5,0)`) and asserts
  that `r` "will not converge" by iterating a one-round estimate. The Lean
  proof covers every non-uniform triple (some color has `δ ≤ 1` because the
  three counts sum to `6`) and makes the iteration rigorous: while `r` has at
  most `2n/5` nodes its count contracts by `0.97` in expectation, a chain
  frozen above `2n/5` turns this into a contraction in every state, and
  Hoeffding's inequality bounds the probability of being frozen.
* **Lemma 4.11** states the factor `1 + h²/k` but proves `1 + 2h²/k`; Theorem
  4.12 uses the proved version. Theorem 4.12 also applies Lemma 4.11 to colors
  with fewer than `n/k` nodes, which the lemma excludes; `lemma_4_11` allows
  `c_j ≤ a` to cover them.
* **Tie-breaking in `h`-plurality** is modelled by a uniform ordering of the
  sample positions: the tied position of smallest rank wins. All tied colors
  appear equally often, so each is chosen with the same probability, as the
  paper specifies.

## 4. Not formalized

* **Observation 3.9 (adversary).** As stated ("Theorem 3.8 still holds")
  it cannot hold literally: an adversary that recolors even one node per round
  prevents exact consensus. The introduction states the intended claim: an
  almost-stable phase where all but `O(T)` nodes agree.
* **The case `Δ_r, Δ_b ≤ 1` of Theorem 4.8 (a)**, see Section 3.
* **v3 Section 4.4** (bias `O(√(kn))` can shrink in one round with constant
  probability) is new in v3. It relies on negative association of
  balls-in-bins counts, a reverse Chernoff bound and a lower bound on
  `P(X ≥ E X)` for binomials, none of which is in the finite probability
  layer yet.
