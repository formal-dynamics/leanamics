# EPI-8L: lower bounds for push, pull and push–pull on the complete graph

Source: B. Doerr, A. Kostrygin, *Randomized rumor spreading revisited*, ICALP 2017; long version
arXiv:2303.11150 (numbering of the long version). The upper bounds (Theorems 51, 52, 53, upper
halves) are in `Revisited/Instances.lean`. This roadmap item pins the matching lower bounds.

## Status

**Done.** All 25 pinned declarations are proved; `lake build Epidemics` succeeds without
warnings and `python3 ../scripts/check_axioms.py` reports only standard Lean axioms. No pinned
statement needed to change.

### Files

| File | Lines | Content |
| --- | --- | --- |
| `LowerGeneric.lean` | 248 | generic tools (pinned, proved at the pin) |
| `LowerRound.lean` | 380 | `prob_deficit_lt_cheb` (lower-tail Chebyshev on the deficit), `one_sub_inv_pow_ge_exp_neg` (`(1 - 1/n)^k ≥ e^{-1}` for `k < n`), `push_level_algebra`, the three one-round proofs |
| `LowerFinal.lean` | 511 | final phases of pull and push–pull: `reach_le_envelope`, targets `pullTarget`, `pushPullTarget`, `pull_final_lower_explicit` (`C = 128`, `r₀ = 5`, `N = 3`), `pushPull_final_lower_explicit` (`C = 128 e²`) |
| `LowerFinalPush.lean` | 226 | final phase of push: targets `pushTarget q = q³ (q - 20)` at `q = pushRoot L i = exp((ln u - i)/4)`, the key step `pushTarget_step`, `push_final_lower_explicit` (`C = 1600`, `κ = 1/2`) |
| `LowerPush.lean`, `LowerPull.lean`, `LowerPushPull.lean` | 73, 69, 80 | pinned phase statements (bodies point to the files above) |
| `LowerTotal.lean` | 427 | `sum_notYet_ge_of_tail`, `lower_expect_of_tail`, `double_tail_generic` (pull and push–pull, growth factor `ρ ∈ {2, 3}`), `push_tail_explicit`, the three `*_expect_explicit` |
| `Lower.lean` | 96 | the six pinned main theorems |

All main tails have rate `κ = ln 2 / 4`. Thresholds: `N = 2` for push; for pull and push–pull,
`N = max 3 N₁` with `ln N₁ ≥ 2^5` (so that `⌊log₂ ln n⌋ ≥ r₀ = 5`).

### Proof outline

1. **One round** (Lemmas 39 and 49): Chebyshev on the lower tail of `n - |T|`
   (`prob_deficit_lt_cheb`, with `Var|T| ≤ E|T| - |S| ≤ u` from Lemma 9 and nonpositive
   covariances), with `E[u'] ≥ u/e` (push), `= u²/n` (pull), `≥ u²/(en)` (push–pull).
2. **Final phases**: `envelope_seq_le` along explicit targets (see the files above). For push the
   step `g(q e^{-1/4}) ≤ g(q)/e - g(q)^{3/4}` reduces to `c⁴ - 20 c + 20 ≤ 0` for
   `c = e^{1/4} ∈ [5/4, 3^{1/4}]`; while `q_i ≥ 40`, round `i` fails with probability at most
   `2 / q_i²` and these sum to `≤ 4 e^{(t - ln u)/2}`; when `q_t < 40` the bound
   `1600 / q_t²` exceeds `1`.
3. **Main tails**: `reach_add_le` with `m' = n/2`. Push: `s = a - ⌈r/2⌉`, `τ = b - ⌊r/2⌋`
   (`a = ⌊log₂ n⌋`, `b = ⌊ln n⌋`). Pull and push–pull: `τ = d - 5`, `s = t* - τ`
   (`d = ⌊log₂ ln n⌋`). A positive `t*` forces `r ≤ 2 log₂ n`, which turns `n^{-1/2}` and `1/n`
   into `e^{-(ln 2/4) r}`; `t* = 0` has reach probability `0`.
4. **Expectations**: reflection of the sum (`sum_range_reflect`) and a geometric series give
   `∑_{t<R} P[T > t] ≥ t₀ - A / (1 - e^{-κ})`, and `t₀ = ⌊X⌋ + ⌊Y⌋ ≥ X + Y - 2`.

## Pinned statements

All of the following are proved.

Notation: `1 - P.notYet m t S` is the probability that at least `m` nodes are informed after
`t` rounds started from the informed set `S`, that is `P[T(|S|, m) ≤ t]`; `u = n - |S|` is the
number of uninformed nodes.

### Generic tools (`LowerGeneric.lean`)

* `envelope_le`: for a finite kernel and an observable `V`, if from every state with `V ≥ v` the
  observable falls below `f v` in one round with probability at most `δ v ≥ 0`, then after `t`
  rounds it is below `f^[t] v` with probability at most `∑_{i<t} δ (f^[i] v)` (round-by-round
  form of the leapfrog arguments, Lemmas 42 and 50).
* `envelope_seq_le`: the same with an explicit target sequence: if from `V ≥ g i` the
  observable falls below `g (i + 1)` with probability at most `δ i`, then from `V ≥ g 0` it is
  below `g t` after `t` rounds with probability at most `∑_{i<t} δ i`.
* `reach_le_of_expect_card_le`: if one round multiplies the expected number of informed nodes
  by at most `μ`, then `P[T(|S|, m) ≤ t] ≤ μ^t |S| / m` (replaces Theorem 27 for the
  instances).
* `reach_add_le`: `P[T(|S|, m) ≤ s + t] ≤ P[T(|S|, m') ≤ s] + B` when every state with fewer than
  `m'` informed nodes reaches `m` within `t` rounds with probability at most `B` (Markov property
  at a fixed time; replaces the use of Lemma 20).

### Push (`LowerPush.lean`, Theorem 51)

* `push_expect_card_le`: `E|S'| ≤ 2|S|`.
* `push_expect_uninformed`: `E[n - |S'|] = (n - |S|)(1 - 1/n)^{|S|}`.
* `push_growth_lower`: `P[T(|S|, m) ≤ t] ≤ 2^t |S| / m`.
* `push_round_lower` (Lemma 39 with `ρ = 1`, `A = 1`, `B = 1/4`, at any level `4 ≤ v ≤ u`):
  `P[u' < v/e - v^{3/4}] ≤ v^{-1/2}`.
* `push_final_lower` (Theorem 38 with `ρ = 1`): there are `C` and `κ > 0` such that for every
  `n`, every `S` and every `t`, `P[T(|S|, n) ≤ t] ≤ C e^{κ (t - ln u)}`.

### Pull (`LowerPull.lean`, Theorem 52)

* `pull_expect_card_le`: `E|S'| ≤ 2|S|`.
* `pull_expect_uninformed`: `E[n - |S'|] = (n - |S|)(1 - |S|/n)`.
* `pull_growth_lower`: `P[T(|S|, m) ≤ t] ≤ 2^t |S| / m`.
* `pull_round_lower` (Lemma 49 with `ℓ = 2`, `a = 1`): `P[u' < u²/(2n)] ≤ 4 n² / u³`.
* `pull_final_lower` (Theorem 48 with `ℓ = 2`): there are `C`, `r₀`, `N` such that for
  `n ≥ N`, every `S` with `2|S| ≤ n` and every `t ≤ log₂ ln n - r₀`,
  `P[T(|S|, n) ≤ t] ≤ C n^{-1/2}`.

### Push–pull (`LowerPushPull.lean`, Theorem 53)

* `pushPull_expect_card_le`: `E|S'| ≤ 3|S|`.
* `pushPull_expect_uninformed`: `E[n - |S'|] = (n - |S|)(1 - 1/n)^{|S|}(1 - |S|/n)`.
* `pushPull_growth_lower`: `P[T(|S|, m) ≤ t] ≤ 3^t |S| / m`.
* `pushPull_round_lower` (Lemma 49 with `ℓ = 2`, `a = 1/e`):
  `P[u' < u²/(2en)] ≤ 4 e² n² / u³`.
* `pushPull_final_lower` (Theorem 48 with `ℓ = 2`): as for pull.

### Main theorems (`Lower.lean`)

Started from one informed node (`S.card = 1`), for `n ≥ N`:

* `push_spreading_lower_tail`: `P[T ≤ ⌊log₂ n⌋ + ⌊ln n⌋ - r] ≤ A e^{-κ r}` for every `r`.
* `push_spreading_lower_expect`: every partial sum `∑_{t<R} P[T > t]` with
  `R ≥ log₂ n + ln n` is at least `log₂ n + ln n - B`; hence `E[T] ≥ log₂ n + ln n - B`.
* `pull_spreading_lower_tail`, `pull_spreading_lower_expect`: the same with
  `log₂ n + log₂ ln n`.
* `pushPull_spreading_lower_tail`, `pushPull_spreading_lower_expect`: the same with
  `log₃ n + log₂ ln n`.

Together with `push_spreading_tail`, `pull_spreading_tail`, `pushPull_spreading_tail` and the
`_expect` forms in `Instances.lean`, these give the paper's `log₂ n + ln n ± O(1)`,
`log₂ n + log₂ ln n ± O(1)` and `log₃ n + log₂ ln n ± O(1)`, with exponential tails on both
sides.

## Correspondence with the paper

| Paper (long version) | Here |
| --- | --- |
| Theorem 51, lower bound | `push_spreading_lower_tail`, `push_spreading_lower_expect` |
| Theorem 52, lower bound | `pull_spreading_lower_tail`, `pull_spreading_lower_expect` |
| Theorem 53, lower bound | `pushPull_spreading_lower_tail`, `pushPull_spreading_lower_expect` |
| Theorem 27 (lower exponential growth), instances | `*_growth_lower` (first-moment proof) |
| Theorem 38 (lower exponential shrinking), push | `push_final_lower` |
| Lemma 39, push | `push_round_lower` |
| Theorem 48 (lower double exponential shrinking) | `pull_final_lower`, `pushPull_final_lower` |
| Lemma 49, pull and push–pull | `pull_round_lower`, `pushPull_round_lower` |
| Lemmas 42 and 50 (no leapfrogging) | `envelope_le`, `envelope_seq_le` |
| Lemma 20 (joining the phases) | not used; `reach_add_le` |

## Deviations from the source

1. **Direct route for the instances.** The general lower bounds (Theorems 27, 38, 48, and the
   lower halves of Theorems 1 to 3) are not formalized. The paper derives the lower halves of
   Theorems 51 to 53 by joining Theorem 27 with Theorem 38 or 48 through Lemma 20, which needs a
   major correction (see `Lemma20.lean` and `FORMALIZATION_DIFFERENCES.md`). Here the phases are
   joined at a fixed time (`reach_add_le`): after `⌊log₂ n⌋ - ⌈r/2⌉` rounds for push (about
   `log_ρ n + 5 - r` rounds for pull, `ρ = 2`, and push–pull, `ρ = 3`) at most `n/2` nodes are
   informed except with probability `O(2^{-r/2})` by the first moment, and from any state with
   at least `n/2` uninformed nodes the final phase is slow. No overshoot estimate is needed.
2. **Growth phase by the first moment.** Instead of the target-phase calculus of Theorem 27
   (Lemmas 28 to 30 and the stochastic domination by a sum of independent variables), the growth
   lower bound is Markov's inequality on `E|S_t| ≤ (1 + γ)^t |S|`, with `γ = 1, 1, 2`. This
   bound is exact in the exponent and has the tail `(1 + γ)^{-r}` directly.
3. **Starting sets.** The main theorems start from one informed node, as the paper. The final
   phase of push starts from any set (the bound depends on the number `u` of uninformed nodes);
   the final phases of pull and push–pull start from any set with at least `n/2` uninformed
   nodes. The paper's Theorems 38 and 48 start from exactly `⌊g n⌋` (resp. `⌈g n⌉`) uninformed
   nodes with `g` small.
4. **Time convention.** The tails are `P[T ≤ ⌊log₂ n⌋ + ⌊ln n⌋ - r]` (natural subtraction,
   so the time is `0` once `r` exceeds the sum), instead of `P[T ≤ log₂ n + ln n - r]`; the two
   differ by at most two rounds, absorbed in `A`. Expectations are bounded from below through
   every partial sum `∑_{t<R} P[T > t]` with `R` at least the bound, which implies the bound on
   `E[T] = ∑_{t ≥ 0} P[T > t]`.
5. **Final phase of pull and push–pull.** The paper's tail for Theorem 48 is
   `P[T ≤ log_ℓ ln n - r] = O(n^{-1 + 2αℓ})` for `r` a large enough constant. Here it is
   `O(n^{-1/2})` for `t ≤ log₂ ln n - r₀`, a weaker exponent that follows from the cruder
   variance bound `Var[u'] ≤ u` (Lemma 9 with nonpositive covariances); it suffices for the
   exponential tails of the main theorems.
6. **Explicit one-round constants.** The one-round lemmas fix the paper's free constants:
   `E₀(u) = u/e - u^{3/4}` for push (`A = 1`, `B = 1/4` in (9), with `E(u) = u/e` since
   `(1 - 1/n)^{n-u} ≥ 1/e`), and the double exponential targets `u²/(2n)` (pull) and
   `u²/(2en)` (push–pull), that is `E(ε)/2` of Lemma 49 with `a = 1` and `a = 1/e`.
   The push envelope uses the targets `g i = q_i³ (q_i - 20)` with `q_i = (u e^{-i})^{1/4}`, in
   place of the paper's recursively defined `u_{j+1} = E₀(u_j)` (Lemma 40), so that its lower
   bound `g i ≥ (u e^{-i})/2` (for `q_i ≥ 40`) is explicit.
7. **Threshold `N`.** The main theorems hold for `n ≥ N`; some threshold is needed (for `n = 1`
   the single informed node is everybody).

## Notes on the source

* Lemma 20 needs a major correction (documented with the upper bounds). The lower halves of
  Theorems 51 to 53 still hold; their proofs need a minor correction in the joining of the
  phases: besides Lemma 20, Theorems 38 and 48 bound the time from an exact number of uninformed
  nodes, which the process started from one node need not visit, so joining them also needs a
  comparison between starting states. The route above avoids both.
* Corollary 17 needs a minor correction: `1/e ≤ (1 - 1/n)^{n-u}` holds for `1 ≤ u < n`, not
  for `u = 0` (Lemma 13 gives `(1 - 1/n)^n ≤ 1/e`). The shrinking regime only uses `u ≥ 1`.
* Lemma 42 needs a minor correction: its proof gives the bound `q(u_{j+1})`, not `q(u_j)` (for
  `u ∈ [u_{j+1}, u_j[`, `q(u) ≤ q(u_{j+1})` since `q` is decreasing). The proof of Theorem 38
  uses it correctly in the form `P[τ = s] ≤ q(u_s)`. Typos in the same subsection: Lemma 39 is
  for `u ≤ g n`, Lemma 40 claims `u_j ≥ (1/2) u_0 e^{-j ρ_n}` for `j ≤ ln n / ρ_n`, the phases
  are defined by the number of uninformed nodes, and `(u_j)` is nonincreasing.
* In the proof of Theorem 27, the bound `P[d_j ≥ h] ≤ q_{h-1}(k_j)` needs a minor correction
  (a constant factor from the rounds spent in phase `j`), and the stochastic domination of `D`
  by a sum of independent variables is a standard domination lemma that is not stated.
