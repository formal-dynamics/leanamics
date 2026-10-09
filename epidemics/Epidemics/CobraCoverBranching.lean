import Epidemics.CobraCover

/-! # COBRA with branching factor `1 + ρ` (EPI-4, Corollary 1 and Theorem 3)

Cooper, Radzik, Rivera, PODC 2016 (arXiv:1602.05768), Corollary 1 (Section 3) and Theorem 3
(Section 1).

In COBRA with expected branching factor `1 + ρ`, each informed vertex pushes to one uniformly
random neighbour and, with probability `ρ`, to a second one (chosen with replacement); in the dual
BIPS each vertex other than the source contacts one random neighbour and, with probability `ρ`, a
second one. Here `ρ = p/q` is rational: a round (`CoinChoices G q`) gives every vertex two
neighbour samples and a uniform coin in `Fin q`, and the vertex uses its second sample iff its
coin is `< p` (`coinTargets`). Both processes read the same rounds.

* `cobraCoin_bips_duality`: the duality of Theorem 4 for these processes (same proof).
* **Corollary 1** (`bipsCoin_expected_growth`):
  `E(|A_{t+1}| ∣ A_t = A) ≥ |A| (1 + ρ (1 - λ²)(1 - |A|/n))`, since a vertex `x` is infected with
  probability `1 - (1 - P(x, A))(1 - ρ P(x, A)) = (1 + ρ) P(x, A) - ρ P(x, A)²`.
* `bipsCoin_infection_time`: the analogue of Theorem 2 (constant `λ` and `ρ`).
* **Theorem 3** (`cobra_cover_time_branching`, `cobra_cover_time_branching_expectation`): for
  `λ ≤ λ₀ < 1` and `ρ ≥ ρ₀ > 0` constant, the cover time is `O(log n)` w.h.p. and in expectation.
-/

namespace Epidemics
open Finset Dynamics

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- One round of the branching-factor-`1 + p/q` processes: two neighbour samples per vertex
(`Choices G 2`) and one coin per vertex, uniform in `Fin q`. Under the uniform distribution all
samples and coins are independent. -/
abbrev CoinChoices (G : SimpleGraph V) (q : ℕ) : Type _ := Choices G 2 × (V → Fin q)

variable {G : SimpleGraph V} {p q : ℕ}

/-- The neighbours used by the vertex `x` in the round `ρ`: its first sample, and also its second
sample when its coin is `< p` (probability `p/q`). COBRA pushes to these vertices, and BIPS
contacts them. -/
def coinTargets (p : ℕ) (ρ : CoinChoices G q) (x : V) : Finset V :=
  if ((ρ.2 x : ℕ) < p) then {(ρ.1 x 0 : V), (ρ.1 x 1 : V)} else {(ρ.1 x 0 : V)}

/-- One round of COBRA with branching factor `1 + p/q`: every vertex of `D` pushes to its
`coinTargets`. -/
def cobraCoinStep (p : ℕ) (D : Finset V) (ρ : CoinChoices G q) : Finset V :=
  D.biUnion (coinTargets p ρ)

/-- COBRA with branching factor `1 + p/q` after the rounds `l` (first round first), from `C`. -/
def cobraCoinRun (p : ℕ) (C : Finset V) (l : List (CoinChoices G q)) : Finset V :=
  l.foldl (cobraCoinStep p) C

/-- One round of BIPS with branching factor `1 + p/q` and persistent source `v`: a vertex is
infected next iff it is `v` or one of its `coinTargets` is in the current infected set `A`. -/
def bipsCoinStep (p : ℕ) (v : V) (A : Finset V) (ρ : CoinChoices G q) : Finset V :=
  insert v (univ.filter fun u => ∃ y ∈ coinTargets p ρ u, y ∈ A)

/-- BIPS with branching factor `1 + p/q` and source `v` after the rounds `l`, from `A₀`. -/
def bipsCoinRun (p : ℕ) (v : V) (A₀ : Finset V) (l : List (CoinChoices G q)) : Finset V :=
  l.foldl (bipsCoinStep p v) A₀

variable [DecidableRel G.Adj]

/-- **Theorem 4 for branching factor `1 + p/q`**: `P(Hit_C(v) > t ∣ C₀ = C) =
P(C ∩ A_t = ∅ ∣ A₀ = {v})` for COBRA and BIPS with branching factor `1 + p/q`. Same proof as
`cobra_bips_duality`: pathwise, COBRA from `C` along `r₁, …, r_t` visits `v` iff BIPS from `{v}`
along `r_t, …, r₁` infects a vertex of `C`. -/
theorem cobraCoin_bips_duality (p : ℕ) (v : V) (C : Finset V) (t : ℕ) :
    expList (CoinChoices G q) t
        (fun l => if ∀ s ≤ t, v ∉ cobraCoinRun p C (l.take s) then (1 : ℝ) else 0) =
      expList (CoinChoices G q) t
        (fun l => if C ∩ bipsCoinRun p v {v} l = ∅ then (1 : ℝ) else 0) := by
  sorry

/-- **Corollary 1** (Section 3). On an `r`-regular graph (`r > 0`), for `0 ≤ ρ = p/q ≤ 1`, one
round of BIPS with branching factor `1 + ρ` from the infected set `A` gives
`E(|A_{t+1}| ∣ A_t = A) ≥ |A| (1 + ρ (1 - λ²)(1 - |A|/n))`. -/
theorem bipsCoin_expected_growth {r : ℕ} (hreg : G.IsRegularOfDegree r) (hr : 0 < r)
    (hq : 0 < q) (hpq : p ≤ q) (v : V) (A : Finset V) :
    (A.card : ℝ) *
        (1 + (p : ℝ) / q * (1 - lambdaG G r ^ 2) * (1 - A.card / Fintype.card V)) ≤
      avg (fun ρ : CoinChoices G q => ((bipsCoinStep p v A ρ).card : ℝ)) := by
  sorry

/-- **Theorem 2 for branching factor `1 + ρ`** (the BIPS half of Theorem 3, "the proof of
Theorem 3 follows from the proof of Theorem 1, by using Corollary 1"). For constants
`λ₀ < 1` and `ρ₀ > 0` there are `C` and `N` such that on every `r`-regular graph (`r > 0`) with
`n ≥ N` vertices and `λ ≤ λ₀`, for `ρ = p/q ∈ [ρ₀, 1]`, every source `v` and every
`T ≥ C log n`, BIPS with branching factor `1 + ρ` from `{v}` has not infected all vertices at
time `T` with probability at most `C / n³`. -/
theorem bipsCoin_infection_time (lam₀ ρ₀ : ℝ) (hlam₀ : lam₀ < 1) (hρ₀ : 0 < ρ₀) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj] (r p q : ℕ), G.IsRegularOfDegree r → 0 < r → p ≤ q →
      ρ₀ ≤ (p : ℝ) / q → lambdaG G r ≤ lam₀ → N ≤ Fintype.card V →
      ∀ (v : V) (T : ℕ), C * Real.log (Fintype.card V) ≤ T →
      expList (CoinChoices G q) T
          (fun l => if bipsCoinRun p v {v} l = univ then (0 : ℝ) else 1) ≤
        C / (Fintype.card V : ℝ) ^ 3 := by
  sorry

/-- **Theorem 3** (Section 1), probability bound. For constants `λ₀ < 1` and `ρ₀ > 0` there are
`C` and `N` such that on every `r`-regular graph (`r > 0`) with `n ≥ N` vertices and `λ ≤ λ₀`,
for `ρ = p/q ∈ [ρ₀, 1]`, every start vertex `u` and every `T ≥ C log n`, COBRA with branching
factor `1 + ρ` from `{u}` fails to visit every vertex at the times `1, …, T` with probability at
most `C / n²`. (The paper assumes `G` connected; `λ < 1` forces it.) -/
theorem cobra_cover_time_branching (lam₀ ρ₀ : ℝ) (hlam₀ : lam₀ < 1) (hρ₀ : 0 < ρ₀) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj] (r p q : ℕ), G.IsRegularOfDegree r → 0 < r → p ≤ q →
      ρ₀ ≤ (p : ℝ) / q → lambdaG G r ≤ lam₀ → N ≤ Fintype.card V →
      ∀ (u : V) (T : ℕ), C * Real.log (Fintype.card V) ≤ T →
      expList (CoinChoices G q) T
          (fun l => if (Icc 1 T).biUnion (fun s => cobraCoinRun p {u} (l.take s)) = univ
            then (0 : ℝ) else 1) ≤
        C / (Fintype.card V : ℝ) ^ 2 := by
  sorry

/-- **Theorem 3** (Section 1), expectation bound: under the same hypotheses, every partial tail
sum `∑_{s < H} P(cov(u) > s)` of the cover time of COBRA with branching factor `1 + ρ` is at most
`C log n`. -/
theorem cobra_cover_time_branching_expectation (lam₀ ρ₀ : ℝ) (hlam₀ : lam₀ < 1)
    (hρ₀ : 0 < ρ₀) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj] (r p q : ℕ), G.IsRegularOfDegree r → 0 < r → p ≤ q →
      ρ₀ ≤ (p : ℝ) / q → lambdaG G r ≤ lam₀ → N ≤ Fintype.card V →
      ∀ (u : V) (H : ℕ),
      ∑ s ∈ range H,
          expList (CoinChoices G q) s
            (fun l => if (Icc 1 s).biUnion (fun t => cobraCoinRun p {u} (l.take t)) = univ
              then (0 : ℝ) else 1) ≤
        C * Real.log (Fintype.card V) := by
  sorry

end Epidemics
