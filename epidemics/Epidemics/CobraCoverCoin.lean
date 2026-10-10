import Epidemics.CobraCoverTargets
import Epidemics.CobraCoverBips

/-! # One round of BIPS with branching factor `1 + p/q` (EPI-4, Corollary 1)

A round of the coin processes is `Choices G 2 × (V → Fin q)`: two neighbour samples and a coin
per vertex. Regrouping by vertex (`coinEquiv`) gives the product of the per-vertex samples
`CoinSample G q u = (Fin 2 → G.neighborSet u) × Fin q`, so the vertices are independent. Vertex
`u` uses its first sample, and also its second one when its coin is `< p` (`coinTgt`), so with
`P = d_A(u)/r` and `ρ = p/q` it meets `A` with probability
`1 - (1 - P)(1 - ρ P) = (1 + ρ) P - ρ P²` (`coin_hit_prob`). As in Lemma 1, the spectral bound
`∑_u P_u² ≤ λ² |A| + (1 - λ²) |A|²/n` gives Corollary 1 (`coin_expected_growth`).
-/

namespace Epidemics
open Finset Dynamics Real

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The samples of one vertex `u` in a round of the coin processes. -/
abbrev CoinSample (G : SimpleGraph V) (q : ℕ) (u : V) : Type _ :=
  (Fin 2 → G.neighborSet u) × Fin q

variable (G) in
/-- Regrouping a round of the coin processes by vertex. -/
def coinEquiv (q : ℕ) : (Choices G 2 × (V → Fin q)) ≃ ((u : V) → CoinSample G q u) where
  toFun ρ u := (ρ.1 u, ρ.2 u)
  invFun ω := (fun u => (ω u).1, fun u => (ω u).2)
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] lemma coinEquiv_apply {q : ℕ} (ρ : Choices G 2 × (V → Fin q)) (u : V) :
    coinEquiv G q ρ u = (ρ.1 u, ρ.2 u) := rfl

/-- The neighbours used by `u` given its samples: the first one, and the second one when the
coin is `< p`. -/
def coinTgt {q : ℕ} (p : ℕ) {u : V} (a : CoinSample G q u) : Finset V :=
  if ((a.2 : ℕ) < p) then {(a.1 0 : V), (a.1 1 : V)} else {(a.1 0 : V)}

omit [Fintype V] [DecidableRel G.Adj] in
lemma coinTgt_nonempty {q : ℕ} (p : ℕ) {u : V} (a : CoinSample G q u) :
    (coinTgt p a).Nonempty := by
  unfold coinTgt
  split_ifs <;> simp

omit [Fintype V] [DecidableRel G.Adj] in
/-- Meeting `A` with the targets: first sample in `A`, or coin `< p` and second sample in `A`,
written as `1 - m₀ + m₀ h₁ c` with `m₀ = 1_{first ∉ A}`, `h₁ = 1_{second ∈ A}`,
`c = 1_{coin < p}`. -/
lemma coinTgt_hit_indicator {q : ℕ} (p : ℕ) {u : V} (A : Finset V) (a : CoinSample G q u) :
    (if ∃ y ∈ coinTgt p a, y ∈ A then (1 : ℝ) else 0) =
      (1 - if (a.1 0 : V) ∈ A then 0 else 1) +
        ((if (a.1 0 : V) ∈ A then 0 else 1) * (if (a.1 1 : V) ∈ A then 1 else 0)) *
          (if (a.2 : ℕ) < p then 1 else 0) := by
  unfold coinTgt
  by_cases hc : (a.2 : ℕ) < p <;> by_cases h0 : (a.1 0 : V) ∈ A <;>
    by_cases h1 : (a.1 1 : V) ∈ A <;> simp [hc, h0, h1]

/-- **Infection probability of a vertex** `u ≠ v` with branching factor `1 + ρ`, `ρ = p/q`:
`(1 + ρ) P - ρ P²` with `P = d_A(u)/r`. -/
lemma coin_hit_prob {r : ℕ} (hreg : G.IsRegularOfDegree r) (hr : 0 < r) {p q : ℕ} (hq : 0 < q)
    (hpq : p ≤ q) (u : V) (A : Finset V) :
    avg (fun a : CoinSample G q u => if ∃ y ∈ coinTgt p a, y ∈ A then (1 : ℝ) else 0) =
      (1 + (p : ℝ) / q) * (((G.neighborFinset u ∩ A).card : ℝ) / r) -
        (p : ℝ) / q * (((G.neighborFinset u ∩ A).card : ℝ) / r) ^ 2 := by
  haveI : Nonempty (G.neighborSet u) :=
    Dynamics.nonempty_neighborSet G (fun w => by rw [hreg w]; exact hr) u
  haveI : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  set P := ((G.neighborFinset u ∩ A).card : ℝ) / r with hP
  let m : G.neighborSet u → ℝ := fun w => if (w : V) ∈ A then 0 else 1
  let h : G.neighborSet u → ℝ := fun w => if (w : V) ∈ A then 1 else 0
  let cp : Fin q → ℝ := fun b => if (b : ℕ) < p then 1 else 0
  have hm : avg m = 1 - P := avg_neighbor_miss hreg hr u A
  have hh : avg h = P := by
    have : h = fun w => 1 - m w := by
      funext w
      simp only [h, m]
      split_ifs <;> norm_num
    rw [this, avg_sub, avg_const, hm]
    ring
  have hcp : avg cp = (p : ℝ) / q := by
    rw [avg_indicator, Fintype.card_fin, Fin.card_filter_val_lt, min_eq_right hpq]
  simp_rw [coinTgt_hit_indicator p A]
  rw [avg_add (fun a : CoinSample G q u => 1 - m (a.1 0))
    (fun a : CoinSample G q u => (m (a.1 0) * h (a.1 1)) * cp a.2)]
  rw [avg_fst_mul (fun σ : Fin 2 → G.neighborSet u => 1 - m (σ 0)),
    avg_mul_prod (fun σ : Fin 2 → G.neighborSet u => m (σ 0) * h (σ 1)) cp, hcp]
  have h1 : avg (fun σ : Fin 2 → G.neighborSet u => 1 - m (σ 0)) = P := by
    rw [avg_sub, avg_const, avg_eval 2 0 m, hm]
    ring
  have h2 : avg (fun σ : Fin 2 → G.neighborSet u => m (σ 0) * h (σ 1)) = (1 - P) * P := by
    have := avg_prod_pi 2 (fun i : Fin 2 => if i = 0 then m else h)
    simp only [Fin.prod_univ_two, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ite_true,
      ite_false] at this
    rw [this, hm, hh]
  rw [h1, h2]
  ring

/-- **Corollary 1** (Section 3), for the target-set form of BIPS with branching factor
`1 + p/q`: `E|A'| ≥ |A| (1 + ρ (1 - λ²)(1 - |A|/n))` with `ρ = p/q`. -/
theorem coin_expected_growth {r : ℕ} (hreg : G.IsRegularOfDegree r) (hr : 0 < r) {p q : ℕ}
    (hq : 0 < q) (hpq : p ≤ q) (v : V) (A : Finset V) :
    (A.card : ℝ) *
        (1 + (p : ℝ) / q * (1 - lambdaG G r ^ 2) * (1 - A.card / Fintype.card V)) ≤
      avg (fun ρ : Choices G 2 × (V → Fin q) =>
        ((tgtBipsStep (fun ρ x => coinTgt p (coinEquiv G q ρ x)) v A ρ).card : ℝ)) := by
  haveI (u : V) : Nonempty (G.neighborSet u) :=
    Dynamics.nonempty_neighborSet G (fun w => by rw [hreg w]; exact hr) u
  haveI : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  have hn : (0 : ℝ) < Fintype.card V := by
    haveI : Nonempty V := ⟨v⟩
    exact_mod_cast Fintype.card_pos
  set ρ : ℝ := (p : ℝ) / q with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ ≤ 1 := by
    rw [hρ, div_le_one (by exact_mod_cast hq)]
    exact_mod_cast hpq
  let P : V → ℝ := fun u => ((G.neighborFinset u ∩ A).card : ℝ) / r
  rw [tgtBips_expected_card (coinEquiv G q) (fun u a => coinTgt p a) (fun _ _ => rfl) v A]
  have hterm (u : V) : (1 + ρ) * P u - ρ * P u ^ 2 ≤
      avg (fun a : CoinSample G q u =>
        if u = v ∨ ∃ y ∈ coinTgt p a, y ∈ A then (1 : ℝ) else 0) := by
    by_cases huv : u = v
    · simp only [huv, true_or, if_true, avg_const]
      obtain ⟨h0, h1⟩ := neighbor_frac_mem hreg hr v A
      nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr (mul_le_one₀ hρ1 h0 h1))]
    · simp only [huv, false_or]
      rw [coin_hit_prob hreg hr hq hpq u A]
  have hsum := Finset.sum_le_sum fun u (_ : u ∈ univ) => hterm u
  have hsq := sum_sq_neighbor_le hreg hr A
  have hlin := sum_neighbor_frac hreg hr A
  have hsplit : ∑ u, ((1 + ρ) * P u - ρ * P u ^ 2) =
      (1 + ρ) * ∑ u, P u - ρ * ∑ u, P u ^ 2 := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
  refine le_trans ?_ hsum
  rw [hsplit]
  have hP : ∑ u, P u = A.card := hlin
  rw [hP]
  have hq2 : ρ * ∑ u, P u ^ 2 ≤ ρ * (lambdaG G r ^ 2 * A.card +
      (1 - lambdaG G r ^ 2) * A.card ^ 2 / Fintype.card V) :=
    mul_le_mul_of_nonneg_left hsq hρ0
  have hid : (A.card : ℝ) *
      (1 + ρ * (1 - lambdaG G r ^ 2) * (1 - A.card / Fintype.card V)) =
      (1 + ρ) * A.card - ρ * (lambdaG G r ^ 2 * A.card +
        (1 - lambdaG G r ^ 2) * A.card ^ 2 / Fintype.card V) := by
    field_simp
    ring
  linarith

/-- **The rate of Theorem 3**: `c = min 1 (ρ₀ (1 - max λ₀ 0))` satisfies `0 < c ≤ 1` and
`c ≤ ρ (1 - λ²)` whenever `ρ ≥ ρ₀` and `0 ≤ λ ≤ λ₀`. -/
lemma coin_rate {lam₀ ρ₀ : ℝ} (hlam₀ : lam₀ < 1) (hρ₀ : 0 < ρ₀) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∀ ρ lam : ℝ, ρ₀ ≤ ρ → 0 ≤ lam → lam ≤ lam₀ → c ≤ ρ * (1 - lam ^ 2) := by
  have hM : max lam₀ 0 < 1 := max_lt hlam₀ one_pos
  refine ⟨min 1 (ρ₀ * (1 - max lam₀ 0)), lt_min one_pos (mul_pos hρ₀ (by linarith)),
    min_le_left _ _, fun ρ lam hρ hlam0 hlam => ?_⟩
  refine (min_le_right _ _).trans ?_
  have h1 : 1 - max lam₀ 0 ≤ 1 - lam := by linarith [le_max_left lam₀ 0]
  have h2 : 1 - lam ≤ 1 - lam ^ 2 := by nlinarith
  calc ρ₀ * (1 - max lam₀ 0) ≤ ρ * (1 - max lam₀ 0) :=
        mul_le_mul_of_nonneg_right hρ (by linarith)
    _ ≤ ρ * (1 - lam ^ 2) := mul_le_mul_of_nonneg_left (h1.trans h2) (by linarith)

/-- **Choice of `N` in Theorem 3**: for a constant `c > 0`, `128 √(log n/n) ≤ c` for all large
`n` (from `log n ≤ 2 √n`). -/
lemma exists_gap_N {c : ℝ} (hc : 0 < c) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → 128 * √(log (n : ℝ) / n) ≤ c := by
  refine ⟨⌈(32768 / c ^ 2) ^ 2⌉₊ + 2, by omega, fun n hn => ?_⟩
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hbig : (32768 / c ^ 2) ^ 2 ≤ (n : ℝ) := by
    have h1 := Nat.le_ceil ((32768 / c ^ 2) ^ 2)
    have h2 : ((⌈(32768 / c ^ 2) ^ 2⌉₊ : ℕ) : ℝ) ≤ n := by
      exact_mod_cast (show ⌈(32768 / c ^ 2) ^ 2⌉₊ ≤ n by omega)
    linarith
  have hsqrt : 32768 / c ^ 2 ≤ √(n : ℝ) := by
    rw [← sqrt_sq (by positivity : (0 : ℝ) ≤ 32768 / c ^ 2)]
    exact sqrt_le_sqrt hbig
  have hs0 : 0 < √(n : ℝ) := sqrt_pos.mpr hn0
  have hlog : log (n : ℝ) ≤ 2 * √(n : ℝ) := by
    have h1 := log_le_sub_one_of_pos hs0
    rw [log_sqrt hn0.le] at h1
    linarith
  have hratio : log (n : ℝ) / n ≤ c ^ 2 / 16384 := by
    rw [div_le_div_iff₀ hn0 (by norm_num)]
    have hsq : √(n : ℝ) * √(n : ℝ) = n := mul_self_sqrt hn0.le
    have hc2 : 32768 ≤ c ^ 2 * √(n : ℝ) := by
      rw [div_le_iff₀ (by positivity)] at hsqrt
      linarith
    nlinarith
  have h := sqrt_le_sqrt hratio
  rw [show c ^ 2 / 16384 = (c / 128) ^ 2 by ring, sqrt_sq (by positivity)] at h
  linarith

end Epidemics
