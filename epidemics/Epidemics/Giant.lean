import Epidemics.GiantAnalysis
import Epidemics.GiantProb

/-! # The supercritical giant component of `G(n, p)` (EPI-3)

M. Krivelevich and B. Sudakov, *The phase transition in random graphs: a simple proof*, Random
Structures & Algorithms 43 (2013) 131–138, arXiv:1201.6529.

The random graph `G(n, p)` is bond percolation on the complete graph: `perc ⊤ ω` with i.i.d.
Bernoulli(`p`) edge coins `ω ~ coins p` on a vertex type `V` with `n = |V|` (`Epidemics.ReedFrost`,
EPI-1). The edge probability `p = (1 + ε) / n` is written `p * n = 1 + ε`, which excludes `n = 0`.
The paper's "with high probability" is made quantitative as "with probability at least
`1 - C / n`", and its "`ε > 0` a small enough constant" as `∃ ε₀ > 0, ∀ ε ∈ (0, ε₀]`.

* `exists_long_path`: Theorem 1, part 2 (a path of length `≥ ε² n / 5`).
* `exists_giant_component`: Theorem 2 (a component with `≥ ε n / 2` vertices).
* `exists_linear_component`: the supercritical half of the Erdős–Rényi phase transition, as quoted
  in the paper's abstract, for every `ε > 0`.

The proof is the paper's: run the depth-first search of `Epidemics.GiantDFS` on `perc ⊤ ω` for
`N₀ = ⌊θ n²⌋` queries (`θ = ε / 2` in the paper). By the principle of deferred decisions
(`prob_queryAnswers`) its answers are i.i.d. Bernoulli(`p`), so by the Chernoff bounds of FND-3
(Lemma 1, part 2, `prob_count_take_far`, and its windowed form `prob_not_good_le`) the numbers of
positive answers are close to their means; then the deterministic properties of the search
(`Epidemics.GiantAnalysis`) force a long stack `U` (a path) and an epoch spanning `ε n / 2`
vertices. Both arguments are first proved for general parameters (`core_path`,
`core_component`), whose conditions are the paper's inequalities; the theorems follow by choosing
the parameters, and the version for every `ε > 0` by taking `θ` small in terms of `ε` (instead of
`θ = ε / 2`).
-/

namespace Epidemics
open Finset Dynamics

/-- The bound `(N₀ + 3) e^{-δ² t₁ p / 3} ≤ C / n` once `t₁ p ≥ η λ n - 1` and `N₀ ≤ n² / 4`. -/
lemma tail_le_div {n N₀ t₁ : ℕ} {p δ η lam : ℝ} (hn : 1 ≤ (n : ℝ)) (hη : 0 < η) (hlam : 0 < lam)
    (hδ : 0 < δ) (hN₀ : (N₀ : ℝ) ≤ n ^ 2 / 4)
    (ht₁ : η * lam * n - 1 ≤ t₁ * p) :
    (N₀ + 3) * Real.exp (-(δ ^ 2 * (t₁ * p) / 3)) ≤
      4 * Real.exp (δ ^ 2 / 3) * (6 / (δ ^ 2 * η * lam / 3) ^ 3) / n := by
  set κ := δ ^ 2 * η * lam / 3 with hκ
  have hκpos : 0 < κ := by positivity
  have hnpos : (0 : ℝ) < n := by linarith
  have hE : Real.exp (-(δ ^ 2 * (t₁ * p) / 3)) ≤ Real.exp (δ ^ 2 / 3) * Real.exp (-(κ * n)) := by
    rw [← Real.exp_add, Real.exp_le_exp, hκ]
    have := mul_le_mul_of_nonneg_left ht₁ (sq_nonneg δ)
    nlinarith
  have hpoly := pow_three_mul_exp_neg_le hκpos hnpos.le
  calc (N₀ + 3 : ℝ) * Real.exp (-(δ ^ 2 * (t₁ * p) / 3))
      ≤ (4 * n ^ 2) * (Real.exp (δ ^ 2 / 3) * Real.exp (-(κ * n))) :=
        mul_le_mul (by nlinarith) hE (Real.exp_pos _).le (by positivity)
    _ = 4 * Real.exp (δ ^ 2 / 3) * (n ^ 3 * Real.exp (-(κ * n))) / n := by
        field_simp
    _ ≤ 4 * Real.exp (δ ^ 2 / 3) * (6 / κ ^ 3) / n := by gcongr

/-- The deterministic part of the proof of Theorem 2: on typical answers (`Good`), and under the
inequalities of the paper (`hi`: `|S ∪ U| < n/3` at time `N₀`; `hcontr`: no epoch starts after
`t₁`; `hc`: enough positive answers after `t₁`), the current epoch of the search on `perc ⊤ ω`
lies in a component with at least `c n` vertices. -/
lemma exists_component_of_good {V : Type*} [Fintype V] [DecidableEq V] (e₀ : Sym2 V)
    (ω : Sym2 V → Bool) {N₀ t₁ : ℕ} {p δ c : ℝ} (hn4 : 4 ≤ Fintype.card V)
    (hN₀N : N₀ ≤ (Fintype.card V).choose 2) (ht₁N₀ : t₁ ≤ N₀) (h0 : 0 ≤ p) (hδ0 : 0 < δ)
    (hδ1 : δ < 1)
    (hi : (N₀ : ℝ) <
      (Fintype.card V / 3 - 1 - (1 + δ) * (N₀ * p)) * ((2 * Fintype.card V - 5) / 3))
    (hcontr : 1 < (1 - δ) * p * (Fintype.card V - N₀ * p))
    (hc : c * Fintype.card V ≤ (1 - δ) * (N₀ * p) - (1 + δ) * (t₁ * p))
    (hG : Good p N₀ t₁ δ (queryAnswers (DFS.nextQuery e₀) ω N₀)) :
    ∃ K : (perc ⊤ ω).ConnectedComponent, c * Fintype.card V ≤ K.supp.ncard := by
  set L := queryAnswers (DFS.nextQuery e₀) ω N₀ with hL
  have hLlen : L.length = N₀ := length_queryAnswers _ _ _
  obtain ⟨hG1, hG2, hG3⟩ := hG
  rw [List.take_of_length_le hLlen.le] at hG1
  have hi' : (L.length : ℝ) <
      (Fintype.card V / 3 - 1 - L.count true) * ((2 * Fintype.card V - 5) / 3) := by
    rw [hLlen]
    refine hi.trans_le (mul_le_mul_of_nonneg_right (by linarith) ?_)
    have : (4 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn4
    linarith
  have h3 := DFS.three_mul_explored_lt L (hLlen ▸ hN₀N) hn4 hi'
  have hlow : ∀ t, t₁ ≤ t → t ≤ L.length → (1 - δ) * (t * p) ≤ ((L.take t).count true : ℝ) :=
    fun t h₁ h₂ => hG3 t (mem_Icc.mpr ⟨h₁, hLlen ▸ h₂⟩)
  have hcomp := DFS.le_card_comp L (hLlen ▸ hN₀N) h3 h0 hδ0.le hδ1.le hlow (hLlen ▸ hcontr)
  have hXN : (1 - δ) * (N₀ * p) ≤ (L.count true : ℝ) := by
    have := hG3 N₀ (mem_Icc.mpr ⟨ht₁N₀, le_rfl⟩)
    rwa [List.take_of_length_le hLlen.le] at this
  have hfinal : c * Fintype.card V ≤ (DFS.ofAnswers V L).comp.card := by linarith
  have hV : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨v⟩ := hV
  by_cases hne : (DFS.ofAnswers V L).comp.Nonempty
  · obtain ⟨u, hu⟩ := hne
    refine ⟨(perc ⊤ ω).connectedComponentMk u, ?_⟩
    have := DFS.card_comp_le_ncard e₀ ω N₀ hu
    exact hfinal.trans (by exact_mod_cast this)
  · rw [not_nonempty_iff_eq_empty] at hne
    refine ⟨(perc ⊤ ω).connectedComponentMk v, ?_⟩
    rw [hne, card_empty, Nat.cast_zero] at hfinal
    exact hfinal.trans (Nat.cast_nonneg _)

/-! ### The paper's inequalities, for large `n` -/

/-- `|S ∪ U| < n/3` at time `N₀` (proof of Theorem 1): `N₀ < (n/3 - 1 - (1 + δ) N₀ p)(2n - 5)/3`
when `N₀ ≤ θ n²`, `N₀ p ≤ θ λ n` and `n` is large. -/
lemma ineq_explored {θ δ lam n N₀ q : ℝ} (hδ : 0 ≤ 1 + δ)
    (h2A : 0 < 2 * (1 / 3 - (1 + δ) * lam * θ) - 3 * θ)
    (hnA : (5 * (1 / 3 - (1 + δ) * lam * θ) + 2) / (2 * (1 / 3 - (1 + δ) * lam * θ) - 3 * θ) + 1
      ≤ n)
    (hn4 : 4 ≤ n) (hN₀ : N₀ ≤ θ * n ^ 2) (hq : q ≤ θ * lam * n) :
    N₀ < (n / 3 - 1 - (1 + δ) * q) * ((2 * n - 5) / 3) := by
  set A := 1 / 3 - (1 + δ) * lam * θ with hA
  have hdiv : 5 * A + 2 ≤ (2 * A - 3 * θ) * (n - 1) := by
    have := hnA
    rw [← le_sub_iff_add_le, div_le_iff₀ h2A] at this
    linarith
  have key : θ * n ^ 2 < (A * n - 1) * ((2 * n - 5) / 3) := by nlinarith
  have hfac : (A * n - 1) * ((2 * n - 5) / 3) ≤ (n / 3 - 1 - (1 + δ) * q) * ((2 * n - 5) / 3) := by
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    have := mul_le_mul_of_nonneg_left hq hδ
    have e : A * n = n / 3 - (1 + δ) * (θ * lam * n) := by rw [hA]; ring
    linarith
  linarith

/-- No epoch starts after `t₁` (proof of Theorem 2): `(1 - δ) p (n - N₀ p) > 1`. -/
lemma ineq_contr {θ δ lam n p q : ℝ} (h0 : 0 ≤ p) (hδ1 : δ < 1) (hp : p * n = lam)
    (hq : q ≤ θ * lam * n) (hC2 : 1 < (1 - δ) * lam * (1 - lam * θ)) :
    1 < (1 - δ) * p * (n - q) := by
  have hge : (1 - δ) * p * (n * (1 - lam * θ)) ≤ (1 - δ) * p * (n - q) :=
    mul_le_mul_of_nonneg_left (by nlinarith) (mul_nonneg (by linarith) h0)
  have heq : (1 - δ) * p * (n * (1 - lam * θ)) = (1 - δ) * lam * (1 - lam * θ) := by
    rw [← hp]; ring
  linarith

/-- Enough positive answers after `t₁` (proof of Theorem 2):
`c n ≤ (1 - δ) N₀ p - (1 + δ) t₁ p`. -/
lemma ineq_count {θ η δ lam c n p N₀ t₁ : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (hlam : 1 < lam) (hp : p * n = lam)
    (hβpos : 0 < ((1 - δ) * θ - (1 + δ) * η) * lam - c)
    (hnβ : lam / (((1 - δ) * θ - (1 + δ) * η) * lam - c) + 1 ≤ n)
    (hN₀ : θ * n ^ 2 - 1 ≤ N₀) (ht₁ : t₁ * p ≤ η * lam * n) :
    c * n ≤ (1 - δ) * (N₀ * p) - (1 + δ) * (t₁ * p) := by
  set β := ((1 - δ) * θ - (1 + δ) * η) * lam - c with hβ
  have hβn : lam + β ≤ β * n := by
    have := hnβ
    rw [← le_sub_iff_add_le, div_le_iff₀ hβpos] at this
    have h' : (n - 1) * β = β * n - β := by ring
    linarith
  have e1 : (1 - δ) * ((θ * n ^ 2 - 1) * p) ≤ (1 - δ) * (N₀ * p) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hN₀ h0) (by linarith)
  have e2 : (1 - δ) * ((θ * n ^ 2 - 1) * p) = (1 - δ) * θ * lam * n - (1 - δ) * p := by
    rw [← hp]; ring
  have e3 : (1 + δ) * (t₁ * p) ≤ (1 + δ) * (η * lam * n) :=
    mul_le_mul_of_nonneg_left ht₁ (by linarith)
  have e4 : (1 - δ) * p ≤ lam + β := by
    have : (1 - δ) * p = p - δ * p := by ring
    have : 0 ≤ δ * p := mul_nonneg hδ0.le h0
    linarith
  have e5 : (1 - δ) * θ * lam * n - (1 + δ) * (η * lam * n) = (β + c) * n := by
    rw [hβ]; ring
  have e6 : (β + c) * n = β * n + c * n := by ring
  linarith

/-- **Theorem 2, for general parameters** (Krivelevich–Sudakov, proof of Theorem 2): let
`p n = λ`, `N₀ = ⌊θ n²⌋` queries, the window `t₁ = ⌊η n²⌋` and the relative deviation `δ`, such that
(i) `θ < (2/3) (1/3 - (1 + δ) λ θ)` (so `|S ∪ U| < n/3` at time `N₀`), (ii)
`(1 - δ) λ (1 - λ θ) > 1` (so no epoch starts in `[t₁, N₀]`), and `c < ((1 - δ) θ - (1 + δ) η) λ`
(the positive answers in `[t₁, N₀]`). Then `G(n, p)` has a component with at least `c n` vertices
with probability at least `1 - C / n`. -/
theorem core_component {lam θ η δ c : ℝ} (hlam : 1 < lam) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hη : 0 < η) (hηθ : η ≤ θ) (hθ : θ ≤ 1 / 4)
    (hC1 : θ < 2 / 3 * (1 / 3 - (1 + δ) * lam * θ))
    (hC2 : 1 < (1 - δ) * lam * (1 - lam * θ))
    (hc : c < ((1 - δ) * θ - (1 + δ) * η) * lam) :
    ∃ C : ℝ, ∀ (V : Type*) [Fintype V] [DecidableEq V] (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1),
      p * Fintype.card V = lam →
      1 - C / Fintype.card V ≤ (coins (V := V) p h0 h1).prob fun ω =>
        ∃ K : (perc ⊤ ω).ConnectedComponent, c * Fintype.card V ≤ K.supp.ncard := by
  set A := 1 / 3 - (1 + δ) * lam * θ with hA
  set β := ((1 - δ) * θ - (1 + δ) * η) * lam - c with hβ
  have hβpos : 0 < β := by rw [hβ]; linarith
  have hθpos : 0 < θ := lt_of_lt_of_le hη hηθ
  have h2A : 0 < 2 * A - 3 * θ := by linarith
  set n₁ : ℝ := max (max 4 ((5 * A + 2) / (2 * A - 3 * θ) + 1)) (lam / β + 1) with hn₁
  set Cp : ℝ := 4 * Real.exp (δ ^ 2 / 3) * (6 / (δ ^ 2 * η * lam / 3) ^ 3) with hCp
  refine ⟨max n₁ Cp, fun V _ _ p h0 h1 hp => ?_⟩
  have hnpos : (0 : ℝ) < Fintype.card V := by
    rcases Nat.eq_zero_or_pos (Fintype.card V) with h | h
    · rw [h, Nat.cast_zero, mul_zero] at hp; linarith
    · exact_mod_cast h
  rcases lt_or_ge (Fintype.card V : ℝ) n₁ with hsmall | hlarge
  · have : 1 ≤ max n₁ Cp / Fintype.card V := by
      rw [le_div_iff₀ hnpos, one_mul]
      exact le_trans hsmall.le (le_max_left _ _)
    exact le_trans (by linarith) (Distribution.prob_nonneg _ _)
  generalize hn : (Fintype.card V : ℝ) = n at hp hnpos hlarge ⊢
  have hn4 : (4 : ℝ) ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hlarge
  have hnA : (5 * A + 2) / (2 * A - 3 * θ) + 1 ≤ n :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hlarge
  have hnβ : lam / β + 1 ≤ n := le_trans (le_max_right _ _) hlarge
  have hn4' : 4 ≤ Fintype.card V := by exact_mod_cast hn ▸ hn4
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨v⟩ := ‹Nonempty V›
  obtain ⟨N₀, t₁, hN₀le, hN₀ge, ht₁le, ht₁ge, ht₁N₀⟩ : ∃ N₀ t₁ : ℕ, (N₀ : ℝ) ≤ θ * n ^ 2 ∧
      θ * n ^ 2 - 1 < N₀ ∧ (t₁ : ℝ) ≤ η * n ^ 2 ∧ η * n ^ 2 - 1 < t₁ ∧ t₁ ≤ N₀ :=
    ⟨⌊θ * n ^ 2⌋₊, ⌊η * n ^ 2⌋₊, Nat.floor_le (by positivity),
      by linarith [Nat.lt_floor_add_one (θ * n ^ 2)], Nat.floor_le (by positivity),
      by linarith [Nat.lt_floor_add_one (η * n ^ 2)],
      Nat.floor_mono (mul_le_mul_of_nonneg_right hηθ (sq_nonneg _))⟩
  have hN₀N : N₀ ≤ (Fintype.card V).choose 2 := by
    have : (N₀ : ℝ) ≤ (((Fintype.card V).choose 2 : ℕ) : ℝ) := by
      rw [Nat.cast_choose_two, hn]; nlinarith
    exact_mod_cast this
  have hN₀p : (N₀ : ℝ) * p ≤ θ * lam * n := by
    calc (N₀ : ℝ) * p ≤ θ * n ^ 2 * p := mul_le_mul_of_nonneg_right hN₀le h0
      _ = θ * lam * n := by rw [← hp]; ring
  have ht₁p : (t₁ : ℝ) * p ≤ η * lam * n := by
    calc (t₁ : ℝ) * p ≤ η * n ^ 2 * p := mul_le_mul_of_nonneg_right ht₁le h0
      _ = η * lam * n := by rw [← hp]; ring
  set e₀ : Sym2 V := s(v, v)
  have hfresh : FreshUpTo (DFS.nextQuery e₀) N₀ := (DFS.fresh_nextQuery e₀).mono hN₀N
  apply one_sub_le_prob (coins p h0 h1)
    (B := fun ω => Good p N₀ t₁ δ (queryAnswers (DFS.nextQuery e₀) ω N₀))
  · intro ω hG
    rw [← hn]
    refine exists_component_of_good e₀ ω hn4' hN₀N ht₁N₀ h0 hδ0 hδ1 ?_ ?_ ?_ hG
    · rw [hn]
      exact ineq_explored (by linarith) h2A hnA hn4 hN₀le hN₀p
    · rw [hn]
      exact ineq_contr h0 hδ1 hp hN₀p hC2
    · rw [hn]
      exact ineq_count h0 h1 hδ0 hδ1 hlam hp hβpos hnβ hN₀ge.le ht₁p
  · -- the answers are typical with high probability
    have hdd := prob_queryAnswers p h0 h1 (DFS.nextQuery e₀) hfresh
      (fun L => ¬Good p N₀ t₁ δ L)
    rw [coins_eq_independent]
    refine (le_of_eq hdd).trans ((prob_not_good_le p h0 h1 ht₁N₀ hδ0 hδ1).trans ?_)
    refine (tail_le_div (n := Fintype.card V) (N₀ := N₀) (t₁ := t₁) (p := p) (lam := lam)
      (by rw [hn]; linarith) hη (by linarith) hδ0 (by rw [hn]; nlinarith) ?_).trans ?_
    · have := mul_le_mul_of_nonneg_right ht₁ge.le h0
      have e : (η * n ^ 2 - 1) * p = η * lam * n - p := by rw [← hp]; ring
      rw [hn]
      linarith
    · rw [hn]
      exact div_le_div_of_nonneg_right (le_max_right _ _) hnpos.le

/-- `(1 - δ) N₀ p ≥ (1 - δ) θ λ n - 1` when `N₀ ≥ θ n² - 1`, `p n = λ`, `p ≤ 1`. -/
lemma ineq_mean_lo {θ δ lam n p N₀ : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hp : p * n = lam) (hN₀ : θ * n ^ 2 - 1 ≤ N₀) :
    (1 - δ) * θ * lam * n - 1 ≤ (1 - δ) * (N₀ * p) := by
  have e1 : (1 - δ) * ((θ * n ^ 2 - 1) * p) ≤ (1 - δ) * (N₀ * p) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hN₀ h0) (by linarith)
  have e2 : (1 - δ) * ((θ * n ^ 2 - 1) * p) = (1 - δ) * θ * lam * n - (1 - δ) * p := by
    rw [← hp]; ring
  have e3 : (1 - δ) * p ≤ 1 := by
    have : (1 - δ) * p = p - δ * p := by ring
    have : 0 ≤ δ * p := mul_nonneg hδ0.le h0
    linarith
  linarith

/-- The stack bound `ℓ n + 1 ≤ (1 - δ) N₀ p` (proof of Theorem 1), for large `n`. -/
lemma ineq_path_lo {θ δ lam ℓ n Xlo : ℝ} (hα : 0 < (1 - δ) * lam * θ - ℓ)
    (hn : 2 / ((1 - δ) * lam * θ - ℓ) + 1 ≤ n) (hX : (1 - δ) * θ * lam * n - 1 ≤ Xlo) :
    ℓ * n + 1 ≤ Xlo := by
  have := hn
  rw [← le_sub_iff_add_le, div_le_iff₀ hα] at this
  have e : ((1 - δ) * lam * θ - ℓ) * n = (1 - δ) * θ * lam * n - ℓ * n := by ring
  nlinarith

/-- `N₀ < (Xlo - (ℓ n + 1)) (n - Xlo)` (proof of Theorem 1), for large `n`. -/
lemma ineq_path_one {θ δ lam ℓ n N₀ Xlo : ℝ} (hn0 : 0 < n) (hN₀ : N₀ ≤ θ * n ^ 2)
    (hα : 0 < (1 - δ) * lam * θ - ℓ) (hγ : 0 < 1 - (1 - δ) * lam * θ)
    (hC3 : θ < ((1 - δ) * lam * θ - ℓ) * (1 - (1 - δ) * lam * θ))
    (hn : 2 * (1 - (1 - δ) * lam * θ) /
      (((1 - δ) * lam * θ - ℓ) * (1 - (1 - δ) * lam * θ) - θ) + 1 ≤ n)
    (hn2 : 2 / ((1 - δ) * lam * θ - ℓ) + 1 ≤ n)
    (hXlo : (1 - δ) * θ * lam * n - 1 ≤ Xlo) (hXhi : Xlo ≤ (1 - δ) * θ * lam * n) :
    N₀ < (Xlo - (ℓ * n + 1)) * (n - Xlo) := by
  set α := (1 - δ) * lam * θ - ℓ with hαd
  set γ := 1 - (1 - δ) * lam * θ with hγd
  have hκ : 0 < α * γ - θ := by linarith
  have h1 : 2 * γ ≤ (α * γ - θ) * (n - 1) := by
    have := hn
    rw [← le_sub_iff_add_le, div_le_iff₀ hκ] at this
    linarith
  have h2 : 2 ≤ α * (n - 1) := by
    have := hn2
    rw [← le_sub_iff_add_le, div_le_iff₀ hα] at this
    linarith
  have hA : α * n - 2 ≤ Xlo - (ℓ * n + 1) := by
    have e : α * n = (1 - δ) * θ * lam * n - ℓ * n := by rw [hαd]; ring
    linarith
  have hB : γ * n ≤ n - Xlo := by
    have e : γ * n = n - (1 - δ) * θ * lam * n := by rw [hγd]; ring
    linarith
  have hA0 : 0 ≤ α * n - 2 := by nlinarith
  have hprod : (α * n - 2) * (γ * n) ≤ (Xlo - (ℓ * n + 1)) * (n - Xlo) :=
    mul_le_mul hA hB (by positivity) (by linarith)
  have key : θ * n ^ 2 < (α * n - 2) * (γ * n) := by nlinarith
  linarith

/-- `N₀ < (n/3 - (ℓ n + 1)) (2n/3)` (proof of Theorem 1), for large `n`. -/
lemma ineq_path_two {θ ℓ n N₀ : ℝ} (hn0 : 0 < n) (hN₀ : N₀ ≤ θ * n ^ 2)
    (hC4 : θ < 2 / 3 * (1 / 3 - ℓ)) (hn : 2 / 3 / (2 / 3 * (1 / 3 - ℓ) - θ) + 1 ≤ n) :
    N₀ < (n / 3 - (ℓ * n + 1)) * (2 * n / 3) := by
  have hκ : 0 < 2 / 3 * (1 / 3 - ℓ) - θ := by linarith
  have h1 : 2 / 3 ≤ (2 / 3 * (1 / 3 - ℓ) - θ) * (n - 1) := by
    have := hn
    rw [← le_sub_iff_add_le, div_le_iff₀ hκ] at this
    linarith
  have key : θ * n ^ 2 < (n / 3 - (ℓ * n + 1)) * (2 * n / 3) := by nlinarith
  linarith

/-- The deterministic part of the proof of Theorem 1, part 2: on typical answers, and under the
inequalities of the paper, the stack of the search on `perc ⊤ ω` at time `N₀` is a path with at
least `ℓ n` edges. -/
lemma exists_path_of_typical {V : Type*} [Fintype V] [DecidableEq V] (e₀ : Sym2 V)
    (ω : Sym2 V → Bool) {N₀ : ℕ} {p δ ℓ : ℝ} (hn4 : 4 ≤ Fintype.card V)
    (hN₀N : N₀ ≤ (Fintype.card V).choose 2) (hℓ : 0 ≤ ℓ)
    (hi : (N₀ : ℝ) <
      (Fintype.card V / 3 - 1 - (1 + δ) * (N₀ * p)) * ((2 * Fintype.card V - 5) / 3))
    (hL : ℓ * Fintype.card V + 1 ≤ (1 - δ) * (N₀ * p))
    (h1 : (N₀ : ℝ) < ((1 - δ) * (N₀ * p) - (ℓ * Fintype.card V + 1)) *
      (Fintype.card V - (1 - δ) * (N₀ * p)))
    (h2 : (N₀ : ℝ) < (Fintype.card V / 3 - (ℓ * Fintype.card V + 1)) *
      (2 * Fintype.card V / 3))
    (hG : (1 - δ) * (N₀ * p) ≤ (((queryAnswers (DFS.nextQuery e₀) ω N₀).take N₀).count true : ℝ) ∧
      (((queryAnswers (DFS.nextQuery e₀) ω N₀).take N₀).count true : ℝ) ≤ (1 + δ) * (N₀ * p)) :
    ∃ (u v : V) (q : (perc ⊤ ω).Walk u v), q.IsPath ∧ ℓ * Fintype.card V ≤ q.length := by
  set L := queryAnswers (DFS.nextQuery e₀) ω N₀ with hL'
  have hLlen : L.length = N₀ := length_queryAnswers _ _ _
  obtain ⟨hlo, hhi⟩ := hG
  rw [List.take_of_length_le hLlen.le] at hlo hhi
  have hi' : (L.length : ℝ) <
      (Fintype.card V / 3 - 1 - L.count true) * ((2 * Fintype.card V - 5) / 3) := by
    rw [hLlen]
    refine hi.trans_le (mul_le_mul_of_nonneg_right (by linarith) ?_)
    have : (4 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn4
    linarith
  have h3 := DFS.three_mul_explored_lt L (hLlen ▸ hN₀N) hn4 hi'
  have hU := DFS.le_length_stack L (hLlen ▸ hN₀N) h3 hlo hL (hLlen ▸ h1) (hLlen ▸ h2)
  have hne : (DFS.ofAnswers V L).stack ≠ [] := by
    intro h
    rw [h, List.length_nil, Nat.cast_zero] at hU
    have : 0 ≤ ℓ * Fintype.card V := mul_nonneg hℓ (Nat.cast_nonneg _)
    linarith
  obtain ⟨u, v, q, hq, hlen⟩ := DFS.exists_path_of_stack e₀ ω N₀ hne
  refine ⟨u, v, q, hq, ?_⟩
  have : ((DFS.ofAnswers V L).stack.length : ℝ) = q.length + 1 := by exact_mod_cast hlen.symm
  linarith

/-- **Theorem 1, part 2, for general parameters** (Krivelevich–Sudakov, proof of Theorem 1): let
`p n = λ`, `N₀ = ⌊θ n²⌋` queries and the relative deviation `δ` such that (i)
`θ < (2/3)(1/3 - (1 + δ) λ θ)` (so `|S ∪ U| < n/3` at time `N₀`), and (ii)
`θ < ((1 - δ) λ θ - ℓ)(1 - (1 - δ) λ θ)`, `θ < (2/3)(1/3 - ℓ)` (so `|U| > ℓ n` at time `N₀`).
Then `G(n, p)` has a path with at least `ℓ n` edges with probability at least `1 - C / n`. -/
theorem core_path {lam θ δ ℓ : ℝ} (hlam : 0 < lam) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hθ0 : 0 < θ)
    (hθ : θ ≤ 1 / 4) (hℓ : 0 ≤ ℓ)
    (hC1 : θ < 2 / 3 * (1 / 3 - (1 + δ) * lam * θ))
    (hC3 : θ < ((1 - δ) * lam * θ - ℓ) * (1 - (1 - δ) * lam * θ))
    (hC4 : θ < 2 / 3 * (1 / 3 - ℓ)) :
    ∃ C : ℝ, ∀ (V : Type*) [Fintype V] [DecidableEq V] (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1),
      p * Fintype.card V = lam →
      1 - C / Fintype.card V ≤ (coins p h0 h1).prob fun ω =>
        ∃ (u v : V) (q : (perc ⊤ ω).Walk u v), q.IsPath ∧ ℓ * Fintype.card V ≤ q.length := by
  set A := 1 / 3 - (1 + δ) * lam * θ with hA
  set α := (1 - δ) * lam * θ - ℓ with hαd
  set γ := 1 - (1 - δ) * lam * θ with hγd
  have h2A : 0 < 2 * A - 3 * θ := by linarith
  have hγ : 0 < γ := by
    have : (1 - δ) * lam * θ ≤ (1 + δ) * lam * θ := by
      have := mul_pos hlam hθ0
      nlinarith
    rw [hγd]; linarith
  have hα : 0 < α := by
    by_contra h
    push Not at h
    have : α * γ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hγ.le
    linarith
  have hκ1 : 0 < α * γ - θ := by linarith
  have hκ2 : 0 < 2 / 3 * (1 / 3 - ℓ) - θ := by linarith
  set n₁ : ℝ := max (max (max 4 ((5 * A + 2) / (2 * A - 3 * θ) + 1)) (2 / α + 1))
    (max (2 * γ / (α * γ - θ) + 1) (2 / 3 / (2 / 3 * (1 / 3 - ℓ) - θ) + 1)) with hn₁
  set Cp : ℝ := 4 * Real.exp (δ ^ 2 / 3) * (6 / (δ ^ 2 * θ * lam / 3) ^ 3) with hCp
  refine ⟨max n₁ Cp, fun V _ _ p h0 h1 hp => ?_⟩
  have hnpos : (0 : ℝ) < Fintype.card V := by
    rcases Nat.eq_zero_or_pos (Fintype.card V) with h | h
    · rw [h, Nat.cast_zero, mul_zero] at hp; linarith
    · exact_mod_cast h
  rcases lt_or_ge (Fintype.card V : ℝ) n₁ with hsmall | hlarge
  · have : 1 ≤ max n₁ Cp / Fintype.card V := by
      rw [le_div_iff₀ hnpos, one_mul]
      exact le_trans hsmall.le (le_max_left _ _)
    exact le_trans (by linarith) (Distribution.prob_nonneg _ _)
  generalize hn : (Fintype.card V : ℝ) = n at hp hnpos hlarge ⊢
  have hn4 : (4 : ℝ) ≤ n :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) hlarge
  have hnA : (5 * A + 2) / (2 * A - 3 * θ) + 1 ≤ n :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) hlarge
  have hnα : 2 / α + 1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hlarge
  have hnκ1 : 2 * γ / (α * γ - θ) + 1 ≤ n :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hlarge
  have hnκ2 : 2 / 3 / (2 / 3 * (1 / 3 - ℓ) - θ) + 1 ≤ n :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hlarge
  have hn4' : 4 ≤ Fintype.card V := by exact_mod_cast hn ▸ hn4
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨v⟩ := ‹Nonempty V›
  obtain ⟨N₀, hN₀le, hN₀ge⟩ : ∃ N₀ : ℕ, (N₀ : ℝ) ≤ θ * n ^ 2 ∧ θ * n ^ 2 - 1 < N₀ :=
    ⟨⌊θ * n ^ 2⌋₊, Nat.floor_le (by positivity), by linarith [Nat.lt_floor_add_one (θ * n ^ 2)]⟩
  have hN₀N : N₀ ≤ (Fintype.card V).choose 2 := by
    have : (N₀ : ℝ) ≤ (((Fintype.card V).choose 2 : ℕ) : ℝ) := by
      rw [Nat.cast_choose_two, hn]; nlinarith
    exact_mod_cast this
  have hN₀p : (N₀ : ℝ) * p ≤ θ * lam * n := by
    calc (N₀ : ℝ) * p ≤ θ * n ^ 2 * p := mul_le_mul_of_nonneg_right hN₀le h0
      _ = θ * lam * n := by rw [← hp]; ring
  have hXlo := ineq_mean_lo h0 h1 hδ0 hδ1 hp hN₀ge.le
  have hXhi : (1 - δ) * (N₀ * p) ≤ (1 - δ) * θ * lam * n := by
    have := mul_le_mul_of_nonneg_left hN₀p (by linarith : (0 : ℝ) ≤ 1 - δ)
    linarith
  set e₀ : Sym2 V := s(v, v)
  have hfresh : FreshUpTo (DFS.nextQuery e₀) N₀ := (DFS.fresh_nextQuery e₀).mono hN₀N
  apply one_sub_le_prob (coins p h0 h1) (B := fun ω =>
    (1 - δ) * (N₀ * p) ≤ (((queryAnswers (DFS.nextQuery e₀) ω N₀).take N₀).count true : ℝ) ∧
      (((queryAnswers (DFS.nextQuery e₀) ω N₀).take N₀).count true : ℝ) ≤ (1 + δ) * (N₀ * p))
  · intro ω hG
    rw [← hn]
    refine exists_path_of_typical e₀ ω hn4' hN₀N hℓ ?_ ?_ ?_ ?_ hG
    · rw [hn]; exact ineq_explored (by linarith) h2A hnA hn4 hN₀le hN₀p
    · rw [hn]; exact ineq_path_lo hα hnα hXlo
    · rw [hn]; exact ineq_path_one hnpos hN₀le hα hγ hC3 hnκ1 hnα hXlo hXhi
    · rw [hn]; exact ineq_path_two hnpos hN₀le hC4 hnκ2
  · have hdd := prob_queryAnswers p h0 h1 (DFS.nextQuery e₀) hfresh (fun L =>
      ¬((1 - δ) * (N₀ * p) ≤ ((L.take N₀).count true : ℝ) ∧
        ((L.take N₀).count true : ℝ) ≤ (1 + δ) * (N₀ * p)))
    rw [coins_eq_independent]
    refine (le_of_eq hdd).trans ?_
    refine (Distribution.prob_mono _ fun x hx => ?_).trans
      ((prob_count_take_far p h0 h1 le_rfl hδ0 hδ1).trans ?_)
    · rw [not_and_or] at hx
      rcases hx with hx | hx
      · rw [le_abs']; left; linarith
      · rw [le_abs']; right; linarith
    · have hN₀p' : θ * lam * n - 1 ≤ N₀ * p := by
        have := mul_le_mul_of_nonneg_right hN₀ge.le h0
        have e : (θ * n ^ 2 - 1) * p = θ * lam * n - p := by rw [← hp]; ring
        linarith
      have := tail_le_div (n := Fintype.card V) (N₀ := 0) (t₁ := N₀) (p := p) (lam := lam)
        (δ := δ) (η := θ) (by rw [hn]; linarith) hθ0 hlam hδ0 (by push_cast; positivity)
        (by rw [hn]; exact hN₀p')
      rw [hn] at this
      have hE : 0 ≤ Real.exp (-(δ ^ 2 * (N₀ * p) / 3)) := (Real.exp_pos _).le
      calc 2 * Real.exp (-(δ ^ 2 * (N₀ * p) / 3))
          ≤ ((0 : ℕ) + 3) * Real.exp (-(δ ^ 2 * (N₀ * p) / 3)) := by push_cast; linarith
        _ ≤ Cp / n := this
        _ ≤ max n₁ Cp / n := div_le_div_of_nonneg_right (le_max_right _ _) hnpos.le

/-- **Long path** (Krivelevich–Sudakov, Theorem 1, part 2; Ajtai, Komlós and Szemerédi): for every
small enough `ε > 0` there is `C` such that, for `p = (1 + ε) / n`, the random graph `G(n, p)`
(bond percolation `perc ⊤ ω` on the complete graph on `n` vertices, with i.i.d. Bernoulli(`p`)
edge coins `ω`) contains a path of length (number of edges) at least `ε² n / 5` with probability
at least `1 - C / n`. -/
theorem exists_long_path :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ C : ℝ,
      ∀ (V : Type*) [Fintype V] [DecidableEq V] (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1),
        p * Fintype.card V = 1 + ε →
        1 - C / Fintype.card V ≤ (coins p h0 h1).prob fun ω =>
          ∃ (u v : V) (q : (perc ⊤ ω).Walk u v), q.IsPath ∧
            ε ^ 2 * Fintype.card V / 5 ≤ q.length := by
  refine ⟨1 / 100, by norm_num, fun ε hε hε₀ => ?_⟩
  have hε2 : ε ^ 2 ≤ 1 / 10000 := by nlinarith
  have hC1 : ε / 2 < 2 / 3 * (1 / 3 - (1 + ε / 20) * (1 + ε) * (ε / 2)) := by nlinarith
  have hC3 : ε / 2 < ((1 - ε / 20) * (1 + ε) * (ε / 2) - ε ^ 2 / 5) *
      (1 - (1 - ε / 20) * (1 + ε) * (ε / 2)) := by
    have key : ((1 - ε / 20) * (1 + ε) * (ε / 2) - ε ^ 2 / 5) *
        (1 - (1 - ε / 20) * (1 + ε) * (ε / 2)) - ε / 2 =
        ε ^ 2 * (1 / 40 - 2 / 5 * ε - 169 / 1600 * ε ^ 2 + 3 / 160 * ε ^ 3 - ε ^ 4 / 1600) := by
      ring
    have hpos : 0 < 1 / 40 - 2 / 5 * ε - 169 / 1600 * ε ^ 2 + 3 / 160 * ε ^ 3 - ε ^ 4 / 1600 := by
      have : ε ^ 4 ≤ 1 := by nlinarith
      have : 0 ≤ ε ^ 3 := by positivity
      linarith
    have := mul_pos (pow_pos hε 2) hpos
    linarith
  have hC4 : ε / 2 < 2 / 3 * (1 / 3 - ε ^ 2 / 5) := by nlinarith
  obtain ⟨C, hC⟩ := core_path (lam := 1 + ε) (θ := ε / 2) (δ := ε / 20) (ℓ := ε ^ 2 / 5)
    (by linarith) (by positivity) (by linarith) (by positivity) (by linarith) (by positivity)
    hC1 hC3 hC4
  refine ⟨C, fun V _ _ p h0 h1 hp =>
    (hC V p h0 h1 hp).trans (Distribution.prob_mono _ fun ω hω => ?_)⟩
  obtain ⟨u, v, q, hq, hl⟩ := hω
  refine ⟨u, v, q, hq, ?_⟩
  have e : ε ^ 2 * (Fintype.card V : ℝ) / 5 = ε ^ 2 / 5 * Fintype.card V := by ring
  rw [e]
  exact hl

/-- **Giant component** (Krivelevich–Sudakov, Theorem 2): for every small enough `ε > 0` there is
`C` such that, for `p = (1 + ε) / n`, the random graph `G(n, p)` (bond percolation `perc ⊤ ω` on
the complete graph on `n` vertices) has a connected component with at least `ε n / 2` vertices with
probability at least `1 - C / n`. -/
theorem exists_giant_component :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ C : ℝ,
      ∀ (V : Type*) [Fintype V] [DecidableEq V] (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1),
        p * Fintype.card V = 1 + ε →
        1 - C / Fintype.card V ≤ (coins (V := V) p h0 h1).prob fun ω =>
          ∃ K : (perc ⊤ ω).ConnectedComponent, ε * Fintype.card V / 2 ≤ K.supp.ncard := by
  refine ⟨1 / 10, by norm_num, fun ε hε hε₀ => ?_⟩
  have hC1 : ε / 2 < 2 / 3 * (1 / 3 - (1 + ε / 10) * (1 + ε) * (ε / 2)) := by
    have h1 : (1 + ε / 10) * (1 + ε) ≤ 4 := by nlinarith
    have hb : (1 + ε / 10) * (1 + ε) * (ε / 2) ≤ 4 * (ε / 2) :=
      mul_le_mul_of_nonneg_right h1 (by linarith)
    linarith
  have hC2 : 1 < (1 - ε / 10) * (1 + ε) * (1 - (1 + ε) * (ε / 2)) := by
    have key : (1 - ε / 10) * (1 + ε) * (1 - (1 + ε) * (ε / 2)) - 1 =
        ε * (2 / 5 - 21 / 20 * ε - 2 / 5 * ε ^ 2 + ε ^ 3 / 20) := by ring
    have hpos : 0 < 2 / 5 - 21 / 20 * ε - 2 / 5 * ε ^ 2 + ε ^ 3 / 20 := by
      have : ε ^ 2 ≤ 1 / 100 := by nlinarith
      have : 0 ≤ ε ^ 3 := by positivity
      linarith
    have := mul_pos hε hpos
    linarith
  have hc : ε / 2 < ((1 - ε / 10) * (ε / 2) - (1 + ε / 10) * (ε ^ 2 / 10)) * (1 + ε) := by
    have key : ((1 - ε / 10) * (ε / 2) - (1 + ε / 10) * (ε ^ 2 / 10)) * (1 + ε) - ε / 2 =
        ε ^ 2 * (7 / 20 - 4 / 25 * ε - ε ^ 2 / 100) := by ring
    have hpos : 0 < 7 / 20 - 4 / 25 * ε - ε ^ 2 / 100 := by nlinarith
    have := mul_pos (pow_pos hε 2) hpos
    linarith
  obtain ⟨C, hC⟩ := core_component (lam := 1 + ε) (θ := ε / 2) (η := ε ^ 2 / 10) (δ := ε / 10)
    (c := ε / 2) (by linarith) (by positivity) (by linarith) (by positivity) (by nlinarith)
    (by linarith) hC1 hC2 hc
  refine ⟨C, fun V _ _ p h0 h1 hp =>
    (hC V p h0 h1 hp).trans (Distribution.prob_mono _ fun ω hω => ?_)⟩
  obtain ⟨K, hK⟩ := hω
  refine ⟨K, ?_⟩
  have e : ε * (Fintype.card V : ℝ) / 2 = ε / 2 * Fintype.card V := by ring
  rw [e]
  exact hK

/-- **Supercritical phase** (Erdős and Rényi, as stated in the abstract of Krivelevich–Sudakov):
for every `ε > 0` there are `c > 0` and `C` such that, for `p = (1 + ε) / n`, the random graph
`G(n, p)` has a connected component with at least `c n` vertices with probability at least
`1 - C / n`. -/
theorem exists_linear_component (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ,
      ∀ (V : Type*) [Fintype V] [DecidableEq V] (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1),
        p * Fintype.card V = 1 + ε →
        1 - C / Fintype.card V ≤ (coins (V := V) p h0 h1).prob fun ω =>
          ∃ K : (perc ⊤ ω).ConnectedComponent, c * Fintype.card V ≤ K.supp.ncard := by
  -- parameters: `λ = u = 1 + ε`, `δ = ε / (2u)`, `θ = ε / (10 u²)`, `η = θ / 4`
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 1 + ε := ⟨_, rfl⟩
  have hu1 : 1 < u := by linarith
  have hu0 : 0 < u := by linarith
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = ε / (2 * u) := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = ε / (10 * u ^ 2) := ⟨_, rfl⟩
  have hd' : d * u = ε / 2 := by rw [hd]; field_simp
  have ht' : t * (10 * u ^ 2) = ε := by rw [ht]; field_simp
  have hd0 : 0 < d := by rw [hd]; positivity
  have hd1 : d < 1 / 2 := by
    rw [hd, div_lt_iff₀ (by positivity)]
    linarith
  have ht0 : 0 < t := by rw [ht]; positivity
  have hθ : t ≤ 1 / 4 := by
    rw [ht, div_le_iff₀ (by positivity)]
    nlinarith
  have hC1 : t < 2 / 3 * (1 / 3 - (1 + d) * u * t) := by
    have h1 : (1 + d) * u * t = u * t + ε / 2 * t := by rw [← hd']; ring
    have h2 : t * (5 / 3 + ε) ≤ 1 / 10 := by
      have h3 : t * (5 / 3 + ε) * (10 * u ^ 2) ≤ 1 / 10 * (10 * u ^ 2) := by
        have : t * (5 / 3 + ε) * (10 * u ^ 2) = ε * (5 / 3 + ε) := by rw [← ht']; ring
        rw [this, hu]
        nlinarith
      exact le_of_mul_le_mul_right h3 (by positivity)
    have e1 : u * t = t + ε * t := by rw [hu]; ring
    have e2 : t * (5 / 3 + ε) = 5 / 3 * t + ε * t := by ring
    rw [h1]
    linarith
  have hC2 : 1 < (1 - d) * u * (1 - u * t) := by
    have hw : u * t * (10 * u) = ε := by rw [← ht']; ring
    have hw' : u * t * (1 + ε / 2) < ε / 2 := by
      have h3 : u * t * (1 + ε / 2) * (10 * u) < ε / 2 * (10 * u) := by
        have : u * t * (1 + ε / 2) * (10 * u) = ε * (1 + ε / 2) := by rw [← hw]; ring
        rw [this, hu]
        nlinarith
      exact lt_of_mul_lt_mul_right h3 (by positivity)
    have e1 : (1 - d) * u = 1 + ε / 2 := by
      have : (1 - d) * u = u - d * u := by ring
      rw [this, hd', hu]; ring
    rw [e1]
    nlinarith
  have hβ : 0 < (1 - d) * t - (1 + d) * (t / 4) := by
    have : (1 - d) * t - (1 + d) * (t / 4) = t * (3 / 4 - 5 / 4 * d) := by ring
    rw [this]
    exact mul_pos ht0 (by linarith)
  set c := ((1 - d) * t - (1 + d) * (t / 4)) * u / 2 with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have hcc : c < ((1 - d) * t - (1 + d) * (t / 4)) * u := by
    rw [hc]
    have := mul_pos hβ hu0
    linarith
  obtain ⟨C, hC⟩ := core_component (lam := u) (θ := t) (η := t / 4) (δ := d) (c := c) hu1 hd0
    (by linarith) (by positivity) (by linarith) hθ hC1 hC2 hcc
  exact ⟨c, hcpos, C, fun V _ _ p h0 h1 hp => hC V p h0 h1 (hp.trans hu.symm)⟩

end Epidemics
