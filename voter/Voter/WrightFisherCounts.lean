import Dynamics.Binomial
import Voter.WrightFisher

/-! # Wright–Fisher on allele counts

Population genetics follows the number `X_t` of copies of an allele in a haploid population of
constant size `n` with non-overlapping generations: every individual of the next generation
picks its parent independently and uniformly at random in the current generation, so
`X_{t+1} ~ Bin(n, X_t / n)`. `wfCountKernel n` is this chain on `{0, …, n}`, defined from the
binomial law alone.

The synchronous voter model on the complete graph with self-loops (`transition (wfKernel V)`:
every vertex copies the colour of a uniformly random vertex, itself included) lumps to it under
the number of vertices of colour `a`, for any set of colours (`transition_wfKernel_lumps`): the
two processes are the same chain on counts (row `wright-fisher` of the cross-field dictionary).
Results transfer through the lumping: the voter's consensus probability `wrightFisher_fixation`
gives the fixation probability `x / n` of the count chain for `n ≥ 1` (`wfCountKernel_fixation`).
-/

namespace Voter
open Dynamics Finset

/-- **Wright–Fisher on allele counts.** In a population of `n` individuals, from `x` copies of an
allele the next generation has `Bin(n, x/n)` copies. -/
noncomputable def wfCountKernel (n : ℕ) : Kernel (Fin (n + 1)) := fun x =>
  Distribution.binomial n ((x : ℝ) / n) (by positivity)
    (div_le_one_of_le₀ (by exact_mod_cast Fin.is_le x) (Nat.cast_nonneg n))

/-- The Wright–Fisher transition probabilities: from `x` copies to `y` copies with probability
`C(n, y) (x/n)^y (1 - x/n)^(n - y)`. -/
theorem wfCountKernel_weight (n : ℕ) (x y : Fin (n + 1)) :
    (wfCountKernel n x).weight y =
      n.choose y * ((x : ℝ) / n) ^ (y : ℕ) * (1 - (x : ℝ) / n) ^ (n - y) := rfl

variable {V C : Type*} [Fintype V] [DecidableEq V]

/-- The number of vertices of colour `a`, in `{0, …, |V|}`. -/
def colorCount [DecidableEq C] (a : C) (s : Config V C) : Fin (Fintype.card V + 1) :=
  countFin fun v => s v = a

/-- **The synchronous voter model on `K_n` with self-loops is Wright–Fisher on counts.** Under
Wright–Fisher sampling (`wfKernel V`: every vertex copies the colour of a uniformly random vertex,
itself included), the number of vertices of colour `a` is the Wright–Fisher chain on
`{0, …, |V|}`: one round from a configuration with `x` vertices of colour `a` leads to
`Bin(|V|, x/|V|)` such vertices. -/
theorem transition_wfKernel_lumps [Nonempty V] [Fintype C] [DecidableEq C] (a : C) :
    Kernel.Lumps (colorCount a) (transition (wfKernel V) : Kernel (Config V C))
      (wfCountKernel (Fintype.card V)) := by
  intro s
  have hq : (Distribution.uniform V).prob (fun j => s j = a) =
      (colorCount a s : ℝ) / Fintype.card V := by
    rw [uniform_prob_eq_card]
    rfl
  calc (transition (wfKernel V) s).map (colorCount a)
      = ((Distribution.independent (wfKernel V)).map fun r v => decide (s (r v) = a)).map
          fun ω => countFin fun v => ω v = true := by
        rw [transition, Distribution.map_map, Distribution.map_map]
        congr 1
        funext r
        exact Fin.ext (by simp only [colorCount, countFin_val, step, decide_eq_true_eq]; congr)
    _ = (Distribution.independent fun _ : V => Distribution.bernoulli _
          ((Distribution.uniform V).prob_nonneg fun j => s j = a)
          ((Distribution.uniform V).prob_le_one fun j => s j = a)).map
          fun ω => countFin fun v => ω v = true := by
        rw [Distribution.independent_map_pi (wfKernel V) fun _ j => decide (s j = a)]
        simp only [wfKernel, Distribution.map_decide_eq_bernoulli]
    _ = wfCountKernel (Fintype.card V) (colorCount a s) := by
        rw [Distribution.independent_bernoulli_map_countFin]
        simp only [wfCountKernel, hq]

omit [DecidableEq V] in
/-- On two colours, all vertices have colour `true` iff `true` has `|V|` vertices. -/
lemma allColor_eq_ite (s : Config V Bool) :
    allColor true s = if colorCount true s = Fin.last (Fintype.card V) then 1 else 0 := by
  have h : s = (fun _ => true) ↔ colorCount true s = Fin.last (Fintype.card V) := by
    rw [Fin.ext_iff, Fin.val_last, colorCount, countFin_val, ← card_univ, card_filter_eq_iff]
    simp [funext_iff]
  unfold allColor
  by_cases hs : s = fun _ => true
  · rw [if_pos hs, if_pos (h.1 hs)]
  · rw [if_neg hs, if_neg fun h' => hs (h.2 h')]

/-- Fixation of the count chain, from the count of a configuration (any population). -/
lemma wfCountKernel_fixation_count [Nonempty V] (s : Config V Bool) :
    ⨆ t, (wfCountKernel (Fintype.card V)).event (· = Fin.last (Fintype.card V)) t
        (colorCount true s) = (colorCount true s : ℝ) / Fintype.card V := by
  have h := wrightFisher_fixation s true
  unfold eventualColor colorProbability at h
  simp only [funext allColor_eq_ite] at h
  calc ⨆ t, (wfCountKernel (Fintype.card V)).event (· = Fin.last (Fintype.card V)) t
        (colorCount true s)
      = ⨆ t, (transition (wfKernel V)).iterate t
          (fun x => if colorCount true x = Fin.last (Fintype.card V) then 1 else 0) s :=
        iSup_congr fun t => by
          rw [← (transition_wfKernel_lumps (V := V) true).event, Kernel.event_eq_iterate]
    _ = _ := h

/-- **Neutral fixation on counts.** Wright–Fisher in a population of `n ≥ 1` fixes the allele
from `x` copies with probability `x / n`: the supremum over `t` of the probability of `n` copies
at time `t`. Derived from the voter model on `K_n` with self-loops (`wrightFisher_fixation`)
through the lumping `transition_wfKernel_lumps`. -/
theorem wfCountKernel_fixation {n : ℕ} (hn : 0 < n) (x : Fin (n + 1)) :
    ⨆ t, (wfCountKernel n).event (· = Fin.last n) t x = x / n := by
  -- the count chain of the voter model on `Fin m`, transported along `|Fin m| = m`
  have key (m : ℕ) (hm : Fintype.card (Fin n) = m) (y : Fin (m + 1)) (s : Config (Fin n) Bool)
      (hs : (colorCount true s : ℕ) = y) :
      ⨆ t, (wfCountKernel m).event (· = Fin.last m) t y = y / m := by
    subst hm
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    obtain rfl : colorCount true s = y := Fin.ext hs
    exact wfCountKernel_fixation_count s
  refine key n (Fintype.card_fin n) x (fun i => decide ((i : ℕ) < x)) ?_
  simp only [colorCount, countFin_val, decide_eq_true_eq]
  rw [Fin.card_filter_val_lt]
  exact min_eq_right (Fin.is_le x)

end Voter
