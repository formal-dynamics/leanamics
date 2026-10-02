import Dynamics.Distribution
import Mathlib

/-! # Reed–Frost epidemics and bond percolation, pathwise (EPI-1)

The Reed–Frost (Independent Cascade) epidemic on a finite graph `G`: in every round, each infected
node infects each susceptible neighbour across the edge between them if that edge is *open*, and
then recovers for good. Every edge carries a single coin `ω e : Bool`, flipped once and for all
(`true` = open). The open edges form the percolated graph `perc G ω`.

Pathwise, for every coin assignment, the nodes infected in round `t` are exactly those at distance
`t` from the initial set `I₀` in `perc G ω`, and the recovered ones those at distance `< t`; the
epidemic is over after `card V` rounds, and its final recovered set is the set of nodes connected to
`I₀` by open edges. With i.i.d. Bernoulli(`p`) coins, the probability that a node is eventually
infected is the probability that bond percolation connects it to `I₀`.
-/

namespace Epidemics
open Finset Dynamics

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The percolated graph: the edges of `G` whose coin is `true`. -/
def perc (G : SimpleGraph V) (ω : Sym2 V → Bool) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ ω s(u, v) = true
  symm := ⟨fun u v h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
  loopless := ⟨fun u h => G.loopless.irrefl u h.1⟩

/-- Infected and recovered nodes; the others are susceptible. -/
structure SIR (V : Type*) where
  infected : Finset V
  recovered : Finset V

/-- One round: a susceptible node becomes infected if it has an infected neighbour across an open
edge; every infected node recovers. -/
def step (G : SimpleGraph V) [DecidableRel G.Adj] (ω : Sym2 V → Bool) (s : SIR V) : SIR V where
  infected := univ.filter fun v => v ∉ s.infected ∧ v ∉ s.recovered ∧ ∃ u ∈ s.infected, G.Adj u v ∧ ω s(u, v) = true
  recovered := s.recovered ∪ s.infected

/-- The epidemic started from the infected set `I₀`, with nobody recovered. -/
def run (G : SimpleGraph V) [DecidableRel G.Adj] (ω : Sym2 V → Bool) (I₀ : Finset V) : ℕ → SIR V
  | 0 => ⟨I₀, ∅⟩
  | t + 1 => step G ω (run G ω I₀ t)

/-- Distance from the set `I₀` in a graph `H` (`⊤` if `v` is not connected to `I₀`). -/
noncomputable def setDist (H : SimpleGraph V) (I₀ : Finset V) (v : V) : ℕ∞ :=
  ⨅ u ∈ I₀, H.edist u v

open SimpleGraph

omit [Fintype V] [DecidableEq V] in
lemma setDist_eq_subtype (H : SimpleGraph V) (I₀ : Finset V) (v : V) :
    setDist H I₀ v = ⨅ u : (I₀ : Set V), H.edist (↑u) v := by
  simpa [setDist] using (iInf_subtype'' (↑I₀) (H.edist · v)).symm

omit [Fintype V] [DecidableEq V] in
lemma setDist_eq_zero_iff (H : SimpleGraph V) (I₀ : Finset V) {v : V} :
    setDist H I₀ v = 0 ↔ v ∈ I₀ := by
  simp only [setDist_eq_subtype, ENat.iInf_eq_zero, edist_eq_zero_iff, Subtype.exists,
    exists_prop, exists_eq_right]
  exact mem_coe

omit [Fintype V] [DecidableEq V] in
lemma setDist_le_add_one (H : SimpleGraph V) (I₀ : Finset V) {u v : V} (huv : H.Adj u v) :
    setDist H I₀ v ≤ setDist H I₀ u + 1 := by
  calc
    setDist H I₀ v = ⨅ w ∈ I₀, H.edist w v := rfl
    _ ≤ ⨅ w ∈ I₀, H.edist w u + 1 := by
      refine iInf₂_mono fun w _ => ?_
      calc
        H.edist w v ≤ H.edist w u + H.edist u v := H.edist_triangle
        _ = H.edist w u + 1 := by rw [(H.edist_eq_one_iff_adj).mpr huv]
    _ = setDist H I₀ u + 1 :=
      (ENat.iInf₂_add (fun w (_ : w ∈ I₀) => H.edist w u) (a := 1)).symm

omit [Fintype V] [DecidableEq V] in
lemma exists_edist_eq_setDist (H : SimpleGraph V) (I₀ : Finset V) {v : V}
    (h : setDist H I₀ v ≠ ⊤) : ∃ u ∈ I₀, H.edist u v = setDist H I₀ v := by
  rw [setDist_eq_subtype] at h ⊢
  cases isEmpty_or_nonempty ((I₀ : Set V) : Type _) with
  | inl hempty => simp [iInf_of_empty] at h
  | inr _ =>
    obtain ⟨u, hu⟩ := ENat.exists_eq_iInf (fun u : (I₀ : Set V) => H.edist (↑u) v)
    exact ⟨↑u, u.2, hu⟩

omit [Fintype V] [DecidableEq V] in
lemma exists_adj_of_setDist_succ (H : SimpleGraph V) (I₀ : Finset V) {v : V} {t : ℕ}
    (h : setDist H I₀ v = t + 1) : ∃ u, H.Adj u v ∧ setDist H I₀ u = t := by
  have hne : setDist H I₀ v ≠ ⊤ := by simp [h]
  obtain ⟨w, hw, hed⟩ := exists_edist_eq_setDist H I₀ hne
  obtain ⟨p, hp⟩ := exists_walk_of_edist_eq_coe (k := t + 1) (hed.trans h)
  have hnotnil : ¬p.Nil := by
    rw [← Walk.length_eq_zero_iff, hp]
    omega
  refine ⟨p.penultimate, p.adj_penultimate hnotnil, ?_⟩
  apply le_antisymm
  · calc
      setDist H I₀ p.penultimate ≤ H.edist w p.penultimate := by
        simpa [setDist] using
          biInf_le (s := (↑I₀ : Set V)) (fun x => H.edist x p.penultimate) hw
      _ ≤ p.dropLast.length := edist_le p.dropLast
      _ = t := by simp [Walk.length_dropLast, hp]
  · have htri : setDist H I₀ v ≤ setDist H I₀ p.penultimate + 1 :=
      setDist_le_add_one H I₀ (p.adj_penultimate hnotnil)
    rw [h] at htri
    have hle : (t : ℕ∞) + 1 ≤ setDist H I₀ p.penultimate + 1 := by
      simpa [Nat.cast_add, Nat.cast_one] using htri
    exact (ENat.add_le_add_iff_right (by simp : (1 : ℕ∞) ≠ ⊤)).mp hle

omit [Fintype V] [DecidableEq V] in
lemma setDist_ne_top_iff (H : SimpleGraph V) (I₀ : Finset V) {v : V} :
    setDist H I₀ v ≠ ⊤ ↔ ∃ u ∈ I₀, H.Reachable u v := by
  constructor
  · intro h
    obtain ⟨u, hu, hed⟩ := exists_edist_eq_setDist H I₀ h
    exact ⟨u, hu, edist_ne_top_iff_reachable.mp (by simpa [hed] using h)⟩
  · rintro ⟨u, hu, hr⟩
    have hle : setDist H I₀ v ≤ H.edist u v := by
      simpa [setDist] using biInf_le (s := (↑I₀ : Set V)) (fun w => H.edist w v) hu
    exact ne_of_lt (hle.trans_lt (WithTop.lt_top_iff_ne_top.mpr (edist_ne_top_iff_reachable.mpr hr)))

omit [DecidableEq V] in
lemma setDist_lt_card (H : SimpleGraph V) (I₀ : Finset V) {v : V} (h : setDist H I₀ v ≠ ⊤) :
    setDist H I₀ v < Fintype.card V := by
  obtain ⟨u, _, hed⟩ := exists_edist_eq_setDist H I₀ h
  have hreach : H.Reachable u v := edist_ne_top_iff_reachable.mp (by simpa [hed] using h)
  obtain ⟨p, hp, hlen⟩ := hreach.exists_path_of_dist
  rw [← hed, ← hreach.coe_dist_eq_edist, ← hlen]
  exact ENat.coe_lt_coe.mpr hp.length_lt

lemma infected_recovered_iff (G : SimpleGraph V) [DecidableRel G.Adj] (ω : Sym2 V → Bool)
    (I₀ : Finset V) (t : ℕ) (v : V) :
    (v ∈ (run G ω I₀ t).infected ↔ setDist (perc G ω) I₀ v = t) ∧
    (v ∈ (run G ω I₀ t).recovered ↔ setDist (perc G ω) I₀ v < t) := by
  induction t generalizing v with
  | zero =>
    constructor
    · simpa [run] using (setDist_eq_zero_iff (perc G ω) I₀ (v := v)).symm
    · simp only [run]
      exact iff_of_false (notMem_empty v) not_lt_zero
  | succ t ih =>
    let H := perc G ω
    have hinf (x : V) : x ∈ (run G ω I₀ t).infected ↔ setDist H I₀ x = t := (ih x).1
    have hrec (x : V) : x ∈ (run G ω I₀ t).recovered ↔ setDist H I₀ x < t := (ih x).2
    constructor
    · simp only [run, step, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨hni, hnr, u, hu, hadj⟩
        have hdu : setDist H I₀ u = t := (hinf u).mp hu
        have hgt : (t : ℕ∞) < setDist H I₀ v := by
          rcases lt_trichotomy (setDist H I₀ v) (t : ℕ∞) with hlt | heq | hgt
          · exact absurd hlt ((hrec v).not.mp hnr)
          · exact absurd heq ((hinf v).not.mp hni)
          · exact hgt
        have hle : setDist H I₀ v ≤ (t + 1 : ℕ∞) := by
          simpa [hdu, Nat.cast_add, Nat.cast_one] using setDist_le_add_one H I₀ hadj
        apply le_antisymm hle
        by_contra hcontra
        have hlt1 : setDist H I₀ v < (t + 1 : ℕ∞) := lt_of_not_ge hcontra
        have hle_t : setDist H I₀ v ≤ t :=
          (ENat.lt_add_one_iff (ENat.coe_ne_top t)).mp
            (by simpa [Nat.cast_add, Nat.cast_one] using hlt1)
        exact (lt_irrefl _ (lt_of_le_of_lt hle_t hgt)).elim
      · intro hdv
        refine ⟨?_, ?_, ?_⟩
        · rw [(hinf v).not, hdv]
          exact Nat.cast_injective.ne (Nat.succ_ne_self t)
        · rw [(hrec v).not, hdv]
          exact not_lt_of_ge (ENat.coe_le_coe.mpr (Nat.le_succ t))
        · obtain ⟨u, hadj, hdu⟩ := exists_adj_of_setDist_succ H I₀ hdv
          exact ⟨u, (hinf u).mpr hdu, hadj⟩
    · simp only [run, step, mem_union]
      rw [hrec v, hinf v, ← le_iff_lt_or_eq, Nat.cast_succ]
      exact (ENat.lt_add_one_iff (ENat.coe_ne_top t)).symm

/-- Pathwise layers: the nodes infected in round `t` are those at percolation distance `t`. -/
theorem infected_iff (G : SimpleGraph V) [DecidableRel G.Adj] (ω : Sym2 V → Bool) (I₀ : Finset V)
    (t : ℕ) (v : V) :
    v ∈ (run G ω I₀ t).infected ↔ setDist (perc G ω) I₀ v = t :=
  (infected_recovered_iff G ω I₀ t v).1

/-- The nodes recovered by round `t` are those at percolation distance `< t`. -/
theorem recovered_iff (G : SimpleGraph V) [DecidableRel G.Adj] (ω : Sym2 V → Bool) (I₀ : Finset V)
    (t : ℕ) (v : V) :
    v ∈ (run G ω I₀ t).recovered ↔ setDist (perc G ω) I₀ v < t :=
  (infected_recovered_iff G ω I₀ t v).2

lemma no_infected_of_dist_lt (G : SimpleGraph V) [DecidableRel G.Adj] (ω : Sym2 V → Bool)
    (I₀ : Finset V) (t : ℕ)
    (h : ∀ v, setDist (perc G ω) I₀ v ≠ ⊤ → setDist (perc G ω) I₀ v < t) :
    (run G ω I₀ t).infected = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro v hv
  have hd : setDist (perc G ω) I₀ v = t := (infected_iff G ω I₀ t v).mp hv
  have hne : setDist (perc G ω) I₀ v ≠ ⊤ := by simp [hd]
  have hlt : setDist (perc G ω) I₀ v < t := h v hne
  simp only [hd] at hlt
  exact lt_irrefl _ hlt

/-- The epidemic is over after `card V` rounds. -/
theorem extinct (G : SimpleGraph V) [DecidableRel G.Adj] (ω : Sym2 V → Bool) (I₀ : Finset V)
    (t : ℕ) (ht : Fintype.card V ≤ t) :
    (run G ω I₀ t).infected = ∅ := by
  refine no_infected_of_dist_lt G ω I₀ t ?_
  intro v hv
  exact (setDist_lt_card (perc G ω) I₀ hv).trans_le (ENat.coe_le_coe.mpr ht)

/-- Final size: the eventually recovered nodes are those connected to `I₀` by open edges. -/
theorem final_recovered_iff (G : SimpleGraph V) [DecidableRel G.Adj] (ω : Sym2 V → Bool)
    (I₀ : Finset V) (v : V) :
    v ∈ (run G ω I₀ (Fintype.card V)).recovered ↔ ∃ u ∈ I₀, (perc G ω).Reachable u v := by
  rw [recovered_iff]
  constructor
  · intro hlt
    exact (setDist_ne_top_iff (perc G ω) I₀).mp
      (WithTop.lt_top_iff_ne_top.mp (hlt.trans_le le_top))
  · intro hr
    exact setDist_lt_card (perc G ω) I₀ ((setDist_ne_top_iff (perc G ω) I₀).mpr hr)

/-- A biased coin: `true` with probability `p`. -/
noncomputable def bernoulli (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : Distribution Bool where
  weight b := if b then p else 1 - p
  nonneg b := by cases b <;> simp [h0, h1]
  sum_one := by simp

/-- Independent Bernoulli(`p`) coins, one per unordered pair of nodes. -/
noncomputable def coins (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : Distribution (Sym2 V → Bool) :=
  Distribution.independent fun _ => bernoulli p h0 h1

/-- The coin of a single pair is open with probability `p`. -/
theorem coins_prob_open (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (e : Sym2 V) :
    (coins (V := V) p h0 h1).prob (fun ω => ω e = true) = p := by
  classical
  have h := Distribution.independent_expect_eval (fun _ : Sym2 V => bernoulli p h0 h1) e
    (fun b => if b = true then (1 : ℝ) else 0)
  calc
    (coins (V := V) p h0 h1).prob (fun ω => ω e = true)
      = (Distribution.independent (fun _ : Sym2 V => bernoulli p h0 h1)).expect
          (fun ω => if ω e = true then (1 : ℝ) else 0) := by
        simp only [Distribution.prob, coins]
        apply congrArg
        funext ω
        by_cases hω : ω e = true
        · rw [if_pos hω, if_pos hω]
        · rw [if_neg hω, if_neg hω]
    _ = (bernoulli p h0 h1).expect (fun b => if b = true then (1 : ℝ) else 0) := h
    _ = p := by
      rw [Distribution.expect, Fintype.sum_bool]
      simp [bernoulli]

/-- Reed–Frost ⇔ bond percolation: the probability that `v` is eventually infected equals the
probability that `v` is connected to `I₀` in the percolated graph. -/
theorem prob_infected_eq_prob_connected (G : SimpleGraph V) [DecidableRel G.Adj] (p : ℝ)
    (h0 : 0 ≤ p) (h1 : p ≤ 1) (I₀ : Finset V) (v : V) :
    (coins p h0 h1).prob (fun ω => v ∈ (run G ω I₀ (Fintype.card V)).recovered) =
      (coins p h0 h1).prob (fun ω => ∃ u ∈ I₀, (perc G ω).Reachable u v) := by
  classical
  simp only [Distribution.prob]
  congr 1
  ext ω
  by_cases hr : v ∈ (run G ω I₀ (Fintype.card V)).recovered
  · rw [if_pos hr, if_pos ((final_recovered_iff G ω I₀ v).mp hr)]
  · rw [if_neg hr, if_neg (fun h => hr ((final_recovered_iff G ω I₀ v).mpr h))]

/-- The epidemic cannot outlast the percolation distances: if every node connected to `I₀` is at
distance `< t`, nobody is infected in round `t`. -/
theorem extinct_of_dist_lt (G : SimpleGraph V) [DecidableRel G.Adj] (ω : Sym2 V → Bool)
    (I₀ : Finset V) (t : ℕ) (h : ∀ v, setDist (perc G ω) I₀ v ≠ ⊤ → setDist (perc G ω) I₀ v < t) :
    (run G ω I₀ t).infected = ∅ :=
  no_infected_of_dist_lt G ω I₀ t h

end Epidemics
