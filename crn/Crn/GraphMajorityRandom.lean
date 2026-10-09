import Crn.GraphMajorityBasic
import Crn.ApproximateMajority
import Dynamics.GraphRounds
import Dynamics.Rounds
import Dynamics.Tail

/-!
# Approximate majority on a graph with a random initial placement (CRN-4)

The 3-state approximate-majority protocol of Angluin, Aspnes and Eisenstat [AAE08] on an
arbitrary graph `G` with the probabilistic scheduler [MNRS14, §2]: each step activates a
uniformly random oriented edge (a uniform edge with a uniform orientation; `Dynamics.EdgeRound`),
whose tail is the initiator and head the responder. The states are the species `X`, `Y`, `B` of
`Crn.ApproxMajority` (CRN-1), and the transition is the one-way rule of [MNRS14, eq. (1)]
(`rule`): the initiator never changes; an `X`/`Y` initiator turns an opposite responder blank
and recruits a blank responder. Every effective transition is one of the four reactions of the
approximate-majority CRN `network` (`rule_mem_network`, `exists_rule_of_mem_network`).

**[MNRS14, Theorem 4]**: if the `m ≥ n − m` majority agents (`Y`, the paper's green `g`) and
the `n − m` minority agents (`X`, red `r`) are placed uniformly at random, the probability that
the protocol converges to the minority is at most the probability that it converges to the
majority.

Convergence is formalized in the finite probability layer of `dynamics/`: `winProb G m s t` is
the probability (over the placement and the scheduler) that at time `t` every agent is in state
`s`. Unanimous configurations are absorbing, so `winProb` is nondecreasing in `t`
(`winProb_monotone`) and the convergence probability is its supremum, `absorbProb G m s`
(the limit, `tendsto_winProb`), as for `Dynamics.Kernel.iSup_event_of_invariant`. We pin:

* the finite-time inequality `winProb_minority_le_majority` (every `t`, every graph with an
  edge), and its limit `absorbProb_minority_le_majority`;
* the paper's literal statement `half_le_absorbProb_majority` ("with probability at least
  `1/2`"), on connected graphs, using that the protocol is absorbed almost surely
  (`tendsto_event_unanimous`), a step the paper leaves implicit.

The proof follows [MNRS14, proof of Theorem 4]:

* **monotonicity** (eq. (19), "increasing the initial number of agents of type `r` increases the
  probability that agents of type `r` win", stated without proof in the paper): for the order
  `Y < B < X` (`rank`) the rule is monotone in both states (`rule_mono`), so running two
  ordered configurations with the same oriented edges keeps them ordered (`graphStep_mono`),
  and `P(all X at time t)` is monotone in the initial configuration (`event_allX_mono`);
* **symmetry** (eq. (20)): exchanging `X` and `Y` (`swap`) commutes with the dynamics
  (`graphStep_swap`, `event_swap`);
* **a system of distinct representatives** (Corollary 1, from Hall's theorem): every `m`-set
  `S` gets an `(n − m)`-subset `A_S ⊆ S`, injectively (`exists_injective_subset`, from the
  general `exists_injective_of_regular`).

## References

* [AAE08] D. Angluin, J. Aspnes, D. Eisenstat, *A simple population protocol for fast robust
  approximate majority*, Distributed Computing 21 (2008).
* [MNRS14] G. B. Mertzios, S. E. Nikoletseas, C. L. Raptopoulos, P. G. Spirakis, *Determining
  majority in networks with local interactions and very small local memory*, ICALP 2014;
  arXiv:1404.7671.
-/

namespace Crn.ApproxMajority

open Dynamics Finset Filter Topology Species

/-! ### The one-way rule of [AAE08] and its relation to the CRN `network` -/

/-- The transition function of the 3-state protocol of [AAE08], [MNRS14, eq. (1)], on the
states of (initiator, responder): `δ(x, y) = (x, x)` if `y = B` and `x ≠ B`, `δ(x, y) = (x, B)`
if `{x, y} = {X, Y}`, and no change otherwise (equal states, or a blank initiator). -/
def rule : Species × Species → Species × Species
  | (X, Y) => (X, B)
  | (Y, X) => (Y, B)
  | (X, B) => (X, X)
  | (Y, B) => (Y, Y)
  | p => p

/-- The 3-state protocol of [AAE08] as a population protocol: input `true ↦ X`,
`false ↦ Y`, output `true` exactly in state `X`. -/
def protocol : Protocol Bool Species where
  input x := if x then X else Y
  output s := decide (s = X)
  δ := rule

/-- Every effective transition of `rule` is a reaction of the approximate-majority CRN
`network` (CRN-1): reactants `{x, y}`, products `δ(x, y)`. -/
theorem rule_mem_network (p : Species × Species) (h : rule p ≠ p) :
    (⟨s(p.1, p.2), s((rule p).1, (rule p).2)⟩ : Reaction Species) ∈ network.reactions := by
  rw [network_reactions]
  obtain ⟨a, b⟩ := p
  cases a <;> cases b <;> simp_all [rule, xyToXB, xyToYB, bxToXX, byToYY, Sym2.eq_swap]

/-- Every reaction of the approximate-majority CRN `network` is an effective transition of
`rule` for some (initiator, responder) pair. -/
theorem exists_rule_of_mem_network (r : Reaction Species) (hr : r ∈ network.reactions) :
    ∃ p : Species × Species, rule p ≠ p ∧
      r = ⟨s(p.1, p.2), s((rule p).1, (rule p).2)⟩ := by
  rw [network_reactions] at hr
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨(X, Y), by decide, rfl⟩
  · exact ⟨(Y, X), by decide, by simp [xyToYB, rule, Sym2.eq_swap]⟩
  · exact ⟨(X, B), by decide, by simp [bxToXX, rule, Sym2.eq_swap]⟩
  · exact ⟨(Y, B), by decide, by simp [byToYY, rule, Sym2.eq_swap]⟩

variable {n : ℕ}

/-! ### The chain on a graph -/

section Chain

variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- One step of the protocol on `G`: the endpoints of the oriented edge `d` interact (tail
initiator, head responder) [MNRS14, §2]. -/
def graphStep (c : Fin n → Species) (d : G.Dart) : Fin n → Species :=
  protocol.interact c (dartPair d)

/-- The Markov chain of the protocol on `G` under the probabilistic scheduler [MNRS14, §2]:
each step activates a uniformly random oriented edge (`EdgeRound G`), i.e. a uniform edge with
a uniform orientation. -/
noncomputable def graphKernel [Nonempty G.Dart] : Kernel (Fin n → Species) :=
  Kernel.ofStep (graphStep G)

end Chain

/-- Every agent is in state `s` (for `s = X`, `Y`: the protocol has converged to `s`). -/
def Unanimous (s : Species) (c : Fin n → Species) : Prop :=
  ∀ v, c v = s

instance instDecidablePredUnanimous (s : Species) : DecidablePred (Unanimous (n := n) s) :=
  fun _ => Fintype.decidableForallFintype

/-- The initial placement with the majority type `Y` exactly on `S` and the minority type `X`
elsewhere [MNRS14, proof of Theorem 4: `(R₀, G₀) = (V − S, S)`]. -/
def placement (S : Finset (Fin n)) : Fin n → Species :=
  fun v => if v ∈ S then Y else X

section Prob

variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] [Nonempty G.Dart]

/-- The probability that at time `t` every agent is in state `s`, when the `m` agents of type
`Y` are placed uniformly at random (a uniform `m`-subset `S`, [MNRS14, eq. (18)]) and the
protocol runs on `G` with the probabilistic scheduler. -/
noncomputable def winProb (m : ℕ) (s : Species) (t : ℕ) : ℝ :=
  avg fun S : {S : Finset (Fin n) // S.card = m} =>
    (graphKernel G).event (Unanimous s) t (placement S.1)

/-- The probability that the protocol eventually converges to `s` from a uniformly random
placement of `m` agents of type `Y`: the supremum (the limit, `tendsto_winProb`) of the
finite-time probabilities `winProb`. -/
noncomputable def absorbProb (m : ℕ) (s : Species) : ℝ :=
  ⨆ t, winProb G m s t

end Prob

/-! ### Monotonicity and symmetry -/

/-- The order `Y < B < X` on states (the paper's `g < b < r`). -/
def rank : Species → ℕ
  | Y => 0
  | B => 1
  | X => 2

/-- The rule is monotone in both states for the order `Y < B < X` (by inspection of the
`3 × 3` table). -/
theorem rule_mono (p q : Species × Species) (h1 : rank p.1 ≤ rank q.1)
    (h2 : rank p.2 ≤ rank q.2) :
    rank (rule p).1 ≤ rank (rule q).1 ∧ rank (rule p).2 ≤ rank (rule q).2 := by
  revert p q
  decide

/-- Exchange of the two opinions `X ↔ Y`. -/
def swap : Species → Species
  | X => Y
  | Y => X
  | B => B

/-- The rule commutes with the exchange of `X` and `Y` (the protocol is symmetric for the two
types [MNRS14, proof of Theorem 4]). -/
theorem rule_swap (p : Species × Species) :
    rule (swap p.1, swap p.2) = (swap (rule p).1, swap (rule p).2) := by
  revert p
  decide

section Coupling

variable (G : SimpleGraph (Fin n))

/-- **Monotone coupling, one step.** Two configurations ordered agentwise stay ordered when the
same oriented edge is activated. -/
theorem graphStep_mono {c c' : Fin n → Species} (h : ∀ v, rank (c v) ≤ rank (c' v))
    (d : G.Dart) : ∀ v, rank (graphStep G c d v) ≤ rank (graphStep G c' d v) := by
  intro v
  have hm := rule_mono (c d.fst, c d.snd) (c' d.fst, c' d.snd) (h _) (h _)
  simp only [graphStep, Protocol.interact_apply]
  split_ifs
  · exact hm.2
  · exact hm.1
  · exact h v

/-- The dynamics commutes with the exchange of `X` and `Y`. -/
theorem graphStep_swap (c : Fin n → Species) (d : G.Dart) :
    graphStep G (swap ∘ c) d = swap ∘ graphStep G c d := by
  funext v
  have hs := rule_swap (c d.fst, c d.snd)
  simp only [graphStep, Protocol.interact_apply, Function.comp]
  split_ifs <;> simp_all [protocol, dartPair]

variable [DecidableRel G.Adj] [Nonempty G.Dart]

/-- One step of the chain averages an observable over the uniformly random oriented edge. -/
theorem graphKernel_apply (f : (Fin n → Species) → ℝ) (c : Fin n → Species) :
    (graphKernel G).apply f c = avg fun d : G.Dart => f (graphStep G c d) :=
  Kernel.apply_ofStep (graphStep G) f c

/-- **Monotone coupling, `t` steps.** If an observable is monotone for the agentwise order
`Y < B < X`, so is its expectation after `t` steps. -/
theorem iterate_graphKernel_mono (t : ℕ) {f : (Fin n → Species) → ℝ}
    (hf : ∀ c c' : Fin n → Species, (∀ v, rank (c v) ≤ rank (c' v)) → f c ≤ f c')
    {c c' : Fin n → Species} (h : ∀ v, rank (c v) ≤ rank (c' v)) :
    (graphKernel G).iterate t f c ≤ (graphKernel G).iterate t f c' := by
  induction t generalizing c c' with
  | zero => exact hf c c' h
  | succ t ih =>
    rw [Kernel.iterate_succ, graphKernel_apply, graphKernel_apply]
    exact avg_le_avg fun d => ih (graphStep_mono G h d)

/-- The dynamics commutes with the exchange of `X` and `Y`, at every time `t`. -/
theorem iterate_graphKernel_swap (t : ℕ) (f : (Fin n → Species) → ℝ) (c : Fin n → Species) :
    (graphKernel G).iterate t (fun c' => f (swap ∘ c')) c =
      (graphKernel G).iterate t f (swap ∘ c) := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih =>
    rw [Kernel.iterate_succ, Kernel.iterate_succ, graphKernel_apply, graphKernel_apply]
    simp only [ih, graphStep_swap]

/-- The exchanged configuration is unanimously `Y` exactly when the configuration is unanimously
`X`. -/
theorem unanimous_swap_iff (c : Fin n → Species) : Unanimous Y (swap ∘ c) ↔ Unanimous X c := by
  refine forall_congr' fun v => ?_
  simp only [Function.comp_apply]
  cases c v <;> decide

/-- **Monotonicity** [MNRS14, eq. (19)]: the probability that every agent is `X` at time `t`
can only increase when the initial configuration increases agentwise in the order
`Y < B < X`. -/
theorem event_allX_mono (t : ℕ) {c c' : Fin n → Species} (h : ∀ v, rank (c v) ≤ rank (c' v)) :
    (graphKernel G).event (Unanimous X) t c ≤ (graphKernel G).event (Unanimous X) t c' := by
  rw [Kernel.event_eq_iterate, Kernel.event_eq_iterate]
  refine iterate_graphKernel_mono G t (fun c c' h => ?_) h
  by_cases hc : Unanimous X c
  · have hc' : Unanimous X c' := fun v => by
      have hv := h v
      rw [hc v] at hv
      revert hv
      cases c' v <;> decide
    rw [if_pos hc, if_pos hc']
  · rw [if_neg hc]
    split <;> norm_num

/-- **Symmetry** [MNRS14, eq. (20)]: the probability that every agent is `X` at time `t` from
`c` is the probability that every agent is `Y` at time `t` from the exchanged configuration. -/
theorem event_swap (t : ℕ) (c : Fin n → Species) :
    (graphKernel G).event (Unanimous X) t c = (graphKernel G).event (Unanimous Y) t (swap ∘ c) := by
  rw [Kernel.event_eq_iterate, Kernel.event_eq_iterate, ← iterate_graphKernel_swap]
  simp only [unanimous_swap_iff]

/-- A unanimous configuration is absorbing. -/
theorem prob_unanimous_of_unanimous (s : Species) {c : Fin n → Species} (hc : Unanimous s c) :
    (graphKernel G c).prob (Unanimous s) = 1 := by
  have hfix : ∀ d : G.Dart, graphStep G c d = c := by
    intro d
    apply Protocol.interact_eq_self
    rw [hc, hc]
    change rule (s, s) = (s, s)
    cases s <;> rfl
  rw [graphKernel, Kernel.prob_ofStep]
  simp only [hfix, if_pos hc]
  exact avg_const 1

end Coupling

/-! ### Systems of distinct representatives -/

/-- **[MNRS14, Corollary 1]** (a consequence of Hall's theorem, Jukna, *Extremal
Combinatorics*, ch. 5): `r`-element subsets `T i` of a universe of `y` elements such that each
element belongs to the same number `d ≥ 1` of them, with `x ≤ y` sets, have a system of
distinct representatives. -/
theorem exists_injective_of_regular {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
    (T : ι → Finset α) {r d : ℕ} (hr : ∀ i, (T i).card = r)
    (hd : ∀ a, (univ.filter fun i => a ∈ T i).card = d) (hd1 : 1 ≤ d)
    (hxy : Fintype.card ι ≤ Fintype.card α) :
    ∃ f : ι → α, Function.Injective f ∧ ∀ i, f i ∈ T i := by
  refine (Finset.all_card_le_biUnion_card_iff_exists_injective T).1 fun s => ?_
  rcases s.eq_empty_or_nonempty with rfl | ⟨i₀, -⟩
  · simp
  -- counting all incidences: `r · card ι = d · card α`, hence `d ≤ r`
  have hall : Fintype.card ι * r = Fintype.card α * d :=
    card_mul_eq_card_mul (fun i a => a ∈ T i)
      (fun i _ => by simp [bipartiteAbove, hr]) (fun a _ => by simp [bipartiteBelow, hd])
  have hα : 0 < Fintype.card α := (Fintype.card_pos_iff.2 ⟨i₀⟩).trans_le hxy
  have hdr : d ≤ r := by
    refine Nat.le_of_mul_le_mul_left ?_ hα
    rw [← hall]
    exact Nat.mul_le_mul_right _ hxy
  -- counting the incidences of `s`: `r · #s ≤ d · #(s.biUnion T)`
  have hs : #s * r ≤ #(s.biUnion T) * d :=
    card_mul_le_card_mul (fun i a => a ∈ T i)
      (fun i hi => by
        rw [← hr i]
        refine card_le_card fun a ha => ?_
        simp only [bipartiteAbove, mem_filter, mem_biUnion]
        exact ⟨⟨i, hi, ha⟩, ha⟩)
      (fun a _ => by
        rw [← hd a]
        exact card_le_card (filter_subset_filter _ (subset_univ s)))
  exact Nat.le_of_mul_le_mul_right ((Nat.mul_le_mul_left _ hdr).trans hs) hd1

/-- [MNRS14, proof of Theorem 4]: if `n − m ≤ m`, every `m`-subset `S` of the agents can be
assigned an `(n − m)`-subset `A_S ⊆ S`, injectively. -/
theorem exists_injective_subset {m : ℕ} (hm : n ≤ 2 * m) :
    ∃ σ : Finset (Fin n) → Finset (Fin n),
      (∀ S, S.card = m → σ S ⊆ S ∧ (σ S).card = n - m) ∧ Set.InjOn σ {S | S.card = m} := by
  rcases lt_or_ge n m with hnm | hmn
  · refine ⟨id, fun S hS => absurd hS ?_, Function.injective_id.injOn⟩
    exact (S.card_le_univ.trans_lt (by simpa using hnm)).ne
  let T : {S : Finset (Fin n) // S.card = m} → Finset {A : Finset (Fin n) // A.card = n - m} :=
    fun S => univ.filter fun A => A.1 ⊆ S.1
  -- each `m`-set contains `C(m, n − m)` sets of size `n − m`
  have hr : ∀ S, (T S).card = m.choose (n - m) := by
    intro S
    refine Eq.trans ?_ ((card_powersetCard (n - m) S.1).trans (by rw [S.2]))
    refine card_bij (fun A _ => A.1) (fun A hA => ?_) (fun A _ A' _ h => Subtype.ext h)
      (fun U hU => ?_)
    · simp only [T, mem_filter, mem_univ, true_and] at hA
      exact mem_powersetCard.2 ⟨hA, A.2⟩
    · obtain ⟨hUS, hU⟩ := mem_powersetCard.1 hU
      exact ⟨⟨U, hU⟩, by simp [T, hUS], rfl⟩
  -- each `(n − m)`-set is contained in `C(m, n − m)` sets of size `m` (complements)
  have hd : ∀ A, (univ.filter fun S => A ∈ T S).card = m.choose (n - m) := by
    intro A
    have hA : A.1ᶜ.card = m := by rw [card_compl, Fintype.card_fin, A.2]; omega
    refine Eq.trans ?_ ((card_powersetCard (n - m) A.1ᶜ).trans (by rw [hA]))
    refine card_bij (fun S _ => S.1ᶜ) (fun S hS => ?_)
      (fun S _ S' _ h => Subtype.ext (compl_injective h)) (fun U hU => ?_)
    · simp only [T, mem_filter, mem_univ, true_and] at hS
      refine mem_powersetCard.2 ⟨compl_subset_compl.2 hS, ?_⟩
      rw [card_compl, Fintype.card_fin, S.2]
    · obtain ⟨hUA, hU⟩ := mem_powersetCard.1 hU
      refine ⟨⟨Uᶜ, by rw [card_compl, Fintype.card_fin, hU]; omega⟩, ?_, compl_compl U⟩
      simpa [T] using subset_compl_comm.1 hUA
  have hcard : Fintype.card {S : Finset (Fin n) // S.card = m} ≤
      Fintype.card {A : Finset (Fin n) // A.card = n - m} := by
    rw [Fintype.card_finset_len, Fintype.card_finset_len, Fintype.card_fin,
      Nat.choose_symm hmn]
  obtain ⟨f, hf, hfT⟩ := exists_injective_of_regular T hr hd
    (Nat.choose_pos (by omega)) hcard
  refine ⟨fun S => if h : S.card = m then (f ⟨S, h⟩).1 else S, fun S hS => ?_, ?_⟩
  · have := hfT ⟨S, hS⟩
    simp only [T, mem_filter, mem_univ, true_and] at this
    simp only [hS, dite_true]
    exact ⟨this, (f ⟨S, hS⟩).2⟩
  · intro S hS S' hS' h
    simp only [Set.mem_setOf_eq] at hS hS'
    simp only [hS, hS', dite_true] at h
    exact congrArg Subtype.val (hf (Subtype.ext h))

/-! ### Almost sure absorption: helper lemmas -/

section Absorption

/-- The initiator never changes its state. -/
theorem rule_fst (p : Species × Species) : (rule p).1 = p.1 := by
  revert p
  decide

/-- A blank initiator leaves the responder unchanged. -/
theorem rule_blank_snd (t : Species) : (rule (B, t)).2 = t := by
  cases t <;> rfl

/-- An initiator in state `s ≠ B` activated twice on the same responder brings it to `s` (a
blank responder is recruited at once; an opposite one is first turned blank). -/
theorem rule_snd_rule_snd {s : Species} (hs : s ≠ B) (t : Species) :
    (rule (s, (rule (s, t)).2)).2 = s := by
  revert s t
  decide

variable (G : SimpleGraph (Fin n))

/-- The initiator keeps its state. -/
theorem graphStep_fst (c : Fin n → Species) (d : G.Dart) : graphStep G c d d.fst = c d.fst :=
  (Protocol.interact_fst _ _ _).trans (rule_fst _)

/-- The responder takes the second component of the rule. -/
theorem graphStep_snd (c : Fin n → Species) (d : G.Dart) :
    graphStep G c d d.snd = (rule (c d.fst, c d.snd)).2 :=
  Protocol.interact_snd _ _ _

/-- The agents other than the two endpoints keep their states. -/
theorem graphStep_of_ne (c : Fin n → Species) (d : G.Dart) {v : Fin n} (h1 : v ≠ d.fst)
    (h2 : v ≠ d.snd) : graphStep G c d v = c v :=
  Protocol.interact_of_ne _ _ _ h1 h2

/-- A unanimous configuration is fixed by every step. -/
theorem graphStep_of_unanimous {s : Species} {c : Fin n → Species} (hc : Unanimous s c)
    (d : G.Dart) : graphStep G c d = c := by
  apply Protocol.interact_eq_self
  rw [hc, hc]
  change rule (s, s) = (s, s)
  cases s <;> rfl

/-- An agent in state `s` keeps it when the initiator is in state `s`. -/
theorem graphStep_eq_of_fst {c : Fin n → Species} {d : G.Dart} {s : Species} (hd : c d.fst = s)
    {v : Fin n} (hv : c v = s) : graphStep G c d v = s := by
  by_cases h2 : v = d.snd
  · subst h2
    rw [graphStep_snd, hd, hv]
    cases s <;> rfl
  · by_cases h1 : v = d.fst
    · subst h1
      rw [graphStep_fst, hv]
    · rw [graphStep_of_ne G c d h1 h2, hv]

/-- A configuration with a non-blank agent keeps one after a step. -/
theorem graphStep_not_unanimous_blank {c : Fin n → Species} (hc : ¬ Unanimous B c)
    (d : G.Dart) : ¬ Unanimous B (graphStep G c d) := by
  intro h
  have h1 : c d.fst = B := by
    rw [← graphStep_fst G c d]
    exact h _
  have h2 : c d.snd = B := by
    have := h d.snd
    rwa [graphStep_snd, h1, rule_blank_snd] at this
  apply hc
  intro v
  by_cases hv1 : v = d.fst
  · rw [hv1, h1]
  by_cases hv2 : v = d.snd
  · rw [hv2, h2]
  rw [← graphStep_of_ne G c d hv1 hv2]
  exact h v

/-- **Spreading** on a connected graph: from a configuration with an agent in state `s ≠ B`,
the configuration in which every agent is in state `s` is reachable (activate twice an edge
from an agent in state `s` to an agent in another state, until there is none). -/
theorem graphReaches_const (hG : G.Connected) {s : Species} (hs : s ≠ B) {c : Fin n → Species}
    (hc : ∃ u, c u = s) : protocol.GraphReaches G c (fun _ => s) := by
  induction hk : (univ.filter fun v => c v ≠ s).card using Nat.strong_induction_on
    generalizing c with
  | _ k ih =>
  obtain ⟨u, hu⟩ := hc
  by_cases hall : ∀ v, c v = s
  · rw [show c = fun _ => s from funext hall]
    exact Relation.ReflTransGen.refl
  obtain ⟨w, hw⟩ := not_forall.mp hall
  obtain ⟨p⟩ := hG.preconnected u w
  obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart {v | c v = s} hu hw
  simp only [Set.mem_setOf_eq] at hd1 hd2
  have h₁ : ∀ v, c v = s → graphStep G c d v = s := fun v hv => graphStep_eq_of_fst G hd1 hv
  have h₂ : ∀ v, c v = s → graphStep G (graphStep G c d) d v = s :=
    fun v hv => graphStep_eq_of_fst G (h₁ _ hd1) (h₁ v hv)
  have hsnd : graphStep G (graphStep G c d) d d.snd = s := by
    rw [graphStep_snd, h₁ _ hd1, graphStep_snd, hd1]
    exact rule_snd_rule_snd hs _
  have hlt : (univ.filter fun v => graphStep G (graphStep G c d) d v ≠ s).card < k := by
    rw [← hk]
    apply card_lt_card
    rw [ssubset_iff_of_subset]
    · exact ⟨d.snd, by simpa using hd2, by simpa using hsnd⟩
    · intro v
      simp only [mem_filter, mem_univ, true_and]
      exact mt (h₂ v)
  exact Relation.ReflTransGen.head ⟨d, rfl⟩ (Relation.ReflTransGen.head ⟨d, rfl⟩
    (ih _ hlt ⟨u, h₂ u hu⟩ rfl))

variable [DecidableRel G.Adj] [Nonempty G.Dart]

/-- **Access**: if `b` is reachable from `a` on `G` and an observable `g ≤ 1` is below `1` at
`b`, then its expectation at some finite time from `a` is below `1`. -/
theorem exists_iterate_lt_one {a b : Fin n → Species} (h : protocol.GraphReaches G a b)
    {g : (Fin n → Species) → ℝ} (hg : ∀ x, g x ≤ 1) (hb : g b < 1) :
    ∃ k, (graphKernel G).iterate k g a < 1 := by
  have hle (k : ℕ) (x : Fin n → Species) : (graphKernel G).iterate k g x ≤ 1 := by
    simpa [Kernel.iterate_const] using (graphKernel G).iterate_mono k hg x
  unfold Protocol.GraphReaches at h
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, hb⟩
  | head hac _ ih =>
    obtain ⟨k, hk⟩ := ih
    obtain ⟨d, rfl⟩ := hac
    refine ⟨k + 1, ?_⟩
    rw [Kernel.iterate_succ, graphKernel_apply]
    exact avg_lt_one (fun d' => hle k _) (b := d) hk

/-- From a configuration with a non-blank agent, all agents are never simultaneously blank. -/
theorem iterate_unanimous_blank (t : ℕ) {c : Fin n → Species} (hc : ¬ Unanimous B c) :
    (graphKernel G).iterate t (fun b => if Unanimous B b then 1 else 0) c = 0 := by
  induction t generalizing c with
  | zero => simp [hc]
  | succ t ih =>
    rw [Kernel.iterate_succ, graphKernel_apply]
    simp only [ih (graphStep_not_unanimous_blank G hc _)]
    exact avg_const 0

end Absorption

/-! ### Theorem 4 -/

section Main

variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] [Nonempty G.Dart]

/-- Unanimity is absorbing, so the finite-time convergence probabilities are nondecreasing. -/
theorem winProb_monotone (m : ℕ) (s : Species) : Monotone (winProb G m s) := by
  intro t₁ t₂ ht
  exact avg_le_avg fun S =>
    Kernel.event_monotone _ (fun _ hc => prob_unanimous_of_unanimous G s hc) _ ht

/-- The finite-time convergence probabilities lie in `[0, 1]`. -/
theorem winProb_mem_Icc (m : ℕ) (s : Species) (t : ℕ) : winProb G m s t ∈ Set.Icc 0 1 := by
  constructor
  · exact avg_nonneg fun _ => Kernel.event_nonneg _ _ _ _
  · unfold winProb avg
    rcases isEmpty_or_nonempty {S : Finset (Fin n) // S.card = m} with h | h
    · simp
    · rw [div_le_one (by exact_mod_cast Fintype.card_pos)]
      calc _ ≤ ∑ _S : {S : Finset (Fin n) // S.card = m}, (1 : ℝ) :=
            sum_le_sum fun _ _ => Kernel.event_le_one _ _ _ _
        _ = _ := by simp

/-- The convergence probability is the limit of the finite-time probabilities. -/
theorem tendsto_winProb (m : ℕ) (s : Species) :
    Tendsto (winProb G m s) atTop (𝓝 (absorbProb G m s)) :=
  tendsto_atTop_ciSup (winProb_monotone G m s)
    ⟨1, by rintro _ ⟨t, rfl⟩; exact (winProb_mem_Icc G m s t).2⟩

/-- **[MNRS14, Theorem 4], finite-time form.** On every graph with an edge, if the `m ≥ n − m`
agents of the majority type `Y` and the `n − m` agents of the minority type `X` are placed
uniformly at random, then at every time `t` the probability that every agent is `X` (the
minority has won) is at most the probability that every agent is `Y` (the majority has won). -/
theorem winProb_minority_le_majority {m : ℕ} (hm : n ≤ 2 * m) (t : ℕ) :
    winProb G m X t ≤ winProb G m Y t := by
  obtain ⟨σ, hσ, hinj⟩ := exists_injective_subset hm
  -- `τ S = (σ S)ᶜ` is again an `m`-set: `#(σ S)ᶜ = n − (n − m) = m`
  have hcard (S : {S : Finset (Fin n) // S.card = m}) : (σ S.1)ᶜ.card = m := by
    have hmn : m ≤ n := S.2 ▸ (card_le_univ S.1).trans_eq (Fintype.card_fin n)
    rw [card_compl, Fintype.card_fin, (hσ S.1 S.2).2]
    omega
  let τ (S : {S : Finset (Fin n) // S.card = m}) : {S : Finset (Fin n) // S.card = m} :=
    ⟨(σ S.1)ᶜ, hcard S⟩
  -- `τ` is injective, hence a bijection of the finite set of `m`-sets
  have hτ : Function.Bijective τ := by
    refine Function.Injective.bijective_of_finite fun S T hST => Subtype.ext ?_
    exact hinj S.2 T.2 (compl_injective (congrArg Subtype.val hST))
  -- exchanging the types of `placement A` gives `placement Aᶜ`
  have hpl (A : Finset (Fin n)) : swap ∘ placement A = placement Aᶜ := by
    funext v
    by_cases hv : v ∈ A <;> simp [placement, hv, swap]
  calc winProb G m X t
      ≤ avg fun S : {S : Finset (Fin n) // S.card = m} =>
          (graphKernel G).event (Unanimous Y) t (placement (τ S).1) := by
        refine avg_le_avg fun S => ?_
        -- eqs. (19), (20): `placement S ≤ placement (σ S)` agentwise, then exchange the types
        rw [show (τ S).1 = (σ S.1)ᶜ from rfl, ← hpl, ← event_swap]
        refine event_allX_mono G t fun v => ?_
        have hsub := (hσ S.1 S.2).1
        by_cases hA : v ∈ σ S.1
        · simp [placement, hA, hsub hA]
        · by_cases hS : v ∈ S.1 <;> simp [placement, hA, hS, rank]
    _ = winProb G m Y t :=
        avg_equiv (Equiv.ofBijective τ hτ) fun S =>
          (graphKernel G).event (Unanimous Y) t (placement S.1)

/-- **[MNRS14, Theorem 4].** On every graph with an edge, with a uniformly random placement of
`m ≥ n − m` majority agents, the protocol of [AAE08] converges to the initial majority with
probability at least the probability that it converges to the initial minority. -/
theorem absorbProb_minority_le_majority {m : ℕ} (hm : n ≤ 2 * m) :
    absorbProb G m X ≤ absorbProb G m Y :=
  ciSup_mono ⟨1, by rintro _ ⟨t, rfl⟩; exact (winProb_mem_Icc G m Y t).2⟩
    (winProb_minority_le_majority G hm)

/-- **Almost sure convergence** (implicit in [MNRS14, Theorem 4]): on a connected graph, from
every configuration with a non-blank agent, the probability that the protocol has converged to
`X` or to `Y` by time `t` tends to `1`. -/
theorem tendsto_event_unanimous (hG : G.Connected) {c : Fin n → Species} (hc : ∃ v, c v ≠ B) :
    Tendsto (fun t => (graphKernel G).event (Unanimous X) t c +
      (graphKernel G).event (Unanimous Y) t c) atTop (𝓝 1) := by
  obtain ⟨d₀⟩ := ‹Nonempty G.Dart›
  have hcB : ¬ Unanimous B c := fun h => by
    obtain ⟨v, hv⟩ := hc
    exact hv (h v)
  -- `f` is the indicator of the configurations that are not yet absorbed
  let f : (Fin n → Species) → ℝ := fun b =>
    if Unanimous X b ∨ Unanimous Y b ∨ Unanimous B b then 0 else 1
  have hfix (a : Fin n → Species) (ha : Unanimous X a ∨ Unanimous Y a ∨ Unanimous B a)
      (d : G.Dart) : graphStep G a d = a := by
    rcases ha with h | h | h <;> exact graphStep_of_unanimous G h d
  have hf (a : Fin n → Species) : f a = 0 ∨ f a = 1 := by
    by_cases ha : Unanimous X a ∨ Unanimous Y a ∨ Unanimous B a
    · exact Or.inl (if_pos ha)
    · exact Or.inr (if_neg ha)
  have hstep (a : Fin n → Species) : (graphKernel G).apply f a ≤ f a := by
    rw [graphKernel_apply]
    by_cases ha : Unanimous X a ∨ Unanimous Y a ∨ Unanimous B a
    · simp only [hfix a ha, avg_const, le_refl]
    · calc _ ≤ avg fun _ : G.Dart => (1 : ℝ) :=
            avg_le_avg fun d => by rcases hf (graphStep G a d) with h | h <;> rw [h]; norm_num
        _ = f a := by rw [avg_const]; exact (if_neg ha).symm
  have haccess (a : Fin n → Species) : ∃ k, (graphKernel G).iterate k f a < 1 := by
    by_cases ha : Unanimous X a ∨ Unanimous Y a ∨ Unanimous B a
    · exact ⟨0, by simp [f, ha]⟩
    · obtain ⟨v, hv⟩ : ∃ v, a v ≠ B := by
        by_contra h
        push Not at h
        exact ha (Or.inr (Or.inr h))
      refine exists_iterate_lt_one G (graphReaches_const G hG hv ⟨v, rfl⟩)
        (fun b => by rcases hf b with h | h <;> rw [h]; norm_num) ?_
      have : f (fun _ => a v) = 0 := by
        apply if_pos
        cases a v <;> simp [Unanimous]
      rw [this]
      norm_num
  have : Nonempty (Fin n → Species) := ⟨c⟩
  have habs := Kernel.finite_absorption (graphKernel G) f hf hstep haccess c
  have hsum (t : ℕ) : (graphKernel G).event (Unanimous X) t c +
      (graphKernel G).event (Unanimous Y) t c = 1 - (graphKernel G).iterate t f c := by
    have hsplit : (fun _ : Fin n → Species => (1 : ℝ)) = fun b =>
        ((if Unanimous X b then 1 else 0) + (if Unanimous Y b then 1 else 0)) +
          ((if Unanimous B b then 1 else 0) + f b) := by
      funext b
      have hex (s s' : Species) (hs : Unanimous s b) (hs' : Unanimous s' b) : s = s' :=
        (hs d₀.fst).symm.trans (hs' d₀.fst)
      by_cases hX : Unanimous X b
      · have hY : ¬ Unanimous Y b := fun h => absurd (hex _ _ hX h) (by decide)
        have hB : ¬ Unanimous B b := fun h => absurd (hex _ _ hX h) (by decide)
        simp [f, hX, hY, hB]
      by_cases hY : Unanimous Y b
      · have hB : ¬ Unanimous B b := fun h => absurd (hex _ _ hY h) (by decide)
        simp [f, hX, hY, hB]
      by_cases hB : Unanimous B b
      · simp [f, hX, hY, hB]
      · simp [f, hX, hY, hB]
    have h1 := congrFun ((graphKernel G).iterate_const t 1) c
    rw [hsplit, Kernel.iterate_add, Kernel.iterate_add, Kernel.iterate_add] at h1
    rw [Kernel.event_eq_iterate, Kernel.event_eq_iterate]
    have h0 := iterate_unanimous_blank G t hcB
    simp only at h1
    linarith
  have hlim := (tendsto_const_nhds (x := (1 : ℝ))).sub habs
  rw [sub_zero] at hlim
  exact hlim.congr fun t => (hsum t).symm

/-- **[MNRS14, Theorem 4], as stated.** On a connected graph, with a uniformly random placement
of `m ≥ n − m` majority agents (`m ≤ n`), the protocol of [AAE08] converges to the initial
majority with probability at least `1/2`. -/
theorem half_le_absorbProb_majority (hG : G.Connected) {m : ℕ} (hm : n ≤ 2 * m)
    (hmn : m ≤ n) : 1 / 2 ≤ absorbProb G m Y := by
  obtain ⟨d₀⟩ := ‹Nonempty G.Dart›
  obtain ⟨S₀, -, hS₀⟩ := exists_subset_card_eq (s := (univ : Finset (Fin n)))
    (by simpa using hmn)
  have : Nonempty {S : Finset (Fin n) // S.card = m} := ⟨⟨S₀, hS₀⟩⟩
  -- every placement has a non-blank agent, so it is absorbed in `X` or `Y` almost surely
  have hS (S : {S : Finset (Fin n) // S.card = m}) : ∃ v, placement S.1 v ≠ B :=
    ⟨d₀.fst, by unfold placement; split_ifs <;> decide⟩
  have hlim : Tendsto (fun t => winProb G m X t + winProb G m Y t) atTop (𝓝 1) := by
    have h := (tendsto_finsetSum univ fun S _ =>
      tendsto_event_unanimous G hG (hS S)).div_const
        (Fintype.card {S : Finset (Fin n) // S.card = m} : ℝ)
    rw [← avg, avg_const] at h
    refine h.congr fun t => ?_
    rw [winProb, winProb, ← avg_add]
    rfl
  have hsum : absorbProb G m X + absorbProb G m Y = 1 :=
    tendsto_nhds_unique ((tendsto_winProb G m X).add (tendsto_winProb G m Y)) hlim
  linarith [absorbProb_minority_le_majority G hm]

end Main

end Crn.ApproxMajority
