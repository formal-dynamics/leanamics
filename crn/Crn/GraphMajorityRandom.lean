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

/-- **Monotonicity** [MNRS14, eq. (19)]: the probability that every agent is `X` at time `t`
can only increase when the initial configuration increases agentwise in the order
`Y < B < X`. -/
theorem event_allX_mono (t : ℕ) {c c' : Fin n → Species} (h : ∀ v, rank (c v) ≤ rank (c' v)) :
    (graphKernel G).event (Unanimous X) t c ≤ (graphKernel G).event (Unanimous X) t c' := by
  sorry

/-- **Symmetry** [MNRS14, eq. (20)]: the probability that every agent is `X` at time `t` from
`c` is the probability that every agent is `Y` at time `t` from the exchanged configuration. -/
theorem event_swap (t : ℕ) (c : Fin n → Species) :
    (graphKernel G).event (Unanimous X) t c = (graphKernel G).event (Unanimous Y) t (swap ∘ c) := by
  sorry

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
  sorry

/-- [MNRS14, proof of Theorem 4]: if `n − m ≤ m`, every `m`-subset `S` of the agents can be
assigned an `(n − m)`-subset `A_S ⊆ S`, injectively. -/
theorem exists_injective_subset {m : ℕ} (hm : n ≤ 2 * m) :
    ∃ σ : Finset (Fin n) → Finset (Fin n),
      (∀ S, S.card = m → σ S ⊆ S ∧ (σ S).card = n - m) ∧ Set.InjOn σ {S | S.card = m} := by
  sorry

/-! ### Theorem 4 -/

section Main

variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] [Nonempty G.Dart]

/-- Unanimity is absorbing, so the finite-time convergence probabilities are nondecreasing. -/
theorem winProb_monotone (m : ℕ) (s : Species) : Monotone (winProb G m s) := by
  sorry

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
  sorry

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
  sorry

/-- **[MNRS14, Theorem 4], as stated.** On a connected graph, with a uniformly random placement
of `m ≥ n − m` majority agents (`m ≤ n`), the protocol of [AAE08] converges to the initial
majority with probability at least `1/2`. -/
theorem half_le_absorbProb_majority (hG : G.Connected) {m : ℕ} (hm : n ≤ 2 * m)
    (hmn : m ≤ n) : 1 / 2 ≤ absorbProb G m Y := by
  sorry

end Main

end Crn.ApproxMajority
