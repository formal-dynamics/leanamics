import Crn.StableInteract

/-!
# Stable computation with general outputs (CRN-5)

`Protocol.StablyComputes` (CRN-3) computes predicates: every agent outputs a `Bool` through the
`output` field of the protocol, and all agents agree. The exact majority and plurality protocols of
[GHMSS16] need two generalizations, which only change the output convention (the transitions,
`Protocol.Reaches` and the fair-execution semantics in reachability form are those of
`StableBasic.lean`):

* outputs in an arbitrary type `Y`, read through a separate map `O : Q → Y` (the sign of a majority
  vote in [GHMSS16, Theorem 3], the absolute majority colour or none in [GHMSS16, Theorem 6]);
  this is the function-computation convention of Chen, Doty and Soloveichik (2014);
* outputs that depend on the agent's own input symbol (`StablyMarks`): in the relative majority
  protocol [GHMSS16, Theorem 7] the agents end up *marked*, each one knowing whether its own colour
  is the winner, not the winner's label.

`StablyComputesWith P O f` is the uniform case, and `StablyComputesWith P P.output φ` is exactly
`P.StablyComputes φ` (`stablyComputesWith_output_iff`).

## References

* [GHMSS16] L. Gąsieniec, D. Hamilton, R. Martin, P. G. Spirakis, G. Stachowiak, *Deterministic
  population protocols for exact majority and plurality*, OPODIS 2016, LIPIcs 70, Article 14.
-/

namespace Crn

variable {X Q Y Z : Type*} {n : ℕ}

namespace Protocol

/-- `c` is output-stable for the output map `O` with the target outputs `y` (one per agent): in
every configuration reachable from `c`, every agent `v` outputs `y v`. -/
def OutputStableAt (P : Protocol X Q) (O : Q → Y) (y : Fin n → Y) (c : Fin n → Q) : Prop :=
  ∀ c', P.Reaches c c' → ∀ v, O (c' v) = y v

variable [Fintype X] [DecidableEq X]

/-- `P` stably *marks* the agents with `g` through the output map `O`: for every nonempty
population and input assignment `ι`, every configuration reachable from `I ∘ ι` reaches a
configuration that is output-stable with the output `g x (ι v)` at each agent `v`, where `x` is
the input count vector. This is `StablyComputes` with outputs in `Y` that may depend on the
agent's own input symbol. -/
def StablyMarks (P : Protocol X Q) (O : Q → Y) (g : (X → ℕ) → X → Y) : Prop :=
  ∀ n, 0 < n → ∀ ι : Fin n → X, ∀ c, P.Reaches (P.input ∘ ι) c →
    ∃ d, P.Reaches c d ∧ P.OutputStableAt O (fun v => g (counts ι).1 (ι v)) d

/-- `P` stably computes `f : (X → ℕ) → Y` through the output map `O`: all agents eventually and
forever output `f` of the input counts (`StablyMarks` with a target independent of the agent). -/
def StablyComputesWith (P : Protocol X Q) (O : Q → Y) (f : (X → ℕ) → Y) : Prop :=
  P.StablyMarks O fun x _ => f x

/-- With the protocol's own `Bool` output, `StablyComputesWith` is `StablyComputes` (CRN-3). -/
theorem stablyComputesWith_output_iff (P : Protocol X Q) (φ : (X → ℕ) → Bool) :
    P.StablyComputesWith P.output φ ↔ P.StablyComputes φ :=
  Iff.rfl

/-- Post-composing the outputs: if `P` stably marks with `g` through `O`, it stably marks with
`F ∘ g` through `F ∘ O`. -/
theorem StablyMarks.map {P : Protocol X Q} {O : Q → Y} {g : (X → ℕ) → X → Y}
    (h : P.StablyMarks O g) (F : Y → Z) :
    P.StablyMarks (fun q => F (O q)) fun x i => F (g x i) := by
  intro n hn ι c hc
  obtain ⟨d, hd, hs⟩ := h n hn ι c hc
  exact ⟨d, hd, fun e he v => congrArg F (hs e he v)⟩

/-- Post-composing the outputs of a uniform computation. -/
theorem StablyComputesWith.map {P : Protocol X Q} {O : Q → Y} {f : (X → ℕ) → Y}
    (h : P.StablyComputesWith O f) (F : Y → Z) :
    P.StablyComputesWith (fun q => F (O q)) fun x => F (f x) :=
  StablyMarks.map h F

/-- `StablyMarks` only evaluates the output map and the targets. -/
theorem StablyMarks.congr {P : Protocol X Q} {O O' : Q → Y} {g g' : (X → ℕ) → X → Y}
    (h : P.StablyMarks O g) (hO : ∀ q, O q = O' q) (hg : ∀ x i, g x i = g' x i) :
    P.StablyMarks O' g' := by
  obtain rfl : O = O' := funext hO
  obtain rfl : g = g' := funext fun x => funext (hg x)
  exact h

end Protocol

/-! ### Tools for the proofs of CRN-5 -/

namespace Protocol

/-- A property preserved by every step, under which every agent `v` outputs `y v`, gives
output-stability with the targets `y`. -/
theorem outputStableAt_of_invariant {P : Protocol X Q} {O : Q → Y} {y : Fin n → Y}
    {I : (Fin n → Q) → Prop} (hI : ∀ c d, I c → P.Step c d → I d)
    (hO : ∀ c, I c → ∀ v, O (c v) = y v) {c : Fin n → Q} (hc : I c) : P.OutputStableAt O y c :=
  fun _ h => hO _ (h.invariant hI hc)

/-- Sums over agents across an encounter: only the initiator and the responder change. -/
theorem sum_interact {M : Type*} [AddCommMonoid M] (P : Protocol X Q) (F : Q → M)
    (c : Fin n → Q) (e : AgentPair n) :
    ∑ w, F (P.interact c e w) + (F (c e.1.1) + F (c e.1.2)) =
      ∑ w, F (c w) + (F (P.δ (c e.1.1, c e.1.2)).1 + F (P.δ (c e.1.1, c e.1.2)).2) := by
  have h := sum_add_pair e.2 (fun w => F (c w)) (fun w => F (P.interact c e w))
    (fun w h1 h2 => by rw [P.interact_of_ne c e h1 h2])
  simpa only [P.interact_fst, P.interact_snd] using h

/-- If every state of an encounter satisfies `p` whenever both states before it do, then
"every agent satisfies `p`" is preserved by steps. -/
theorem forall_step {P : Protocol X Q} {p : Q → Prop}
    (hp : ∀ a b, p a → p b → p (P.δ (a, b)).1 ∧ p (P.δ (a, b)).2) {c d : Fin n → Q}
    (h : P.Step c d) (hc : ∀ v, p (c v)) : ∀ v, p (d v) := by
  obtain ⟨e, rfl⟩ := h
  intro w
  rw [interact_apply]
  split_ifs
  · exact (hp _ _ (hc _) (hc _)).2
  · exact (hp _ _ (hc _) (hc _)).1
  · exact hc w

/-- If some state after an encounter satisfies `p` whenever some state before it does, then
"some agent satisfies `p`" is preserved by steps. -/
theorem exists_step {P : Protocol X Q} {p : Q → Prop}
    (hp : ∀ a b, p a ∨ p b → p (P.δ (a, b)).1 ∨ p (P.δ (a, b)).2) {c d : Fin n → Q}
    (h : P.Step c d) (hc : ∃ v, p (c v)) : ∃ v, p (d v) := by
  obtain ⟨e, rfl⟩ := h
  obtain ⟨v, hv⟩ := hc
  by_cases h1 : v = e.1.1
  · subst h1
    rcases hp _ _ (Or.inl hv) with h' | h'
    · exact ⟨_, by rwa [interact_fst]⟩
    · exact ⟨_, by rwa [interact_snd]⟩
  by_cases h2 : v = e.1.2
  · subst h2
    rcases hp _ _ (Or.inr hv) with h' | h'
    · exact ⟨_, by rwa [interact_fst]⟩
    · exact ⟨_, by rwa [interact_snd]⟩
  exact ⟨v, by rwa [interact_of_ne _ _ _ h1 h2]⟩

end Protocol

/-- Strong induction on a potential `μ`: if from every `a` satisfying `I` either `G a` holds or a
step leads to some `b` satisfying `I` with a smaller potential, then from every `a` satisfying `I`
a configuration satisfying `I` and `G` is reachable. -/
theorem exists_reflTransGen_of_measure {α : Type*} {r : α → α → Prop} (I G : α → Prop)
    (μ : α → ℕ) (h : ∀ a, I a → G a ∨ ∃ b, r a b ∧ I b ∧ μ b < μ a) {a : α} (ha : I a) :
    ∃ b, Relation.ReflTransGen r a b ∧ I b ∧ G b := by
  induction hμ : μ a using Nat.strong_induction_on generalizing a with
  | _ m ih =>
    rcases h a ha with hG | ⟨b, hab, hb, hlt⟩
    · exact ⟨a, Relation.ReflTransGen.refl, ha, hG⟩
    · obtain ⟨d, hbd, hd, hGd⟩ := ih _ (hμ ▸ hlt) hb rfl
      exact ⟨d, Relation.ReflTransGen.head hab hbd, hd, hGd⟩

/-- Recruitment: if every agent `v` outside its target set `T v` can be moved into it by a step
that keeps `I` and moves no other agent out of its target set, then a configuration satisfying
`I` with every agent in its target set is reachable (a strong induction on the number of agents
outside their target sets). -/
theorem exists_recruit {r : (Fin n → Q) → (Fin n → Q) → Prop} (I : (Fin n → Q) → Prop)
    (T : Fin n → Q → Prop)
    (h : ∀ c, I c → ∀ v, ¬ T v (c v) →
      ∃ c', r c c' ∧ I c' ∧ T v (c' v) ∧ ∀ w, T w (c w) → T w (c' w))
    {c : Fin n → Q} (hc : I c) : ∃ d, Relation.ReflTransGen r c d ∧ I d ∧ ∀ v, T v (d v) := by
  classical
  refine exists_reflTransGen_of_measure I (fun c => ∀ v, T v (c v))
    (fun c => (Finset.univ.filter fun v => ¬ T v (c v)).card) (fun c hc => ?_) hc
  by_cases hall : ∀ v, T v (c v)
  · exact Or.inl hall
  obtain ⟨v, hv⟩ := not_forall.1 hall
  obtain ⟨c', hcc', hc', hv', hmono⟩ := h c hc v hv
  refine Or.inr ⟨c', hcc', hc', Finset.card_lt_card ?_⟩
  have hsub : (Finset.univ.filter fun w => ¬ T w (c' w)) ⊆
      Finset.univ.filter fun w => ¬ T w (c w) := fun w hw => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    exact fun hT => hw (hmono w hT)
  exact (Finset.ssubset_iff_of_subset hsub).2 ⟨v, by simp [hv], by simp [hv']⟩

end Crn
