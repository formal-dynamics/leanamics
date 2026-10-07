import Crn.StableInteract

/-!
# Leader protocols (CRN-3)

The common shape of the threshold and remainder protocols of [AADFP06, proof of Lemma 5]. A
state is a triple (leader bit, output bit, value `u ∈ V`). An encounter in which at least one
agent is a leader makes the initiator the leader with value `q(u, u')` and the responder a
non-leader with value `r(u, u')`, and sets both output bits to `t(q(u, u'))`; an encounter of
two non-leaders changes nothing. Inputs start as leaders with output bit `t(u)` (this
initialisation makes the protocols correct also for a single agent, see Deviation 2 in
`PROGRESS-CRN3.md`).

Generic facts proved here:
* invariants closed under steps: leaders output `t` of their value (`LeadOut`), a leader exists
  (`HasLeader`), weighted sums of the values are conserved if `q + r` conserves them
  (`sum_step`), non-leaders hold `z` if `r` always returns `z` (`nonLeaderVal_step`);
* leaders can be merged until at most one is left (`exists_reaches_atMostOne`), and a potential
  on the non-leaders' values can be decreased until no encounter with the leader decreases it
  (`exists_reaches_noImprove`);
* *good* configurations (one leader, with value `L`, and non-leaders with values satisfying
  `R`, where `q(L, y) = q(y, L) = L` and `r(L, y) = r(y, L) = y` for `R y`) are closed under
  steps, and from them the leader's output `t L` can be broadcast to every agent, which yields
  an output-stable configuration (`Good.exists_outputStable`).
-/

namespace Crn

open Finset

namespace Leader

variable {X V : Type*} {n : ℕ}

/-- The leader protocol with initial values `init`, merge functions `q` (initiator) and `r`
(responder) and output test `t`. -/
def protocol (init : X → V) (q r : V → V → V) (t : V → Bool) : Protocol X (Bool × Bool × V) where
  input i := (true, t (init i), init i)
  output s := s.2.1
  δ p := if (p.1.1 || p.2.1) = true then
      ((true, t (q p.1.2.2 p.2.2.2), q p.1.2.2 p.2.2.2),
        (false, t (q p.1.2.2 p.2.2.2), r p.1.2.2 p.2.2.2))
    else p

variable {init : X → V} {q r : V → V → V} {t : V → Bool}

/-- An encounter of two non-leaders changes nothing. -/
lemma interact_of_not (c : Fin n → Bool × Bool × V) (e : AgentPair n)
    (h : ((c e.1.1).1 || (c e.1.2).1) = false) :
    (protocol init q r t).interact c e = c :=
  Protocol.interact_eq_self _ c e (by simp only [protocol, h, Bool.false_eq_true, ↓reduceIte])

/-- In an encounter with a leader, the initiator becomes the leader with value `q(u, u')`. -/
lemma interact_fst (c : Fin n → Bool × Bool × V) (e : AgentPair n)
    (h : ((c e.1.1).1 || (c e.1.2).1) = true) :
    (protocol init q r t).interact c e e.1.1 =
      (true, t (q (c e.1.1).2.2 (c e.1.2).2.2), q (c e.1.1).2.2 (c e.1.2).2.2) := by
  rw [Protocol.interact_fst]
  simp only [protocol, h, ↓reduceIte]

/-- In an encounter with a leader, the responder becomes a non-leader with value `r(u, u')`. -/
lemma interact_snd (c : Fin n → Bool × Bool × V) (e : AgentPair n)
    (h : ((c e.1.1).1 || (c e.1.2).1) = true) :
    (protocol init q r t).interact c e e.1.2 =
      (false, t (q (c e.1.1).2.2 (c e.1.2).2.2), r (c e.1.1).2.2 (c e.1.2).2.2) := by
  rw [Protocol.interact_snd]
  simp only [protocol, h, ↓reduceIte]

/-- A step either changes nothing or is an encounter involving a leader. -/
lemma step_cases {c d : Fin n → Bool × Bool × V} (h : (protocol init q r t).Step c d) :
    d = c ∨ ∃ e : AgentPair n, ((c e.1.1).1 || (c e.1.2).1) = true ∧
      d = (protocol init q r t).interact c e := by
  obtain ⟨e, rfl⟩ := h
  cases hb : ((c e.1.1).1 || (c e.1.2).1)
  · exact Or.inl (interact_of_not c e hb)
  · exact Or.inr ⟨e, hb, rfl⟩

/-! ### Invariants -/

/-- Every leader outputs `t` of its value. -/
def LeadOut (t : V → Bool) (c : Fin n → Bool × Bool × V) : Prop :=
  ∀ w, (c w).1 = true → (c w).2.1 = t (c w).2.2

/-- Some agent is a leader. -/
def HasLeader (c : Fin n → Bool × Bool × V) : Prop := ∃ w, (c w).1 = true

/-- At most one agent is a leader. -/
def AtMostOne (c : Fin n → Bool × Bool × V) : Prop :=
  ∀ u w, (c u).1 = true → (c w).1 = true → u = w

/-- Every non-leader holds the value `z`. -/
def NonLeaderVal (z : V) (c : Fin n → Bool × Bool × V) : Prop :=
  ∀ w, (c w).1 = false → (c w).2.2 = z

/-- `LeadOut` is preserved by steps. -/
lemma leadOut_step {c d : Fin n → Bool × Bool × V} (hc : LeadOut t c)
    (h : (protocol init q r t).Step c d) : LeadOut t d := by
  rcases step_cases h with rfl | ⟨e, he, rfl⟩
  · exact hc
  intro w hw
  by_cases h2 : w = e.1.2
  · subst h2
    rw [interact_snd c e he] at hw
    exact absurd hw Bool.false_ne_true
  by_cases h1 : w = e.1.1
  · subst h1
    rw [interact_fst c e he]
  rw [Protocol.interact_of_ne _ c e h1 h2] at hw ⊢
  exact hc w hw

/-- `HasLeader` is preserved by steps. -/
lemma hasLeader_step {c d : Fin n → Bool × Bool × V}
    (h : (protocol init q r t).Step c d) (hc : HasLeader c) : HasLeader d := by
  rcases step_cases h with rfl | ⟨e, he, rfl⟩
  · exact hc
  exact ⟨e.1.1, by rw [interact_fst c e he]⟩

/-- After an encounter involving the only leader, the initiator is the only leader. -/
lemma eq_fst_of_atMostOne {c : Fin n → Bool × Bool × V} (hc : AtMostOne c) (e : AgentPair n)
    (he : ((c e.1.1).1 || (c e.1.2).1) = true) {w : Fin n}
    (hw : ((protocol init q r t).interact c e w).1 = true) : w = e.1.1 := by
  by_cases h2 : w = e.1.2
  · subst h2
    rw [interact_snd c e he] at hw
    exact absurd hw Bool.false_ne_true
  by_cases h1 : w = e.1.1
  · exact h1
  rw [Protocol.interact_of_ne _ c e h1 h2] at hw
  rcases Bool.or_eq_true_iff.1 he with hu | hv
  · exact absurd (hc w _ hw hu) h1
  · exact absurd (hc w _ hw hv) h2

/-- `AtMostOne` is preserved by steps. -/
lemma atMostOne_step {c d : Fin n → Bool × Bool × V} (hc : AtMostOne c)
    (h : (protocol init q r t).Step c d) : AtMostOne d := by
  rcases step_cases h with rfl | ⟨e, he, rfl⟩
  · exact hc
  intro u w hu hw
  rw [eq_fst_of_atMostOne hc e he hu, eq_fst_of_atMostOne hc e he hw]

/-- If `r` always returns `z`, then `NonLeaderVal z` is preserved by steps. -/
lemma nonLeaderVal_step {z : V} (hr : ∀ a b, r a b = z) {c d : Fin n → Bool × Bool × V}
    (hc : NonLeaderVal z c) (h : (protocol init q r t).Step c d) : NonLeaderVal z d := by
  rcases step_cases h with rfl | ⟨e, he, rfl⟩
  · exact hc
  intro w hw
  by_cases h2 : w = e.1.2
  · subst h2
    rw [interact_snd c e he]
    exact hr _ _
  by_cases h1 : w = e.1.1
  · subst h1
    rw [interact_fst c e he] at hw
    exact absurd hw (by decide : ¬(true = false))
  rw [Protocol.interact_of_ne _ c e h1 h2] at hw ⊢
  exact hc w hw

/-- Weighted sums of the values are conserved if `F(q(u, u')) + F(r(u, u')) = F(u) + F(u')`. -/
lemma sum_step {M : Type*} [AddCancelCommMonoid M] {F : V → M}
    (hF : ∀ a b, F (q a b) + F (r a b) = F a + F b) {c d : Fin n → Bool × Bool × V}
    (h : (protocol init q r t).Step c d) : ∑ w, F (d w).2.2 = ∑ w, F (c w).2.2 := by
  rcases step_cases h with rfl | ⟨e, he, rfl⟩
  · rfl
  have hp := sum_add_pair e.2 (fun w => F (c w).2.2)
    (fun w => F ((protocol init q r t).interact c e w).2.2)
    (fun w h1 h2 => by simp only [Protocol.interact_of_ne _ c e h1 h2])
  simp only [interact_fst c e he, interact_snd c e he, hF] at hp
  exact add_right_cancel hp

/-- Initially every agent is a leader, so a nonempty population has one. -/
lemma hasLeader_input (hn : 0 < n) (ι : Fin n → X) :
    HasLeader ((protocol init q r t).input ∘ ι) := ⟨⟨0, hn⟩, rfl⟩

/-- Initially every leader outputs `t` of its value. -/
lemma leadOut_input (ι : Fin n → X) : LeadOut t ((protocol init q r t).input ∘ ι) :=
  fun _ _ => rfl

/-- Initially there are no non-leaders. -/
lemma nonLeaderVal_input (z : V) (ι : Fin n → X) :
    NonLeaderVal z ((protocol init q r t).input ∘ ι) :=
  fun _ hw => by simp [protocol] at hw

/-- The initial values, grouped by input symbol. -/
lemma sum_input [Fintype X] [DecidableEq X] {M : Type*} [AddCommMonoid M] (F : V → M)
    (ι : Fin n → X) :
    ∑ w, F (((protocol init q r t).input ∘ ι) w).2.2 = ∑ i, (counts ι).1 i • F (init i) :=
  sum_comp_eq_sum_counts ι fun i => F (init i)

/-! ### Merging the leaders -/

/-- The leaders can be merged until at most one is left. -/
lemma exists_reaches_atMostOne (c : Fin n → Bool × Bool × V) :
    ∃ d, (protocol init q r t).Reaches c d ∧ AtMostOne d := by
  suffices H : ∀ k (c : Fin n → Bool × Bool × V), #{w | (c w).1 = true} = k →
      ∃ d, (protocol init q r t).Reaches c d ∧ AtMostOne d from H _ c rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro c hk
  by_cases h : AtMostOne c
  · exact ⟨c, Protocol.Reaches.refl c, h⟩
  simp only [AtMostOne, not_forall] at h
  obtain ⟨u, v, hu, hv, huv⟩ := h
  let e : AgentPair n := ⟨(u, v), huv⟩
  have he : ((c e.1.1).1 || (c e.1.2).1) = true := by simp [e, hu]
  have hset : #{w | ((protocol init q r t).interact c e w).1 = true} =
      #{w | (c w).1 = true} - 1 := by
    have : ({w | ((protocol init q r t).interact c e w).1 = true} : Finset (Fin n)) =
        ({w | (c w).1 = true} : Finset (Fin n)).erase v := by
      ext w
      simp only [mem_filter, mem_univ, true_and, mem_erase]
      by_cases h2 : w = e.1.2
      · rw [h2, interact_snd c e he]
        simp [e]
      by_cases h1 : w = e.1.1
      · rw [h1, interact_fst c e he]
        simp [e, huv, hu]
      rw [Protocol.interact_of_ne _ c e h1 h2]
      simp [e] at h2
      simp [h2]
    rw [this, card_erase_of_mem (by simp [hv])]
  have hpos : 0 < #{w | (c w).1 = true} := card_pos.2 ⟨v, by simp [hv]⟩
  obtain ⟨d, hd, hd1⟩ := ih (k - 1) (by omega) _ (by rw [hset, hk])
  exact ⟨d, (Protocol.reaches_interact c e).trans hd, hd1⟩

/-! ### Decreasing a potential -/

/-- No encounter of a leader (as initiator) with a non-leader decreases the weight `μ` of the
non-leader's value. -/
def NoImprove (r : V → V → V) (μ : V → ℕ) (c : Fin n → Bool × Bool × V) : Prop :=
  ∀ ℓ j, (c ℓ).1 = true → (c j).1 = false → μ (c j).2.2 ≤ μ (r (c ℓ).2.2 (c j).2.2)

/-- The total weight `∑ μ` of the non-leaders' values. -/
def pot (μ : V → ℕ) (c : Fin n → Bool × Bool × V) : ℕ :=
  ∑ w, if (c w).1 = true then 0 else μ (c w).2.2

/-- An encounter of a leader (initiator) with a non-leader whose value decreases in weight
decreases the potential. -/
lemma pot_interact_lt (μ : V → ℕ) {c : Fin n → Bool × Bool × V} {ℓ j : Fin n} (hne : ℓ ≠ j)
    (hℓ : (c ℓ).1 = true) (hj : (c j).1 = false)
    (hlt : μ (r (c ℓ).2.2 (c j).2.2) < μ (c j).2.2) :
    pot μ ((protocol init q r t).interact c ⟨(ℓ, j), hne⟩) < pot μ c := by
  set e : AgentPair n := ⟨(ℓ, j), hne⟩ with he_def
  have he : ((c e.1.1).1 || (c e.1.2).1) = true := by simp [e, hℓ]
  have hp := sum_add_pair hne (fun w => if (c w).1 = true then 0 else μ (c w).2.2)
    (fun w => if ((protocol init q r t).interact c e w).1 = true then 0
      else μ ((protocol init q r t).interact c e w).2.2)
    (fun w h1 h2 => by simp only [Protocol.interact_of_ne _ c e h1 h2])
  have h1 : (protocol init q r t).interact c e ℓ =
      (true, t (q (c ℓ).2.2 (c j).2.2), q (c ℓ).2.2 (c j).2.2) := interact_fst c e he
  have h2 : (protocol init q r t).interact c e j =
      (false, t (q (c ℓ).2.2 (c j).2.2), r (c ℓ).2.2 (c j).2.2) := interact_snd c e he
  simp only [h1, h2, hℓ, hj, if_true, Bool.false_eq_true, if_false, zero_add] at hp
  unfold pot
  omega

/-- With at most one leader, encounters of the leader with non-leaders can be performed until
none decreases the total weight `∑ μ` of the non-leaders' values. -/
lemma exists_reaches_noImprove (μ : V → ℕ) (c : Fin n → Bool × Bool × V) (hc : AtMostOne c) :
    ∃ d, (protocol init q r t).Reaches c d ∧ AtMostOne d ∧ NoImprove r μ d := by
  suffices H : ∀ k (c : Fin n → Bool × Bool × V), AtMostOne c → pot μ c = k →
      ∃ d, (protocol init q r t).Reaches c d ∧ AtMostOne d ∧ NoImprove r μ d from
    H _ c hc rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro c hc hk
  by_cases h : NoImprove r μ c
  · exact ⟨c, Protocol.Reaches.refl c, hc, h⟩
  simp only [NoImprove, not_forall, not_le] at h
  obtain ⟨ℓ, j, hℓ, hj, hlt⟩ := h
  have hne : ℓ ≠ j := fun h' => by rw [h', hj] at hℓ; exact Bool.false_ne_true hℓ
  have hd : (protocol init q r t).Step c ((protocol init q r t).interact c ⟨(ℓ, j), hne⟩) :=
    ⟨_, rfl⟩
  obtain ⟨d', hd', hd'1, hd'2⟩ := ih _ (hk ▸ pot_interact_lt μ hne hℓ hj hlt) _
    (atMostOne_step hc hd) rfl
  exact ⟨d', hd.reaches.trans hd', hd'1, hd'2⟩

/-! ### Good configurations and broadcasting the output -/

/-- Good configurations for the leader value `L` and the non-leader condition `R`: exactly one
leader, which holds `L` and outputs `t L`, and non-leaders whose values satisfy `R`. -/
structure Good (t : V → Bool) (L : V) (R : V → Prop) (c : Fin n → Bool × Bool × V) : Prop where
  exists_leader : ∃ w, (c w).1 = true
  unique : AtMostOne c
  leader : ∀ w, (c w).1 = true → (c w).2.2 = L ∧ (c w).2.1 = t L
  nonleader : ∀ w, (c w).1 = false → R (c w).2.2

variable {L : V} {R : V → Prop}

/-- In a good configuration, an encounter involving the leader gives the initiator the value
`L` and the responder the value of the non-leader. -/
lemma Good.merge (H : ∀ y, R y → q L y = L ∧ r L y = y ∧ q y L = L ∧ r y L = y)
    {c : Fin n → Bool × Bool × V} (hc : Good t L R c) (e : AgentPair n)
    (he : ((c e.1.1).1 || (c e.1.2).1) = true) :
    q (c e.1.1).2.2 (c e.1.2).2.2 = L ∧ R (r (c e.1.1).2.2 (c e.1.2).2.2) := by
  cases hu : (c e.1.1).1
  · have hv : (c e.1.2).1 = true := by simpa [hu] using he
    have hR := hc.nonleader _ hu
    rw [(hc.leader _ hv).1, (H _ hR).2.2.1, (H _ hR).2.2.2]
    exact ⟨rfl, hR⟩
  · have hv : (c e.1.2).1 = false := by
      cases hv' : (c e.1.2).1
      · rfl
      · exact absurd (hc.unique _ _ hu hv') e.2
    have hR := hc.nonleader _ hv
    rw [(hc.leader _ hu).1, (H _ hR).1, (H _ hR).2.1]
    exact ⟨rfl, hR⟩

/-- Good configurations are closed under steps. -/
lemma Good.step (H : ∀ y, R y → q L y = L ∧ r L y = y ∧ q y L = L ∧ r y L = y)
    {c d : Fin n → Bool × Bool × V} (hc : Good t L R c) (h : (protocol init q r t).Step c d) :
    Good t L R d := by
  rcases step_cases h with rfl | ⟨e, he, rfl⟩
  · exact hc
  obtain ⟨hq, hR⟩ := hc.merge H e he
  have h1 := interact_fst (init := init) (q := q) (r := r) (t := t) c e he
  have h2 := interact_snd (init := init) (q := q) (r := r) (t := t) c e he
  rw [hq] at h1 h2
  refine ⟨⟨e.1.1, by rw [h1]⟩, atMostOne_step hc.unique ⟨e, rfl⟩, fun w hw => ?_,
    fun w hw => ?_⟩
  · rw [eq_fst_of_atMostOne hc.unique e he hw, h1]
    exact ⟨rfl, rfl⟩
  · by_cases hw2 : w = e.1.2
    · rw [hw2, h2]
      exact hR
    by_cases hw1 : w = e.1.1
    · rw [hw1, h1] at hw
      exact absurd hw (by decide : ¬(true = false))
    rw [Protocol.interact_of_ne _ c e hw1 hw2] at hw ⊢
    exact hc.nonleader w hw

/-- In a good configuration, every encounter keeps correct outputs correct. -/
lemma Good.out_step (H : ∀ y, R y → q L y = L ∧ r L y = y ∧ q y L = L ∧ r y L = y)
    {c : Fin n → Bool × Bool × V} (hc : Good t L R c) (e : AgentPair n) {w : Fin n}
    (hw : (c w).2.1 = t L) : ((protocol init q r t).interact c e w).2.1 = t L := by
  cases he : ((c e.1.1).1 || (c e.1.2).1)
  · rw [interact_of_not c e he]
    exact hw
  obtain ⟨hq, -⟩ := hc.merge H e he
  by_cases hw2 : w = e.1.2
  · rw [hw2, interact_snd c e he, hq]
  by_cases hw1 : w = e.1.1
  · rw [hw1, interact_fst c e he, hq]
  rw [Protocol.interact_of_ne _ c e hw1 hw2]
  exact hw

/-- In a good configuration, an encounter involving the leader sets the responder's output to
`t L`. -/
lemma Good.out_snd (H : ∀ y, R y → q L y = L ∧ r L y = y ∧ q y L = L ∧ r y L = y)
    {c : Fin n → Bool × Bool × V} (hc : Good t L R c) (e : AgentPair n)
    (he : ((c e.1.1).1 || (c e.1.2).1) = true) :
    ((protocol init q r t).interact c e e.1.2).2.1 = t L := by
  rw [interact_snd c e he, (hc.merge H e he).1]

/-- From a good configuration, the leader's output `t L` can be broadcast to all agents. -/
lemma Good.exists_allOut (H : ∀ y, R y → q L y = L ∧ r L y = y ∧ q y L = L ∧ r y L = y)
    {c : Fin n → Bool × Bool × V} (hc : Good t L R c) :
    ∃ d, (protocol init q r t).Reaches c d ∧ Good t L R d ∧ ∀ w, (d w).2.1 = t L := by
  suffices hT : ∀ T : Finset (Fin n), ∃ d, (protocol init q r t).Reaches c d ∧ Good t L R d ∧
      ∀ w ∈ T, (d w).2.1 = t L by
    obtain ⟨d, hd, hd1, hd2⟩ := hT univ
    exact ⟨d, hd, hd1, fun w => hd2 w (mem_univ w)⟩
  intro T
  induction T using Finset.induction_on with
  | empty => exact ⟨c, Protocol.Reaches.refl c, hc, by simp⟩
  | insert j T _ ih =>
    obtain ⟨d, hd, hgd, hdT⟩ := ih
    cases hj : (d j).1
    · obtain ⟨ℓ, hℓ⟩ := hgd.exists_leader
      have hne : ℓ ≠ j := fun h' => by rw [h', hj] at hℓ; exact Bool.false_ne_true hℓ
      let e : AgentPair n := ⟨(ℓ, j), hne⟩
      have he : ((d e.1.1).1 || (d e.1.2).1) = true := by simp [e, hℓ]
      refine ⟨_, hd.trans (Protocol.reaches_interact d e), hgd.step H ⟨e, rfl⟩, ?_⟩
      intro w hw
      rcases mem_insert.1 hw with rfl | hw
      · exact hgd.out_snd H e he
      · exact hgd.out_step H e (hdT w hw)
    · refine ⟨d, hd, hgd, fun w hw => ?_⟩
      rcases mem_insert.1 hw with rfl | hw
      · exact (hgd.leader w hj).2
      · exact hdT w hw

/-- **Output-stability of leader protocols.** From a good configuration the protocol reaches an
output-stable configuration with output `t L`. -/
theorem Good.exists_outputStable
    (H : ∀ y, R y → q L y = L ∧ r L y = y ∧ q y L = L ∧ r y L = y)
    {c : Fin n → Bool × Bool × V} (hc : Good t L R c) :
    ∃ d, (protocol init q r t).Reaches c d ∧ (protocol init q r t).OutputStable (t L) d := by
  obtain ⟨d, hd, hgd, hout⟩ := hc.exists_allOut H
  refine ⟨d, hd, Protocol.outputStable_of_invariant
    (I := fun c => Good t L R c ∧ ∀ w, (c w).2.1 = t L) ?_ (fun c hc w => hc.2 w) ⟨hgd, hout⟩⟩
  rintro c d ⟨hgc, hoc⟩ ⟨e, rfl⟩
  exact ⟨hgc.step H ⟨e, rfl⟩, fun w => hgc.out_step H e (hoc w)⟩

end Leader

end Crn
