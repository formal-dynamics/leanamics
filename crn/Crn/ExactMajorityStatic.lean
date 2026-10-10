import Crn.ExactMajorityOutput

/-!
# Static exact majority with ties (CRN-5, [GHMSS16, Section 2])

The protocol `P₁` of [GHMSS16, Section 2] (the majority protocol of [AADFP06], reporting ties).
Every agent has a colour in `{-1, 0, 1}` (`SignType`); the protocol decides the sign of the sum of
the colours, i.e. whether there are more `1`s than `-1`s, fewer, or as many. The six states are
the strong states `[x]` and the weak states `⟨x⟩`, `x ∈ {-1, 0, 1}`, with weight `w([x]) = x`,
`w(⟨x⟩) = 0` (Fig. 1). Transitions (Fig. 2): `[1]` and `[-1]` annihilate into `[0], [0]`; a strong
`[x]` turns a weak state into `⟨x⟩`, and a strong `[x]`, `x ≠ 0`, turns `[0]` into `⟨x⟩`; other
encounters change nothing. The table of Fig. 2 agrees with these rules (checked exhaustively).

Main statements:
* `StaticState.weight_sum_eq` (Lemma 1): the weight sum equals the colour sum.
* `StaticState.absWeight_sum_step_le`, `StaticState.exists_reaches_absWeight_sum_eq` (Lemma 2):
  `R = ∑ |w|` does not increase and can be brought down to `|∑ colours|`.
* `staticMajority_stablyComputes` (Theorem 3): the protocol stably computes the sign of
  `#1 - #(-1)`.
-/

namespace Crn

open Finset

/-- The six states of the static majority protocol [GHMSS16, Fig. 1]: strong `[x]` and weak
`⟨x⟩` for `x ∈ {-1, 0, 1}`. -/
inductive StaticState
  /-- The strong state `[x]`. -/
  | strong (x : SignType)
  /-- The weak state `⟨x⟩`. -/
  | weak (x : SignType)
  deriving DecidableEq, Fintype

namespace StaticState

/-- The weight [GHMSS16, Fig. 1]: `w([x]) = x`, `w(⟨x⟩) = 0`. -/
def weight : StaticState → ℤ
  | strong x => x
  | weak _ => 0

/-- The output (the reported sign of the colour sum): `x` in `[x]` and in `⟨x⟩`. -/
def out : StaticState → SignType
  | strong x => x
  | weak x => x

/-- The new state of an agent in state `a` meeting an agent in state `b`, outside annihilations
[GHMSS16, Section 2]: a weak state meeting `[y]` becomes `⟨y⟩`; `[0]` meeting `[y]`, `y ≠ 0`,
becomes `⟨y⟩`; otherwise nothing changes. -/
def recruit : StaticState → StaticState → StaticState
  | weak _, strong y => weak y
  | strong 0, strong y => if y = 0 then strong 0 else weak y
  | a, _ => a

/-- The transition function of [GHMSS16, Fig. 2]: `[1]` and `[-1]` annihilate into `[0], [0]`,
all other encounters recruit (`recruit`). -/
def δ : StaticState × StaticState → StaticState × StaticState
  | (strong 1, strong (-1)) => (strong 0, strong 0)
  | (strong (-1), strong 1) => (strong 0, strong 0)
  | (a, b) => (recruit a b, recruit b a)

end StaticState

/-- The static majority protocol `P₁` [GHMSS16, Section 2]: input colour `x ↦ [x]`. Its `Bool`
output (more `1`s than `-1`s) is not used; the outputs are `StaticState.out`. -/
def staticMajority : Protocol SignType StaticState where
  input := StaticState.strong
  output s := decide (s.out = 1)
  δ := StaticState.δ

/-- Six states. -/
theorem card_staticState : Fintype.card StaticState = 6 := rfl

namespace StaticState

variable {n : ℕ}

/-- Transitions preserve the total weight of the two agents [GHMSS16, proof of Lemma 1]. -/
theorem δ_weight (a b : StaticState) :
    (δ (a, b)).1.weight + (δ (a, b)).2.weight = a.weight + b.weight := by
  revert a b; decide

/-- Strong states. -/
def isStrong : StaticState → Bool
  | strong _ => true
  | weak _ => false

/-- `R = ∑ |w|` does not increase in an encounter [GHMSS16, proof of Lemma 2]. -/
theorem absWeight_δ_le (a b : StaticState) :
    |(δ (a, b)).1.weight| + |(δ (a, b)).2.weight| ≤ |a.weight| + |b.weight| := by
  revert a b; decide

/-- Only `[-1]` has a negative weight. -/
theorem weight_neg_iff {a : StaticState} : a.weight < 0 ↔ a = strong (-1) := by
  revert a; decide

/-- All states but `[1]` have a nonpositive weight. -/
theorem weight_nonpos_of_ne {a : StaticState} (h : a ≠ strong 1) : a.weight ≤ 0 := by
  revert a h; decide

/-- An encounter never removes the last strong state. -/
theorem δ_isStrong (a b : StaticState) (h : a.isStrong ∨ b.isStrong) :
    (δ (a, b)).1.isStrong ∨ (δ (a, b)).2.isStrong := by
  revert a b; decide

/-- The states reporting `s` are closed under encounters. -/
theorem δ_out (s : SignType) (a b : StaticState) (ha : a.out = s) (hb : b.out = s) :
    (δ (a, b)).1.out = s ∧ (δ (a, b)).2.out = s := by
  revert s a b; decide

/-- `[s]` recruits every state of weight `0` or `s` that does not report `s` into `⟨s⟩`. -/
theorem δ_recruit (s : SignType) (b : StaticState) (hb : b.weight = 0 ∨ b.weight = s)
    (hs : b.out ≠ s) : δ (strong s, b) = (strong s, weak s) := by
  revert s b; decide

/-- `s · w ≤ |w|` for a sign `s`. -/
theorem sign_mul_weight_le (s : SignType) (a : StaticState) : (s : ℤ) * a.weight ≤ |a.weight| := by
  revert s a; decide

/-- `|w| = s · w` for a sign `s` forces `w ∈ {0, s}`. -/
theorem weight_eq_of_abs {s : SignType} {a : StaticState} (h : |a.weight| = (s : ℤ) * a.weight) :
    a.weight = 0 ∨ a.weight = s := by
  revert s a; decide

/-- The only strong state of weight `0` is `[0]`. -/
theorem eq_strong_zero {a : StaticState} (h : a.isStrong) (h0 : a.weight = 0) : a = strong 0 := by
  revert a; decide

/-- The only state of weight `s ≠ 0` is `[s]`. -/
theorem eq_strong_of_weight {s : SignType} {a : StaticState} (h : a.weight = s) (hs : s ≠ 0) :
    a = strong s := by
  revert s a; decide

/-- **[GHMSS16, Lemma 1]** (Invariant 1). Along every execution, the sum of the weights equals the
sum of the input colours. -/
theorem weight_sum_eq {ι : Fin n → SignType} {c : Fin n → StaticState}
    (h : staticMajority.Reaches (staticMajority.input ∘ ι) c) :
    ∑ v, (c v).weight = ∑ v, ((ι v : SignType) : ℤ) := by
  refine h.invariant (I := fun c => ∑ v, (c v).weight = ∑ v, ((ι v : SignType) : ℤ)) ?_ rfl
  rintro c d hc ⟨e, rfl⟩
  have h1 := staticMajority.sum_interact weight c e
  rw [show staticMajority.δ = δ from rfl, δ_weight] at h1
  rw [← hc]
  exact add_right_cancel h1

/-- **[GHMSS16, Lemma 2]**, first part (Invariant 2). `R = ∑ |w|` does not increase along a step. -/
theorem absWeight_sum_step_le {c d : Fin n → StaticState} (h : staticMajority.Step c d) :
    ∑ v, |(d v).weight| ≤ ∑ v, |(c v).weight| := by
  obtain ⟨e, rfl⟩ := h
  have h1 := staticMajority.sum_interact (fun s => |s.weight|) c e
  have h2 := absWeight_δ_le (c e.1.1) (c e.1.2)
  simp only [show staticMajority.δ = δ from rfl] at h1
  linarith

/-- **[GHMSS16, Lemma 2]**, second part. From every reachable configuration, a configuration with
`R = |S|` is reachable, `S` the sum of the input colours. -/
theorem exists_reaches_absWeight_sum_eq {ι : Fin n → SignType} {c : Fin n → StaticState}
    (h : staticMajority.Reaches (staticMajority.input ∘ ι) c) :
    ∃ d, staticMajority.Reaches c d ∧ ∑ v, |(d v).weight| = |∑ v, ((ι v : SignType) : ℤ)| := by
  suffices H : ∃ d, staticMajority.Reaches c d ∧ ∑ v, |(d v).weight| = |∑ v, (d v).weight| by
    obtain ⟨d, hd, hR⟩ := H
    exact ⟨d, hd, by rw [hR, weight_sum_eq (h.trans hd)]⟩
  refine (exists_reflTransGen_of_measure (r := staticMajority.Step (n := n))
    (fun _ => True) (fun d => ∑ v, |(d v).weight| = |∑ v, (d v).weight|)
    (fun d => ∑ v, (d v).weight.natAbs) (fun d _ => ?_) trivial).imp fun d hd => ⟨hd.1, hd.2.2⟩
  by_cases hpair : ∃ u v, d u = strong 1 ∧ d v = strong (-1)
  · obtain ⟨u, v, hu, hv⟩ := hpair
    have huv : u ≠ v := fun h => by rw [h, hv] at hu; cases hu
    refine Or.inr ⟨staticMajority.interact d ⟨(u, v), huv⟩, ⟨_, rfl⟩, trivial, ?_⟩
    have h1 := staticMajority.sum_interact (fun s => s.weight.natAbs) d ⟨(u, v), huv⟩
    dsimp only at h1
    rw [hu, hv] at h1
    have h2 : (staticMajority.δ (strong 1, strong (-1))) = (strong 0, strong 0) := rfl
    rw [h2] at h1
    change _ + (1 + 1) = _ + (0 + 0) at h1
    omega
  · left
    by_cases hpos : ∀ v, 0 ≤ (d v).weight
    · rw [abs_of_nonneg (sum_nonneg fun v _ => hpos v)]
      exact sum_congr rfl fun v _ => abs_of_nonneg (hpos v)
    obtain ⟨v₀, hv₀⟩ := not_forall.1 hpos
    have h0 : d v₀ = strong (-1) := weight_neg_iff.1 (lt_of_not_ge hv₀)
    have hneg : ∀ v, (d v).weight ≤ 0 := fun v =>
      weight_nonpos_of_ne fun hv => hpair ⟨v, v₀, hv, h0⟩
    rw [abs_of_nonpos (sum_nonpos fun v _ => hneg v), ← sum_neg_distrib]
    exact sum_congr rfl fun v _ => abs_of_nonpos (hneg v)

end StaticState

/-- The colour sum is `#1 - #(-1)`. -/
theorem sum_signType_eq_counts {n : ℕ} (ι : Fin n → SignType) :
    ∑ v, ((ι v : SignType) : ℤ) = ((counts ι).1 1 : ℤ) - (counts ι).1 (-1) := by
  have h3 : ∀ f : SignType → ℤ, ∑ t, f t = f 0 + f (-1) + f 1 := fun f => by
    rw [show (univ : Finset SignType) = {0, -1, 1} from rfl]
    simp [add_assoc]
  rw [sum_comp_eq_sum_counts ι fun t : SignType => (t : ℤ),
    h3 fun t => (counts ι).1 t • ((t : SignType) : ℤ)]
  simp
  ring

/-- **[GHMSS16, Theorem 3]** The static majority protocol stably computes the sign of
`#1 - #(-1)`: all agents eventually and forever output `1` if there are more `1`s than `-1`s,
`-1` if fewer, and `0` (a tie) if as many. -/
theorem staticMajority_stablyComputes :
    staticMajority.StablyComputesWith StaticState.out
      fun x => SignType.sign ((x 1 : ℤ) - x (-1)) := by
  intro n hn ι c hc
  have hstrong : ∀ d, staticMajority.Reaches c d → ∃ v, (d v).isStrong := fun d hd =>
    (hc.trans hd).invariant (fun _ _ hs h => Protocol.exists_step
      (p := fun a => a.isStrong = true) StaticState.δ_isStrong h hs) ⟨⟨0, hn⟩, rfl⟩
  obtain ⟨d, hd, hR⟩ := StaticState.exists_reaches_absWeight_sum_eq hc
  have hS := StaticState.weight_sum_eq (hc.trans hd)
  rw [← hS] at hR
  obtain ⟨s, hs⟩ : ∃ s, s = SignType.sign (∑ v, (d v).weight) := ⟨_, rfl⟩
  -- every weight is `0` or `s`
  have hzero := (sum_eq_zero_iff_of_nonneg fun v _ =>
    sub_nonneg.2 (StaticState.sign_mul_weight_le s (d v))).1 (by
      rw [sum_sub_distrib, ← mul_sum, hR, hs, sign_mul_self, sub_self])
  have hok : ∀ v, (d v).weight = 0 ∨ (d v).weight = s := fun v =>
    StaticState.weight_eq_of_abs (sub_eq_zero.1 (hzero v (mem_univ v)))
  -- an agent in `[s]`
  have hwit : ∃ r, d r = .strong s := by
    by_cases hs0 : s = 0
    · obtain ⟨r, hr⟩ := hstrong d hd
      refine ⟨r, ?_⟩
      have h0 : (d r).weight = 0 := by simpa [hs0] using hok r
      rw [hs0]
      exact StaticState.eq_strong_zero hr h0
    · have hne : ∑ v, (d v).weight ≠ 0 := fun h0 => hs0 (by rw [hs, h0, sign_zero])
      obtain ⟨r, -, hr⟩ := exists_ne_zero_of_sum_ne_zero hne
      exact ⟨r, StaticState.eq_strong_of_weight ((hok r).resolve_left hr) hs0⟩
  -- `[s]` recruits every agent into `{[s], ⟨s⟩}`
  have hstep : ∀ c : Fin n → StaticState,
      ((∃ r, c r = .strong s) ∧ ∀ v, (c v).weight = 0 ∨ (c v).weight = s) →
      ∀ v, ¬ (c v).out = s → ∃ c', staticMajority.Step c c' ∧
        ((∃ r, c' r = .strong s) ∧ ∀ v, (c' v).weight = 0 ∨ (c' v).weight = s) ∧
        (c' v).out = s ∧ ∀ w, (c w).out = s → (c' w).out = s := by
    rintro c ⟨⟨r, hr⟩, hok⟩ v hv
    have hrv : r ≠ v := fun h => hv (by rw [← h, hr]; rfl)
    have happ : ∀ w, staticMajority.interact c ⟨(r, v), hrv⟩ w =
        if w = v then .weak s else if w = r then .strong s else c w := fun w => by
      rw [Protocol.interact_apply]
      dsimp only
      rw [hr, show staticMajority.δ = StaticState.δ from rfl,
        StaticState.δ_recruit s (c v) (hok v) hv]
    refine ⟨staticMajority.interact c ⟨(r, v), hrv⟩, ⟨⟨(r, v), hrv⟩, rfl⟩,
      ⟨⟨r, ?_⟩, fun w => ?_⟩, ?_, fun w hw => ?_⟩
    · rw [happ, if_neg hrv, if_pos rfl]
    · rw [happ]
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact hok w
    · rw [happ, if_pos rfl]
      rfl
    · rw [happ]
      split_ifs
      · rfl
      · rfl
      · exact hw
  obtain ⟨f, hdf, -, hf⟩ := exists_recruit (r := staticMajority.Step) _ (fun _ q => q.out = s)
    hstep ⟨hwit, hok⟩
  refine ⟨f, hd.trans hdf, Protocol.outputStableAt_of_invariant
    (I := fun c => ∀ v, (c v).out = s)
    (fun _ _ hc h => Protocol.forall_step (StaticState.δ_out s) h hc) (fun c hc v => ?_) hf⟩
  rw [hc v, hs, hS, sum_signType_eq_counts]

end Crn
