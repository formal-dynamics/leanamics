import Dynamics.Kernel

/-! # Geometric convergence from a uniform absorption block -/
namespace Dynamics.Kernel
open Filter Finset Topology
variable {α : Type*} [Fintype α]

/-- If a nonnegative survival observable contracts every `m` rounds, its
expectation has a geometric bound at multiples of `m`. -/
lemma geometric_blocks (K : Dynamics.Kernel α) (f : α → ℝ)
    (q : ℝ) (hq : 0 ≤ q) (m : ℕ)
    (hblock : ∀ a, K.iterate m f a ≤ q * f a) (n : ℕ) (a : α) :
    K.iterate (n * m) f a ≤ q ^ n * f a := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul, Nat.add_comm, K.iterate_add_time]
    calc
      K.iterate m (K.iterate (n * m) f) a ≤
          K.iterate m (fun b => q ^ n * f b) a := K.iterate_mono m ih a
      _ = q ^ n * K.iterate m f a := congrFun (K.iterate_mul m (q ^ n) f) a
      _ ≤ q ^ n * (q * f a) := mul_le_mul_of_nonneg_left (hblock a) (pow_nonneg hq n)
      _ = q ^ (n + 1) * f a := by rw [pow_succ]; ring

/-- The block bound tends to zero whenever the contraction factor is below one. -/
lemma geometric_blocks_tendsto (K : Dynamics.Kernel α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a)
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) (m : ℕ)
    (hblock : ∀ a, K.iterate m f a ≤ q * f a) (a : α) :
    Tendsto (fun n => K.iterate (n * m) f a) atTop (nhds 0) := by
  apply squeeze_zero (fun n => K.iterate_nonneg _ hf a)
    (fun n => K.geometric_blocks f q hq m hblock n a)
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1).mul_const (f a)

/-- An observable satisfying `K f ≤ f` has antitone finite-time expectations. -/
lemma iterate_antitone (K : Dynamics.Kernel α) (f : α → ℝ)
    (h : ∀ a, K.apply f a ≤ f a) (a : α) : Antitone (fun n => K.iterate n f a) := by
  apply antitone_nat_of_succ_le
  intro n
  have he : K.iterate (n + 1) f = K.iterate n (K.apply f) := by
    rw [K.iterate_add_time]
    rfl
  rw [he]
  exact K.iterate_mono n h a

/-- Finiteness turns state-dependent access into a uniform contraction block. -/
lemma exists_uniform_block [Nonempty α] (K : Dynamics.Kernel α) (f : α → ℝ)
    (hf : ∀ a, f a = 0 ∨ f a = 1) (hstep : ∀ a, K.apply f a ≤ f a)
    (haccess : ∀ a, ∃ n, K.iterate n f a < 1) :
    ∃ m : ℕ, 0 < m ∧ ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧
      ∀ a, K.iterate m f a ≤ q * f a := by
  classical
  choose n hn using haccess
  let m := (univ.sup n) + 1
  have htime (a : α) : n a ≤ m :=
    (le_sup (f := n) (mem_univ a)).trans (Nat.le_succ _)
  have hlt (a : α) : K.iterate m f a < 1 :=
    (K.iterate_antitone f hstep a (htime a)).trans_lt (hn a)
  have hnonneg (a : α) : 0 ≤ f a := by rcases hf a with h | h <;> simp [h]
  let q := univ.sup' univ_nonempty (fun a => K.iterate m f a)
  have hle (a : α) : K.iterate m f a ≤ q := le_sup' _ (mem_univ a)
  refine ⟨m, Nat.succ_pos _, q, ?_, ?_, fun a => ?_⟩
  · obtain ⟨a⟩ := ‹Nonempty α›
    exact (K.iterate_nonneg m hnonneg a).trans (hle a)
  · exact (sup'_lt_iff univ_nonempty).mpr (fun a _ => hlt a)
  · rcases hf a with ha | ha
    · have hz := K.iterate_antitone f hstep a (Nat.zero_le m)
      simpa [ha] using hz
    · simpa [ha] using hle a

/-- An accessible absorbing target in a finite chain has vanishing survival probability.
`f` is its complement indicator; `hstep` expresses absorption and `haccess` access. -/
theorem finite_absorption [Nonempty α] (K : Dynamics.Kernel α) (f : α → ℝ)
    (hf : ∀ a, f a = 0 ∨ f a = 1) (hstep : ∀ a, K.apply f a ≤ f a)
    (haccess : ∀ a, ∃ n, K.iterate n f a < 1) (a : α) :
    Tendsto (fun n => K.iterate n f a) atTop (𝓝 0) := by
  obtain ⟨m, hm, q, hq, hq1, hblock⟩ := K.exists_uniform_block f hf hstep haccess
  have hnonneg (a : α) : 0 ≤ f a := by rcases hf a with h | h <;> simp [h]
  have hb := K.geometric_blocks_tendsto f hnonneg q hq hq1 m hblock a
  apply squeeze_zero (fun n => K.iterate_nonneg n hnonneg a)
    (fun n => K.iterate_antitone f hstep a (Nat.div_mul_le_self n m))
  apply hb.comp
  exact tendsto_atTop.mpr (fun b => eventually_atTop.mpr ⟨b * m, fun n hn => (Nat.le_div_iff_mul_le hm).mpr hn⟩)

end Dynamics.Kernel
