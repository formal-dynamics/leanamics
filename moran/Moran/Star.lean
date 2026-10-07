import Moran.StarFixation

/-! # Exact fixation on the star; the star is an amplifier (MOR-3, first item)

Birth–death Moran process (`moranKernel`, mutants of fitness `r`) on the star with `n` leaves,
`starGraph c` on a vertex type with `n + 1` elements. Write `q = starRatio n r` and
`κ = starCentreWeight n r`. Then:

* the potential `q ^ (#mutant leaves) * κ ^ [centre is mutant]` is invariant in expectation
  (`star_potential_invariant`), so for `r ≠ 1` the fixation probability from any configuration
  `s` is `(1 - Φ s) / (1 - Φ (all mutant))` (`star_fixation`), as in the isothermal theorem;
* a single mutant fixes with probability `(1 - q) / (1 - κ q ^ n)` from a leaf
  (`star_fixation_leaf`), `(1 - κ) / (1 - κ q ^ n)` from the centre (`star_fixation_centre`), and
  the average of these from a uniformly random vertex (`star_fixation_uniform`), which is the
  exact formula of Broom and Rychtář (2008, §5) (`star_fixation_uniform_sum`);
* for every `n ≥ 2` the star is an amplifier of selection: from a uniformly random vertex an
  advantageous mutant (`r > 1`) fixes with larger probability than in Moran's well-mixed
  population, `(1 - 1/r) / (1 - 1/r^N)` with `N = n + 1` (`star_amplifier`), and a
  disadvantageous one (`r < 1`) with smaller probability (`star_amplifier_deleterious`);
* as `n → ∞` the fixation probability tends to `1 - 1/r^2` for `r > 1`: the star amplifies `r`
  to `r ^ 2` (Lieberman, Hauert and Nowak 2005) (`star_fixation_uniform_tendsto`).

The fixation probability is the supremum of the finite-time fixation probabilities (`fixation`),
as in `Moran.Isothermal`; no path-space measure is used.
-/

namespace Moran
open Dynamics Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Invariance on the star.** On the star centred at `c` with `n` leaves, the potential
`q ^ (#mutant leaves) * κ ^ [centre is mutant]`, with `q = (n + r) / (r (n r + 1))` and
`κ = (n r + 1) / (r (n + r))`, is preserved in expectation by one Birth–death step. This
encodes the system (5.1)–(5.2) of Broom–Rychtář (2008). -/
theorem star_potential_invariant [Nonempty V] (c : V) {n : ℕ} (hn : Fintype.card V = n + 1)
    {r : ℝ} (hr : 0 < r) (s : Config V) :
    (moranKernel (starGraph c) r hr).apply (starPotential c n r) s = starPotential c n r s :=
  starPotential_apply c hn hr s

/-- **Fixation on the star from any configuration** (Broom–Rychtář 2008, §5, solved in closed
form). For `r ≠ 1`, the fixation probability from `s` is `(1 - Φ s) / (1 - Φ (all mutant))` for
the star potential `Φ`; explicitly `(1 - q ^ i) / (1 - κ q ^ n)` from `i` mutant leaves and a
resident centre, and `(1 - κ q ^ i) / (1 - κ q ^ n)` from `i` mutant leaves and a mutant centre. -/
theorem star_fixation [Nonempty V] (c : V) {n : ℕ} (hn : Fintype.card V = n + 1) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≠ 1) (s : Config V) :
    fixation (moranKernel (starGraph c) r hr) s =
      (1 - starPotential c n r s) / (1 - starPotential c n r (fun _ => true)) :=
  star_fixation_eq c hn hr hr1 s

/-- **Single mutant on a leaf** (Broom–Rychtář 2008, §5). For `r ≠ 1`, a single mutant on a leaf
of the star with `n` leaves fixes with probability `(1 - q) / (1 - κ q ^ n)`, where
`q = (n + r) / (r (n r + 1))` and `κ = (n r + 1) / (r (n + r))`. -/
theorem star_fixation_leaf [Nonempty V] (c : V) {n : ℕ} (hn : Fintype.card V = n + 1) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≠ 1) {v : V} (hv : v ≠ c) :
    fixation (moranKernel (starGraph c) r hr) (fun w => decide (w = v)) =
      (1 - starRatio n r) / (1 - starCentreWeight n r * starRatio n r ^ n) :=
  star_fixation_single_leaf c hn hr hr1 hv

/-- **Single mutant at the centre** (Broom–Rychtář 2008, §5). For `r ≠ 1`, a single mutant at the
centre of the star with `n` leaves fixes with probability `(1 - κ) / (1 - κ q ^ n)`, where
`q = (n + r) / (r (n r + 1))` and `κ = (n r + 1) / (r (n + r))`. -/
theorem star_fixation_centre [Nonempty V] (c : V) {n : ℕ} (hn : Fintype.card V = n + 1) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≠ 1) :
    fixation (moranKernel (starGraph c) r hr) (fun w => decide (w = c)) =
      (1 - starCentreWeight n r) / (1 - starCentreWeight n r * starRatio n r ^ n) :=
  star_fixation_single_centre c hn hr hr1

/-- **Single mutant at a uniformly random vertex** (Broom–Rychtář 2008, §5, closed form). For
`r ≠ 1`, a single mutant placed at a uniformly random vertex of the star with `n` leaves fixes
with probability `(n (1 - q) + (1 - κ)) / ((n + 1) (1 - κ q ^ n))`. -/
theorem star_fixation_uniform [Nonempty V] (c : V) {n : ℕ} (hn : Fintype.card V = n + 1) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≠ 1) :
    (Distribution.uniform V).expect
        (fun v => fixation (moranKernel (starGraph c) r hr) (fun w => decide (w = v))) =
      (n * (1 - starRatio n r) + (1 - starCentreWeight n r)) /
        ((n + 1) * (1 - starCentreWeight n r * starRatio n r ^ n)) :=
  star_fixation_uniform_eq c hn hr hr1

/-- **The formula of Broom and Rychtář** (2008, §5, the average fixation probability displayed
after (5.3)), for every `r > 0`, including the neutral case `r = 1`: from a uniformly random
vertex of the star with `n` leaves, a single mutant fixes with probability
`(n · n r/(n r + 1) + r/(r + n)) / ((n + 1) (1 + n/(n + r) · ∑_{j=1}^{n-1} q ^ j))`,
where `q = (n + r) / (r (n r + 1))`. -/
theorem star_fixation_uniform_sum [Nonempty V] (c : V) {n : ℕ} (hn : Fintype.card V = n + 1)
    {r : ℝ} (hr : 0 < r) :
    (Distribution.uniform V).expect
        (fun v => fixation (moranKernel (starGraph c) r hr) (fun w => decide (w = v))) =
      (n * (n * r / (n * r + 1)) + r / (r + n)) /
        ((n + 1) * (1 + n / (n + r) * ∑ j ∈ Ico 1 n, ((n + r) / (r * (n * r + 1))) ^ j)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · -- a single vertex: the mutant has already fixed
    have hsub : ∀ v w : V, w = v := fun v w => Fintype.card_le_one_iff.mp (le_of_eq hn) w v
    have hfun : ∀ v : V, (fun w => decide (w = v)) = fun _ => true :=
      fun v => funext fun w => by simp [hsub v w]
    simp_rw [hfun, fixation_true, Distribution.expect_const]
    simp [hr.ne']
  · by_cases hr1 : r = 1
    · subst hr1
      haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
      rw [neutral_uniform_fixation _ (connected_starGraph c) hr, star_sum_neutral hn1, hn,
        Nat.cast_add, Nat.cast_one]
    · rw [star_fixation_uniform_eq c hn hr hr1, star_closed_eq_sum hn1 hr hr1]

/-- **The star is an amplifier of selection** (Lieberman–Hauert–Nowak 2005; observed for all
tested `n` and `r` by Broom–Rychtář 2008). For every star with `n ≥ 2` leaves and every
`r > 1`, a single advantageous mutant at a uniformly random vertex fixes with strictly larger
probability than in Moran's well-mixed population of the same size `N = n + 1`, whose fixation
probability is `(1 - 1/r) / (1 - 1/r^N)` (Broom–Rychtář 2008, (1.1)). -/
theorem star_amplifier [Nonempty V] (c : V) {n : ℕ} (hn : Fintype.card V = n + 1) (hn2 : 2 ≤ n)
    {r : ℝ} (hr : 0 < r) (hr1 : 1 < r) :
    (1 - 1 / r) / (1 - (1 / r) ^ Fintype.card V) <
      (Distribution.uniform V).expect
        (fun v => fixation (moranKernel (starGraph c) r hr) (fun w => decide (w = v))) := by
  have h := star_amplifier_sign hn2 hr hr1.ne'
  rw [hn, star_fixation_uniform_eq c hn hr hr1.ne']
  have hpos : 0 < 1 - 1 / r := by rw [sub_pos, div_lt_one hr]; exact hr1
  exact sub_pos.mp ((pos_iff_pos_of_mul_pos h).mp hpos)

/-- **The star suppresses disadvantageous mutants** (the other half of the amplifier property
of Lieberman–Hauert–Nowak 2005). For every star with `n ≥ 2` leaves and every `0 < r < 1`, a
single disadvantageous mutant at a uniformly random vertex fixes with strictly smaller
probability than in Moran's well-mixed population of the same size `N = n + 1`,
`(1 - 1/r) / (1 - 1/r^N)`. -/
theorem star_amplifier_deleterious [Nonempty V] (c : V) {n : ℕ} (hn : Fintype.card V = n + 1)
    (hn2 : 2 ≤ n) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    (Distribution.uniform V).expect
        (fun v => fixation (moranKernel (starGraph c) r hr) (fun w => decide (w = v))) <
      (1 - 1 / r) / (1 - (1 / r) ^ Fintype.card V) := by
  have h := star_amplifier_sign hn2 hr hr1.ne
  rw [hn, star_fixation_uniform_eq c hn hr hr1.ne]
  have hneg : 1 - 1 / r < 0 := by rw [sub_neg, one_lt_div hr]; exact hr1
  exact sub_neg.mp ((neg_iff_neg_of_mul_pos h).mp hneg)

/-- **Large stars amplify `r` to `r ^ 2`** (Lieberman–Hauert–Nowak 2005, whose large-`n`
approximation `(1 - 1/r^2) / (1 - 1/r^(2N))` is quoted as (1.2) in Broom–Rychtář 2008). For
`r > 1`, the fixation probability of a single mutant at a uniformly random vertex of the star
with `n` leaves (on `Fin (n + 1)`, centred at `0`) tends to `1 - 1/r^2` as `n → ∞`. -/
theorem star_fixation_uniform_tendsto {r : ℝ} (hr : 0 < r) (hr1 : 1 < r) :
    Filter.Tendsto
      (fun n : ℕ => (Distribution.uniform (Fin (n + 1))).expect
        (fun v => fixation (moranKernel (starGraph (0 : Fin (n + 1))) r hr)
          (fun w => decide (w = v))))
      Filter.atTop (nhds (1 - 1 / r ^ 2)) := by
  refine (star_closed_tendsto hr1).congr fun n => ?_
  exact (star_fixation_uniform_eq (0 : Fin (n + 1)) (by simp) hr hr1.ne').symm

end Moran
