/-
Copyright (c) 2026 Romain Popescu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Romain Popescu
-/
import ConwayGolden.Subprime.Extension

/-!
# Increasing a profile when the maximum runs ahead

A profile with ratio `λ < φ` at `(j, L)` propagates at rate `λ`, whereas the maxima `genMax`
may grow at rate up to `φ`. This file shows that whenever the maximum is ahead of the profile,
`genMax j > (1 + δ) L`, the profile can be *increased by a fixed factor* `1 + κ` within three
generations. This is the mechanism that keeps profiles close to the maxima in the bounded-step
comparison of `ConwayGolden.Subprime.Comparison`.

The argument: the first maximum `t` exceeding `(1 + δ) L` is a prime in `((1 + δ) L, 2 (1 + δ) L]`
present in `gen j`. For an integer `u` in a suitable interval `U`, the odd target `N = 2 u - t` is
admissible for `N = 2 p + q` with `p ∈ [(λ - 2a) L, (λ - a) L] ⊆ gen (j + 1)` and
`q ∈ [(1 - 5a) L, (1 - a/2) L] ⊆ gen j`; the restricted binary hypothesis `RestrictedBinary 2`
then shows that all but `o(L / log L)` primes `u ∈ U` are generated as `u = p + (t + q) / 2` in
`gen (j + 2)`. Pairing such a `u` with a complement `r - u` in the buffered filled range of
`gen (j + 2)` produces every prime `r ≤ (λ³ + δ/8) L` in `gen (j + 3)`, and one proportional
extension turns this into a profile at `(j + 3, (1 + κ) λ³ L)`.

Since the hypothesis `RestrictedBinary 2` has fixed parameters, the ratio `t / L ∈ (1 + δ, 2 + 2δ]`
is rounded down to a finite grid of mesh `δ / 200`; the interval `U` depends on the grid point.

## Main definitions

* `Conway.boostGain δ λ`: the factor `κ = δ / (8 λ² (λ + 1))` by which the profile increases.

## Main statements

* `Conway.eventually_profile_boost`: for `0 < δ ≤ 1/10`, `8/5 ≤ λ < φ` and all large `L`, a
  profile at `(j, L)` with `genMax j > (1 + δ) L` yields a profile at `(j + 3, (1 + κ) λ³ L)`.
-/

namespace Conway

open Filter Finset Real Topology
open scoped goldenRatio

/-- The relative increase of the profile produced by `eventually_profile_boost`. -/
noncomputable def boostGain (δ lam : ℝ) : ℝ := δ / (8 * lam ^ 2 * (lam + 1))

/-! ### Numerical facts about `λ ∈ [8/5, φ)` -/

theorem goldenRatio_lt_five_thirds : φ < 5 / 3 := by
  nlinarith [goldenRatio_sq, goldenRatio_pos]

/-- `λ³ ≤ 2 λ + 1` for `8/5 ≤ λ ≤ φ`, since `φ³ = 2 φ + 1`. -/
theorem pow_three_le_of_le_goldenRatio {lam : ℝ} (h1 : 8 / 5 ≤ lam) (hφ : lam ≤ φ) :
    lam ^ 3 ≤ 2 * lam + 1 := by
  have hsq := goldenRatio_sq
  have hcube : φ ^ 3 = 2 * φ + 1 := by linear_combination (φ + 1) * hsq
  have hfac : lam ^ 3 - 2 * lam - 1 = (lam - φ) * (lam ^ 2 + φ * lam + φ ^ 2 - 2) := by
    linear_combination hcube
  have hpos : 0 < lam ^ 2 + φ * lam + φ ^ 2 - 2 := by nlinarith [goldenRatio_pos]
  nlinarith [mul_nonpos_of_nonpos_of_nonneg (by linarith : lam - φ ≤ 0) hpos.le]

/-- `λ³ - λ ≥ 312 / 125` for `λ ≥ 8/5`. -/
theorem le_pow_three_sub {lam : ℝ} (h1 : 8 / 5 ≤ lam) : 312 / 125 ≤ lam ^ 3 - lam := by
  nlinarith [mul_nonneg (by linarith : 0 ≤ lam - 8 / 5)
    (by nlinarith : 0 ≤ lam ^ 2 + 8 / 5 * lam + 39 / 25)]

theorem boostGain_pos {δ lam : ℝ} (hδ : 0 < δ) (hlam : 0 < lam) : 0 < boostGain δ lam := by
  unfold boostGain
  positivity

/-- The identity `(1 - ε) (λ³ + δ/8 + λ²) = (1 + κ) λ⁴` for `1 - ε = λ² / (λ + 1)`. -/
theorem boostGain_identity {δ lam : ℝ} (hlam : 0 < lam) :
    lam ^ 2 / (lam + 1) * ((lam ^ 3 + δ / 8) + lam ^ 2) = (1 + boostGain δ lam) * lam ^ 4 := by
  unfold boostGain
  field_simp
  ring

/-- `(1 + κ) λ³ ≤ λ³ + δ / 8`. -/
theorem boostGain_mul_pow_three_le {δ lam : ℝ} (hδ : 0 ≤ δ) (hlam : 0 < lam) :
    (1 + boostGain δ lam) * lam ^ 3 ≤ lam ^ 3 + δ / 8 := by
  unfold boostGain
  rw [add_mul, one_mul, add_le_add_iff_left, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith [pow_pos hlam 3, pow_pos hlam 2]

/-! ### The grid of ratios `t / L` -/

/-- A finite grid of mesh `δ / 200` covering `[1 + δ, 2 + 2 δ]` from below. -/
noncomputable def boostGrid (δ : ℝ) : Finset ℝ :=
  {T ∈ (range (⌈(1 + δ) / (δ / 200)⌉₊ + 1)).image (fun k : ℕ ↦ 1 + δ + k * (δ / 200)) |
    T ≤ 2 + 2 * δ}

theorem one_add_le_of_mem_boostGrid {δ T : ℝ} (hδ : 0 < δ) (hT : T ∈ boostGrid δ) : 1 + δ ≤ T := by
  simp only [boostGrid, mem_filter, mem_image, mem_range] at hT
  obtain ⟨⟨k, -, rfl⟩, -⟩ := hT
  have : (0 : ℝ) ≤ k * (δ / 200) := by positivity
  linarith

theorem le_of_mem_boostGrid {δ T : ℝ} (hT : T ∈ boostGrid δ) : T ≤ 2 + 2 * δ :=
  (mem_filter.mp hT).2

/-- Every `τ ∈ [1 + δ, 2 + 2 δ]` is within `δ / 200` above some grid point. -/
theorem exists_mem_boostGrid {δ τ : ℝ} (hδ : 0 < δ) (h1 : 1 + δ ≤ τ) (h2 : τ ≤ 2 + 2 * δ) :
    ∃ T ∈ boostGrid δ, T ≤ τ ∧ τ ≤ T + δ / 200 := by
  have hmesh : 0 < δ / 200 := by positivity
  set k : ℕ := ⌊(τ - (1 + δ)) / (δ / 200)⌋₊ with hk
  have hnonneg : 0 ≤ (τ - (1 + δ)) / (δ / 200) := div_nonneg (by linarith) hmesh.le
  have hk1 : (k : ℝ) ≤ (τ - (1 + δ)) / (δ / 200) := Nat.floor_le hnonneg
  have hk2 : (τ - (1 + δ)) / (δ / 200) < k + 1 := Nat.lt_floor_add_one _
  rw [le_div_iff₀ hmesh] at hk1
  rw [div_lt_iff₀ hmesh] at hk2
  refine ⟨1 + δ + k * (δ / 200), ?_, by linarith, by linarith⟩
  simp only [boostGrid, mem_filter, mem_image, mem_range]
  refine ⟨⟨k, ?_, rfl⟩, by linarith⟩
  have hkle : (k : ℝ) ≤ (1 + δ) / (δ / 200) := by
    rw [le_div_iff₀ hmesh]
    linarith
  have := Nat.le_ceil ((1 + δ) / (δ / 200))
  have : (k : ℝ) < ⌈(1 + δ) / (δ / 200)⌉₊ + 1 := by linarith
  exact_mod_cast this

/-! ### Interval arithmetic for the boost -/

section IntervalArithmetic

variable {δ lam T L t u v r : ℝ}

/-- For `p ∈ [(λ - 2a) L, (λ - a) L]`, the complement `q = 2 u - t - 2 p` lies in
`[(1 - 5a) L, (1 - a/2) L]`. Here `a = δ / 100`. -/
theorem boost_q_mem (ht1 : T * L ≤ t) (ht2 : t ≤ (T + δ / 200) * L)
    (hu1 : (lam + (T + 1) / 2 - 3 * (δ / 100)) * L ≤ u)
    (hu2 : u ≤ (lam + (T + 1) / 2 - 5 / 2 * (δ / 100)) * L)
    (hv1 : (lam - 2 * (δ / 100)) * L ≤ v) (hv2 : v ≤ (lam - δ / 100) * L) :
    (1 - 5 * (δ / 100)) * L ≤ 2 * u - t - 2 * v ∧ 2 * u - t - 2 * v ≤ (1 - δ / 200) * L := by
  constructor <;> nlinarith

/-- The target `N = 2 u - t` is positive and at most `6 L`. -/
theorem boost_target_bounds (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 10) (h1 : 8 / 5 ≤ lam) (h2 : lam < 5 / 3)
    (hL : 0 < L) (ht1 : T * L ≤ t) (ht2 : t ≤ (T + δ / 200) * L)
    (hu1 : (lam + (T + 1) / 2 - 3 * (δ / 100)) * L ≤ u)
    (hu2 : u ≤ (lam + (T + 1) / 2 - 5 / 2 * (δ / 100)) * L) :
    t < 2 * u ∧ 2 * u - t ≤ 6 * L := by
  constructor <;> nlinarith

/-- The complement `v = r - u` of a target prime `r ∈ [λ³ L, (λ³ + δ/8) L]` lies in
`[L / 2, (λ - δ/4) L]`. -/
theorem boost_v_bounds (hδ1 : δ ≤ 1 / 10) (h1 : 8 / 5 ≤ lam) (hφ : lam < φ)
    (hL : 0 < L) (hT1 : 1 + δ ≤ T) (hT2 : T ≤ 2 + 2 * δ)
    (hu1 : (lam + (T + 1) / 2 - 3 * (δ / 100)) * L ≤ u)
    (hu2 : u ≤ (lam + (T + 1) / 2 - 5 / 2 * (δ / 100)) * L)
    (hr1 : lam ^ 3 * L ≤ r) (hr2 : r ≤ (lam ^ 3 + δ / 8) * L) :
    L / 2 ≤ r - u ∧ r - u ≤ (lam - δ / 4) * L := by
  have hc := pow_three_le_of_le_goldenRatio h1 hφ.le
  have hc' := le_pow_three_sub h1
  have e1 : (1 + δ) * L ≤ T * L := mul_le_mul_of_nonneg_right hT1 hL.le
  have e2 : T * L ≤ (2 + 2 * δ) * L := mul_le_mul_of_nonneg_right hT2 hL.le
  have e3 : δ * L ≤ 1 / 10 * L := mul_le_mul_of_nonneg_right hδ1 hL.le
  have e4 : lam ^ 3 * L ≤ (2 * lam + 1) * L := mul_le_mul_of_nonneg_right hc hL.le
  have e5 : 312 / 125 * L ≤ (lam ^ 3 - lam) * L := mul_le_mul_of_nonneg_right hc' hL.le
  constructor <;> nlinarith

end IntervalArithmetic

/-! ### The boost at a fixed grid point -/

section Boost

variable {δ lam : ℝ}

/-- The primes in the candidate interval `U_T L = [(λ + (T+1)/2 - 3a) L, (λ + (T+1)/2 - 5a/2) L]`
that are missing from `gen (j + 2)` inject, via `u ↦ 2 u - t`, into the exceptional set of the
restricted problem `N = 2 p + q` at scale `L`. -/
theorem card_boost_missing_le (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 10) (h1 : 8 / 5 ≤ lam) (hφ : lam < φ)
    {T L : ℝ} (hL : 4 ≤ L) (hT1 : 1 + δ ≤ T) {j t : ℕ} (hprof : Profile lam j L)
    (ht : t ∈ gen j) (htodd : Odd t) (ht1 : T * L ≤ t) (ht2 : (t : ℝ) ≤ (T + δ / 200) * L) :
    #{u ∈ Nat.primesIcc ((lam + (T + 1) / 2 - 3 * (δ / 100)) * L)
        ((lam + (T + 1) / 2 - 5 / 2 * (δ / 100)) * L) | u ∉ gen (j + 2)} ≤
      #(exceptionalSet 2 (lam - 2 * (δ / 100)) (lam - δ / 100) (1 - 5 * (δ / 100))
        (1 - δ / 200) (δ / 100) 6 L) := by
  have hL0 : 0 < L := by linarith
  have h53 : lam < 5 / 3 := hφ.trans goldenRatio_lt_five_thirds
  have ht3 : 3 ≤ t := by
    have : (3 : ℝ) ≤ t := by nlinarith [mul_le_mul_of_nonneg_right hT1 hL0.le]
    exact_mod_cast this
  refine card_le_card_of_injOn (fun u ↦ 2 * u - t) ?_ ?_
  · intro u hu
    rw [mem_coe, mem_filter, Nat.mem_primesIcc] at hu
    obtain ⟨⟨hup, hu1, hu2⟩, hun⟩ := hu
    obtain ⟨htu, hN6⟩ := boost_target_bounds hδ0 hδ1 h1 h53 hL0 ht1 ht2 hu1 hu2
    have htu' : t ≤ 2 * u := by
      have : (t : ℝ) < 2 * u := htu
      exact_mod_cast this.le
    have hcast : ((2 * u - t : ℕ) : ℝ) = 2 * u - t := by push_cast [htu']; ring
    show 2 * u - t ∈ exceptionalSet 2 _ _ _ _ _ 6 L
    rw [mem_exceptionalSet]
    refine ⟨mem_Icc.mpr ⟨?_, Nat.le_floor ?_⟩, ?_, ?_, ?_⟩
    · have : t < 2 * u := by exact_mod_cast htu
      omega
    · rw [hcast]; linarith
    · have : Odd (2 * u - t) := by
        rw [Nat.odd_sub htu']
        exact ⟨fun h ↦ absurd h (Nat.not_odd_iff_even.mpr (even_two_mul u)),
          fun h ↦ absurd h (Nat.not_even_iff_odd.mpr htodd)⟩
      exact this.add_even even_two
    · refine ⟨(lam - 2 * (δ / 100)) * L, le_rfl, by nlinarith, ?_⟩
      intro v hv1 hv2
      rw [hcast]
      have hv2' : v ≤ (lam - δ / 100) * L := by linarith
      have := boost_q_mem ht1 ht2 hu1 hu2 hv1 hv2'
      push_cast
      constructor <;> linarith [this.1, this.2]
    · rintro ⟨p, q, hp, hq, hpq⟩
      rw [Nat.mem_primesIcc] at hp hq
      have hpC : p ∈ gen (j + 1) := hprof.right p hp.1 (by nlinarith [hp.2.2])
      have hqC : q ∈ gen j := hprof.left q hq.1 (by nlinarith [hq.2.2])
      have hq3 : 3 ≤ q := by
        have : (3 : ℝ) ≤ q := by nlinarith [hq.2.1, mul_le_mul_of_nonneg_right hδ1 hL0.le]
        exact_mod_cast this
      have hqodd : Odd q := hq.1.odd_of_ne_two (by omega)
      exact hun (mem_gen_add_two_of_two_mul_eq ht hqC hpC htodd hqodd ht3 hup (by omega))
  · intro u hu u' hu' huu'
    rw [mem_coe, mem_filter, Nat.mem_primesIcc] at hu hu'
    have h1u := (boost_target_bounds hδ0 hδ1 h1 h53 hL0 ht1 ht2 hu.1.2.1 hu.1.2.2).1
    have h1u' := (boost_target_bounds hδ0 hδ1 h1 h53 hL0 ht1 ht2 hu'.1.2.1 hu'.1.2.2).1
    have : t ≤ 2 * u := by
      have : (t : ℝ) ≤ 2 * u := h1u.le
      exact_mod_cast this
    have : t ≤ 2 * u' := by
      have : (t : ℝ) ≤ 2 * u' := h1u'.le
      exact_mod_cast this
    simp only at huu'
    omega

/-- **Boost at a grid point.** For fixed `T ∈ [1 + δ, 2 + 2δ]` and all large `L`: given a profile at
`(j, L)` and an odd prime `t ∈ gen j` with `t / L ∈ [T, T + δ/200]`, every prime
`r ∈ (λ³ L, (λ³ + δ/8) L]` lies in `gen (j + 3)`. -/
theorem eventually_mem_gen_add_three_of_boost (h : Hypotheses) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 10)
    (h1 : 8 / 5 ≤ lam) (hφ : lam < φ) {T : ℝ} (hT1 : 1 + δ ≤ T) (hT2 : T ≤ 2 + 2 * δ) :
    ∀ᶠ L : ℝ in atTop, ∀ j t : ℕ, Profile lam j L → t ∈ gen j → Odd t →
      T * L ≤ t → (t : ℝ) ≤ (T + δ / 200) * L →
      ∀ r : ℕ, r.Prime → lam ^ 3 * L < r → (r : ℝ) ≤ (lam ^ 3 + δ / 8) * L → r ∈ gen (j + 3) := by
  have hlam0 : 0 < lam := by linarith
  have h53 : lam < 5 / 3 := hφ.trans goldenRatio_lt_five_thirds
  -- The candidate interval and its prime count.
  set α : ℝ := lam + (T + 1) / 2 - 3 * (δ / 100) with hα
  set β : ℝ := lam + (T + 1) / 2 - 5 / 2 * (δ / 100) with hβ
  obtain ⟨c, hc, hcev⟩ := h.primesIcc_lower α β (by rw [hα]; linarith) (by rw [hα, hβ]; linarith)
  -- The exceptional set of the `2 p + q` problem is small.
  have hexc := h.restrictedBinary_two (lam - 2 * (δ / 100)) (lam - δ / 100) (1 - 5 * (δ / 100))
    (1 - δ / 200) (δ / 100) 6 (by linarith) (by linarith) (by linarith) (by linarith)
    (by positivity) (by norm_num)
  have hexc' : ∀ᶠ L : ℝ in atTop,
      (#(exceptionalSet 2 (lam - 2 * (δ / 100)) (lam - δ / 100) (1 - 5 * (δ / 100))
        (1 - δ / 200) (δ / 100) 6 L) : ℝ) ≤ c / 4 * (L / log L) := by
    filter_upwards [(tendsto_order.mp hexc).2 _ (by positivity : (0 : ℝ) < c / 4),
      eventually_gt_atTop 1] with L hL hL1
    exact (div_le_iff₀ (div_pos (by linarith) (log_pos hL1))).mp hL.le
  -- Buffered filling at scale `λ L` with buffer `θ = δ / (4 λ)`.
  set θ : ℝ := δ / (4 * lam) with hθ
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ < 1 := by
    rw [hθ, div_lt_one (by positivity)]
    linarith
  have hfill := h.restrictedBinary_one.eventually_holes_le hθ0 hθ1
    (ε := c / (4 * lam)) (by positivity)
  have hfill' := (tendsto_id.const_mul_atTop' hlam0 : Tendsto (fun L : ℝ ↦ lam * L) atTop atTop)
    |>.eventually hfill
  filter_upwards [hcev, hexc', hfill', eventually_ge_atTop 4, eventually_ge_atTop (exp 1)]
    with L hprimes hexcL hfillL hL4 hLe
  intro j t hprof ht htodd ht1 ht2 r hr hr1 hr2
  have hL0 : 0 < L := by linarith
  have hL1 : 1 < L := by linarith
  have hlogL : 0 < log L := log_pos hL1
  have hLlog : 0 < L / log L := div_pos hL0 hlogL
  -- The candidates and the two exclusions.
  set U := Nat.primesIcc (α * L) (β * L) with hU
  have hmissing : (#{u ∈ U | u ∉ gen (j + 2)} : ℝ) ≤ c / 4 * (L / log L) :=
    (Nat.cast_le.mpr (card_boost_missing_le hδ0 hδ1 h1 hφ hL4 hT1 hprof ht htodd ht1 ht2)).trans
      hexcL
  have hholes : (holes (j + 2) ⌊(lam - δ / 4) * L⌋₊ : ℝ) ≤ c / 4 * (L / log L) := by
    have hid : (1 - θ) * (lam * L) = (lam - δ / 4) * L := by
      rw [hθ]
      field_simp
    have := hfillL (j + 1) hprof.right
    rw [hid] at this
    refine this.trans ?_
    have hlogle : log L ≤ log (lam * L) :=
      log_le_log hL0 (le_mul_of_one_le_left hL0.le (by linarith))
    have heq : c / (4 * lam) * (lam * L / log (lam * L)) = c / 4 * (L / log (lam * L)) := by
      field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hL0.le hlogL hlogle)
      (by positivity)
  -- Complements `r - u` lie in `[1, (λ - δ/4) L]`.
  have hUbounds : ∀ u ∈ U, L / 2 ≤ (r : ℝ) - u ∧ (r : ℝ) - u ≤ (lam - δ / 4) * L := by
    intro u hu
    rw [hU, Nat.mem_primesIcc] at hu
    exact boost_v_bounds hδ1 h1 hφ hL0 hT1 hT2 hu.2.1 hu.2.2 hr1.le hr2
  have hUle : ∀ u ∈ U, u ≤ r := fun u hu ↦ by
    have := (hUbounds u hu).1
    have : (u : ℝ) ≤ r := by linarith
    exact_mod_cast this
  have hmaps : ∀ u ∈ U, r - u ∈ Icc 1 ⌊(lam - δ / 4) * L⌋₊ := by
    intro u hu
    obtain ⟨hv1, hv2⟩ := hUbounds u hu
    refine mem_Icc.mpr ⟨?_, Nat.le_floor ?_⟩
    · have : (u : ℝ) < r := by linarith
      have : u < r := by exact_mod_cast this
      omega
    · rw [Nat.cast_sub (hUle u hu)]
      exact hv2
  have hinj : Set.InjOn (fun u ↦ r - u) U := by
    intro u hu u' hu' huu'
    have := hUle u hu
    have := hUle u' hu'
    simp only at huu'
    omega
  have hcount : #{u ∈ U | u ∉ gen (j + 2)} + holes (j + 2) ⌊(lam - δ / 4) * L⌋₊ < #U := by
    have hprimes' : c * (L / log L) ≤ #U := hprimes
    have : (#{u ∈ U | u ∉ gen (j + 2)} : ℝ) + holes (j + 2) ⌊(lam - δ / 4) * L⌋₊ < #U := by
      nlinarith [mul_pos hc hLlog]
    exact_mod_cast this
  obtain ⟨u, hu, huC, hruC⟩ := exists_mem_gen_and_apply_mem_gen_of_lt hinj hmaps hcount
  have hur : u ≤ r := hUle u hu
  have := add_mem_gen_succ_of_prime huC hruC (by rwa [Nat.add_sub_cancel' hur])
  rwa [Nat.add_sub_cancel' hur] at this

/-- The first maximum exceeding a bound `M` is a prime in `(M, 2 M]`, present in every later
generation. -/
theorem exists_genMax_mem_Ioc {j : ℕ} {M : ℝ} (hM : 1 ≤ M) (hj : M < genMax j) :
    ∃ t : ℕ, t ∈ gen j ∧ t.Prime ∧ M < t ∧ (t : ℝ) ≤ 2 * M := by
  classical
  have hex : ∃ i, M < genMax i := ⟨j, hj⟩
  have hi_spec : M < genMax (Nat.find hex) := Nat.find_spec hex
  have hij : Nat.find hex ≤ j := Nat.find_min' hex hj
  obtain ⟨i', hi'⟩ : ∃ i', Nat.find hex = i' + 1 := by
    refine Nat.exists_eq_succ_of_ne_zero fun h0 ↦ ?_
    rw [h0, genMax_zero] at hi_spec
    push_cast at hi_spec
    linarith
  have hprev : (genMax i' : ℝ) ≤ M := by
    have := Nat.find_min hex (show i' < Nat.find hex by omega)
    push Not at this
    exact this
  rw [hi'] at hi_spec hij
  refine ⟨genMax (i' + 1), gen_mono hij (genMax_mem _), genMax_prime (Nat.succ_pos _), hi_spec, ?_⟩
  have : (genMax (i' + 1) : ℝ) ≤ 2 * genMax i' := by exact_mod_cast genMax_le_two_mul i'
  linarith

/-- **Increase of the profile.** For `0 < δ ≤ 1/10`, `8/5 ≤ λ < φ` and all large `L`: a profile
with ratio `λ` at `(j, L)` whose maximum runs ahead, `genMax j > (1 + δ) L`, produces a profile at
`(j + 3, (1 + κ) λ³ L)` with `κ = boostGain δ λ`. -/
theorem eventually_profile_boost (h : Hypotheses) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 10)
    (h1 : 8 / 5 ≤ lam) (hφ : lam < φ) :
    ∀ᶠ L : ℝ in atTop, ∀ j : ℕ, Profile lam j L → (1 + δ) * L < genMax j →
      Profile lam (j + 3) ((1 + boostGain δ lam) * lam ^ 3 * L) := by
  have hlam0 : 0 < lam := by linarith
  have hlam1 : 1 ≤ lam := by linarith
  have hsq := sq_lt_add_one_of_lt_goldenRatio hlam1 hφ
  -- The boost at every grid point, simultaneously.
  have hgrid : ∀ᶠ L : ℝ in atTop, ∀ T ∈ boostGrid δ, ∀ j t : ℕ, Profile lam j L → t ∈ gen j →
      Odd t → T * L ≤ t → (t : ℝ) ≤ (T + δ / 200) * L →
      ∀ r : ℕ, r.Prime → lam ^ 3 * L < r → (r : ℝ) ≤ (lam ^ 3 + δ / 8) * L → r ∈ gen (j + 3) :=
    (eventually_all_finset (boostGrid δ)).mpr fun T hT ↦
      eventually_mem_gen_add_three_of_boost h hδ0 hδ1 h1 hφ (one_add_le_of_mem_boostGrid hδ0 hT)
        (le_of_mem_boostGrid hT)
  -- Ordinary propagation, and the proportional extension at scale `λ² L`.
  set ε : ℝ := 1 - lam ^ 2 / (lam + 1) with hε
  have hε0 : 0 < ε := by
    rw [hε, sub_pos, div_lt_one (by linarith)]
    exact hsq
  have hε1 : ε < 1 := by
    rw [hε, sub_lt_self_iff]
    positivity
  have hext := (tendsto_id.const_mul_atTop' (by positivity : 0 < lam ^ 2) :
    Tendsto (fun L : ℝ ↦ lam ^ 2 * L) atTop atTop).eventually
    (eventually_primePrefix_add_two h.restrictedBinary_one h.primesIcc_lower hε0 hε1)
  filter_upwards [hgrid, hext, eventually_profile_add h.restrictedBinary_one h.primesIcc_lower
    hlam1 hφ, eventually_ge_atTop 3] with L hgridL hextL hpropL hL3 j hprof hMj
  have hL0 : 0 < L := by linarith
  -- The outlier prime `t`.
  obtain ⟨t, ht, htp, ht1, ht2⟩ := exists_genMax_mem_Ioc (M := (1 + δ) * L) (by nlinarith) hMj
  have ht3 : 3 ≤ t := by
    have : (3 : ℝ) < t := by nlinarith
    exact_mod_cast this.le
  have htodd : Odd t := htp.odd_of_ne_two (by omega)
  obtain ⟨T, hT, hTt, htT⟩ := exists_mem_boostGrid hδ0 (τ := t / L)
    (by rw [le_div_iff₀ hL0]; exact ht1.le) (by rw [div_le_iff₀ hL0]; linarith)
  rw [le_div_iff₀ hL0] at hTt
  rw [div_le_iff₀ hL0] at htT
  -- Every prime up to `(λ³ + δ/8) L` lies in `gen (j + 3)`.
  have hpre3 : PrimePrefix (j + 3) ((lam ^ 3 + δ / 8) * L) := by
    intro r hr hrL
    by_cases hrsmall : (r : ℝ) ≤ lam ^ 3 * L
    · have := (hpropL j hprof 2).right
      rw [show j + 2 + 1 = j + 3 by ring, ← mul_assoc, ← pow_succ'] at this
      exact this r hr hrsmall
    · exact hgridL T hT j t hprof ht htodd hTt htT r hr (not_le.mp hrsmall) hrL
  have hpre2 : PrimePrefix (j + 2) (lam ^ 2 * L) := (hpropL j hprof 2).left
  have hle : lam ^ 2 * L ≤ (lam ^ 3 + δ / 8) * L := by
    have h23 : lam ^ 2 * L ≤ lam ^ 3 * L :=
      mul_le_mul_of_nonneg_right (by nlinarith [pow_pos hlam0 2]) hL0.le
    have : 0 ≤ δ / 8 * L := by positivity
    linarith
  have hpre4 := hextL ((lam ^ 3 + δ / 8) * L) hle (j + 2) hpre2 hpre3
  have hid : (1 - ε) * ((lam ^ 3 + δ / 8) * L + lam ^ 2 * L) =
      lam * ((1 + boostGain δ lam) * lam ^ 3 * L) := by
    rw [hε, sub_sub_cancel, ← add_mul, ← mul_assoc, boostGain_identity hlam0]
    ring
  rw [hid] at hpre4
  refine ⟨hpre3.anti ?_, hpre4⟩
  have := boostGain_mul_pow_three_le (δ := δ) hδ0.le hlam0
  nlinarith

end Boost

end Conway
