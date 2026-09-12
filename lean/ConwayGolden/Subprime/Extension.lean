/-
Copyright (c) 2026 Romain Popescu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Romain Popescu
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.Real.GoldenRatio
import ConwayGolden.Subprime.Filling

/-!
# Proportional extension of prime prefixes and profiles

If every prime up to `Y` lies in `gen j` and every prime up to `X ≥ Y` lies in `gen (j + 1)`,
then every prime up to `(1 - ε) (X + Y)` lies in `gen (j + 2)`, for large `Y`. The argument is a
pigeonhole: a prime `r ∈ (X, (1 - ε) (X + Y)]` is `p + (r - p)` for `≫ X / log X` primes
`p ∈ [(1 - ε) X, X]`, while by buffered filling only `o(X / log X)` of the complements `r - p`,
which lie in `[1, (1 - ε) Y]`, are missing from `gen (j + 1)`.

A *profile* is a pair of consecutive cutoffs `L, λ L`. For `1 ≤ λ < φ`, the extension lemma
propagates a profile at `(j, L)` to a profile at `(j + 1, λ L)`, since `λ² = (1 - ε) (λ + 1)`
for `ε = 1 - λ² / (λ + 1) ∈ (0, 1)`.

## Main definitions

* `Conway.Profile λ j L`: `PrimePrefix j L` and `PrimePrefix (j + 1) (λ L)`.

## Main statements

* `Conway.eventually_primePrefix_add_two`: the proportional extension lemma.
* `Conway.eventually_profile_succ`: a profile propagates one generation.
* `Conway.eventually_profile_add`: a profile propagates any number of generations.
* `Conway.PrimesIccLower.eventually_le_genMax`: `PrimePrefix n L` forces `(1 - ρ) L ≤ genMax n`.
-/

namespace Conway

open Filter Finset Real Topology

/-! ### Prime prefixes bound the maximum from below -/

/-- If every prime up to `L` lies in `gen n`, then `genMax n ≥ (1 - ρ) L`, for large `L`. -/
theorem PrimesIccLower.eventually_le_genMax (h : PrimesIccLower) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) :
    ∀ᶠ L : ℝ in atTop, ∀ n : ℕ, PrimePrefix n L → (1 - ρ) * L ≤ genMax n := by
  filter_upwards [h.eventually_nonempty (α := 1 - ρ) (β := 1) (by linarith) (by linarith)]
    with L hL n hn
  rw [one_mul] at hL
  exact hn.le_genMax_of_nonempty hL

/-! ### The proportional extension lemma -/

/-- **Proportional extension.** For fixed `0 < ε < 1` and all large `Y`: if `Y ≤ X`,
`PrimePrefix j Y` and `PrimePrefix (j + 1) X`, then `PrimePrefix (j + 2) ((1 - ε) (X + Y))`. -/
theorem eventually_primePrefix_add_two (hG : RestrictedBinary 1) (hP : PrimesIccLower) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ Y : ℝ in atTop, ∀ X : ℝ, Y ≤ X → ∀ j : ℕ, PrimePrefix j Y → PrimePrefix (j + 1) X →
      PrimePrefix (j + 2) ((1 - ε) * (X + Y)) := by
  obtain ⟨c, hc, hcev⟩ := hP (1 - ε) 1 (by linarith) (by linarith)
  obtain ⟨Y₁, hY₁⟩ := eventually_atTop.mp hcev
  filter_upwards [hG.eventually_holes_le hε0 hε1 (half_pos hc), eventually_ge_atTop Y₁,
    eventually_ge_atTop (exp 1)] with Y hfill hYY₁ hYe
  intro X hYX j hj hj1 r hr hrXY
  have hX1 : 1 < X := (one_lt_exp_iff.mpr one_pos).trans_le (hYe.trans hYX)
  by_cases hrX : (r : ℝ) ≤ X
  · exact gen_mono (Nat.le_succ _) (hj1 r hr hrX)
  push Not at hrX
  -- The candidates are the primes `p ∈ [(1 - ε) X, X]`; their complements `r - p` lie in
  -- `[1, (1 - ε) Y]`.
  set U := Nat.primesIcc ((1 - ε) * X) (1 * X) with hU
  have hUle : ∀ u ∈ U, u ≤ r := fun u hu ↦ by
    have := Nat.le_of_mem_primesIcc' hu
    rw [one_mul] at this
    exact_mod_cast (this.trans hrX.le)
  have hmaps : ∀ u ∈ U, r - u ∈ Icc 1 ⌊(1 - ε) * Y⌋₊ := by
    intro u hu
    have hu1 := Nat.le_of_mem_primesIcc hu
    have hu2 := Nat.le_of_mem_primesIcc' hu
    rw [one_mul] at hu2
    have hur : (u : ℝ) < r := hu2.trans_lt hrX
    refine mem_Icc.mpr ⟨?_, Nat.le_floor ?_⟩
    · have : u < r := by exact_mod_cast hur
      omega
    · rw [Nat.cast_sub (hUle u hu)]
      linarith
  have hinj : Set.InjOn (fun u ↦ r - u) U := by
    intro u hu v hv huv
    have := hUle u hu
    have := hUle v hv
    simp only at huv
    omega
  -- Counting: `≫ X / log X` candidates against `o(X / log X)` holes.
  have hXlog : 0 < X / log X := div_pos (by linarith) (log_pos hX1)
  have hholes : (holes (j + 1) ⌊(1 - ε) * Y⌋₊ : ℝ) ≤ c / 2 * (Y / log Y) := hfill j hj
  have hmono : Y / log Y ≤ X / log X := self_div_log_le_self_div_log hYe hYX
  have hprimes : c * (X / log X) ≤ #U := hY₁ X (hYY₁.trans hYX)
  have hlt : holes (j + 1) ⌊(1 - ε) * Y⌋₊ < #U := by
    have : (holes (j + 1) ⌊(1 - ε) * Y⌋₊ : ℝ) < #U := by nlinarith
    exact_mod_cast this
  obtain ⟨p, hp, hrp⟩ := exists_apply_mem_gen_of_holes_lt hinj hmaps hlt
  have hpr : p ≤ r := hUle p hp
  have hpC : p ∈ gen (j + 1) := hj1 p (Nat.prime_of_mem_primesIcc hp)
    (by simpa using Nat.le_of_mem_primesIcc' hp)
  have := add_mem_gen_succ_of_prime hpC hrp (by rwa [Nat.add_sub_cancel' hpr])
  rwa [Nat.add_sub_cancel' hpr] at this

/-! ### Profiles -/

/-- A *profile* with ratio `λ` at `(j, L)`: every prime up to `L` lies in `gen j` and every prime
up to `λ L` lies in `gen (j + 1)`. -/
structure Profile (lam : ℝ) (j : ℕ) (L : ℝ) : Prop where
  /-- Every prime up to `L` lies in `gen j`. -/
  left : PrimePrefix j L
  /-- Every prime up to `λ L` lies in `gen (j + 1)`. -/
  right : PrimePrefix (j + 1) (lam * L)

namespace Profile

variable {lam L : ℝ} {j : ℕ}

theorem anti (h : Profile lam j L) {L' : ℝ} (hL : L' ≤ L) (hlam : 0 ≤ lam) : Profile lam j L' :=
  ⟨h.left.anti hL, h.right.anti (mul_le_mul_of_nonneg_left hL hlam)⟩

end Profile

/-- For `1 ≤ λ < φ`, the polynomial identity `λ² = (1 - ε) (λ + 1)` holds with
`ε = 1 - λ² / (λ + 1) ∈ (0, 1)`. -/
theorem sq_lt_add_one_of_lt_goldenRatio {lam : ℝ} (h1 : 1 ≤ lam) (hφ : lam < goldenRatio) :
    lam ^ 2 < lam + 1 := by
  have hψ : goldenConj < 0 := goldenConj_neg
  have hsum : goldenRatio + goldenConj = 1 := goldenRatio_add_goldenConj
  have hprod : goldenRatio * goldenConj = -1 := goldenRatio_mul_goldenConj
  have hfac : lam ^ 2 - lam - 1 = (lam - goldenRatio) * (lam - goldenConj) := by
    nlinarith [hsum, hprod]
  have : (lam - goldenRatio) * (lam - goldenConj) < 0 :=
    mul_neg_of_neg_of_pos (by linarith) (by linarith)
  linarith

/-- **Propagation of profiles.** For `1 ≤ λ < φ` and all large `L`, a profile with ratio `λ` at
`(j, L)` yields a profile at `(j + 1, λ L)`. -/
theorem eventually_profile_succ (hG : RestrictedBinary 1) (hP : PrimesIccLower) {lam : ℝ}
    (h1 : 1 ≤ lam) (hφ : lam < goldenRatio) :
    ∀ᶠ L : ℝ in atTop, ∀ j : ℕ, Profile lam j L → Profile lam (j + 1) (lam * L) := by
  have hsq := sq_lt_add_one_of_lt_goldenRatio h1 hφ
  have hpos : 0 < lam + 1 := by linarith
  set ε : ℝ := 1 - lam ^ 2 / (lam + 1) with hε
  have hε0 : 0 < ε := by
    rw [hε, sub_pos, div_lt_one hpos]
    exact hsq
  have hε1 : ε < 1 := by
    rw [hε, sub_lt_self_iff]
    positivity
  filter_upwards [eventually_primePrefix_add_two hG hP hε0 hε1, eventually_ge_atTop 0]
    with L hL hL0 j hprof
  refine ⟨hprof.right, ?_⟩
  have h := hL (lam * L) (by nlinarith) j hprof.left hprof.right
  have hid : (1 - ε) * (lam * L + L) = lam * (lam * L) := by
    rw [hε, sub_sub_cancel]
    field_simp
  rwa [hid] at h

/-- A profile propagates any number of generations: from `(j, L)` to `(j + r, λ ^ r L)`. -/
theorem eventually_profile_add (hG : RestrictedBinary 1) (hP : PrimesIccLower) {lam : ℝ}
    (h1 : 1 ≤ lam) (hφ : lam < goldenRatio) :
    ∀ᶠ L : ℝ in atTop, ∀ j : ℕ, Profile lam j L → ∀ r : ℕ, Profile lam (j + r) (lam ^ r * L) := by
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp (eventually_profile_succ hG hP h1 hφ)
  filter_upwards [eventually_ge_atTop L₀, eventually_ge_atTop 0] with L hL hL0 j hprof r
  induction r with
  | zero => simpa using hprof
  | succ r ih =>
    have hge : L₀ ≤ lam ^ r * L := hL.trans (le_mul_of_one_le_left hL0 (one_le_pow₀ h1))
    have := hL₀ _ hge (j + r) ih
    rwa [pow_succ, mul_comm (lam ^ r) lam, mul_assoc, ← add_assoc]

end Conway
