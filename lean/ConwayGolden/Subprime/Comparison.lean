/-
Copyright (c) 2026 Romain Popescu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Romain Popescu
-/
import ConwayGolden.Subprime.Boost
import ConwayGolden.Subprime.Weight

/-!
# Approximate prime completeness

This file proves that, under `Conway.Hypotheses`, every prime up to `(1 - ζ) genMax n` lies in
`gen n` for all large `n`, for every fixed `0 < ζ < 1` (`Conway.eventually_primePrefix_genMax`).

The proof is a *bounded-step comparison* between profiles and maxima. Fix `0 < δ ≤ 1/10` and the
ratio `λ = compRatio δ`, slightly below `φ`. A profile `(j, L)` propagates normally to
`(j + 1, λ L)`, and its normalised weight `profileRatio λ j L` grows by at most `A₀ = φ / λ` per
step. Whenever the weight exceeds `1 + δ`, one of the two maxima `genMax j`, `genMax (j + 1)` is
ahead of the profile, and the increase lemma `eventually_profile_boost` produces, after `3` or `4`
steps, a profile whose scale is larger by the factor `1 + κ`; this *contracts* the weight by the
factor `ρ = A₀⁴ / (1 + κ) < 1`. The parameters are chosen so that `A₀⁵ ≤ 1 + δ` and `ρ < 1`.

Iterating, the weight eventually drops below `1 + δ` and then stays below `A₀ (1 + δ)` at the
selected nodes, hence below `(1 + δ)²` at every generation. Solving the weight bound for
`genMax n`, with `genMax (n + 1) ≥ (1 - δ) λ L` from the prime prefix, gives
`genMax n ≤ (1 + 12 δ) L` and therefore `PrimePrefix n (genMax n / (1 + 12 δ))`.

## Main definitions

* `Conway.compRatio δ`: the ratio `λ = φ - (δ / 100) (φ - 8/5)` used in the comparison.
* `Conway.Thresholds δ L₀`: the finitely many "for all large `L`" statements needed, collected at
  a common threshold `L₀`.
* `Conway.IsNode δ L₀ j L`: a selected node of the comparison.
* `Conway.IsCovered δ L₀ n`: generation `n` carries a profile of weight at most `(1 + δ)²`.

## Main statements

* `Conway.eventually_primePrefix_genMax_div`: `PrimePrefix n (genMax n / (1 + 12 δ))` eventually.
* `Conway.eventually_primePrefix_genMax`: `PrimePrefix n ((1 - ζ) genMax n)` eventually.
-/

namespace Conway

open Filter Finset Real Topology
open scoped goldenRatio

/-! ### The ratio `λ` and its numerical properties -/

/-- The ratio `λ = φ - (δ / 100) (φ - 8/5)` of the profiles used in the comparison. -/
noncomputable def compRatio (δ : ℝ) : ℝ := φ - δ / 100 * (φ - 8 / 5)

theorem eight_fifths_lt_goldenRatio : 8 / 5 < φ := by
  have h : (2.2 : ℝ) < √5 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  unfold goldenRatio
  linarith

section Numerics

variable {δ : ℝ}

theorem compRatio_lt_goldenRatio (hδ0 : 0 < δ) : compRatio δ < φ := by
  unfold compRatio
  have := eight_fifths_lt_goldenRatio
  nlinarith

theorem eight_fifths_le_compRatio (hδ1 : δ ≤ 1 / 10) : 8 / 5 ≤ compRatio δ := by
  unfold compRatio
  have := eight_fifths_lt_goldenRatio
  nlinarith

theorem compRatio_pos (hδ1 : δ ≤ 1 / 10) : 0 < compRatio δ :=
  lt_of_lt_of_le (by norm_num) (eight_fifths_le_compRatio hδ1)

theorem one_le_compRatio (hδ1 : δ ≤ 1 / 10) : 1 ≤ compRatio δ :=
  le_trans (by norm_num) (eight_fifths_le_compRatio hδ1)

theorem one_le_goldenRatio_div_compRatio (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 10) :
    1 ≤ φ / compRatio δ := by
  rw [le_div_iff₀ (compRatio_pos hδ1)]
  unfold compRatio
  have := eight_fifths_lt_goldenRatio
  nlinarith

/-- `A₀ = φ / λ ≤ 1 + δ / 2400`. -/
theorem goldenRatio_div_compRatio_le (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 10) :
    φ / compRatio δ ≤ 1 + δ / 2400 := by
  have hpos := compRatio_pos hδ1
  have h85 := eight_fifths_le_compRatio hδ1
  rw [div_le_iff₀ hpos]
  have h53 := goldenRatio_lt_five_thirds
  unfold compRatio at h85 ⊢
  nlinarith

theorem one_add_pow_four_le {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 100) :
    (1 + y) ^ 4 ≤ 1 + 5 * y := by
  have h2 : y ^ 2 ≤ y / 100 := by nlinarith
  have h3 : y ^ 3 ≤ y / 10000 := by nlinarith
  have h4 : y ^ 4 ≤ y / 1000000 := by nlinarith
  have : (1 + y) ^ 4 = 1 + 4 * y + 6 * y ^ 2 + 4 * y ^ 3 + y ^ 4 := by ring
  rw [this]
  linarith

theorem one_add_pow_five_le {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 100) :
    (1 + y) ^ 5 ≤ 1 + 6 * y := by
  have h2 : y ^ 2 ≤ y / 100 := by nlinarith
  have h3 : y ^ 3 ≤ y / 10000 := by nlinarith
  have h4 : y ^ 4 ≤ y / 1000000 := by nlinarith
  have h5 : y ^ 5 ≤ y / 100000000 := by nlinarith
  have : (1 + y) ^ 5 = 1 + 5 * y + 10 * y ^ 2 + 10 * y ^ 3 + 5 * y ^ 4 + y ^ 5 := by ring
  rw [this]
  linarith

/-- `A₀ ^ 5 ≤ 1 + δ`. -/
theorem goldenRatio_div_compRatio_pow_five_le (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 10) :
    (φ / compRatio δ) ^ 5 ≤ 1 + δ := by
  have h1 := one_le_goldenRatio_div_compRatio hδ0 hδ1
  have h2 := goldenRatio_div_compRatio_le hδ0 hδ1
  calc (φ / compRatio δ) ^ 5 ≤ (1 + δ / 2400) ^ 5 := by gcongr
    _ ≤ 1 + 6 * (δ / 2400) := one_add_pow_five_le (by positivity) (by linarith)
    _ ≤ 1 + δ := by linarith

/-- `A₀ ^ 4 < 1 + κ`, so that the boost contracts the normalised weight. -/
theorem goldenRatio_div_compRatio_pow_four_lt (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 10) :
    (φ / compRatio δ) ^ 4 < 1 + boostGain δ (compRatio δ) := by
  have h1 := one_le_goldenRatio_div_compRatio hδ0.le hδ1
  have h2 := goldenRatio_div_compRatio_le hδ0.le hδ1
  have hlam := compRatio_pos hδ1
  have h53 : compRatio δ < 5 / 3 := (compRatio_lt_goldenRatio hδ0).trans goldenRatio_lt_five_thirds
  have hκ : δ / 480 < boostGain δ (compRatio δ) := by
    unfold boostGain
    rw [div_lt_div_iff_of_pos_left hδ0 (by norm_num) (by positivity)]
    nlinarith [pow_pos hlam 2, mul_pos hlam hlam]
  calc (φ / compRatio δ) ^ 4 ≤ (1 + δ / 2400) ^ 4 := by gcongr
    _ ≤ 1 + 5 * (δ / 2400) := one_add_pow_four_le (by positivity) (by linarith)
    _ = 1 + δ / 480 := by ring
    _ < 1 + boostGain δ (compRatio δ) := by linarith

/-- The final numerical estimate `(1 + δ)² (φ λ + 1) - (1 - δ) φ λ ≤ 1 + 12 δ`. -/
theorem comparison_final_bound (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 10) :
    (1 + δ) ^ 2 * (φ * compRatio δ + 1) - (1 - δ) * φ * compRatio δ ≤ 1 + 12 * δ := by
  have h53 := goldenRatio_lt_five_thirds
  have hlam53 : compRatio δ ≤ 5 / 3 := by
    unfold compRatio
    have := eight_fifths_lt_goldenRatio
    nlinarith
  have hlam0 := compRatio_pos hδ1
  have hprod : φ * compRatio δ ≤ 3 := by nlinarith [goldenRatio_pos]
  have hprod0 : 0 ≤ φ * compRatio δ := by positivity
  rw [mul_assoc (1 - δ)]
  generalize φ * compRatio δ = P at *
  have h1 : δ * P ≤ 3 * δ := by nlinarith
  have h2 : δ * (δ * P) ≤ δ * (3 * δ) := mul_le_mul_of_nonneg_left h1 hδ0
  have h3 : δ * δ ≤ δ / 10 := by nlinarith
  have : (1 + δ) ^ 2 * (P + 1) - (1 - δ) * P = 1 + 2 * δ + δ * δ + 3 * (δ * P) + δ * (δ * P) := by
    ring
  rw [this]
  nlinarith

end Numerics

/-! ### Thresholds -/

/-- The "for all large `L`" statements used in the comparison, at a common threshold `L₀`. -/
structure Thresholds (δ L₀ : ℝ) : Prop where
  /-- The threshold is at least `1`. -/
  one_le : 1 ≤ L₀
  /-- Normal propagation of profiles (`eventually_profile_add`). -/
  propagate : ∀ L : ℝ, L₀ ≤ L → ∀ j : ℕ, Profile (compRatio δ) j L →
    ∀ r : ℕ, Profile (compRatio δ) (j + r) (compRatio δ ^ r * L)
  /-- Increase of the profile (`eventually_profile_boost`). -/
  boost : ∀ L : ℝ, L₀ ≤ L → ∀ j : ℕ, Profile (compRatio δ) j L → (1 + δ) * L < genMax j →
    Profile (compRatio δ) (j + 3) ((1 + boostGain δ (compRatio δ)) * compRatio δ ^ 3 * L)
  /-- A prime prefix at scale `λ L` bounds the maximum from below (`eventually_le_genMax`). -/
  genMax_ge : ∀ L : ℝ, L₀ ≤ L → ∀ n : ℕ, PrimePrefix n (compRatio δ * L) →
    (1 - δ) * (compRatio δ * L) ≤ genMax n

theorem exists_thresholds (h : Hypotheses) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 10) :
    ∃ L₀ : ℝ, Thresholds δ L₀ := by
  have hlam1 := one_le_compRatio hδ1
  have hlam85 := eight_fifths_le_compRatio hδ1
  have hlamφ := compRatio_lt_goldenRatio hδ0
  have hprop := eventually_profile_add h.restrictedBinary_one h.primesIcc_lower hlam1 hlamφ
  have hboost := eventually_profile_boost h hδ0 hδ1 hlam85 hlamφ
  have hmax := (tendsto_id.const_mul_atTop' (by linarith : 0 < compRatio δ) :
    Tendsto (fun L : ℝ ↦ compRatio δ * L) atTop atTop).eventually
    (h.primesIcc_lower.eventually_le_genMax hδ0 (by linarith))
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp
    ((eventually_ge_atTop (1 : ℝ)).and (hprop.and (hboost.and hmax)))
  exact ⟨L₀, (hL₀ L₀ le_rfl).1, fun L hL ↦ (hL₀ L hL).2.1, fun L hL ↦ (hL₀ L hL).2.2.1,
    fun L hL ↦ (hL₀ L hL).2.2.2⟩

/-! ### The comparison -/

section Comparison

variable {δ L₀ : ℝ}

/-- A selected node of the comparison: a profile at scale at least `L₀` whose normalised weight
is at most `A₀ (1 + δ)`. -/
structure IsNode (δ L₀ : ℝ) (j : ℕ) (L : ℝ) : Prop where
  /-- The node carries a profile. -/
  profile : Profile (compRatio δ) j L
  /-- The scale is beyond the threshold. -/
  le : L₀ ≤ L
  /-- The normalised weight is at most `A₀ (1 + δ)`. -/
  ratio_le : profileRatio (compRatio δ) j L ≤ φ / compRatio δ * (1 + δ)

/-- Generation `n` is *covered*: it carries a profile, at scale at least `L₀`, of normalised
weight at most `(1 + δ)²`. -/
def IsCovered (δ L₀ : ℝ) (n : ℕ) : Prop :=
  ∃ L : ℝ, Profile (compRatio δ) n L ∧ L₀ ≤ L ∧ profileRatio (compRatio δ) n L ≤ (1 + δ) ^ 2

variable (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 10) (hT : Thresholds δ L₀)
include hδ0 hδ1 hT

/-- **Boost step.** A profile beyond the threshold whose weight exceeds `1 + δ` is increased after
`h ∈ {3, 4}` steps, and its weight contracts by the factor `ρ = A₀⁴ / (1 + κ)`. -/
theorem exists_boost_of_lt_profileRatio {j : ℕ} {L : ℝ} (hprof : Profile (compRatio δ) j L)
    (hL : L₀ ≤ L) (hZ : 1 + δ < profileRatio (compRatio δ) j L) :
    ∃ h : ℕ, (h = 3 ∨ h = 4) ∧
      Profile (compRatio δ) (j + h) ((1 + boostGain δ (compRatio δ)) * compRatio δ ^ h * L) ∧
      profileRatio (compRatio δ) (j + h) ((1 + boostGain δ (compRatio δ)) * compRatio δ ^ h * L) ≤
        (φ / compRatio δ) ^ 4 / (1 + boostGain δ (compRatio δ)) *
          profileRatio (compRatio δ) j L := by
  set lam := compRatio δ with hlam
  set κ := boostGain δ lam with hκ
  have hlam0 : 0 < lam := compRatio_pos hδ1
  have hlam1 : 1 ≤ lam := one_le_compRatio hδ1
  have hL0 : 0 < L := lt_of_lt_of_le (by linarith [hT.one_le]) hL
  have hκ0 : 0 ≤ κ := (boostGain_pos hδ0 hlam0).le
  have hA1 : 1 ≤ φ / lam := one_le_goldenRatio_div_compRatio hδ0.le hδ1
  have hZ0 : 0 < profileRatio lam j L := profileRatio_pos hlam0 hL0
  rcases genMax_lt_or_of_lt_profileRatio hlam0 hL0 hZ with hMj | hMj
  · refine ⟨3, Or.inl rfl, hT.boost L hL j hprof hMj, ?_⟩
    refine (profileRatio_boost_le hlam0 hL0 hκ0 3).trans ?_
    have h34 : (φ / lam) ^ 3 ≤ (φ / lam) ^ 4 := pow_le_pow_right₀ hA1 (by norm_num)
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right h34 (by linarith)) hZ0.le
  · have hprof1 : Profile lam (j + 1) (lam * L) := by
      have := hT.propagate L hL j hprof 1
      rwa [pow_one] at this
    have hL1 : L₀ ≤ lam * L := hL.trans (le_mul_of_one_le_left hL0.le hlam1)
    have hb := hT.boost (lam * L) hL1 (j + 1) hprof1 hMj
    refine ⟨4, Or.inr rfl, ?_, profileRatio_boost_le hlam0 hL0 hκ0 4⟩
    rwa [show j + 1 + 3 = j + 4 by ring, show (1 + κ) * lam ^ 3 * (lam * L) = (1 + κ) * lam ^ 4 * L
      by ring] at hb

/-- **Contraction phase.** From any profile beyond the threshold one reaches a profile of weight
at most `1 + δ`. -/
theorem exists_profileRatio_le {j : ℕ} {L : ℝ} (hprof : Profile (compRatio δ) j L)
    (hL : L₀ ≤ L) :
    ∃ j' : ℕ, ∃ L' : ℝ, Profile (compRatio δ) j' L' ∧ L₀ ≤ L' ∧
      profileRatio (compRatio δ) j' L' ≤ 1 + δ := by
  set lam := compRatio δ with hlam
  set ρ : ℝ := (φ / lam) ^ 4 / (1 + boostGain δ lam) with hρ
  have hlam0 : 0 < lam := compRatio_pos hδ1
  have hκ0 : 0 < boostGain δ lam := boostGain_pos hδ0 hlam0
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ < 1 := by
    rw [hρ, div_lt_one (by positivity)]
    exact goldenRatio_div_compRatio_pow_four_lt hδ0 hδ1
  have hL0 : 0 < L := lt_of_lt_of_le (by linarith [hT.one_le]) hL
  -- Induction on the number `m` of boosts needed.
  have key : ∀ m : ℕ, ∀ j : ℕ, ∀ L : ℝ, Profile lam j L → L₀ ≤ L →
      profileRatio lam j L ≤ (1 + δ) / ρ ^ m →
      ∃ j' : ℕ, ∃ L' : ℝ, Profile lam j' L' ∧ L₀ ≤ L' ∧ profileRatio lam j' L' ≤ 1 + δ := by
    intro m
    induction m with
    | zero =>
      intro j L hprof hL hZ
      exact ⟨j, L, hprof, hL, by simpa using hZ⟩
    | succ m ih =>
      intro j L hprof hL hZ
      by_cases hle : profileRatio lam j L ≤ 1 + δ
      · exact ⟨j, L, hprof, hL, hle⟩
      obtain ⟨h, -, hprof', hZ'⟩ :=
        exists_boost_of_lt_profileRatio hδ0 hδ1 hT hprof hL (not_le.mp hle)
      have hL0' : 0 < L := lt_of_lt_of_le (by linarith [hT.one_le]) hL
      have hL' : L₀ ≤ (1 + boostGain δ lam) * lam ^ h * L := by
        refine hL.trans (le_mul_of_one_le_left hL0'.le ?_)
        have : 1 ≤ lam ^ h := one_le_pow₀ (one_le_compRatio hδ1)
        nlinarith
      refine ih _ _ hprof' hL' ?_
      calc profileRatio lam (j + h) ((1 + boostGain δ lam) * lam ^ h * L) ≤
          ρ * profileRatio lam j L := hZ'
        _ ≤ ρ * ((1 + δ) / ρ ^ (m + 1)) := by gcongr
        _ = (1 + δ) / ρ ^ m := by
          rw [pow_succ]
          field_simp
  -- Choose `m` with `ρ ^ m` small enough.
  have hZ0 : 0 < profileRatio lam j L := profileRatio_pos hlam0 hL0
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (div_pos (by linarith : 0 < 1 + δ) hZ0) hρ1
  refine key m j L hprof hL ?_
  rw [le_div_iff₀ (pow_pos hρ0 m)]
  rw [lt_div_iff₀ hZ0] at hm
  linarith

/-- **Node step.** From a node, the comparison selects a next node `h ∈ {1, 3, 4}` generations
later, and every generation in between is covered. -/
theorem exists_isNode_add {j : ℕ} {L : ℝ} (hnode : IsNode δ L₀ j L) :
    ∃ h : ℕ, 1 ≤ h ∧ h ≤ 4 ∧ (∃ L' : ℝ, IsNode δ L₀ (j + h) L') ∧
      ∀ r : ℕ, r < h → IsCovered δ L₀ (j + r) := by
  set lam := compRatio δ with hlam
  set κ := boostGain δ lam with hκ
  set A : ℝ := φ / lam with hA
  have hlam0 : 0 < lam := compRatio_pos hδ1
  have hlam1 : 1 ≤ lam := one_le_compRatio hδ1
  have hL0 : 0 < L := lt_of_lt_of_le (by linarith [hT.one_le]) hnode.le
  have hA1 : 1 ≤ A := one_le_goldenRatio_div_compRatio hδ0.le hδ1
  have hA5 : A ^ 5 ≤ 1 + δ := goldenRatio_div_compRatio_pow_five_le hδ0.le hδ1
  have hA4 : A ^ 4 < 1 + κ := goldenRatio_div_compRatio_pow_four_lt hδ0 hδ1
  have hκ0 : 0 < κ := boostGain_pos hδ0 hlam0
  have hZ0 : 0 < profileRatio lam j L := profileRatio_pos hlam0 hL0
  -- Every intermediate generation `j + r`, `r ≤ 3`, is covered.
  have hcover : ∀ r : ℕ, r ≤ 3 → IsCovered δ L₀ (j + r) := by
    intro r hr
    refine ⟨lam ^ r * L, hT.propagate L hnode.le j hnode.profile r,
      hnode.le.trans (le_mul_of_one_le_left hL0.le (one_le_pow₀ hlam1)), ?_⟩
    calc profileRatio lam (j + r) (lam ^ r * L) ≤ A ^ r * profileRatio lam j L :=
          profileRatio_add_le hlam0 hL0 r
      _ ≤ A ^ r * (A * (1 + δ)) := by gcongr; exact hnode.ratio_le
      _ = A ^ (r + 1) * (1 + δ) := by ring
      _ ≤ A ^ 5 * (1 + δ) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hA1 (by omega)) (by linarith)
      _ ≤ (1 + δ) * (1 + δ) := mul_le_mul_of_nonneg_right hA5 (by linarith)
      _ = (1 + δ) ^ 2 := by ring
  by_cases hle : profileRatio lam j L ≤ 1 + δ
  · -- Normal step.
    refine ⟨1, le_rfl, by norm_num, ⟨lam * L, ?_, ?_, ?_⟩, fun r hr ↦ hcover r (by omega)⟩
    · have := hT.propagate L hnode.le j hnode.profile 1
      rwa [pow_one] at this
    · exact hnode.le.trans (le_mul_of_one_le_left hL0.le hlam1)
    · calc profileRatio lam (j + 1) (lam * L) ≤ A * profileRatio lam j L :=
            profileRatio_succ_le hlam0 hL0
        _ ≤ A * (1 + δ) := by gcongr
  · -- Boost.
    obtain ⟨h, hh, hprof', hZ'⟩ :=
      exists_boost_of_lt_profileRatio hδ0 hδ1 hT hnode.profile hnode.le (not_le.mp hle)
    have hh1 : 1 ≤ h := by rcases hh with rfl | rfl <;> norm_num
    have hh4 : h ≤ 4 := by rcases hh with rfl | rfl <;> norm_num
    refine ⟨h, hh1, hh4, ⟨(1 + κ) * lam ^ h * L, hprof', ?_, ?_⟩, fun r hr ↦ hcover r (by omega)⟩
    · refine hnode.le.trans (le_mul_of_one_le_left hL0.le ?_)
      have : 1 ≤ lam ^ h := one_le_pow₀ hlam1
      nlinarith
    · have hρ1 : A ^ 4 / (1 + κ) ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact hA4.le
      calc profileRatio lam (j + h) ((1 + κ) * lam ^ h * L) ≤
            A ^ 4 / (1 + κ) * profileRatio lam j L := hZ'
        _ ≤ 1 * profileRatio lam j L := by gcongr
        _ = profileRatio lam j L := one_mul _
        _ ≤ A * (1 + δ) := hnode.ratio_le

/-- Every generation after a node is covered. -/
theorem isCovered_of_isNode {j : ℕ} {L : ℝ} (hnode : IsNode δ L₀ j L) (k : ℕ) :
    IsCovered δ L₀ (j + k) := by
  induction k using Nat.strong_induction_on generalizing j L with
  | _ k ih =>
    obtain ⟨h, hh1, -, ⟨L', hnode'⟩, hcover⟩ := exists_isNode_add hδ0 hδ1 hT hnode
    rcases lt_or_ge k h with hk | hk
    · exact hcover k hk
    · have := ih (k - h) (by omega) hnode'
      rwa [show j + h + (k - h) = j + k by omega] at this

end Comparison

/-- Under the analytic hypotheses, all large generations are covered. -/
theorem eventually_isCovered (h : Hypotheses) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 10) :
    ∃ L₀ : ℝ, Thresholds δ L₀ ∧ ∀ᶠ n : ℕ in atTop, IsCovered δ L₀ n := by
  obtain ⟨L₀, hT⟩ := exists_thresholds h hδ0 hδ1
  refine ⟨L₀, hT, ?_⟩
  set lam := compRatio δ with hlam
  have hlam1 : 1 ≤ lam := one_le_compRatio hδ1
  have hL0 : 0 < L₀ := by linarith [hT.one_le]
  -- An initial profile at scale `L₀`, from exhaustion.
  obtain ⟨j₀, hj₀⟩ := h.exhaustion ⌈lam * L₀⌉₊
  have hpre : PrimePrefix j₀ (lam * L₀) :=
    (PrimePrefix.of_Icc_subset hj₀).anti (Nat.le_ceil _)
  have hprof : Profile lam j₀ L₀ :=
    ⟨hpre.anti (le_mul_of_one_le_left hL0.le hlam1), hpre.mono (Nat.le_succ _)⟩
  -- Contract to a node, then cover everything after it.
  obtain ⟨j₁, L₁, hprof₁, hL₁, hZ₁⟩ := exists_profileRatio_le hδ0 hδ1 hT hprof le_rfl
  have hnode : IsNode δ L₀ j₁ L₁ :=
    ⟨hprof₁, hL₁, hZ₁.trans (le_mul_of_one_le_left (by linarith)
      (one_le_goldenRatio_div_compRatio hδ0.le hδ1))⟩
  filter_upwards [eventually_ge_atTop j₁] with n hn
  have := isCovered_of_isNode hδ0 hδ1 hT hnode (n - j₁)
  rwa [Nat.add_sub_cancel' hn] at this

/-- **Approximate prime completeness**, quantitative form: for `0 < δ ≤ 1/10`, every prime up to
`genMax n / (1 + 12 δ)` lies in `gen n`, for all large `n`. -/
theorem eventually_primePrefix_genMax_div (h : Hypotheses) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1 / 10) :
    ∀ᶠ n : ℕ in atTop, PrimePrefix n (genMax n / (1 + 12 * δ)) := by
  obtain ⟨L₀, hT, hcov⟩ := eventually_isCovered h hδ0 hδ1
  have hlam0 : 0 < compRatio δ := compRatio_pos hδ1
  filter_upwards [hcov] with n ⟨L, hprof, hL, hZ⟩
  have hL0 : 0 < L := lt_of_lt_of_le (by linarith [hT.one_le]) hL
  have hM := hT.genMax_ge L hL (n + 1) hprof.right
  have hbound := genMax_le_of_profileRatio_le hlam0 hL0 hZ hM
  have hfinal := comparison_final_bound hδ0.le hδ1
  refine hprof.left.anti ?_
  rw [div_le_iff₀ (by linarith)]
  calc (genMax n : ℝ) ≤ ((1 + δ) ^ 2 * (φ * compRatio δ + 1) - (1 - δ) * φ * compRatio δ) * L :=
        hbound
    _ ≤ (1 + 12 * δ) * L := mul_le_mul_of_nonneg_right hfinal hL0.le
    _ = L * (1 + 12 * δ) := mul_comm _ _

/-- **Approximate prime completeness.** For every `0 < ζ < 1`, every prime up to
`(1 - ζ) genMax n` lies in `gen n`, for all large `n`. -/
theorem eventually_primePrefix_genMax (h : Hypotheses) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) :
    ∀ᶠ n : ℕ in atTop, PrimePrefix n ((1 - ζ) * genMax n) := by
  set δ : ℝ := min (1 / 10) (ζ / 24) with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 / 10 := min_le_left _ _
  have hδζ : 12 * δ ≤ ζ := by
    have := min_le_right (1 / 10 : ℝ) (ζ / 24)
    linarith
  filter_upwards [eventually_primePrefix_genMax_div h hδ0 hδ1] with n hn
  refine hn.anti ?_
  rw [le_div_iff₀ (by linarith)]
  have hM : (0 : ℝ) ≤ genMax n := Nat.cast_nonneg _
  have h1 : (1 - ζ) * (1 + 12 * δ) ≤ 1 := by nlinarith [mul_pos hδ0 hζ0]
  calc (1 - ζ) * (genMax n : ℝ) * (1 + 12 * δ) = (1 - ζ) * (1 + 12 * δ) * genMax n := by ring
    _ ≤ 1 * genMax n := mul_le_mul_of_nonneg_right h1 hM
    _ = genMax n := one_mul _

end Conway
