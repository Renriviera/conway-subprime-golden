/-
Copyright (c) 2026 Romain Popescu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Romain Popescu
-/
import Mathlib.NumberTheory.Real.GoldenRatio
import ConwayGolden.Subprime.Basic

/-!
# The golden weight of consecutive maxima

The Fibonacci inequality `genMax (j + 2) ≤ genMax (j + 1) + genMax j` is equivalent, via
`φ = 1 + φ⁻¹`, to the statement that the *golden weight*
`genWeight j = genMax (j + 1) + genMax j / φ` grows at most by a factor `φ` per generation.
Comparing this weight with the scale of a profile with ratio `λ`, we obtain the normalised
quantity `profileRatio λ j L = genWeight j / ((λ + φ⁻¹) L)`, which grows at most by the factor
`φ / λ` under a normal propagation step `(j, L) ↦ (j + 1, λ L)` and *contracts* when the profile
is increased by a factor `1 + κ`.

## Main definitions

* `Conway.genWeight j`: the golden weight `genMax (j + 1) + genMax j / φ`.
* `Conway.profileRatio λ j L`: the normalised weight `genWeight j / ((λ + φ⁻¹) L)`.

## Main statements

* `Conway.genWeight_succ_le`: `genWeight (j + 1) ≤ φ * genWeight j`.
* `Conway.profileRatio_add_le`:
  `profileRatio λ (j + r) (λ ^ r L) ≤ (φ / λ) ^ r * profileRatio λ j L`.
* `Conway.profileRatio_boost_le`: the contraction under an increase of the profile.
* `Conway.genMax_lt_or_of_lt_profileRatio`: a large ratio forces one of the two maxima ahead.
-/

namespace Conway

open Real
open scoped goldenRatio

theorem one_add_inv_goldenRatio : 1 + φ⁻¹ = φ := by
  rw [inv_goldenRatio, ← one_sub_goldenConj]
  ring

theorem inv_goldenRatio_pos : 0 < φ⁻¹ := inv_pos.mpr goldenRatio_pos

theorem inv_goldenRatio_lt_one : φ⁻¹ < 1 := inv_lt_one_of_one_lt₀ one_lt_goldenRatio

/-- The golden weight `genMax (j + 1) + genMax j / φ`. -/
noncomputable def genWeight (j : ℕ) : ℝ := genMax (j + 1) + genMax j / φ

theorem genWeight_pos (j : ℕ) : 0 < genWeight j := by
  unfold genWeight
  have := genMax_pos (j + 1)
  positivity

/-- The Fibonacci inequality in weighted form: `genWeight (j + 1) ≤ φ * genWeight j`. -/
theorem genWeight_succ_le (j : ℕ) : genWeight (j + 1) ≤ φ * genWeight j := by
  have hfib : (genMax (j + 2) : ℝ) ≤ genMax (j + 1) + genMax j := by
    exact_mod_cast genMax_add_two_le j
  have hφ : φ * (genMax (j + 1) + genMax j / φ) = φ * genMax (j + 1) + genMax j := by
    field_simp
  have hφ' : (genMax (j + 1) : ℝ) + genMax (j + 1) / φ = φ * genMax (j + 1) := by
    rw [div_eq_mul_inv, ← mul_one_add, mul_comm, one_add_inv_goldenRatio]
  unfold genWeight
  rw [hφ]
  linarith

theorem genWeight_add_le (j r : ℕ) : genWeight (j + r) ≤ φ ^ r * genWeight j := by
  induction r with
  | zero => simp
  | succ r ih =>
    calc genWeight (j + (r + 1)) = genWeight (j + r + 1) := by rw [add_assoc]
      _ ≤ φ * genWeight (j + r) := genWeight_succ_le _
      _ ≤ φ * (φ ^ r * genWeight j) := by gcongr
      _ = φ ^ (r + 1) * genWeight j := by ring

/-- The weight of a profile with ratio `λ` at `(j, L)`, normalised by `(λ + φ⁻¹) L`. -/
noncomputable def profileRatio (lam : ℝ) (j : ℕ) (L : ℝ) : ℝ :=
  genWeight j / ((lam + φ⁻¹) * L)

section

variable {lam L : ℝ} {j : ℕ}

theorem profileRatio_pos (hlam : 0 < lam) (hL : 0 < L) : 0 < profileRatio lam j L := by
  unfold profileRatio
  have := genWeight_pos j
  have := inv_goldenRatio_pos
  positivity

/-- A normal propagation step multiplies the ratio by at most `φ / λ`. -/
theorem profileRatio_succ_le (hlam : 0 < lam) (hL : 0 < L) :
    profileRatio lam (j + 1) (lam * L) ≤ φ / lam * profileRatio lam j L := by
  unfold profileRatio
  have hpos : 0 < (lam + φ⁻¹) * L := by have := inv_goldenRatio_pos; positivity
  have hW := genWeight_succ_le j
  have hg := goldenRatio_pos
  generalize φ = g at *
  rw [div_le_iff₀ (by positivity)]
  calc genWeight (j + 1) ≤ g * genWeight j := hW
    _ = g / lam * (genWeight j / ((lam + g⁻¹) * L)) * ((lam + g⁻¹) * (lam * L)) := by
      field_simp

theorem profileRatio_add_le (hlam : 0 < lam) (hL : 0 < L) (r : ℕ) :
    profileRatio lam (j + r) (lam ^ r * L) ≤ (φ / lam) ^ r * profileRatio lam j L := by
  unfold profileRatio
  have hpos : 0 < (lam + φ⁻¹) * L := by have := inv_goldenRatio_pos; positivity
  have hW := genWeight_add_le j r
  have hg := goldenRatio_pos
  generalize φ = g at *
  rw [div_le_iff₀ (by positivity)]
  calc genWeight (j + r) ≤ g ^ r * genWeight j := hW
    _ = (g / lam) ^ r * (genWeight j / ((lam + g⁻¹) * L)) * ((lam + g⁻¹) * (lam ^ r * L)) := by
      rw [div_pow]
      field_simp

/-- Increasing the scale by `1 + κ` after `h` steps multiplies the ratio by at most
`(φ / λ) ^ h / (1 + κ)`. -/
theorem profileRatio_boost_le (hlam : 0 < lam) (hL : 0 < L) {κ : ℝ} (hκ : 0 ≤ κ) (h : ℕ) :
    profileRatio lam (j + h) ((1 + κ) * lam ^ h * L) ≤
      (φ / lam) ^ h / (1 + κ) * profileRatio lam j L := by
  unfold profileRatio
  have hpos : 0 < (lam + φ⁻¹) * L := by have := inv_goldenRatio_pos; positivity
  have hκ' : 0 < 1 + κ := by linarith
  have hW := genWeight_add_le j h
  have hg := goldenRatio_pos
  generalize φ = g at *
  rw [div_le_iff₀ (by positivity)]
  calc genWeight (j + h) ≤ g ^ h * genWeight j := hW
    _ = (g / lam) ^ h / (1 + κ) * (genWeight j / ((lam + g⁻¹) * L)) *
        ((lam + g⁻¹) * ((1 + κ) * lam ^ h * L)) := by
      rw [div_pow]
      field_simp

/-- If the ratio exceeds `1 + δ`, one of the two maxima is ahead of the profile. -/
theorem genMax_lt_or_of_lt_profileRatio (hlam : 0 < lam) (hL : 0 < L) {δ : ℝ}
    (h : 1 + δ < profileRatio lam j L) :
    (1 + δ) * L < genMax j ∨ (1 + δ) * (lam * L) < genMax (j + 1) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  unfold profileRatio genWeight at h
  have hpos : 0 < (lam + φ⁻¹) * L := by have := inv_goldenRatio_pos; positivity
  rw [lt_div_iff₀ hpos] at h
  have hinv := inv_goldenRatio_pos
  have : (genMax j : ℝ) / φ ≤ (1 + δ) * L * φ⁻¹ := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right h1 hinv.le
  nlinarith

/-- The bound `genMax j ≤ ((1 + δ)² (φ λ + 1) - (1 - δ) φ λ) L` obtained by solving
`profileRatio λ j L ≤ (1 + δ)²` for `genMax j`, given `genMax (j + 1) ≥ (1 - δ) λ L`. -/
theorem genMax_le_of_profileRatio_le (hlam : 0 < lam) (hL : 0 < L) {δ : ℝ}
    (hZ : profileRatio lam j L ≤ (1 + δ) ^ 2) (hM : (1 - δ) * (lam * L) ≤ genMax (j + 1)) :
    (genMax j : ℝ) ≤ ((1 + δ) ^ 2 * (φ * lam + 1) - (1 - δ) * φ * lam) * L := by
  unfold profileRatio genWeight at hZ
  have hpos : 0 < (lam + φ⁻¹) * L := by have := inv_goldenRatio_pos; positivity
  rw [div_le_iff₀ hpos] at hZ
  have hφ : (lam + φ⁻¹) * φ = φ * lam + 1 := by
    rw [add_mul, inv_mul_cancel₀ goldenRatio_ne_zero]
    ring
  have hM' : (genMax j : ℝ) = φ * (genMax j / φ) := by
    field_simp
  have key : (genMax j : ℝ) / φ ≤ (1 + δ) ^ 2 * ((lam + φ⁻¹) * L) - (1 - δ) * (lam * L) := by
    linarith
  rw [hM']
  calc φ * ((genMax j : ℝ) / φ) ≤ φ * ((1 + δ) ^ 2 * ((lam + φ⁻¹) * L) - (1 - δ) * (lam * L)) :=
        mul_le_mul_of_nonneg_left key goldenRatio_pos.le
    _ = ((1 + δ) ^ 2 * (φ * lam + 1) - (1 - δ) * φ * lam) * L := by
      rw [← hφ]
      ring

end

end Conway
