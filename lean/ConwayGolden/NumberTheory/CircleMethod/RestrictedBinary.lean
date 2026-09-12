/-
Copyright (c) 2026 Romain Popescu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Romain Popescu
-/
import ConwayGolden.NumberTheory.CircleMethod.MinorArcs

/-!
# Almost-all restricted binary representations from the standard inputs

This file assembles the discrete circle method: with `P = ⌊(log X)^60⌋₊`,

`rep N = 𝔖_P(N) · W(N) + (majorSum N - 𝔖_P(N) W(N)) + minorSum N`,

where for admissible `N ≤ B X`:

* `W(N) ≥ count N - 2 X / P - 4 (log Q + 2) ≥ η X - o(X)`;
* `|𝔖_P(N)| ≤ 4 (log P + 1)⁴` and `𝔖_P(N) ≥ 1/2` outside a set of size `≪ X P^{-1/4}`;
* the major-arc error is `≪ P⁵ X (log X + 1) (log X)⁻ᴬ = o(X)` for `A = 305`;
* `‖minorSum N‖ < η X / 8` outside a set of size `≪ X (log X)¹⁰ / P`.

Hence `rep N ≥ η X / 8` for all admissible `N ≤ B X` outside a set of size `o(X / log X)`, and
de-weighting produces a representation by primes. This is `Conway.RestrictedBinary ν` for
`ν ∈ {1, 2}`.

## Main statements

* `CircleMethod.StandardInputs.restrictedBinary`: `StandardInputs → RestrictedBinary ν` for
  `ν = 1, 2`.
-/

namespace CircleMethod

namespace Ranges

open Conway Filter Finset Real Topology

variable (R : Ranges)

private theorem eventually_log_pow_le (n : ℕ) :
    ∀ᶠ X : ℝ in atTop, log X ^ n ≤ X := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := n)).def one_pos
  filter_upwards [h, eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (0 : ℝ)] with X hX hXpos hlog
  simpa [Real.norm_eq_abs, abs_pow, abs_of_nonneg
    hlog, abs_of_pos hXpos] using hX

private theorem eventually_log_ge (c : ℝ) :
    ∀ᶠ X : ℝ in atTop, c ≤ log X :=
  Real.tendsto_log_atTop.eventually_ge_atTop c

/-- The truncation parameter `P = ⌊(log X)^60⌋₊`. -/
noncomputable def truncation (X : ℝ) : ℕ := ⌊log X ^ (60 : ℝ)⌋₊

/-- The exponent `A` fed to Siegel–Walfisz in the assembly. -/
noncomputable def swExponent : ℝ := 305

/-- For large `X`, the parameter `P = truncation X` satisfies all the side conditions used in the
arc analysis. -/
theorem eventually_truncation_bounds :
    ∀ᶠ X : ℝ in atTop, 1 ≤ truncation X ∧ (truncation X : ℝ) ^ 5 ≤ X ∧
      8 * (truncation X : ℝ) ^ 3 ≤ X ∧ X ≤ truncation X * R.Q X (truncation X) ∧
      (truncation X : ℝ) ≤ log X ^ swExponent ∧ log X ^ (60 : ℝ) / 2 ≤ truncation X := by
  filter_upwards [eventually_log_pow_le 300, eventually_log_pow_le 181,
    eventually_log_ge 8, eventually_log_ge 2, eventually_log_ge 1,
    eventually_log_ge (2 / R.B), eventually_gt_atTop (0 : ℝ)] with
    X h300 h181 h8 h2 h1 hB hX
  let y : ℝ := log X ^ (60 : ℝ)
  let P : ℕ := ⌊y⌋₊
  have hy : 0 ≤ y := by positivity
  have hy1 : 1 ≤ y := by
    dsimp [y]
    exact Real.one_le_rpow (by linarith) (by norm_num)
  have hP1 : 1 ≤ P := by
    dsimp [P]
    exact Nat.le_floor (by exact_mod_cast hy1)
  have hP_le : (P : ℝ) ≤ y := by
    dsimp [P]
    exact Nat.floor_le hy
  have hy2 : 2 ≤ y := by
    dsimp [y]
    have hly : log X ≤ log X ^ (60 : ℝ) := by
      have ht := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ log X)
        (by norm_num : (1 : ℝ) ≤ 60)
      simpa [Real.rpow_one] using ht
    nlinarith
  have hhalf : y / 2 ≤ P := by
    have hfloor := Nat.lt_floor_add_one y
    dsimp [P] at hfloor ⊢
    have hP0 : (0 : ℝ) ≤ P := by positivity
    linarith
  have hPpow5 : (P : ℝ) ^ 5 ≤ X := by
    have hy5 : y ^ 5 = log X ^ 300 := by
      dsimp [y]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    calc
      (P : ℝ) ^ 5 ≤ y ^ 5 := by gcongr
      _ = log X ^ 300 := hy5
      _ ≤ X := h300
  have hPpow3 : 8 * (P : ℝ) ^ 3 ≤ X := by
    have hlog : 8 * (log X) ^ 180 ≤ (log X) ^ 181 := by
      nlinarith [mul_le_mul_of_nonneg_left h8 (by positivity : 0 ≤ log X ^ 180)]
    calc
      8 * (P : ℝ) ^ 3 ≤ 8 * y ^ 3 := by gcongr
      _ = 8 * log X ^ 180 := by
        dsimp [y]
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
      _ ≤ log X ^ 181 := hlog
      _ ≤ X := h181
  have hP_le_sw : (P : ℝ) ≤ log X ^ swExponent := by
    dsimp [P, y, swExponent]
    apply le_trans (Nat.floor_le (by positivity))
    apply Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hPQ : X ≤ P * R.Q X P := by
    have hspan : R.span X ≤ R.Q X P := le_of_lt (R.span_lt_Q X P)
    have hcoef : R.B * X ≤ R.span X := by
      rw [Ranges.span]
      have hν : 0 ≤ (R.ν : ℝ) := by positivity
      have hβ : 0 ≤ R.β := (R.α_pos.trans R.α_lt_β).le
      have hδ : 0 ≤ R.δ := (R.γ_pos.trans R.γ_lt_δ).le
      nlinarith [mul_nonneg (add_nonneg (mul_nonneg hν hβ) hδ) hX.le]
    have hBP : X ≤ P * (R.B * X) := by
      have hPB : (1 / R.B) ≤ P := by
        have hyB : 2 / R.B ≤ y := by
          dsimp [y]
          have hly : log X ≤ log X ^ (60 : ℝ) := by
            have ht := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ log X)
              (by norm_num : (1 : ℝ) ≤ 60)
            simpa [Real.rpow_one] using ht
          nlinarith [hly]
        have hBmul' : 2 ≤ log X * R.B := (div_le_iff₀ R.B_pos).mp hB
        have hBmul : 2 ≤ R.B * y := by
          have hly : log X ≤ y := by
            dsimp [y]
            have ht := Real.rpow_le_rpow_of_exponent_le
              (by linarith : (1 : ℝ) ≤ log X) (by norm_num : (1 : ℝ) ≤ 60)
            simpa [Real.rpow_one] using ht
          have hmul := mul_le_mul_of_nonneg_right hly R.B_pos.le
          nlinarith
        have hBPmul : R.B * y / 2 ≤ R.B * P := by
          calc
            R.B * y / 2 = R.B * (y / 2) := by ring
            _ ≤ R.B * P := mul_le_mul_of_nonneg_left hhalf R.B_pos.le
        rw [div_le_iff₀ R.B_pos]
        nlinarith
      have hBpos : 0 < R.B := R.B_pos
      calc
        X = (1 / R.B) * (R.B * X) := by field_simp
        _ ≤ P * (R.B * X) := by gcongr
    exact hBP.trans (mul_le_mul_of_nonneg_left (hcoef.trans hspan) (by positivity))
  dsimp [truncation, P, y] at *
  exact ⟨hP1, hPpow5, hPpow3, hPQ, hP_le_sw, hhalf⟩

open Classical in
/-- The set of admissible-parity targets `N ≤ B X` where the singular series is small. -/
noncomputable def badSingular (X : ℝ) : Finset ℕ :=
  {N ∈ Icc 1 ⌊R.B * X⌋₊ | Odd (N + R.ν) ∧ singularSeries R.ν N (truncation X) < 1 / 2}

open Classical in
/-- The set of targets `N < Q` where the minor arcs are large. -/
noncomputable def badMinor (X : ℝ) : Finset ℕ :=
  {N ∈ range (R.Q X (truncation X)) | R.η / 8 * X ≤ ‖R.minorSum X (truncation X) N‖}

/-- **Lower bound for `rep` off the bad sets.** For large `X`, every admissible `N ≤ B X` of
the right parity outside `badSingular ∪ badMinor` has `rep N ≥ η X / 8`. -/
theorem eventually_le_rep (h : StandardInputs) :
    ∀ᶠ X : ℝ in atTop, ∀ N : ℕ, N ∈ Icc 1 ⌊R.B * X⌋₊ → Odd (N + R.ν) →
      IsAdmissible R.ν (R.α * X) (R.β * X) (R.γ * X) (R.δ * X) (R.η * X) N →
        N ∉ R.badSingular X → N ∉ R.badMinor X → R.η / 8 * X ≤ R.rep X N := by
  obtain ⟨C, hC, hmaj⟩ :=
    R.exists_norm_majorSum_sub_le h.siegelWalfisz (A := swExponent) (by
      norm_num [swExponent])
  let c : ℝ := (R.ν : ℝ) * R.β + R.δ + R.B
  have hc : 0 < c := by
    dsimp [c]
    have hν : (1 : ℝ) ≤ R.ν := by exact_mod_cast R.one_le_ν
    have hβ : 0 < R.β := R.α_pos.trans R.α_lt_β
    have hδ : 0 < R.δ := R.γ_pos.trans R.γ_lt_δ
    nlinarith [R.B_pos]
  have hF1 : ∀ᶠ X : ℝ in atTop,
      2 * X / truncation X ≤ R.η / 16 * X := by
    filter_upwards [R.eventually_truncation_bounds,
      eventually_log_ge (max 1 (64 / R.η))] with X htr hlog
    obtain ⟨hP, hP5, _, _, _, hhalf⟩ := htr
    have hlog1 : 1 ≤ log X := le_trans (le_max_left _ _) hlog
    have hpow : log X ≤ log X ^ (60 : ℝ) := by
      calc
        log X = log X ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ log X ^ (60 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hlog1 (by norm_num)
    have hPlo : 32 / R.η ≤ (truncation X : ℝ) := by
      calc
        32 / R.η ≤ log X / 2 := by
          have he := (le_max_right 1 (64 / R.η)).trans hlog
          calc
            32 / R.η = (64 / R.η) / 2 := by ring
            _ ≤ log X / 2 := div_le_div_of_nonneg_right he (by norm_num)
        _ ≤ (log X ^ (60 : ℝ)) / 2 := by gcongr
        _ ≤ (truncation X : ℝ) := hhalf
    have hPpos : 0 < (truncation X : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hP)
    have hp : 2 / (truncation X : ℝ) ≤ R.η / 16 := by
      apply (div_le_iff₀ hPpos).2
      have he := (div_le_iff₀ R.η_pos).mp hPlo
      nlinarith
    have hPone : 1 ≤ (truncation X : ℝ) := by exact_mod_cast hP
    have hX0 : 0 ≤ X :=
      le_trans (by positivity : 0 ≤ (truncation X : ℝ) ^ 5) hP5
    calc
      2 * X / truncation X = X * (2 / (truncation X : ℝ)) := by ring
      _ ≤ X * (R.η / 16) := mul_le_mul_of_nonneg_left hp hX0
      _ = R.η / 16 * X := by ring
  have hF3 : ∀ᶠ X : ℝ in atTop,
      C * (truncation X : ℝ) ^ 5 * X * (log X + 1) /
          log X ^ swExponent ≤ R.η / 16 * X := by
    filter_upwards [R.eventually_truncation_bounds,
      eventually_log_ge (max 1 (32 * C / R.η))] with X htr hlog
    obtain ⟨hP, hP5, _, _, _, _⟩ := htr
    have hlog1 : 1 ≤ log X := le_trans (le_max_left _ _) hlog
    have hpow : (truncation X : ℝ) ^ 5 ≤ log X ^ 300 := by
      have hp : (truncation X : ℝ) ≤ log X ^ (60 : ℝ) := by
        dsimp [truncation]
        exact Nat.floor_le (by positivity)
      have hp0 : 0 ≤ (truncation X : ℝ) := by positivity
      have hl0 : 0 ≤ log X := by linarith
      have hpow' := pow_le_pow_left₀ hp0 hp 5
      have he : (log X ^ (60 : ℝ)) ^ 5 = log X ^ (300 : ℕ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hl0]
        norm_num
      calc
        (truncation X : ℝ) ^ 5 ≤ (log X ^ (60 : ℝ)) ^ 5 := hpow'
        _ = log X ^ 300 := he
    have hden : 0 < log X ^ swExponent := by positivity
    have hlog4 : 32 * C / R.η ≤ log X ^ 4 := by
      exact ((le_max_right 1 (32 * C / R.η)).trans hlog).trans
        (le_self_pow₀ hlog1 (by norm_num))
    have hplus : log X + 1 ≤ 2 * log X := by linarith
    rw [div_le_iff₀ hden]
    have h305 : log X ^ swExponent = log X ^ 305 := by
      simp [swExponent]
    rw [h305]
    have hprod : C * (truncation X : ℝ) ^ 5 * (log X + 1) ≤
        R.η / 16 * log X ^ 305 := by
      have hfirst : C * (truncation X : ℝ) ^ 5 * (log X + 1) ≤
          2 * C * log X ^ 301 := by
        have hcp : C * (truncation X : ℝ) ^ 5 ≤ C * log X ^ 300 :=
          mul_le_mul_of_nonneg_left hpow hC.le
        have hmul := mul_le_mul hcp hplus
          (by positivity : 0 ≤ log X + 1)
          (by positivity : 0 ≤ C * log X ^ 300)
        calc
          C * (truncation X : ℝ) ^ 5 * (log X + 1) ≤
              (C * log X ^ 300) * (2 * log X) := hmul
          _ = 2 * C * log X ^ 301 := by
            rw [show log X ^ 301 = log X ^ 300 * log X by
              rw [← pow_succ]]
            ring
      calc
        C * (truncation X : ℝ) ^ 5 * (log X + 1) ≤ 2 * C * log X ^ 301 := hfirst
        _ ≤ R.η / 16 * log X ^ 305 := by
          have hc' : 2 * C ≤ R.η / 16 * log X ^ 4 := by
            have hη : 0 < R.η := R.η_pos
            have hmul := (div_le_iff₀ hη).mp hlog4
            calc
              2 * C = (32 * C) / 16 := by ring
              _ ≤ (R.η * log X ^ 4) / 16 :=
                div_le_div_of_nonneg_right (by simpa [mul_comm] using hmul) (by norm_num)
              _ = R.η / 16 * log X ^ 4 := by ring
          have hh := mul_le_mul_of_nonneg_right hc'
            (by positivity : 0 ≤ log X ^ 301)
          have hpow_add : log X ^ 301 * log X ^ 4 = log X ^ 305 := by
            calc
              log X ^ 301 * log X ^ 4 = log X ^ (301 + 4) := (pow_add _ _ _).symm
              _ = log X ^ 305 := by norm_num
          calc
            2 * C * log X ^ 301 ≤ (R.η / 16 * log X ^ 4) * log X ^ 301 := hh
            _ = R.η / 16 * log X ^ 305 := by
              ring_nf
    have hX0 : 0 ≤ X :=
      le_trans (by positivity : 0 ≤ (truncation X : ℝ) ^ 5) hP5
    calc
      C * (truncation X : ℝ) ^ 5 * X * (log X + 1) =
          X * (C * (truncation X : ℝ) ^ 5 * (log X + 1)) := by ring
      _ ≤ X * (R.η / 16 * log X ^ 305) :=
        mul_le_mul_of_nonneg_left hprod hX0
      _ = R.η / 16 * X * log X ^ 305 := by ring
  have hF2 : ∀ᶠ X : ℝ in atTop,
      4 * (Real.log (R.Q X (truncation X)) + 2) ≤ R.η / 16 * X := by
    filter_upwards [eventually_log_pow_le 121,
      eventually_log_ge (max 1 (256 / R.η)),
      Filter.eventually_ge_atTop
        (max 1 (32 * (4 * log (c + 1) + 8) / R.η))] with X h121 hlog hX
    let P := truncation X
    have hlog1 : 1 ≤ log X := (le_max_left _ _).trans hlog
    have hX1 : 1 ≤ X := (le_max_left _ _).trans hX
    have hP60 : (P : ℝ) ≤ log X ^ (60 : ℝ) := by
      dsimp [P, truncation]
      exact Nat.floor_le (by positivity)
    have hP1 : 1 ≤ P := by
      apply Nat.le_floor
      exact_mod_cast (Real.one_le_rpow hlog1 (by norm_num : (0 : ℝ) ≤ 60))
    have hP120 : (P : ℝ) ^ 2 ≤ log X ^ 120 := by
      have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ (P : ℝ)) hP60 2
      have he : (log X ^ (60 : ℝ)) ^ 2 = log X ^ (120 : ℕ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ log X)]
        norm_num
      exact hsq.trans_eq he
    have hQ : (R.Q X P : ℝ) ≤ (P : ℝ) ^ P * (c * X + 1) := by
      rw [Ranges.Q]
      push_cast
      apply mul_le_mul
      · exact_mod_cast Nat.factorial_le_pow P
      · change (⌊c * X⌋₊ : ℝ) + 1 ≤ c * X + 1
        linarith [Nat.floor_le (show 0 ≤ c * X by positivity)]
      · positivity
      · positivity
    have hQpos : 0 < (R.Q X P : ℝ) := by
      rw [Ranges.Q]
      positivity
    have hPpos : 0 < (P : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hP1
    have hcX1 : 0 < c * X + 1 := by positivity
    have hlogQ : log (R.Q X P) ≤ (P : ℝ) * log P + log (c * X + 1) := by
      calc
        log (R.Q X P) ≤ log ((P : ℝ) ^ P * (c * X + 1)) :=
          Real.log_le_log hQpos hQ
        _ = log ((P : ℝ) ^ P) + log (c * X + 1) :=
          Real.log_mul (pow_ne_zero _ hPpos.ne') hcX1.ne'
        _ = (P : ℝ) * log P + log (c * X + 1) := by
          rw [Real.log_pow]
    have hPlog : (P : ℝ) * log (P : ℝ) ≤ (P : ℝ) ^ 2 := by
      simpa [pow_two] using mul_le_mul_of_nonneg_left
        (Real.log_le_self (show 0 ≤ (P : ℝ) by positivity))
        (show 0 ≤ (P : ℝ) by positivity)
    have hcX : c * X + 1 ≤ (c + 1) * X := by nlinarith
    have hlogc : log (c * X + 1) ≤ log (c + 1) + log X := by
      calc
        log (c * X + 1) ≤ log ((c + 1) * X) :=
          Real.log_le_log hcX1 hcX
        _ = log (c + 1) + log X :=
          Real.log_mul (by positivity) (by linarith)
    have hlog120 : log X ≤ log X ^ 120 :=
      le_self_pow₀ hlog1 (by norm_num)
    have hlogQ' : log (R.Q X P) ≤ log X ^ 120 + log (c + 1) + log X := by
      linarith [hlogQ, hPlog, hP120, hlogc]
    have hsmall : 8 * log X ^ 120 ≤ R.η / 32 * X := by
      have hdiv : log X ^ 120 ≤ X / log X := by
        apply (le_div_iff₀ (by linarith : 0 < log X)).2
        calc
          log X ^ 120 * log X = log X ^ 121 := by rw [← pow_succ]
          _ ≤ X := h121
      have hlarge : 256 / R.η ≤ log X := (le_max_right _ _).trans hlog
      have hη : 0 < R.η := R.η_pos
      have hmul := (div_le_iff₀ hη).mp hlarge
      have hfrac : 8 / log X ≤ R.η / 32 := by
        apply (div_le_iff₀ (by linarith : 0 < log X)).2
        calc
          8 = 256 / 32 := by norm_num
          _ ≤ (log X * R.η) / 32 :=
            div_le_div_of_nonneg_right hmul (by norm_num)
          _ = R.η / 32 * log X := by ring
      calc
        8 * log X ^ 120 ≤ 8 * (X / log X) :=
          mul_le_mul_of_nonneg_left hdiv (by norm_num)
        _ = X * (8 / log X) := by ring
        _ ≤ X * (R.η / 32) := mul_le_mul_of_nonneg_left hfrac (by linarith)
        _ = R.η / 32 * X := by ring
    have hconstant : 4 * log (c + 1) + 8 ≤ R.η / 32 * X := by
      have hlarge := (le_max_right 1 (32 * (4 * log (c + 1) + 8) / R.η)).trans hX
      have hη : 0 < R.η := R.η_pos
      calc
        4 * log (c + 1) + 8 =
            (32 * (4 * log (c + 1) + 8) / R.η) * (R.η / 32) := by
              field_simp
        _ ≤ X * (R.η / 32) :=
          mul_le_mul_of_nonneg_right hlarge (by positivity)
        _ = R.η / 32 * X := by ring
    change 4 * (log (R.Q X P) + 2) ≤ R.η / 16 * X
    nlinarith [hlogQ', hlog120, hsmall, hconstant]
  filter_upwards [R.eventually_truncation_bounds, hmaj, hF1, hF2, hF3,
    Filter.eventually_ge_atTop (max 1 (16 / R.η)),
    eventually_log_pow_le 62] with X htr hmajX hF1X hF2X hF3X hX hlogpow
  obtain ⟨hP, _, hP8, hPQ, hPA, _⟩ := htr
  have hX0 : 0 ≤ X := by
    have hx : 0 ≤ max 1 (16 / R.η) := by positivity
    linarith
  have hηX : 1 ≤ R.η / 16 * X := by
    have he := (le_max_right 1 (16 / R.η)).trans hX
    have hm := (div_le_iff₀ R.η_pos).mp he
    nlinarith
  intro N hNI hodd hadm hS hM
  have hN : (N : ℝ) ≤ R.B * X := by
    have hfloor := (Finset.mem_Icc.mp hNI).2
    have hle := Nat.floor_le (mul_nonneg R.B_pos.le hX0)
    calc
      (N : ℝ) ≤ (⌊R.B * X⌋₊ : ℝ) := by exact_mod_cast hfloor
      _ ≤ R.B * X := hle
  have hSge : (1 / 2 : ℝ) ≤ singularSeries R.ν N (truncation X) := by
    by_contra hn
    apply hS
    exact Finset.mem_filter.mpr ⟨hNI, hodd, by linarith⟩
  have hNQ : N < R.Q X (truncation X) := by
    exact_mod_cast R.le_Q_of_le X (truncation X) hX0 hN
  have hMlt : ‖R.minorSum X (truncation X) N‖ < R.η / 8 * X := by
    by_contra hn
    apply hM
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hNQ, by linarith⟩
  have hE := hmajX (truncation X) hP hPA hP8 hPQ N
  have hW := R.norm_singularIntegral_sub_count_le X (truncation X) hP hP8 hPQ hN
  have hcount := R.le_count_of_isAdmissible X hadm
  have hrep := R.rep_eq_majorSum_add_minorSum X (truncation X) hP hP8 hN
  have hre := congrArg Complex.re hrep
  simp only [Complex.ofReal_re, Complex.add_re] at hre
  have hWre : R.η * X - 1 - R.η / 8 * X ≤
      (R.singularIntegral X (truncation X) N).re := by
    have ht := (abs_le.mp (Complex.abs_re_le_norm
      (R.singularIntegral X (truncation X) N - R.count X N))).1
    simp [Complex.sub_re, Complex.natCast_re] at ht
    linarith [hW, hF1X, hF2X]
  have hWnonneg : 0 ≤ (R.singularIntegral X (truncation X) N).re := by
    linarith [hηX]
  have hmajor : R.η / 4 * X ≤
      (R.majorSum X (truncation X) N).re := by
    have hser : (1 / 2 : ℝ) * (R.singularIntegral X (truncation X) N).re ≤
        ((singularSeries R.ν N (truncation X) : ℂ) *
          R.singularIntegral X (truncation X) N).re := by
      rw [Complex.re_ofReal_mul]
      exact mul_le_mul_of_nonneg_right hSge hWnonneg
    have he := (abs_le.mp (Complex.abs_re_le_norm
      (R.majorSum X (truncation X) N -
        (singularSeries R.ν N (truncation X) : ℂ) *
          R.singularIntegral X (truncation X) N))).1
    simp only [Complex.sub_re] at he
    linarith [hE, hF3X, hWre, hser, he, hηX]
  have hminor : -(R.η / 8 * X) ≤
      (R.minorSum X (truncation X) N).re := by
    have hm := (abs_le.mp (Complex.abs_re_le_norm
      (R.minorSum X (truncation X) N))).1
    linarith
  linarith

private theorem two_sqrt_mul_log_sq_le {t : ℝ} (ht : 1 ≤ t) :
    2 * √t * log t ^ 2 ≤ 128 * t ^ ((3 : ℝ) / 4) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have h8 : log t ≤ 8 * t ^ ((1 : ℝ) / 8) := by
    have h := Real.log_le_sub_one_of_pos
      (Real.rpow_pos_of_pos ht0 ((1 : ℝ) / 8))
    rw [Real.log_rpow ht0] at h
    nlinarith
  have hl0 : 0 ≤ log t := Real.log_nonneg ht
  have hsq : log t ^ 2 ≤ 64 * t ^ ((1 : ℝ) / 4) := by
    have h := pow_le_pow_left₀ hl0 h8 2
    rw [mul_pow] at h
    have he : (t ^ ((1 : ℝ) / 8)) ^ 2 = t ^ ((1 : ℝ) / 4) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
      norm_num
    rw [he] at h
    norm_num at h ⊢
    exact h
  rw [Real.sqrt_eq_rpow]
  calc
    2 * t ^ ((1 : ℝ) / 2) * log t ^ 2 ≤
        2 * t ^ ((1 : ℝ) / 2) * (64 * t ^ ((1 : ℝ) / 4)) := by
          gcongr
    _ = 128 * t ^ ((3 : ℝ) / 4) := by
      ring_nf
      rw [← Real.rpow_add ht0]
      norm_num

private theorem eventually_sqrt_log_sq_lt :
    ∀ᶠ X : ℝ in atTop,
      2 * √(R.span X) * log (R.span X) ^ 2 < R.η / 8 * X := by
  let c : ℝ := (R.ν : ℝ) * R.β + R.δ + R.B
  have hc : 0 < c := by
    dsimp [c]
    have hν : (1 : ℝ) ≤ R.ν := by exact_mod_cast R.one_le_ν
    have hβ : 0 < R.β := R.α_pos.trans R.α_lt_β
    have hδ : 0 < R.δ := R.γ_pos.trans R.γ_lt_δ
    nlinarith [R.B_pos]
  let M : ℝ := 1024 * c ^ ((3 : ℝ) / 4) / R.η
  filter_upwards [Filter.eventually_gt_atTop (M ^ 4),
    Filter.eventually_ge_atTop (1 / c), Filter.eventually_gt_atTop 0] with X hM hXc hX0
  have ht : 1 ≤ c * X := by
    calc
      1 = c * (1 / c) := by field_simp
      _ ≤ c * X := mul_le_mul_of_nonneg_left hXc hc.le
  have hroot : M < X ^ ((1 : ℝ) / 4) := by
    have hM0 : 0 ≤ M := by
      dsimp [M]
      exact div_nonneg
        (mul_nonneg (by norm_num) (Real.rpow_nonneg hc.le _)) R.η_pos.le
    have hr := Real.rpow_lt_rpow (by positivity : 0 ≤ M ^ 4) hM
      (by norm_num : 0 < (1 : ℝ) / 4)
    calc
      M = (M ^ 4) ^ ((1 : ℝ) / 4) := by
        symm
        simpa [show (1 : ℝ) / 4 = (4 : ℝ)⁻¹ by norm_num] using
          (Real.pow_rpow_inv_natCast (by positivity : 0 ≤ M) (by norm_num : (4 : ℕ) ≠ 0))
      _ < X ^ ((1 : ℝ) / 4) := hr
  have hXsplit : X = X ^ ((1 : ℝ) / 4) * X ^ ((3 : ℝ) / 4) := by
    rw [← Real.rpow_add hX0]
    norm_num
  have hmain : 128 * c ^ ((3 : ℝ) / 4) * X ^ ((3 : ℝ) / 4) <
      R.η / 8 * X := by
    have hM : 128 * c ^ ((3 : ℝ) / 4) < R.η / 8 * X ^ ((1 : ℝ) / 4) := by
      dsimp [M] at hroot
      rw [div_lt_iff₀ R.η_pos] at hroot
      nlinarith
    calc
      128 * c ^ ((3 : ℝ) / 4) * X ^ ((3 : ℝ) / 4) <
          (R.η / 8 * X ^ ((1 : ℝ) / 4)) * X ^ ((3 : ℝ) / 4) :=
        mul_lt_mul_of_pos_right hM (Real.rpow_pos_of_pos hX0 _)
      _ = R.η / 8 * (X ^ ((1 : ℝ) / 4) * X ^ ((3 : ℝ) / 4)) := by ring
      _ = R.η / 8 * X := by rw [← hXsplit]
  change 2 * √(c * X) * log (c * X) ^ 2 < R.η / 8 * X
  exact (two_sqrt_mul_log_sq_le ht).trans_lt (by
    rw [Real.mul_rpow hc.le hX0.le]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmain)

/-- For large `X`, the exceptional set is contained in `badSingular ∪ badMinor`. -/
theorem eventually_exceptionalSet_subset (h : StandardInputs) :
    ∀ᶠ X : ℝ in atTop,
      exceptionalSet R.ν R.α R.β R.γ R.δ R.η R.B X ⊆ R.badSingular X ∪ R.badMinor X := by
  filter_upwards [R.eventually_le_rep h, R.eventually_sqrt_log_sq_lt,
    Filter.eventually_ge_atTop 1] with X hrep hsmall hX1
  intro N hN
  rw [mem_exceptionalSet] at hN
  obtain ⟨hNI, hodd, hadm, hnorep⟩ := hN
  rw [Finset.mem_union]
  by_contra hnot
  push Not at hnot
  have hge := hrep N hNI hodd hadm hnot.1 hnot.2
  exact hnorep (R.hasPrimeRepr_of_lt_rep X hX1 (lt_of_lt_of_le hsmall hge))

private theorem log_add_one_le_sixteen_rpow {t : ℝ} (ht : 1 ≤ t) :
    log t + 1 ≤ 16 * t ^ ((1 : ℝ) / 16) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hr : 0 < t ^ ((1 : ℝ) / 16) := Real.rpow_pos_of_pos ht0 _
  have hlog := Real.log_le_sub_one_of_pos hr
  have hpow : log t = 16 * log (t ^ ((1 : ℝ) / 16)) := by
    rw [Real.log_rpow ht0]
    ring
  nlinarith

private theorem tail_hyp_of_le {Y : ℕ}
    (hY : ((2 * 10 ^ 4 * 4096 * 4 : ℝ)) ^ 16 ≤ Y) :
    2 * 10 ^ 4 * √(Y : ℝ) * (log Y + 1) ^ 3 *
        (Y : ℝ) ^ (-(3 : ℝ) / 4) ≤ 1 / 4 := by
  let K : ℝ := 2 * 10 ^ 4 * 4096 * 4
  have hK : 0 < K := by
    dsimp [K]
    norm_num
  have hY0 : 0 < (Y : ℝ) := by
    have hKY : K ^ 16 ≤ (Y : ℝ) := by simpa [K] using hY
    have hK1 : 1 ≤ K ^ 16 := by
      have : 1 ≤ K := by linarith
      exact one_le_pow₀ this
    linarith
  have hY1 : (1 : ℝ) ≤ Y := by
    have hKY : K ^ 16 ≤ (Y : ℝ) := by simpa [K] using hY
    have hK1 : 1 ≤ K ^ 16 := by
      have : 1 ≤ K := by linarith
      exact one_le_pow₀ this
    exact hK1.trans hKY
  have hlog := log_add_one_le_sixteen_rpow hY1
  have hpow : (log Y + 1) ^ 3 ≤ 4096 * (Y : ℝ) ^ ((3 : ℝ) / 16) := by
    calc
      (log Y + 1) ^ 3 ≤ (16 * (Y : ℝ) ^ ((1 : ℝ) / 16)) ^ 3 := by
        gcongr
      _ = 4096 * (Y : ℝ) ^ ((3 : ℝ) / 16) := by
        rw [mul_pow]
        have he : ((Y : ℝ) ^ ((1 : ℝ) / 16)) ^ 3 =
            (Y : ℝ) ^ ((3 : ℝ) / 16) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hY0.le]
          norm_num
        rw [he]
        norm_num
  have hprod : √(Y : ℝ) * (log Y + 1) ^ 3 *
      (Y : ℝ) ^ (-(3 : ℝ) / 4) ≤ 4096 * (Y : ℝ) ^ (-(1 : ℝ) / 16) := by
    rw [Real.sqrt_eq_rpow]
    calc
      (Y : ℝ) ^ ((1 : ℝ) / 2) * (log Y + 1) ^ 3 *
          (Y : ℝ) ^ (-(3 : ℝ) / 4) ≤
          (Y : ℝ) ^ ((1 : ℝ) / 2) *
            (4096 * (Y : ℝ) ^ ((3 : ℝ) / 16)) *
              (Y : ℝ) ^ (-(3 : ℝ) / 4) := by gcongr
      _ = 4096 * (Y : ℝ) ^ (-(1 : ℝ) / 16) := by
        ring_nf
        rw [← Real.rpow_add hY0, ← Real.rpow_add hY0]
        congr 1
        norm_num
  have hroot : K ≤ (Y : ℝ) ^ ((1 : ℝ) / 16) := by
    have hKY : K ^ 16 ≤ (Y : ℝ) := by simpa [K] using hY
    have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ K ^ 16) hKY
      (by norm_num : 0 ≤ (1 : ℝ) / 16)
    calc
      K = (K ^ 16) ^ ((1 : ℝ) / 16) := by
        symm
        simpa [show (1 : ℝ) / 16 = (16 : ℝ)⁻¹ by norm_num] using
          (Real.pow_rpow_inv_natCast hK.le (show (16 : ℕ) ≠ 0 by norm_num))
      _ ≤ (Y : ℝ) ^ ((1 : ℝ) / 16) := hpow
  have hinv : (Y : ℝ) ^ (-(1 : ℝ) / 16) ≤ 1 / K := by
    rw [show -(1 : ℝ) / 16 = -((1 : ℝ) / 16) by ring, Real.rpow_neg hY0.le]
    rw [one_div]
    simpa [show (1 : ℝ) / 16 = (16 : ℝ)⁻¹ by norm_num] using inv_anti₀ hK hroot
  calc
    2 * 10 ^ 4 * √(Y : ℝ) * (log Y + 1) ^ 3 *
        (Y : ℝ) ^ (-(3 : ℝ) / 4) =
        2 * 10 ^ 4 * (√(Y : ℝ) * (log Y + 1) ^ 3 *
          (Y : ℝ) ^ (-(3 : ℝ) / 4)) := by ring
    _ ≤ 2 * 10 ^ 4 * (4096 * (Y : ℝ) ^ (-(1 : ℝ) / 16)) := by
      gcongr
    _ ≤ 1 / 4 := by
      dsimp [K] at hinv ⊢
      nlinarith

theorem tendsto_card_badSingular :
    Tendsto (fun X : ℝ ↦ (#(R.badSingular X) : ℝ) / (X / log X)) atTop (𝓝 0) := by
  let K : ℝ := 2 * 10 ^ 4 * 4096 * 4
  let u : ℝ → ℝ := fun X => (4 * 10 ^ 5 * R.B * 2) / log X ^ 14
  have hu : Tendsto u atTop (𝓝 0) := by
    dsimp [u]
    apply tendsto_const_nhds.div_atTop
    exact (tendsto_pow_atTop (by norm_num : (14 : ℕ) ≠ 0)).comp
      Real.tendsto_log_atTop
  have hle : ∀ᶠ X : ℝ in atTop,
      (#(R.badSingular X) : ℝ) / (X / log X) ≤ u X := by
    filter_upwards [R.eventually_truncation_bounds, Filter.eventually_gt_atTop 1,
      Filter.eventually_ge_atTop ((K ^ 16 + 1) / R.B)] with X htr hX1 hX
    obtain ⟨hP1, _, _, _, _, hPhalf⟩ := htr
    let Y : ℕ := ⌊R.B * X⌋₊
    let P : ℕ := truncation X
    have hYKnat : (2 * 10 ^ 4 * 4096 * 4 : ℕ) ^ 16 ≤ Y := by
      apply Nat.le_floor
      have hmul : (2 * 10 ^ 4 * 4096 * 4 : ℝ) ^ 16 + 1 ≤ R.B * X := by
        have := (div_le_iff₀ R.B_pos).mp hX
        simpa [K, mul_comm] using this
      exact_mod_cast (show (2 * 10 ^ 4 * 4096 * 4 : ℝ) ^ 16 ≤ R.B * X by
        linarith)
    have hYK : K ^ 16 ≤ (Y : ℝ) := by
      change (2 * 10 ^ 4 * 4096 * 4 : ℝ) ^ 16 ≤ (Y : ℝ)
      exact_mod_cast hYKnat
    have htail : 2 * 10 ^ 4 * √(Y : ℝ) * (log Y + 1) ^ 3 *
        (Y : ℝ) ^ (-(3 : ℝ) / 4) ≤ 1 / 4 := by
      simpa [K] using tail_hyp_of_le hYK
    have hb := card_singularSeries_lt_le R.ν_eq hP1 htail
    change (#(R.badSingular X) : ℝ) ≤
      4 * 10 ^ 5 * Y * (P : ℝ) ^ (-(1 : ℝ) / 4) at hb
    have hBY : (Y : ℝ) ≤ R.B * X := by
      dsimp [Y]
      exact Nat.floor_le (mul_nonneg R.B_pos.le (by linarith))
    have hlog : 0 < log X := Real.log_pos hX1
    have hPhalf' : log X ^ 60 / 2 ≤ (P : ℝ) := by
      simpa [P, Real.rpow_natCast] using hPhalf
    have hP4 : (log X ^ 15 / 2) ^ 4 ≤ (P : ℝ) := by
      calc
        (log X ^ 15 / 2) ^ 4 = log X ^ 60 / 16 := by
          rw [div_pow, ← pow_mul]
          ring
        _ ≤ log X ^ 60 / 2 := by
          gcongr
          norm_num
        _ ≤ (P : ℝ) := hPhalf'
    have hroot : log X ^ 15 / 2 ≤ (P : ℝ) ^ ((1 : ℝ) / 4) := by
      have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ (log X ^ 15 / 2) ^ 4) hP4
        (by norm_num : 0 ≤ (1 : ℝ) / 4)
      calc
        log X ^ 15 / 2 = ((log X ^ 15 / 2) ^ 4) ^ ((1 : ℝ) / 4) := by
          symm
          simpa [show (1 : ℝ) / 4 = (4 : ℝ)⁻¹ by norm_num] using
            (Real.pow_rpow_inv_natCast (by positivity : 0 ≤ log X ^ 15 / 2)
              (by norm_num : (4 : ℕ) ≠ 0))
        _ ≤ (P : ℝ) ^ ((1 : ℝ) / 4) := hpow
    have hPneg : (P : ℝ) ^ (-(1 : ℝ) / 4) ≤ 2 / log X ^ 15 := by
      have hPpos : 0 < (P : ℝ) := by exact_mod_cast hP1
      rw [show -(1 : ℝ) / 4 = -((1 : ℝ) / 4) by ring, Real.rpow_neg hPpos.le]
      rw [inv_le_comm₀ (Real.rpow_pos_of_pos hPpos _) (by positivity), inv_div]
      exact hroot
    have hden : 0 < X / log X := div_pos (by linarith) hlog
    have hcoef : 0 ≤ 4 * 10 ^ 5 * (R.B * X) := by
      exact mul_nonneg (by positivity) (mul_nonneg R.B_pos.le (by linarith))
    rw [div_le_iff₀ hden]
    calc
      (#(R.badSingular X) : ℝ) ≤
          4 * 10 ^ 5 * Y * (P : ℝ) ^ (-(1 : ℝ) / 4) := hb
      _ ≤ 4 * 10 ^ 5 * (R.B * X) * (2 / log X ^ 15) := by
        gcongr
      _ = u X * (X / log X) := by
        dsimp [u]
        field_simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu ?_ hle
  filter_upwards [Filter.eventually_gt_atTop 1] with X hX
  have hlog : 0 < log X := Real.log_pos hX
  positivity
  /-
  let K : ℝ := 2 * 10 ^ 4 * 4096 * 4
  have hK : 0 < K := by positivity
  have hupper : Tendsto (fun X : ℝ => (4 * 10 ^ 5 * R.B *
      (2 : ℝ) ^ ((1 : ℝ) / 4)) / log X ^ 14) atTop (𝓝 0) := by
    apply tendsto_const_nhds.div_atTop
    exact (tendsto_pow_atTop (by norm_num : (14 : ℕ) ≠ 0)).comp
      Real.tendsto_log_atTop
  have hY : ∀ᶠ X : ℝ in atTop, ∀ Y : ℕ, K ^ 16 ≤ Y →
      2 * 10 ^ 4 * √Y * (log Y + 1) ^ 3 *
        (Y : ℝ) ^ (-(3 : ℝ) / 4) ≤ 1 / 4 := by
    filter_upwards [Filter.eventually_ge_atTop (K ^ 16 : ℝ)] with X hX
    intro Y hYK
    have hY1 : (1 : ℝ) ≤ Y := by
      have : (1 : ℝ) ≤ K ^ 16 := by nlinarith
      exact this.trans (by exact_mod_cast hYK)
    have hlog := log_add_one_le_sixteen_rpow hY1
    have hpow : (log Y + 1) ^ 3 ≤ 4096 * (Y : ℝ) ^ ((3 : ℝ) / 16) := by
      calc
        (log Y + 1) ^ 3 ≤ (16 * (Y : ℝ) ^ ((1 : ℝ) / 16)) ^ 3 := by gcongr
        _ = 4096 * (Y : ℝ) ^ ((3 : ℝ) / 16) := by
          rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
          norm_num
    have hprod : √Y * (log Y + 1) ^ 3 *
        (Y : ℝ) ^ (-(3 : ℝ) / 4) ≤ 4096 * (Y : ℝ) ^ (-(1 : ℝ) / 16) := by
      rw [Real.sqrt_eq_rpow]
      calc
        (Y : ℝ) ^ ((1 : ℝ) / 2) * (log Y + 1) ^ 3 *
            (Y : ℝ) ^ (-(3 : ℝ) / 4) ≤
            (Y : ℝ) ^ ((1 : ℝ) / 2) *
              (4096 * (Y : ℝ) ^ ((3 : ℝ) / 16)) *
                (Y : ℝ) ^ (-(3 : ℝ) / 4) := by gcongr
        _ = 4096 * (Y : ℝ) ^ (-(1 : ℝ) / 16) := by
          rw [← Real.rpow_add (by positivity), ← Real.rpow_add (by positivity)]
          congr 1
          norm_num
    have hroot : K ≤ (Y : ℝ) ^ ((1 : ℝ) / 16) := by
      calc
        K = (K ^ 16) ^ ((1 : ℝ) / 16) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hK)]
          norm_num
        _ ≤ (Y : ℝ) ^ ((1 : ℝ) / 16) := by
          gcongr
    have hinv : (Y : ℝ) ^ (-(1 : ℝ) / 16) ≤ 1 / K := by
      rw [← Real.rpow_neg (by positivity)]
      rw [← one_div]
      gcongr
    calc
      2 * 10 ^ 4 * √Y * (log Y + 1) ^ 3 *
          (Y : ℝ) ^ (-(3 : ℝ) / 4) ≤
          2 * 10 ^ 4 * (4096 * (Y : ℝ) ^ (-(1 : ℝ) / 16)) := by
            gcongr
      _ ≤ 1 / 4 := by
        rw [show K = 2 * 10 ^ 4 * 4096 * 4 by rfl]
        nlinarith
  have hle : ∀ᶠ X : ℝ in atTop,
      (#(R.badSingular X) : ℝ) / (X / log X) ≤
        (4 * 10 ^ 5 * R.B * (2 : ℝ) ^ ((1 : ℝ) / 4)) / log X ^ 14 := by
    filter_upwards [R.eventually_truncation_bounds,
      Filter.eventually_gt_atTop 1, Filter.eventually_ge_atTop (exp 1),
      Filter.eventually_ge_atTop ((K ^ 16 + 1) / R.B)] with
      X htr hX1 hXe hX
    obtain ⟨hP1, hP5, _hP8, _hPQ, _hPA, hPhalf⟩ := htr
    let Y : ℕ := ⌊R.B * X⌋₊
    let P : ℕ := truncation X
    have hBY : (Y : ℝ) ≤ R.B * X := by
      dsimp [Y]
      exact Nat.floor_le (by positivity)
    have hYK : K ^ 16 ≤ Y := by
      apply Nat.le_floor
      have hmul : K ^ 16 + 1 ≤ R.B * X := by
        have := hX
        have hB := R.B_pos
        nlinarith
      linarith
    have hYbound := hY X Y hYK
    have hb := card_singularSeries_lt_le R.ν_eq hP1 hYbound
    change (#(R.badSingular X) : ℝ) ≤
      4 * 10 ^ 5 * Y * (P : ℝ) ^ (-(1 : ℝ) / 4) at hb
    have hlog : 0 < log X := Real.log_pos hX1
    have hP0 : (0 : ℝ) < P := by exact_mod_cast hP1
    have hPpow : (P : ℝ) ^ (-(1 : ℝ) / 4) ≤
        (2 : ℝ) ^ ((1 : ℝ) / 4) / log X ^ 15 := by
      have hhalf : log X ^ 60 / 2 ≤ (P : ℝ) := by
        simpa [Real.rpow_natCast] using hPhalf
      have hneg := Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < log X ^ 60 / 2)
        hhalf (by norm_num : -(1 : ℝ) / 4 ≤ 0)
      calc
        (P : ℝ) ^ (-(1 : ℝ) / 4) ≤
            (log X ^ 60 / 2) ^ (-(1 : ℝ) / 4) := hneg
        _ = (2 : ℝ) ^ ((1 : ℝ) / 4) / log X ^ 15 := by
          rw [div_rpow (by positivity) (by positivity), Real.rpow_neg (by positivity)]
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
          norm_num
    have hquot : (#(R.badSingular X) : ℝ) / (X / log X) ≤
        (4 * 10 ^ 5 * R.B * (2 : ℝ) ^ ((1 : ℝ) / 4)) / log X ^ 14 := by
      rw [div_le_iff₀ (div_pos (by linarith) hlog)]
      calc
        (#(R.badSingular X) : ℝ) ≤
            4 * 10 ^ 5 * Y * (P : ℝ) ^ (-(1 : ℝ) / 4) := hb
        _ ≤ 4 * 10 ^ 5 * (R.B * X) *
            ((2 : ℝ) ^ ((1 : ℝ) / 4) / log X ^ 15) := by
          gcongr
        _ = ((4 * 10 ^ 5 * R.B * (2 : ℝ) ^ ((1 : ℝ) / 4)) /
            log X ^ 14) * (X / log X) := by
          field_simp
    exact hquot
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ hle
  filter_upwards [Filter.eventually_gt_atTop 1] with X hX
  have hlog : 0 < log X := Real.log_pos hX
  positivity
-/

theorem tendsto_card_badMinor (hVM : VinogradovMinorArc) :
    Tendsto (fun X : ℝ ↦ (#(R.badMinor X) : ℝ) / (X / log X)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hev⟩ := R.exists_card_minor_exceptional_le hVM
  let u : ℝ → ℝ := fun X => (128 * C / R.η ^ 2) / log X ^ 49
  have hu : Tendsto u atTop (𝓝 0) := by
    dsimp [u]
    apply tendsto_const_nhds.div_atTop
    exact (tendsto_pow_atTop (by norm_num : (49 : ℕ) ≠ 0)).comp
      Real.tendsto_log_atTop
  have hle : ∀ᶠ X : ℝ in atTop,
      (#(R.badMinor X) : ℝ) / (X / log X) ≤ u X := by
    filter_upwards [hev, R.eventually_truncation_bounds,
      Filter.eventually_gt_atTop 1, Filter.eventually_ge_atTop (exp 1)] with
      X hEv htr hX1 hXe
    obtain ⟨hP1, hP5, _hP8, hPQ, _hPA, hPhalf⟩ := htr
    let P := truncation X
    have hb := hEv P hP1 hP5 hPQ (R.η / 8)
      (div_pos R.η_pos (by norm_num))
    change (#(R.badMinor X) : ℝ) ≤ C * X * log X ^ 10 /
      ((R.η / 8) ^ 2 * P) at hb
    have hlog : 0 < log X := Real.log_pos hX1
    have hP0 : (0 : ℝ) < P := by exact_mod_cast hP1
    have hhalf : log X ^ 60 / 2 ≤ (P : ℝ) := by
      simpa [P, Real.rpow_natCast] using hPhalf
    have hinv : 1 / (P : ℝ) ≤ 2 / log X ^ 60 := by
      calc
        1 / (P : ℝ) ≤ 1 / (log X ^ 60 / 2) := by
          apply one_div_le_one_div_of_le
          · positivity
          · exact hhalf
        _ = 2 / log X ^ 60 := by field_simp
    have hbound : (#(R.badMinor X) : ℝ) ≤
        128 * C * X * log X ^ 10 / (R.η ^ 2 * log X ^ 60) := by
      calc
        (#(R.badMinor X) : ℝ) ≤ C * X * log X ^ 10 /
            ((R.η / 8) ^ 2 * P) := hb
        _ = C * X * log X ^ 10 / (R.η / 8) ^ 2 * (1 / P) := by
          field_simp
        _ ≤ C * X * log X ^ 10 / (R.η / 8) ^ 2 *
            (2 / log X ^ 60) := by
          gcongr
        _ = 128 * C * X * log X ^ 10 / (R.η ^ 2 * log X ^ 60) := by
          field_simp
          ring
    have hquot : (#(R.badMinor X) : ℝ) / (X / log X) ≤
        128 * C * log X ^ 11 / (R.η ^ 2 * log X ^ 60) := by
      have hden : 0 < X / log X := div_pos (by linarith) hlog
      rw [div_le_iff₀ hden]
      calc
        (#(R.badMinor X) : ℝ) ≤
            128 * C * X * log X ^ 10 / (R.η ^ 2 * log X ^ 60) := hbound
        _ = (128 * C * log X ^ 11 / (R.η ^ 2 * log X ^ 60)) *
            (X / log X) := by
          field_simp
    convert hquot using 1
    dsimp [u]
    have hη : R.η ≠ 0 := ne_of_gt R.η_pos
    field_simp [hη, hlog.ne']
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu ?_ hle
  filter_upwards [Filter.eventually_gt_atTop 1] with X hX
  have hlog : 0 < log X := Real.log_pos hX
  positivity

/-- The exceptional set at scale `X` has `o(X / log X)` elements. -/
theorem tendsto_card_exceptionalSet (h : StandardInputs) :
    Tendsto (fun X : ℝ ↦ (#(exceptionalSet R.ν R.α R.β R.γ R.δ R.η R.B X) : ℝ) / (X / log X))
      atTop (𝓝 0) := by
  have hS := R.tendsto_card_badSingular
  have hM := R.tendsto_card_badMinor h.vinogradovMinorArc
  have hsum := hS.add hM
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum ?_ ?_
  · filter_upwards [Filter.eventually_gt_atTop 1] with X hX
    have hpos : 0 < X / log X := div_pos (by linarith) (Real.log_pos hX)
    positivity
  · filter_upwards [R.eventually_exceptionalSet_subset h,
      Filter.eventually_gt_atTop 1] with X hsub hX
    have hpos : 0 < X / log X := div_pos (by linarith) (Real.log_pos hX)
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ hpos.le
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (R.badSingular X) (R.badMinor X)
    exact_mod_cast h1.trans h2

end Ranges

/-- **Restricted almost-all binary representations from the standard inputs.** -/
theorem StandardInputs.restrictedBinary (h : StandardInputs) {ν : ℕ} (hν : ν = 1 ∨ ν = 2) :
    Conway.RestrictedBinary ν := by
  intro α β γ δ η B hα hαβ hγ hγδ hη hB
  exact Ranges.tendsto_card_exceptionalSet ⟨ν, α, β, γ, δ, η, B, hν, hα, hαβ, hγ, hγδ, hη, hB⟩ h

end CircleMethod
