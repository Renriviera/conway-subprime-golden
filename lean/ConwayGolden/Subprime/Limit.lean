/-
Copyright (c) 2026 Romain Popescu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Romain Popescu
-/
import ConwayGolden.Analysis.TendstoOfEventually
import ConwayGolden.NumberTheory.PrimeCountingLittleO
import ConwayGolden.Subprime.Comparison
import ConwayGolden.Subprime.Filling

/-!
# The golden ratio limits

Under `Conway.Hypotheses`, this file derives the asymptotics of Conway's subprime generations:

* `genMax (n + 1) / genMax n → φ`,
* `#(gen (n + 1)) / genMax n → 1`,
* `#(gen (n + 1)) / #(gen n) → φ`,
* `#(gen n) / genMax n → φ⁻¹`.

## Outline

Approximate prime completeness (`eventually_primePrefix_genMax`) provides consecutive prime
prefixes at scales `(1 - ζ) genMax n` and `(1 - ζ) genMax (n + 1)`. The proportional extension
lemma then puts every prime up to `(1 - ζ)² (genMax (n + 1) + genMax n)` into `gen (n + 2)`, and
a prime in the top proportional window gives
`genMax (n + 2) ≥ (1 - ζ)³ (genMax (n + 1) + genMax n)`. Together with the elementary upper bound
`genMax (n + 2) ≤ genMax (n + 1) + genMax n` this is the *Fibonacci saturation*
`genMax (n + 2) / (genMax (n + 1) + genMax n) → 1`.

Writing `r n = genMax (n + 1) / genMax n ∈ [1, 2]`, saturation gives `r (n + 1) ≈ 1 + 1 / r n`;
since `φ = 1 + 1 / φ`, the error `|r n - φ|` satisfies the contractive recursion
`|r (n + 1) - φ| ≤ φ⁻¹ |r n - φ| + e n` with `e n → 0`, hence tends to `0`
(`tendsto_zero_of_le_mul_add`).

For the cardinalities, `#(gen (n + 1)) ≤ genMax n + π (2 genMax n)` and `π x = o(x)` give the
upper bound, while buffered filling below `(1 - ζ)² genMax n` gives the lower bound.

## Main statements

* `Conway.tendsto_genMax_succ_div`: `genMax (n + 1) / genMax n → φ`.
* `Conway.tendsto_card_gen_succ_div_genMax`: `#(gen (n + 1)) / genMax n → 1`.
* `Conway.tendsto_card_gen_succ_div`: `#(gen (n + 1)) / #(gen n) → φ`.
* `Conway.tendsto_card_gen_div_genMax`: `#(gen n) / genMax n → φ⁻¹`.
-/

namespace Conway

open Filter Finset Real Topology
open scoped goldenRatio Nat.Prime

/-! ### The maximum tends to infinity -/

theorem tendsto_genMax_atTop (h : Hypotheses) : Tendsto genMax atTop atTop := by
  refine tendsto_atTop_atTop.mpr fun k ↦ ?_
  obtain ⟨n, hn⟩ := h.exhaustion k
  refine ⟨n, fun m hm ↦ ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact Nat.zero_le _
  · exact (le_genMax (hn (mem_Icc.mpr ⟨hk, le_rfl⟩))).trans (genMax_mono hm)

theorem tendsto_genMax_cast_atTop (h : Hypotheses) :
    Tendsto (fun n : ℕ ↦ (genMax n : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp (tendsto_genMax_atTop h)

theorem genMax_cast_pos (n : ℕ) : (0 : ℝ) < genMax n := by exact_mod_cast genMax_pos n

/-! ### Fibonacci saturation -/

/-- For fixed `0 < ζ < 1`, `(1 - ζ)³ (genMax (n + 1) + genMax n) ≤ genMax (n + 2)` for all
large `n`. -/
theorem eventually_le_genMax_add_two (h : Hypotheses) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) :
    ∀ᶠ n : ℕ in atTop, (1 - ζ) ^ 3 * (genMax (n + 1) + genMax n) ≤ genMax (n + 2) := by
  have hM := tendsto_genMax_cast_atTop h
  have h1ζ : 0 < 1 - ζ := by linarith
  obtain ⟨Y₁, hY₁⟩ := eventually_atTop.mp
    (eventually_primePrefix_add_two h.restrictedBinary_one h.primesIcc_lower hζ0 hζ1)
  obtain ⟨L₁, hL₁⟩ := eventually_atTop.mp (h.primesIcc_lower.eventually_le_genMax hζ0 hζ1)
  have hpre := eventually_primePrefix_genMax h hζ0 hζ1
  have hpre' : ∀ᶠ n : ℕ in atTop, PrimePrefix (n + 1) ((1 - ζ) * genMax (n + 1)) :=
    (tendsto_add_atTop_nat 1).eventually hpre
  have hY : ∀ᶠ n : ℕ in atTop, Y₁ ≤ (1 - ζ) * genMax n :=
    (hM.const_mul_atTop' h1ζ).eventually_ge_atTop Y₁
  have hsum : Tendsto (fun n : ℕ ↦ (genMax (n + 1) : ℝ) + genMax n) atTop atTop :=
    (hM.comp (tendsto_add_atTop_nat 1)).atTop_add_atTop hM
  have hL : ∀ᶠ n : ℕ in atTop, L₁ ≤ (1 - ζ) ^ 2 * (genMax (n + 1) + genMax n) :=
    (hsum.const_mul_atTop' (by positivity)).eventually_ge_atTop L₁
  filter_upwards [hpre, hpre', hY, hL] with n hn hn1 hnY hnL
  have hmono : (genMax n : ℝ) ≤ genMax (n + 1) := by exact_mod_cast genMax_mono (Nat.le_succ n)
  have hXY : (1 - ζ) * genMax n ≤ (1 - ζ) * genMax (n + 1) := by gcongr
  have h2 := hY₁ _ hnY _ hXY n hn hn1
  rw [show (1 - ζ) * ((1 - ζ) * genMax (n + 1) + (1 - ζ) * genMax n) =
      (1 - ζ) ^ 2 * (genMax (n + 1) + genMax n) by ring] at h2
  have h3 := hL₁ _ hnL (n + 2) h2
  calc (1 - ζ) ^ 3 * ((genMax (n + 1) : ℝ) + genMax n)
      = (1 - ζ) * ((1 - ζ) ^ 2 * ((genMax (n + 1) : ℝ) + genMax n)) := by ring
    _ ≤ (genMax (n + 2) : ℝ) := h3

/-- **Fibonacci saturation**: `genMax (n + 2) / (genMax (n + 1) + genMax n) → 1`. -/
theorem tendsto_genMax_add_two_div (h : Hypotheses) :
    Tendsto (fun n : ℕ ↦ (genMax (n + 2) : ℝ) / (genMax (n + 1) + genMax n)) atTop (𝓝 1) := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < genMax (n + 1) + genMax n := fun n ↦ by
    have := genMax_cast_pos (n + 1)
    have := genMax_cast_pos n
    linarith
  refine tendsto_nhds_of_eventually_le_of_eventually_ge
    (fun ε hε ↦ Eventually.of_forall fun n ↦ ?_) (fun ε hε ↦ ?_)
  · rw [div_le_iff₀ (hpos n)]
    have : (genMax (n + 2) : ℝ) ≤ genMax (n + 1) + genMax n := by
      exact_mod_cast genMax_add_two_le n
    nlinarith [hpos n]
  · set ζ : ℝ := min (ε / 6) (1 / 2) with hζ
    have hζ0 : 0 < ζ := lt_min (by positivity) (by norm_num)
    have hζ1 : ζ < 1 := (min_le_right _ _).trans_lt (by norm_num)
    have hζε : 3 * ζ ≤ ε / 2 := by
      have := min_le_left (ε / 6) (1 / 2 : ℝ)
      linarith
    have hbern : 1 - 3 * ζ ≤ (1 - ζ) ^ 3 := by
      calc 1 - 3 * ζ = 1 + ((3 : ℕ) : ℝ) * (-ζ) := by push_cast; ring
        _ ≤ (1 + -ζ) ^ 3 := one_add_mul_le_pow (by linarith) 3
        _ = (1 - ζ) ^ 3 := by ring
    filter_upwards [eventually_le_genMax_add_two h hζ0 hζ1] with n hn
    rw [le_div_iff₀ (hpos n)]
    calc (1 - ε) * (genMax (n + 1) + genMax n)
        ≤ (1 - 3 * ζ) * (genMax (n + 1) + genMax n) :=
          mul_le_mul_of_nonneg_right (by linarith) (hpos n).le
      _ ≤ (1 - ζ) ^ 3 * (genMax (n + 1) + genMax n) :=
          mul_le_mul_of_nonneg_right hbern (hpos n).le
      _ ≤ genMax (n + 2) := hn

/-! ### The ratio of consecutive maxima -/

/-- The one-step error recursion for `r n = genMax (n + 1) / genMax n`:
`|r (n + 1) - φ| ≤ φ⁻¹ |r n - φ| + 2 |genMax (n + 2) / (genMax (n + 1) + genMax n) - 1|`. -/
theorem abs_genMax_div_sub_goldenRatio_succ_le (n : ℕ) :
    |(genMax (n + 2) : ℝ) / genMax (n + 1) - φ| ≤
      φ⁻¹ * |(genMax (n + 1) : ℝ) / genMax n - φ| +
        2 * |(genMax (n + 2) : ℝ) / (genMax (n + 1) + genMax n) - 1| := by
  have ha : (0 : ℝ) < genMax n := genMax_cast_pos n
  have hb : (0 : ℝ) < genMax (n + 1) := genMax_cast_pos (n + 1)
  have hab : (genMax n : ℝ) ≤ genMax (n + 1) := by exact_mod_cast genMax_mono (Nat.le_succ n)
  set a : ℝ := (genMax n : ℝ) with ha_def
  set b : ℝ := (genMax (n + 1) : ℝ) with hb_def
  set c : ℝ := (genMax (n + 2) : ℝ) with hc_def
  have hab' : a / b ≤ 1 := (div_le_one hb).mpr hab
  have hab0 : 0 < a / b := div_pos ha hb
  have hφ := one_add_inv_goldenRatio
  have hφ0 := goldenRatio_pos
  -- Algebraic decomposition of the error.
  have hq : c / (b + a) * (1 + a / b) = c / b := by
    field_simp
  have hsplit : c / b - φ = (c / (b + a) - 1) * (1 + a / b) + (a / b - φ⁻¹) := by
    linear_combination -hq + hφ
  -- The two error terms.
  have h1 : |(c / (b + a) - 1) * (1 + a / b)| ≤ 2 * |c / (b + a) - 1| := by
    rw [abs_mul, abs_of_pos (by linarith : 0 < 1 + a / b)]
    nlinarith [abs_nonneg (c / (b + a) - 1)]
  have h2 : |a / b - φ⁻¹| ≤ φ⁻¹ * |b / a - φ| := by
    have hid : a / b - φ⁻¹ = a / b * (φ⁻¹ * (φ - b / a)) := by
      field_simp
    rw [hid, abs_mul, abs_mul, abs_of_pos hab0, abs_of_pos inv_goldenRatio_pos, abs_sub_comm]
    have h0 : 0 ≤ φ⁻¹ * |b / a - φ| := by positivity
    calc a / b * (φ⁻¹ * |b / a - φ|) ≤ 1 * (φ⁻¹ * |b / a - φ|) :=
          mul_le_mul_of_nonneg_right hab' h0
      _ = φ⁻¹ * |b / a - φ| := one_mul _
  calc |c / b - φ| = |(c / (b + a) - 1) * (1 + a / b) + (a / b - φ⁻¹)| := by rw [hsplit]
    _ ≤ |(c / (b + a) - 1) * (1 + a / b)| + |a / b - φ⁻¹| := abs_add_le _ _
    _ ≤ 2 * |c / (b + a) - 1| + φ⁻¹ * |b / a - φ| := add_le_add h1 h2
    _ = φ⁻¹ * |b / a - φ| + 2 * |c / (b + a) - 1| := add_comm _ _

/-- **The ratio of consecutive maxima tends to the golden ratio.** -/
theorem tendsto_genMax_succ_div (h : Hypotheses) :
    Tendsto (fun n : ℕ ↦ (genMax (n + 1) : ℝ) / genMax n) atTop (𝓝 φ) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [Real.norm_eq_abs]
  have he : Tendsto
      (fun n : ℕ ↦ 2 * |(genMax (n + 2) : ℝ) / (genMax (n + 1) + genMax n) - 1|) atTop (𝓝 0) := by
    have := ((tendsto_genMax_add_two_div h).sub_const 1).abs.const_mul 2
    simpa using this
  exact tendsto_zero_of_le_mul_add inv_goldenRatio_pos.le inv_goldenRatio_lt_one
    (fun n ↦ abs_nonneg _) (fun n ↦ abs_genMax_div_sub_goldenRatio_succ_le n) he

/-! ### The cardinality of a generation -/

/-- `#(gen (n + 1)) ≤ genMax n + π (2 * genMax n)`. -/
theorem card_gen_succ_le_add_primeCounting (n : ℕ) :
    #(gen (n + 1)) ≤ genMax n + π (2 * genMax n) := by
  refine (card_gen_succ_le n).trans ?_
  gcongr
  exact (Nat.card_filter_prime_Icc_le_primeCounting _ _).trans
    (Nat.monotone_primeCounting (genMax_le_two_mul n))

theorem eventually_card_gen_succ_div_le (h : Hypotheses) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (#(gen (n + 1)) : ℝ) / genMax n ≤ 1 + ε := by
  have h2M : Tendsto (fun n : ℕ ↦ 2 * (genMax n : ℝ)) atTop atTop :=
    (tendsto_genMax_cast_atTop h).const_mul_atTop' two_pos
  have hπ := Chebyshev.tendsto_primeCounting_div.comp h2M
  filter_upwards [(tendsto_order.mp hπ).2 (ε / 2) (by positivity)] with n hn
  have hMpos := genMax_cast_pos n
  have hfloor : ⌊(2 : ℝ) * genMax n⌋₊ = 2 * genMax n := by
    rw [show (2 : ℝ) * genMax n = ((2 * genMax n : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
  simp only [Function.comp_apply] at hn
  rw [hfloor, div_lt_iff₀ (by positivity)] at hn
  have hcard : (#(gen (n + 1)) : ℝ) ≤ genMax n + π (2 * genMax n) := by
    exact_mod_cast card_gen_succ_le_add_primeCounting n
  rw [div_le_iff₀ hMpos]
  linarith

theorem eventually_le_card_gen_succ_div (h : Hypotheses) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, 1 - ε ≤ (#(gen (n + 1)) : ℝ) / genMax n := by
  have hM := tendsto_genMax_cast_atTop h
  set ζ : ℝ := min (ε / 8) (1 / 2) with hζ
  have hζ0 : 0 < ζ := lt_min (by positivity) (by norm_num)
  have hζ1 : ζ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hζε : ζ ≤ ε / 8 := min_le_left _ _
  have h1ζ : 0 < 1 - ζ := by linarith
  -- Buffered filling at `X = (1 - ζ) genMax n`, with buffer `θ = ζ` and error `ε / 4`.
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp
    (h.restrictedBinary_one.eventually_holes_le hζ0 hζ1 (by positivity : (0 : ℝ) < ε / 4))
  have hX : ∀ᶠ n : ℕ in atTop, max X₁ (exp 1) ≤ (1 - ζ) * genMax n :=
    (hM.const_mul_atTop' h1ζ).eventually_ge_atTop _
  have hinv : ∀ᶠ n : ℕ in atTop, (4 : ℝ) / ε ≤ genMax n := hM.eventually_ge_atTop _
  filter_upwards [eventually_primePrefix_genMax h hζ0 hζ1, hX, hinv] with n hpre hXn hMn
  have hMpos := genMax_cast_pos n
  set X : ℝ := (1 - ζ) * genMax n with hXdef
  have hXpos : 0 < X := by positivity
  have hXe : exp 1 ≤ X := (le_max_right _ _).trans hXn
  have hlog : 1 ≤ log X := (le_log_iff_exp_le hXpos).mpr hXe
  have hholes : (holes (n + 1) ⌊(1 - ζ) * X⌋₊ : ℝ) ≤ ε / 4 * (X / log X) :=
    hX₁ X ((le_max_left _ _).trans hXn) n hpre
  have hXlog : ε / 4 * (X / log X) ≤ ε / 4 * X :=
    mul_le_mul_of_nonneg_left (div_le_self hXpos.le hlog) (by positivity)
  have hcount : (⌊(1 - ζ) * X⌋₊ : ℝ) ≤ #(gen (n + 1)) + holes (n + 1) ⌊(1 - ζ) * X⌋₊ := by
    exact_mod_cast le_card_gen_add_holes (n + 1) ⌊(1 - ζ) * X⌋₊
  have hfloor : (1 - ζ) * X - 1 ≤ ⌊(1 - ζ) * X⌋₊ := by
    linarith [Nat.lt_floor_add_one ((1 - ζ) * X)]
  have hsq : (1 - 2 * ζ) * genMax n ≤ (1 - ζ) * X := by
    rw [hXdef, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (by nlinarith) hMpos.le
  have hXle : ε / 4 * X ≤ ε / 4 * genMax n := by
    rw [hXdef]
    exact mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  have h4 : (1 : ℝ) ≤ ε / 4 * genMax n := by
    rw [div_le_iff₀ hε] at hMn
    linarith
  have hζM : 2 * ζ * genMax n ≤ ε / 4 * genMax n :=
    mul_le_mul_of_nonneg_right (by linarith) hMpos.le
  rw [le_div_iff₀ hMpos]
  nlinarith

/-- **The cardinality of a generation is asymptotic to the previous maximum.** -/
theorem tendsto_card_gen_succ_div_genMax (h : Hypotheses) :
    Tendsto (fun n : ℕ ↦ (#(gen (n + 1)) : ℝ) / genMax n) atTop (𝓝 1) :=
  tendsto_nhds_of_eventually_le_of_eventually_ge (fun _ hε ↦ eventually_card_gen_succ_div_le h hε)
    (fun _ hε ↦ eventually_le_card_gen_succ_div h hε)

/-- **The ratio of consecutive generation sizes tends to the golden ratio.** -/
theorem tendsto_card_gen_succ_div (h : Hypotheses) :
    Tendsto (fun n : ℕ ↦ (#(gen (n + 1)) : ℝ) / #(gen n)) atTop (𝓝 φ) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  have h1 : Tendsto (fun n : ℕ ↦ (#(gen (n + 1 + 1)) : ℝ) / genMax (n + 1)) atTop (𝓝 1) :=
    (tendsto_card_gen_succ_div_genMax h).comp (tendsto_add_atTop_nat 1)
  have h2 := tendsto_genMax_succ_div h
  have h3 := tendsto_card_gen_succ_div_genMax h
  have := (h1.mul h2).div h3 one_ne_zero
  rw [one_mul, div_one] at this
  refine this.congr' (Eventually.of_forall fun n ↦ ?_)
  have hM0 : (genMax n : ℝ) ≠ 0 := (genMax_cast_pos n).ne'
  have hM1 : (genMax (n + 1) : ℝ) ≠ 0 := (genMax_cast_pos (n + 1)).ne'
  have hc : (#(gen (n + 1)) : ℝ) ≠ 0 := by
    exact_mod_cast (card_pos.mpr (gen_nonempty (n + 1))).ne'
  simp only [Pi.div_apply]
  field_simp

/-- `#(gen n) / genMax n → φ⁻¹`. -/
theorem tendsto_card_gen_div_genMax (h : Hypotheses) :
    Tendsto (fun n : ℕ ↦ (#(gen n) : ℝ) / genMax n) atTop (𝓝 φ⁻¹) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  have := (tendsto_card_gen_succ_div_genMax h).div (tendsto_genMax_succ_div h) goldenRatio_ne_zero
  rw [one_div] at this
  refine this.congr' (Eventually.of_forall fun n ↦ ?_)
  have hM0 : (genMax n : ℝ) ≠ 0 := (genMax_cast_pos n).ne'
  have hM1 : (genMax (n + 1) : ℝ) ≠ 0 := (genMax_cast_pos (n + 1)).ne'
  simp only [Pi.div_apply]
  field_simp

end Conway
