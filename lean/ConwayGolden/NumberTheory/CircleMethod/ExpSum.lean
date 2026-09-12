/-
Copyright (c) 2026 Romain Popescu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Romain Popescu
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.Order.Round

/-!
# Additive characters, discrete orthogonality and summation by parts

This file collects the elementary Fourier-analytic tools used by the discrete circle method in
`ConwayGolden.NumberTheory.CircleMethod`. Everything here is finite: the "circle" is the cyclic
group `ZMod Q`, sampled through `k ↦ k / Q` for `k < Q`.

## Main definitions

* `CircleMethod.e x`: the additive character `exp (2 π i x)`.
* `CircleMethod.distInt θ`: the distance from `θ` to the nearest integer.

## Main statements

* `CircleMethod.sum_e_mul_div`: orthogonality `∑_{k < Q} e (k h / Q) = Q · [Q ∣ h]`.
* `CircleMethod.sum_mul_e_neg_eq`: discrete Fourier inversion, extracting the coefficient at `N`
  of a finite exponential sum whose frequencies lie in a window of length `< Q` around `N`.
* `CircleMethod.sum_norm_sq_sum_mul_e`: discrete Parseval identity.
* `CircleMethod.sum_norm_sq_sum_mul_e_neg`: Parseval identity for the inverse transform.
* `CircleMethod.norm_sum_e_Icc_le`: the geometric-series bound
  `‖∑_{n ∈ [a, b]} e (n θ)‖ ≤ 1 / (2 ‖θ‖)`.
* `CircleMethod.norm_sum_Ioc_sub_mul_le`: summation by parts comparing `∑ f n v n` with
  `∑ g n v n` in terms of the partial sums of `f - g`.

## Implementation notes

`e` is defined directly through `Complex.exp` rather than through `Circle` or `AddChar` so that
`ring`/`field_simp` can be used freely on arguments. The nearest-integer distance `distInt` is
defined through `round`; the only facts needed are periodicity, the bound `≤ 1/2`, and the
characterisation of its zeros.
-/

namespace CircleMethod

open Complex Finset Real

/-! ### The additive character `e` -/

/-- The additive character `e x = exp (2 π i x)`. -/
noncomputable def e (x : ℝ) : ℂ := Complex.exp (2 * π * I * x)

@[simp]
theorem e_zero : e 0 = 1 := by
  simp [e]

theorem e_add (x y : ℝ) : e (x + y) = e x * e y := by
  rw [e, e, e, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem e_neg (x : ℝ) : e (-x) = (starRingEnd ℂ) (e x) := by
  have h : (starRingEnd ℂ) (2 : ℂ) = 2 := by
    change star (2 : ℂ) = 2
    norm_num
  simp [e, ← Complex.exp_conj, h]

@[simp]
theorem e_intCast (n : ℤ) : e n = 1 := by
  rw [e]
  convert Complex.exp_int_mul_two_pi_mul_I n using 1
  · push_cast
    ring

theorem e_add_intCast (x : ℝ) (n : ℤ) : e (x + n) = e x := by
  rw [e_add, e_intCast, mul_one]

theorem e_add_one (x : ℝ) : e (x + 1) = e x := by
  simpa using e_add_intCast x (1 : ℤ)

@[simp]
theorem norm_e (x : ℝ) : ‖e x‖ = 1 := by
  rw [e, Complex.norm_exp]
  simp

theorem e_ne_zero (x : ℝ) : e x ≠ 0 := by
  exact Complex.exp_ne_zero _

theorem e_nat_mul (n : ℕ) (x : ℝ) : e (n * x) = e x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, e_add, ih]
    simp [pow_succ]

theorem e_eq_one_iff (x : ℝ) : e x = 1 ↔ ∃ n : ℤ, x = n := by
  rw [e, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hc : (2 * (π : ℂ) * I) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr pi_ne_zero))
        I_ne_zero
    have hmul : (2 * (π : ℂ) * I) * (x : ℂ) =
        (2 * (π : ℂ) * I) * (n : ℂ) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hn
    have hcast : (x : ℂ) = (n : ℂ) := mul_left_cancel₀ hc hmul
    exact_mod_cast hcast
  · rintro ⟨n, rfl⟩
    push_cast
    ring_nf
    simp

theorem norm_e_sub_one_le (x : ℝ) : ‖e x - 1‖ ≤ 2 * π * |x| := by
  rw [e]
  have harg : 2 * (π : ℂ) * I * (x : ℂ) = I * ((2 * π * x : ℝ) : ℂ) := by
    push_cast
    ring
  rw [harg]
  calc
    ‖Complex.exp (I * ((2 * π * x : ℝ) : ℂ)) - 1‖ ≤ ‖2 * π * x‖ :=
      norm_exp_I_mul_ofReal_sub_one_le
    _ = 2 * π * |x| := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by norm_num),
        abs_of_pos Real.pi_pos]

/-! ### Orthogonality and discrete Fourier inversion -/

/-- **Orthogonality of additive characters.** For `h : ℤ`,
`∑_{k < Q} e (k h / Q)` equals `Q` if `Q ∣ h` and `0` otherwise. -/
theorem sum_e_mul_div {Q : ℕ} (hQ : 0 < Q) (h : ℤ) :
    ∑ k ∈ range Q, e (k * h / Q) = if (Q : ℤ) ∣ h then (Q : ℂ) else 0 := by
  classical
  by_cases hd : (Q : ℤ) ∣ h
  · obtain ⟨c, rfl⟩ := hd
    rw [if_pos (dvd_mul_right (Q : ℤ) c)]
    have hk (k : ℕ) : e (k * (((Q : ℤ) * c : ℤ) : ℝ) / Q) = 1 := by
      rw [show (k * (((Q : ℤ) * c : ℤ) : ℝ) / Q : ℝ) = ((k : ℤ) * c : ℤ) by
        push_cast
        field_simp]
      exact e_intCast _
    rw [Finset.sum_congr rfl fun k hk' => hk k]
    simp
  · simp only [if_neg hd]
    let z : ℂ := e (h / Q)
    have hsum : ∑ k ∈ range Q, e (k * h / Q) = ∑ k ∈ range Q, z ^ k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [show (k * h / Q : ℝ) = k * (h / Q) by ring, e_nat_mul]
    have hzpow : z ^ Q = 1 := by
      rw [← e_nat_mul Q (h / Q)]
      calc
        e (Q * (h / Q)) = e h := by
          congr 1
          field_simp [Nat.cast_ne_zero.mpr hQ.ne']
        _ = 1 := e_intCast h
    have hz : z ≠ 1 := by
      intro hz
      obtain ⟨n, hn⟩ := (e_eq_one_iff _).mp hz
      apply hd
      refine ⟨n, ?_⟩
      have hn' : (h : ℝ) / Q = n := hn
      field_simp [Nat.cast_ne_zero.mpr hQ.ne'] at hn'
      exact_mod_cast hn'
    rw [hsum, geom_sum_eq hz, hzpow]
    simp

/-- **Discrete Fourier inversion.** If all frequencies `g x`, `x ∈ s`, lie within `Q` of `N`,
then the inverse transform at `N` of `k ↦ ∑_{x ∈ s} f x · e (g x · k / Q)` recovers the total
weight of the `x ∈ s` with `g x = N`. -/
theorem sum_mul_e_neg_eq {ι : Type*} (s : Finset ι) (f : ι → ℂ) (g : ι → ℤ) (N : ℤ) {Q : ℕ}
    (hQ : 0 < Q) (hs : ∀ x ∈ s, |g x - N| < Q) :
    (1 / (Q : ℂ)) * ∑ k ∈ range Q, (∑ x ∈ s, f x * e (g x * k / Q)) * e (-(N * k / Q)) =
      ∑ x ∈ s with g x = N, f x := by
  classical
  have h1 (k : ℕ) : (∑ x ∈ s, f x * e (g x * k / Q)) * e (-(N * k / Q)) =
      ∑ x ∈ s, f x * e (k * ((g x - N : ℤ) : ℝ) / Q) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x hx
    rw [mul_assoc, ← e_add]
    congr 2
    push_cast
    ring
  have hdiv (x : ι) (hx : x ∈ s) : (Q : ℤ) ∣ g x - N ↔ g x = N := by
    constructor
    · intro hd
      exact sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd hd (hs x hx))
    · intro h
      rw [h, sub_self]
      exact dvd_zero _
  have horth (x : ι) (hx : x ∈ s) :
      ∑ k ∈ range Q, e (k * ((g x - N : ℤ) : ℝ) / Q) =
        if g x = N then (Q : ℂ) else 0 := by
    rw [sum_e_mul_div hQ (g x - N)]
    exact if_congr (hdiv x hx) rfl rfl
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∑ x ∈ s, ∑ k ∈ range Q, f x * e (k * ((g x - N : ℤ) : ℝ) / Q) =
      ∑ x ∈ s, f x * (if g x = N then (Q : ℂ) else 0) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [← Finset.mul_sum, horth x hx]
  rw [h2]
  simp only [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  have hQ' : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  apply mul_left_cancel₀ hQ'
  field_simp
  rw [Finset.mul_sum]

/-- Squared norm expressed as the real part of a product with its conjugate. -/
private theorem norm_sq_eq_re_mul_conj (z : ℂ) :
    (‖z‖ ^ 2 : ℝ) = (z * (starRingEnd ℂ) z).re := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rfl

/-- A complex number times its conjugate is its squared norm. -/
private theorem mul_conj_eq_norm_sq (z : ℂ) :
    z * (starRingEnd ℂ) z = (‖z‖ ^ 2 : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  norm_cast

/-- **Discrete Parseval identity.** If the frequencies `g x`, `x ∈ s`, are pairwise distinct
modulo `Q`, then `∑_{k < Q} ‖∑_{x ∈ s} f x · e (g x · k / Q)‖² = Q · ∑_{x ∈ s} ‖f x‖²`. -/
theorem sum_norm_sq_sum_mul_e {ι : Type*} (s : Finset ι) (f : ι → ℂ) (g : ι → ℤ) {Q : ℕ}
    (hQ : 0 < Q) (hg : ∀ x ∈ s, ∀ y ∈ s, (Q : ℤ) ∣ g x - g y → x = y) :
    ∑ k ∈ range Q, ‖∑ x ∈ s, f x * e (g x * k / Q)‖ ^ 2 = Q * ∑ x ∈ s, ‖f x‖ ^ 2 := by
  classical
  have hconj (k : ℕ) :
      (starRingEnd ℂ) (∑ x ∈ s, f x * e (g x * k / Q)) =
        ∑ x ∈ s, (starRingEnd ℂ) (f x) * e (-(g x * k / Q)) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [map_mul, ← e_neg]
  have hterm (k : ℕ) (x y : ι) :
      (f x * e (g x * k / Q)) *
          ((starRingEnd ℂ) (f y) * e (-(g y * k / Q))) =
        f x * (starRingEnd ℂ) (f y) * e (k * ((g x - g y : ℤ) : ℝ) / Q) := by
    rw [mul_mul_mul_comm, ← e_add]
    congr 1
    push_cast
    ring
  have hdiv (x : ι) (hx : x ∈ s) (y : ι) (hy : y ∈ s) :
      (Q : ℤ) ∣ g x - g y ↔ x = y := by
    constructor
    · exact hg x hx y hy
    · intro hxy
      rw [hxy, sub_self]
      exact dvd_zero _
  have horth (x : ι) (hx : x ∈ s) (y : ι) (hy : y ∈ s) :
      ∑ k ∈ range Q, e (k * ((g x - g y : ℤ) : ℝ) / Q) =
        if x = y then (Q : ℂ) else 0 := by
    rw [sum_e_mul_div hQ (g x - g y)]
    exact if_congr (hdiv x hx y hy) rfl rfl
  have hcomplex :
      ∑ k ∈ range Q, (∑ x ∈ s, f x * e (g x * k / Q)) *
          (starRingEnd ℂ) (∑ x ∈ s, f x * e (g x * k / Q)) =
        (Q : ℂ) * ∑ x ∈ s, (‖f x‖ ^ 2 : ℂ) := by
    calc
      ∑ k ∈ range Q, (∑ x ∈ s, f x * e (g x * k / Q)) *
          (starRingEnd ℂ) (∑ x ∈ s, f x * e (g x * k / Q)) =
          ∑ k ∈ range Q, ∑ x ∈ s, ∑ y ∈ s,
            f x * (starRingEnd ℂ) (f y) * e (k * ((g x - g y : ℤ) : ℝ) / Q) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hconj k, Finset.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        exact hterm k x y
      _ = ∑ x ∈ s, ∑ k ∈ range Q, ∑ y ∈ s,
            f x * (starRingEnd ℂ) (f y) * e (k * ((g x - g y : ℤ) : ℝ) / Q) :=
        Finset.sum_comm
      _ = ∑ x ∈ s, ∑ y ∈ s, ∑ k ∈ range Q,
            f x * (starRingEnd ℂ) (f y) * e (k * ((g x - g y : ℤ) : ℝ) / Q) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact Finset.sum_comm
      _ = ∑ x ∈ s, ∑ y ∈ s, f x * (starRingEnd ℂ) (f y) *
            ∑ k ∈ range Q, e (k * ((g x - g y : ℤ) : ℝ) / Q) := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        rw [← Finset.mul_sum]
      _ = ∑ x ∈ s, f x * (starRingEnd ℂ) (f x) * Q := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.sum_eq_single_of_mem x hx]
        · rw [horth x hx x hx]
          simp
        · intro y hy hyx
          rw [horth x hx y hy, if_neg (Ne.symm hyx)]
          simp
      _ = (Q : ℂ) * ∑ x ∈ s, (‖f x‖ ^ 2 : ℂ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        rw [mul_conj_eq_norm_sq]
        ring
  calc
    ∑ k ∈ range Q, ‖∑ x ∈ s, f x * e (g x * k / Q)‖ ^ 2 =
        (∑ k ∈ range Q, (∑ x ∈ s, f x * e (g x * k / Q)) *
          (starRingEnd ℂ) (∑ x ∈ s, f x * e (g x * k / Q))).re := by
      rw [Complex.re_sum]
      apply Finset.sum_congr rfl
      intro k hk
      exact norm_sq_eq_re_mul_conj _
    _ = ((Q : ℂ) * ∑ x ∈ s, (‖f x‖ ^ 2 : ℂ)).re := congrArg Complex.re hcomplex
    _ = Q * ∑ x ∈ s, ‖f x‖ ^ 2 := by
      rw [Complex.mul_re, Complex.re_sum]
      simp
      left
      apply Finset.sum_congr rfl
      intro x hx
      rw [← Complex.ofReal_pow]
      exact Complex.ofReal_re _

/-- **Parseval identity for the inverse transform.** -/
theorem sum_norm_sq_sum_mul_e_neg {Q : ℕ} (hQ : 0 < Q) (F : ℕ → ℂ) :
    ∑ N ∈ range Q, ‖(1 / (Q : ℂ)) * ∑ k ∈ range Q, F k * e (-(N * k / Q))‖ ^ 2 =
      (1 / (Q : ℝ)) * ∑ k ∈ range Q, ‖F k‖ ^ 2 := by
  have hfreq (k : ℕ) (hk : k ∈ range Q) (l : ℕ) (hl : l ∈ range Q) :
      (Q : ℤ) ∣ (-(k : ℤ)) - -(l : ℤ) → k = l := by
    intro hd
    have hkQ : k < Q := mem_range.mp hk
    have hlQ : l < Q := mem_range.mp hl
    have hd' : (Q : ℤ) ∣ (l : ℤ) - k := by
      convert hd using 1
      ring
    have habs : |(l : ℤ) - k| < (Q : ℤ) := by
      rw [abs_lt]
      constructor <;> omega
    have hzero : (l : ℤ) - k = 0 := Int.eq_zero_of_abs_lt_dvd hd' habs
    omega
  have hparseval := sum_norm_sq_sum_mul_e (range Q) F (fun k => -(k : ℤ)) hQ hfreq
  have hparseval' :
      ∑ N ∈ range Q, ‖∑ k ∈ range Q, F k * e (-(N * k / Q))‖ ^ 2 =
        Q * ∑ k ∈ range Q, ‖F k‖ ^ 2 := by
    convert hparseval using 1
    apply Finset.sum_congr rfl
    intro N hN
    congr 2
    apply Finset.sum_congr rfl
    intro k hk
    congr 2
    push_cast
    ring
  have hnorm : ‖1 / (Q : ℂ)‖ = 1 / (Q : ℝ) := by
    rw [norm_div, norm_one, Complex.norm_natCast]
  calc
    ∑ N ∈ range Q, ‖(1 / (Q : ℂ)) * ∑ k ∈ range Q, F k * e (-(N * k / Q))‖ ^ 2 =
        ∑ N ∈ range Q, (1 / (Q : ℝ)) ^ 2 *
          ‖∑ k ∈ range Q, F k * e (-(N * k / Q))‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro N hN
      rw [norm_mul, hnorm, mul_pow]
    _ = (1 / (Q : ℝ)) ^ 2 *
          ∑ N ∈ range Q, ‖∑ k ∈ range Q, F k * e (-(N * k / Q))‖ ^ 2 := by
      rw [Finset.mul_sum]
    _ = (1 / (Q : ℝ)) * ∑ k ∈ range Q, ‖F k‖ ^ 2 := by
      rw [hparseval']
      field_simp [Nat.cast_ne_zero.mpr hQ.ne']

/-! ### Distance to the nearest integer -/

/-- The distance from `θ` to the nearest integer. -/
noncomputable def distInt (θ : ℝ) : ℝ := |θ - round θ|

theorem distInt_nonneg (θ : ℝ) : 0 ≤ distInt θ := abs_nonneg _

theorem distInt_le_half (θ : ℝ) : distInt θ ≤ 1 / 2 := by
  exact abs_sub_round θ

theorem distInt_le_abs (θ : ℝ) : distInt θ ≤ |θ| := by
  simpa [distInt] using round_le θ 0

theorem distInt_eq_abs_of_abs_le_half {θ : ℝ} (hθ : |θ| ≤ 1 / 2) : distInt θ = |θ| := by
  by_cases hneg : θ < 0
  · have h : round θ = 0 := by
      apply (round_eq_zero_iff).2
      constructor
      · linarith [neg_le_of_abs_le hθ]
      · linarith [abs_nonneg θ]
    simp [distInt, h, abs_of_neg hneg]
  · have hnonneg : 0 ≤ θ := le_of_not_gt hneg
    have hupper : θ ≤ 1 / 2 := by simpa [abs_of_nonneg hnonneg] using hθ
    by_cases hlt : θ < 1 / 2
    · have h : round θ = 0 := (round_eq_zero_iff).2 ⟨by linarith, hlt⟩
      simp [distInt, h, abs_of_nonneg hnonneg]
    · have : θ = 1 / 2 := le_antisymm hupper (le_of_not_gt hlt)
      subst θ
      norm_num [distInt]

theorem distInt_add_intCast (θ : ℝ) (n : ℤ) : distInt (θ + n) = distInt θ := by
  simp [distInt, round_add_intCast, sub_eq_add_neg, add_assoc, add_comm]

theorem distInt_neg (θ : ℝ) : distInt (-θ) = distInt θ := by
  unfold distInt
  rw [abs_sub_round_eq_min, abs_sub_round_eq_min]
  by_cases h : Int.fract θ = 0
  · have h' : Int.fract (-θ) = 0 := (Int.fract_neg_eq_zero).2 h
    simp [h, h']
  · rw [Int.fract_neg h]
    simp [min_comm]

theorem distInt_eq_zero_iff (θ : ℝ) : distInt θ = 0 ↔ ∃ n : ℤ, θ = n := by
  simp only [distInt, abs_eq_zero, sub_eq_zero]
  constructor
  · intro h
    exact ⟨round θ, h⟩
  · rintro ⟨n, rfl⟩
    simp

/-- The standard lower bound `‖e θ - 1‖ = 2 |sin (π θ)| ≥ 4 ‖θ‖`. -/
theorem four_mul_distInt_le_norm_e_sub_one (θ : ℝ) : 4 * distInt θ ≤ ‖e θ - 1‖ := by
  let x : ℝ := θ - round θ
  have hx : |x| ≤ 1 / 2 := by
    simpa [x, distInt] using distInt_le_half θ
  have he : e θ = e x := by
    rw [show θ = x + round θ by dsimp [x]; ring, e_add_intCast]
  have hnorm : ‖e x - 1‖ = 2 * |Real.sin (π * x)| := by
    rw [e]
    have harg : 2 * (π : ℂ) * I * (x : ℂ) = I * ((2 * π * x : ℝ) : ℂ) := by
      push_cast
      ring
    rw [harg, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by norm_num)]
    congr 2
    ring
  have hxp : π * |x| ≤ π / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hx Real.pi_pos.le]
  have hsin : 2 * |x| ≤ Real.sin (π * |x|) := by
    calc
      2 * |x| = 2 / π * (π * |x|) := by field_simp
      _ ≤ Real.sin (π * |x|) :=
        Real.mul_le_sin (mul_nonneg Real.pi_pos.le (abs_nonneg _)) hxp
  have hsin_abs : |Real.sin (π * x)| = Real.sin (π * |x|) := by
    have hpi : π / 2 ≤ π := by nlinarith [Real.pi_pos]
    have habs : |π * x| ≤ π := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      exact hxp.trans hpi
    simpa [abs_mul, abs_of_pos Real.pi_pos] using
      Real.abs_sin_eq_sin_abs_of_abs_le_pi habs
  change 4 * |x| ≤ ‖e θ - 1‖
  rw [he, hnorm, hsin_abs]
  linarith

/-! ### The geometric-series bound -/

/-- Trivial bound for a sum of characters over an interval. -/
theorem norm_sum_e_Icc_le_card (a b : ℕ) (θ : ℝ) :
    ‖∑ n ∈ Icc a b, e (n * θ)‖ ≤ #(Icc a b) := by
  calc
    ‖∑ n ∈ Icc a b, e (n * θ)‖ ≤
        ∑ n ∈ Icc a b, ‖e (n * θ)‖ := norm_sum_le (Icc a b) _
    _ = #(Icc a b) := by simp

/-- **Geometric-series bound.** For `θ` not an integer,
`‖∑_{n ∈ [a, b]} e (n θ)‖ ≤ 1 / (2 ‖θ‖)`, where `‖θ‖ = distInt θ`. -/
theorem norm_sum_e_Icc_le (a b : ℕ) {θ : ℝ} (hθ : distInt θ ≠ 0) :
    ‖∑ n ∈ Icc a b, e (n * θ)‖ ≤ 1 / (2 * distInt θ) := by
  by_cases hab : a ≤ b
  · have hsum :
        ∑ n ∈ Icc a b, e (n * θ) =
          e (a * θ) * ∑ i ∈ range (b + 1 - a), e θ ^ i := by
      rw [show Icc a b = Ico a (b + 1) by ext; simp,
        Finset.sum_Ico_eq_sum_range]
      convert (show
        ∑ i ∈ range (b + 1 - a), e ((a : ℝ) * θ + i * θ) =
          e (a * θ) * ∑ i ∈ range (b + 1 - a), e θ ^ i from by
        calc
          ∑ i ∈ range (b + 1 - a), e ((a : ℝ) * θ + i * θ) =
              ∑ i ∈ range (b + 1 - a), e (a * θ) * e (i * θ) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [e_add]
          _ = ∑ i ∈ range (b + 1 - a), e (a * θ) * e θ ^ i := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [e_nat_mul i θ]
          _ = e (a * θ) * ∑ i ∈ range (b + 1 - a), e θ ^ i :=
            (Finset.mul_sum _ _ _).symm) using 1
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      push_cast
      ring
    have hene : e θ ≠ 1 := by
      intro he
      obtain ⟨n, hn⟩ := (e_eq_one_iff _).mp he
      apply hθ
      exact (distInt_eq_zero_iff θ).mpr ⟨n, hn⟩
    have hnum : ‖e θ ^ (b + 1 - a) - 1‖ ≤ 2 := by
      calc
        ‖e θ ^ (b + 1 - a) - 1‖ ≤ ‖e θ ^ (b + 1 - a)‖ + ‖1‖ :=
          norm_sub_le _ _
        _ = 2 := by norm_num
    have hdist : 0 < distInt θ := lt_of_le_of_ne (distInt_nonneg _) (Ne.symm hθ)
    have hden : 4 * distInt θ ≤ ‖e θ - 1‖ :=
      four_mul_distInt_le_norm_e_sub_one θ
    have hden_pos : 0 < ‖e θ - 1‖ :=
      lt_of_lt_of_le (mul_pos (by norm_num) hdist) hden
    rw [hsum, geom_sum_eq hene, norm_mul, norm_e, one_mul, norm_div]
    calc
      ‖e θ ^ (b + 1 - a) - 1‖ / ‖e θ - 1‖ ≤ 2 / ‖e θ - 1‖ :=
        (div_le_div_iff_of_pos_right hden_pos).mpr hnum
      _ ≤ 2 / (4 * distInt θ) := by
        rw [div_le_iff₀ hden_pos]
        calc
          2 = (2 / (4 * distInt θ)) * (4 * distInt θ) := by field_simp
          _ ≤ (2 / (4 * distInt θ)) * ‖e θ - 1‖ :=
            mul_le_mul_of_nonneg_left hden (by positivity)
      _ = 1 / (2 * distInt θ) := by field_simp; ring
  · rw [Finset.Icc_eq_empty_of_lt (lt_of_not_ge hab)]
    simp only [sum_empty, norm_zero]
    have hdist : 0 < distInt θ := lt_of_le_of_ne (distInt_nonneg _) (Ne.symm hθ)
    exact div_nonneg (by norm_num) (le_of_lt (mul_pos (by norm_num) hdist))

/-! ### Summation by parts -/

/-- Finite Abel summation over a nonempty half-open natural interval. -/
private theorem sum_Ioc_sub_mul_eq (A v : ℕ → ℂ) {L R : ℕ} (hLR : L < R) :
    ∑ n ∈ Ioc L R, (A n - A (n - 1)) * v n =
      A R * v R - A L * v (L + 1) -
        ∑ n ∈ Ico (L + 1) R, A n * (v (n + 1) - v n) := by
  refine Nat.le_induction ?_ ?_ R (Nat.succ_le_iff.mpr hLR)
  · simp [sub_mul]
  intro R hR ih
  rw [sum_Ioc_succ_top (Nat.le_of_succ_le hR), ih, sum_Ico_succ_top hR]
  simp only [Nat.add_sub_cancel]
  ring

/-- A sequence value is controlled by a later value and its intervening variation. -/
private theorem norm_le_norm_add_sum_norm_sub (v : ℕ → ℂ) {L R : ℕ} (hLR : L < R) :
    ‖v (L + 1)‖ ≤ ‖v R‖ + ∑ n ∈ Ico (L + 1) R, ‖v (n + 1) - v n‖ := by
  refine Nat.le_induction ?_ ?_ R (Nat.succ_le_iff.mpr hLR)
  · simp
  intro R hR ih
  rw [sum_Ico_succ_top hR]
  have hnorm := norm_sub_norm_le (v R) (v (R + 1))
  have hdiff : ‖v R - v (R + 1)‖ = ‖v (R + 1) - v R‖ := by
    rw [show v (R + 1) - v R = -(v R - v (R + 1)) by ring, norm_neg]
  rw [hdiff] at hnorm
  linarith

/-- **Summation by parts, comparison form.** If the partial sums of `f` and `g` over `[1, n]`
differ by at most `D` for all `n ∈ [L, R]`, then `∑_{n ∈ (L, R]} (f n - g n) v n` is bounded by
`2 D` times the total variation of `v` on `[L, R]` plus `‖v R‖`. -/
theorem norm_sum_Ioc_sub_mul_le (f g v : ℕ → ℂ) {L R : ℕ} (hLR : L ≤ R) {D : ℝ}
    (hD : ∀ n ∈ Icc L R, ‖∑ m ∈ Icc 1 n, f m - ∑ m ∈ Icc 1 n, g m‖ ≤ D) :
    ‖∑ n ∈ Ioc L R, (f n - g n) * v n‖ ≤
      2 * D * (‖v R‖ + ∑ n ∈ Ico L R, ‖v (n + 1) - v n‖) := by
  by_cases hEq : L = R
  · subst R
    have hD0 : 0 ≤ D :=
      (norm_nonneg _).trans (hD L (Finset.mem_Icc.mpr ⟨le_rfl, le_rfl⟩))
    simp
    positivity
  · have hLR : L < R := lt_of_le_of_ne hLR hEq
    let A : ℕ → ℂ := fun n ↦ ∑ m ∈ Icc 1 n, (f m - g m)
    have hA (n : ℕ) (hn : n ∈ Icc L R) : ‖A n‖ ≤ D := by
      rw [show A n = ∑ m ∈ Icc 1 n, f m - ∑ m ∈ Icc 1 n, g m by
        dsimp [A]
        rw [sum_sub_distrib]]
      exact hD n hn
    have hD0 : 0 ≤ D :=
      (norm_nonneg _).trans (hA L (Finset.mem_Icc.mpr ⟨le_rfl, hLR.le⟩))
    have hdiff (n : ℕ) (hn : n ∈ Ioc L R) : f n - g n = A n - A (n - 1) := by
      have hn1 : 1 ≤ n := Nat.succ_le_iff.mpr (Nat.zero_lt_of_lt (mem_Ioc.mp hn).1)
      dsimp [A]
      rw [← Nat.sub_add_cancel hn1, sum_Icc_succ_top (by omega)]
      simp only [Nat.add_sub_cancel]
      ring
    have hsum :
        ∑ n ∈ Ioc L R, (f n - g n) * v n =
          ∑ n ∈ Ioc L R, (A n - A (n - 1)) * v n := by
      apply sum_congr rfl
      intro n hn
      rw [hdiff n hn]
    have habel := sum_Ioc_sub_mul_eq A v hLR
    have hsmall :
        ∑ n ∈ Ico (L + 1) R, ‖v (n + 1) - v n‖ ≤
          ∑ n ∈ Ico L R, ‖v (n + 1) - v n‖ := by
      apply sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_left (Nat.le_succ L))
      intro n hn _
      exact norm_nonneg _
    have hvariation :
        ‖v (L + 1)‖ ≤ ‖v R‖ + ∑ n ∈ Ico L R, ‖v (n + 1) - v n‖ :=
      (norm_le_norm_add_sum_norm_sub v hLR).trans (add_le_add_right hsmall _)
    have hfirst : ‖A R * v R‖ ≤ D * ‖v R‖ := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (hA R (Finset.mem_Icc.mpr ⟨hLR.le, le_rfl⟩)) (norm_nonneg _)
    have hsecond :
        ‖A L * v (L + 1)‖ ≤
          D * (‖v R‖ + ∑ n ∈ Ico L R, ‖v (n + 1) - v n‖) := by
      rw [norm_mul]
      calc
        ‖A L‖ * ‖v (L + 1)‖ ≤ D * ‖v (L + 1)‖ :=
          mul_le_mul_of_nonneg_right
            (hA L (Finset.mem_Icc.mpr ⟨le_rfl, hLR.le⟩)) (norm_nonneg _)
        _ ≤ D * (‖v R‖ + ∑ n ∈ Ico L R, ‖v (n + 1) - v n‖) :=
          mul_le_mul_of_nonneg_left hvariation hD0
    have hthird :
        ‖∑ n ∈ Ico (L + 1) R, A n * (v (n + 1) - v n)‖ ≤
          D * ∑ n ∈ Ico L R, ‖v (n + 1) - v n‖ := by
      calc
        ‖∑ n ∈ Ico (L + 1) R, A n * (v (n + 1) - v n)‖ ≤
            ∑ n ∈ Ico (L + 1) R, ‖A n * (v (n + 1) - v n)‖ :=
          norm_sum_le _ _
        _ ≤ ∑ n ∈ Ico (L + 1) R, D * ‖v (n + 1) - v n‖ := by
          apply sum_le_sum
          intro n hn
          rw [norm_mul]
          apply mul_le_mul_of_nonneg_right
          · apply hA n
            exact Finset.mem_Icc.mpr
              ⟨le_trans (Nat.le_succ L) (mem_Ico.mp hn).1, (mem_Ico.mp hn).2.le⟩
          · exact norm_nonneg _
        _ = D * ∑ n ∈ Ico (L + 1) R, ‖v (n + 1) - v n‖ := (mul_sum _ _ _).symm
        _ ≤ D * ∑ n ∈ Ico L R, ‖v (n + 1) - v n‖ :=
          mul_le_mul_of_nonneg_left hsmall hD0
    rw [hsum, habel]
    calc
      ‖A R * v R - A L * v (L + 1) -
          ∑ n ∈ Ico (L + 1) R, A n * (v (n + 1) - v n)‖ ≤
          ‖A R * v R - A L * v (L + 1)‖ +
            ‖∑ n ∈ Ico (L + 1) R, A n * (v (n + 1) - v n)‖ :=
        norm_sub_le _ _
      _ ≤ (‖A R * v R‖ + ‖A L * v (L + 1)‖) +
            ‖∑ n ∈ Ico (L + 1) R, A n * (v (n + 1) - v n)‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ (D * ‖v R‖ +
            D * (‖v R‖ + ∑ n ∈ Ico L R, ‖v (n + 1) - v n‖)) +
            D * ∑ n ∈ Ico L R, ‖v (n + 1) - v n‖ :=
        add_le_add (add_le_add hfirst hsecond) hthird
      _ = 2 * D * (‖v R‖ + ∑ n ∈ Ico L R, ‖v (n + 1) - v n‖) := by ring

end CircleMethod
