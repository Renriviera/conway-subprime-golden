/-
Copyright (c) 2026 Romain Popescu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Romain Popescu
-/
import ConwayGolden.NumberTheory.CircleMethod.Inputs
import ConwayGolden.Subprime.Hypotheses

/-!
# Set-up of the discrete circle method for `N = ν p + q`

We fix proportional ranges `p ∈ [α X, β X]`, `q ∈ [γ X, δ X]`, a coefficient `ν ∈ {1, 2}` and a
target bound `N ≤ B X`, packaged as `CircleMethod.Ranges`. This file defines the weighted
representation count, the generating exponential sums, the modulus `Q` of the discrete circle,
and proves the exact Fourier inversion formulas.

## Main definitions

* `CircleMethod.Ranges`: the fixed parameters `ν, α, β, γ, δ, η, B` and their constraints.
* `Ranges.I R X`, `Ranges.J R X`: the integer intervals `[α X, β X]`, `[γ X, δ X]`.
* `Ranges.rep R X N`: the weighted count `∑_{ν m + n = N} Λ m Λ n` over `m ∈ I`, `n ∈ J`.
* `Ranges.count R X N`: the number of pairs `(m, n) ∈ I × J` with `ν m + n = N`.
* `Ranges.SI`, `Ranges.SJ`, `Ranges.TI`, `Ranges.TJ`: the exponential sums
  `∑ Λ m e (ν m θ)`, `∑ Λ n e (n θ)`, `∑ e (ν m θ)`, `∑ e (n θ)`.
* `Ranges.Q R X P`: the modulus `P! · (⌊span⌋ + 1)`, divisible by every `q ≤ P` and larger than
  every `ν m + n` and every target `N`.

## Main statements

* `Ranges.rep_eq_sum`: `rep N = Q⁻¹ ∑_{k < Q} SI(k/Q) SJ(k/Q) e (-N k / Q)`.
* `Ranges.count_eq_sum`: the same identity for the unweighted count.
* `Ranges.le_count_of_isAdmissible`: `η X - 1 ≤ count N` for admissible `N`.
* `Ranges.hasPrimeRepr_of_lt_rep`: de-weighting: if `rep N` exceeds the contribution of proper
  prime powers, `N` has a representation by primes in the ranges.
-/

namespace CircleMethod

open Finset Real
open scoped ArithmeticFunction.vonMangoldt

/-- The fixed parameters of the restricted binary problem `N = ν p + q`,
`p ∈ [α X, β X]`, `q ∈ [γ X, δ X]`, `N ≤ B X`, with admissibility margin `η`. -/
structure Ranges where
  /-- The coefficient of the first prime; `1` or `2`. -/
  ν : ℕ
  /-- Lower endpoint ratio for `p`. -/
  α : ℝ
  /-- Upper endpoint ratio for `p`. -/
  β : ℝ
  /-- Lower endpoint ratio for `q`. -/
  γ : ℝ
  /-- Upper endpoint ratio for `q`. -/
  δ : ℝ
  /-- Admissibility margin ratio. -/
  η : ℝ
  /-- Upper bound ratio for the targets `N`. -/
  B : ℝ
  ν_eq : ν = 1 ∨ ν = 2
  α_pos : 0 < α
  α_lt_β : α < β
  γ_pos : 0 < γ
  γ_lt_δ : γ < δ
  η_pos : 0 < η
  B_pos : 0 < B

namespace Ranges

variable (R : Ranges) (X : ℝ)

theorem one_le_ν : 1 ≤ R.ν := by
  rcases R.ν_eq with h | h <;> omega

theorem ν_le_two : R.ν ≤ 2 := by
  rcases R.ν_eq with h | h <;> omega

/-! ### Intervals and counting functions -/

/-- The integers in `[α X, β X]`. -/
noncomputable def I : Finset ℕ := Icc ⌈R.α * X⌉₊ ⌊R.β * X⌋₊

/-- The integers in `[γ X, δ X]`. -/
noncomputable def J : Finset ℕ := Icc ⌈R.γ * X⌉₊ ⌊R.δ * X⌋₊

theorem mem_I (hX : 0 ≤ X) {m : ℕ} : m ∈ R.I X ↔ R.α * X ≤ m ∧ (m : ℝ) ≤ R.β * X := by
  rw [I, Finset.mem_Icc, Nat.ceil_le,
    Nat.le_floor_iff (mul_nonneg (R.α_pos.trans R.α_lt_β).le hX)]

theorem mem_J (hX : 0 ≤ X) {n : ℕ} : n ∈ R.J X ↔ R.γ * X ≤ n ∧ (n : ℝ) ≤ R.δ * X := by
  rw [J, Finset.mem_Icc, Nat.ceil_le, Nat.le_floor_iff (mul_nonneg (R.γ_pos.trans R.γ_lt_δ).le hX)]

theorem card_I_le (hX : 0 ≤ X) : (#(R.I X) : ℝ) ≤ R.β * X + 1 := by
  simp only [I]
  rw [Nat.card_Icc]
  have hβ : 0 ≤ R.β * X := mul_nonneg
    (le_of_lt (R.α_pos.trans R.α_lt_β)) hX
  calc
    (↑(⌊R.β * X⌋₊ + 1 - ⌈R.α * X⌉₊) : ℝ) ≤
        (↑(⌊R.β * X⌋₊ + 1) : ℝ) := by
      exact_mod_cast Nat.sub_le _ _
    _ ≤ R.β * X + 1 := by
      norm_num only [Nat.cast_add, Nat.cast_one]
      linarith [Nat.floor_le hβ]

theorem card_J_le (hX : 0 ≤ X) : (#(R.J X) : ℝ) ≤ R.δ * X + 1 := by
  simp only [J]
  rw [Nat.card_Icc]
  have hδ : 0 ≤ R.δ * X := mul_nonneg
    (le_of_lt (R.γ_pos.trans R.γ_lt_δ)) hX
  calc
    (↑(⌊R.δ * X⌋₊ + 1 - ⌈R.γ * X⌉₊) : ℝ) ≤
        (↑(⌊R.δ * X⌋₊ + 1) : ℝ) := by
      exact_mod_cast Nat.sub_le _ _
    _ ≤ R.δ * X + 1 := by
      norm_num only [Nat.cast_add, Nat.cast_one]
      linarith [Nat.floor_le hδ]

/-- The weighted representation count `∑_{m ∈ I, n ∈ J, ν m + n = N} Λ m Λ n`. -/
noncomputable def rep (N : ℕ) : ℝ :=
  ∑ p ∈ R.I X ×ˢ R.J X with R.ν * p.1 + p.2 = N, Λ p.1 * Λ p.2

/-- The number of pairs `(m, n) ∈ I × J` with `ν m + n = N`. -/
noncomputable def count (N : ℕ) : ℕ := #{p ∈ R.I X ×ˢ R.J X | R.ν * p.1 + p.2 = N}

/-! ### Exponential sums -/

/-- `SI θ = ∑_{m ∈ I} Λ m · e (ν m θ)`. -/
noncomputable def SI (θ : ℝ) : ℂ := ∑ m ∈ R.I X, (Λ m : ℂ) * e (R.ν * m * θ)

/-- `SJ θ = ∑_{n ∈ J} Λ n · e (n θ)`. -/
noncomputable def SJ (θ : ℝ) : ℂ := ∑ n ∈ R.J X, (Λ n : ℂ) * e (n * θ)

/-- `TI θ = ∑_{m ∈ I} e (ν m θ)`. -/
noncomputable def TI (θ : ℝ) : ℂ := ∑ m ∈ R.I X, e (R.ν * m * θ)

/-- `TJ θ = ∑_{n ∈ J} e (n θ)`. -/
noncomputable def TJ (θ : ℝ) : ℂ := ∑ n ∈ R.J X, e (n * θ)

theorem SI_add_one (θ : ℝ) : R.SI X (θ + 1) = R.SI X θ := by
  simp only [SI]
  apply Finset.sum_congr rfl
  intro m hm
  rw [show R.ν * (m : ℝ) * (θ + 1) = R.ν * m * θ + (R.ν * m : ℤ) by
    push_cast
    ring, e_add_intCast]

theorem SJ_add_one (θ : ℝ) : R.SJ X (θ + 1) = R.SJ X θ := by
  simp only [SJ]
  apply Finset.sum_congr rfl
  intro n hn
  rw [show (n : ℝ) * (θ + 1) = n * θ + (n : ℤ) by
    push_cast
    ring, e_add_intCast]

theorem norm_SI_le (hX : 1 ≤ X) (θ : ℝ) :
    ‖R.SI X θ‖ ≤ (R.β * X + 1) * log (R.β * X + 1) := by
  have hX0 : 0 ≤ X := by linarith
  have hβ : 0 ≤ R.β * X := mul_nonneg
    (R.α_pos.trans R.α_lt_β).le hX0
  have hlog : 0 ≤ log (R.β * X + 1) :=
    Real.log_nonneg (by linarith)
  rw [SI]
  calc
    ‖∑ m ∈ R.I X, (Λ m : ℂ) * e (R.ν * m * θ)‖ ≤
        ∑ m ∈ R.I X, ‖(Λ m : ℂ) * e (R.ν * m * θ)‖ := norm_sum_le _ _
    _ = ∑ m ∈ R.I X, (Λ m : ℝ) := by
      apply Finset.sum_congr rfl
      intro m hm
      simp only [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    _ ≤ ∑ _m ∈ R.I X, log (R.β * X + 1) := by
      apply Finset.sum_le_sum
      intro m hm
      have hm' := (R.mem_I X hX0).mp hm
      have hmpos : 0 < (m : ℝ) := lt_of_lt_of_le
        (mul_pos R.α_pos (lt_of_lt_of_le zero_lt_one hX)) hm'.1
      have hm1 : 1 ≤ m := by
        have : 0 < m := by exact_mod_cast hmpos
        omega
      apply vonMangoldt_le_log_of_le hm1
      linarith [hm'.2]
    _ = (#(R.I X) : ℝ) * log (R.β * X + 1) := by
      simp [nsmul_eq_mul]
    _ ≤ (R.β * X + 1) * log (R.β * X + 1) :=
      mul_le_mul_of_nonneg_right (R.card_I_le X hX0) hlog

theorem norm_SJ_le (hX : 1 ≤ X) (θ : ℝ) :
    ‖R.SJ X θ‖ ≤ (R.δ * X + 1) * log (R.δ * X + 1) := by
  have hX0 : 0 ≤ X := by linarith
  have hδ : 0 ≤ R.δ * X := mul_nonneg
    (R.γ_pos.trans R.γ_lt_δ).le hX0
  have hlog : 0 ≤ log (R.δ * X + 1) :=
    Real.log_nonneg (by linarith)
  rw [SJ]
  calc
    ‖∑ n ∈ R.J X, (Λ n : ℂ) * e (n * θ)‖ ≤
        ∑ n ∈ R.J X, ‖(Λ n : ℂ) * e (n * θ)‖ := norm_sum_le _ _
    _ = ∑ n ∈ R.J X, (Λ n : ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      simp only [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    _ ≤ ∑ _n ∈ R.J X, log (R.δ * X + 1) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn' := (R.mem_J X hX0).mp hn
      have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le
        (mul_pos R.γ_pos (lt_of_lt_of_le zero_lt_one hX)) hn'.1
      have hn1 : 1 ≤ n := by
        have : 0 < n := by exact_mod_cast hnpos
        omega
      apply vonMangoldt_le_log_of_le hn1
      linarith [hn'.2]
    _ = (#(R.J X) : ℝ) * log (R.δ * X + 1) := by
      simp [nsmul_eq_mul]
    _ ≤ (R.δ * X + 1) * log (R.δ * X + 1) :=
      mul_le_mul_of_nonneg_right (R.card_J_le X hX0) hlog

theorem norm_TI_le (hX : 0 ≤ X) (θ : ℝ) : ‖R.TI X θ‖ ≤ R.β * X + 1 := by
  rw [TI]
  calc
    ‖∑ m ∈ R.I X, e (R.ν * m * θ)‖ ≤
        ∑ m ∈ R.I X, ‖e (R.ν * m * θ)‖ := norm_sum_le _ _
    _ = (#(R.I X) : ℝ) := by simp [norm_e]
    _ ≤ R.β * X + 1 := R.card_I_le X hX

theorem norm_TJ_le (hX : 0 ≤ X) (θ : ℝ) : ‖R.TJ X θ‖ ≤ R.δ * X + 1 := by
  rw [TJ]
  calc
    ‖∑ n ∈ R.J X, e (n * θ)‖ ≤
        ∑ n ∈ R.J X, ‖e (n * θ)‖ := norm_sum_le _ _
    _ = (#(R.J X) : ℝ) := by simp [norm_e]
    _ ≤ R.δ * X + 1 := R.card_J_le X hX

/-- The geometric-series bound for `TJ`. -/
theorem norm_TJ_le_inv (θ : ℝ) (hθ : distInt θ ≠ 0) : ‖R.TJ X θ‖ ≤ 1 / (2 * distInt θ) := by
  rw [TJ]
  exact norm_sum_e_Icc_le _ _ hθ

/-- The geometric-series bound for `TI` (at frequency `ν θ`). -/
theorem norm_TI_le_inv (θ : ℝ) (hθ : distInt (R.ν * θ) ≠ 0) :
    ‖R.TI X θ‖ ≤ 1 / (2 * distInt (R.ν * θ)) := by
  rw [TI]
  rw [I]
  have he :
      (∑ m ∈ Icc ⌈R.α * X⌉₊ ⌊R.β * X⌋₊, e (R.ν * m * θ)) =
        ∑ m ∈ Icc ⌈R.α * X⌉₊ ⌊R.β * X⌋₊, e (m * (R.ν * θ)) := by
    apply Finset.sum_congr rfl
    intro m hm
    congr 1
    ring
  rw [he]
  exact norm_sum_e_Icc_le _ _ hθ

/-! ### The modulus of the discrete circle -/

/-- Every `ν m + n` with `m ∈ I`, `n ∈ J` and every target `N ≤ B X` is below `span`. -/
noncomputable def span : ℝ := (R.ν * R.β + R.δ + R.B) * X

theorem span_pos (hX : 0 < X) : 0 < R.span X := by
  rw [span]
  have hν : 1 ≤ R.ν := R.one_le_ν
  have hβ : 0 < R.β := R.α_pos.trans R.α_lt_β
  have hδ : 0 < R.δ := R.γ_pos.trans R.γ_lt_δ
  have hν' : 0 < (R.ν : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hν)
  have hcoef : 0 < (R.ν : ℝ) * R.β + R.δ + R.B := by
    exact add_pos (add_pos (mul_pos hν' hβ) hδ) R.B_pos
  exact mul_pos hcoef hX

/-- The modulus `Q = P! · (⌊span⌋₊ + 1)`. -/
noncomputable def Q (P : ℕ) : ℕ := P.factorial * (⌊R.span X⌋₊ + 1)

variable (P : ℕ)

theorem Q_pos : 0 < R.Q X P := by
  rw [Q]
  exact Nat.mul_pos (Nat.factorial_pos P) (Nat.succ_pos _)

theorem span_lt_Q : R.span X < R.Q X P := by
  have hfloor : R.span X < (⌊R.span X⌋₊ + 1 : ℕ) := by
    simpa using (Nat.lt_floor_add_one (R.span X))
  have hmul : (⌊R.span X⌋₊ + 1 : ℕ) ≤ R.Q X P := by
    rw [Q]
    exact Nat.le_mul_of_pos_left _ (Nat.factorial_pos P)
  exact hfloor.trans_le (by exact_mod_cast hmul)

theorem dvd_Q {q : ℕ} (hq0 : 0 < q) (hqP : q ≤ P) : q ∣ R.Q X P := by
  rw [Q]
  exact dvd_mul_of_dvd_left (Nat.dvd_factorial hq0 hqP) _

theorem le_Q_of_le (hX : 0 ≤ X) {x : ℝ} (hx : x ≤ R.B * X) : x < R.Q X P := by
  have hBX : R.B * X ≤ R.span X := by
    rw [span]
    have hν : 0 ≤ (R.ν : ℝ) := by exact_mod_cast (Nat.zero_le R.ν)
    have hβ : 0 < R.β := R.α_pos.trans R.α_lt_β
    have hδ : 0 < R.δ := R.γ_pos.trans R.γ_lt_δ
    nlinarith [mul_nonneg
      (add_nonneg (mul_nonneg hν (le_of_lt hβ)) (le_of_lt hδ)) hX]
  exact lt_of_le_of_lt (hx.trans hBX) (R.span_lt_Q X P)

/-- All frequencies `ν m + n`, `m ∈ I`, `n ∈ J`, lie in `[0, Q)`. -/
theorem add_lt_Q (hX : 0 ≤ X) {m n : ℕ} (hm : m ∈ R.I X) (hn : n ∈ R.J X) :
    R.ν * m + n < R.Q X P := by
  have hm' : m ∈ (Icc ⌈R.α * X⌉₊ ⌊R.β * X⌋₊ : Finset ℕ) := by
    simpa [I] using hm
  have hn' : n ∈ (Icc ⌈R.γ * X⌉₊ ⌊R.δ * X⌋₊ : Finset ℕ) := by
    simpa [J] using hn
  have hβ : 0 ≤ R.β * X := mul_nonneg
    (le_of_lt (R.α_pos.trans R.α_lt_β)) hX
  have hδ : 0 ≤ R.δ * X := mul_nonneg
    (le_of_lt (R.γ_pos.trans R.γ_lt_δ)) hX
  have hm0 : (m : ℝ) ≤ ⌊R.β * X⌋₊ := by
    exact_mod_cast (Finset.mem_Icc.mp hm').2
  have hn0 : (n : ℝ) ≤ ⌊R.δ * X⌋₊ := by
    exact_mod_cast (Finset.mem_Icc.mp hn').2
  have hmR : (m : ℝ) ≤ R.β * X := hm0.trans (Nat.floor_le hβ)
  have hnR : (n : ℝ) ≤ R.δ * X := hn0.trans (Nat.floor_le hδ)
  have hν : 0 ≤ (R.ν : ℝ) := by exact_mod_cast Nat.zero_le R.ν
  have hsum : (R.ν * m + n : ℝ) ≤ R.span X := by
    rw [span]
    have hmul := mul_le_mul_of_nonneg_left hmR hν
    nlinarith [mul_nonneg R.B_pos.le hX]
  have hreal : (R.ν * m + n : ℝ) < (R.Q X P : ℝ) :=
    hsum.trans_lt (R.span_lt_Q X P)
  exact_mod_cast hreal

/-! ### Fourier inversion -/

/-- **Fourier inversion for the weighted count.** -/
theorem rep_eq_sum (hX : 0 ≤ X) {N : ℕ} (hN : (N : ℝ) ≤ R.B * X) :
    (R.rep X N : ℂ) = (1 / (R.Q X P : ℂ)) * ∑ k ∈ range (R.Q X P),
      R.SI X (k / R.Q X P) * R.SJ X (k / R.Q X P) * e (-(N * k / R.Q X P)) := by
  let s := R.I X ×ˢ R.J X
  let f : ℕ × ℕ → ℂ := fun p => (Λ p.1 : ℂ) * Λ p.2
  let g : ℕ × ℕ → ℤ := fun p => ((R.ν * p.1 + p.2 : ℕ) : ℤ)
  have hprod (k : ℕ) :
      R.SI X (k / R.Q X P) * R.SJ X (k / R.Q X P) =
        ∑ p ∈ s, f p * e (g p * k / R.Q X P) := by
    simp only [s, f, g, SI, SJ]
    rw [Finset.sum_mul_sum, ← Finset.sum_product']
    apply Finset.sum_congr rfl
    intro p hp
    calc
      _ = (Λ p.1 : ℂ) * (Λ p.2 : ℂ) *
          (e (R.ν * p.1 * (k / R.Q X P)) *
            e (p.2 * (k / R.Q X P))) := by ring
      _ = (Λ p.1 : ℂ) * (Λ p.2 : ℂ) *
          e (((R.ν * p.1 + p.2 : ℕ) : ℝ) * (k / R.Q X P)) := by
        rw [← e_add]
        congr 2
        push_cast
        ring_nf
      _ = f p * e (g p * k / R.Q X P) := by
        dsimp [f, g]
        congr 2
        norm_num
        ring
  have hfreq : ∀ p ∈ s, |g p - (N : ℤ)| < (R.Q X P : ℤ) := by
    intro p hp
    have hp' := Finset.mem_product.mp hp
    have hlt := R.add_lt_Q X P hX hp'.1 hp'.2
    have hNlt : N < R.Q X P := by
      exact_mod_cast R.le_Q_of_le X P hX hN
    simp only [g]
    rw [abs_lt]
    constructor <;> omega
  have hfourier := sum_mul_e_neg_eq s f g (N : ℤ) (R.Q_pos X P) hfreq
  have hfilter : ∀ p, g p = (N : ℤ) ↔ R.ν * p.1 + p.2 = N := by
    intro p
    simp only [g]
    exact_mod_cast Int.natCast_inj
  have hsfilter :
      s.filter (fun p => g p = (N : ℤ)) =
        s.filter (fun p => R.ν * p.1 + p.2 = N) := by
    apply Finset.filter_congr
    intro p hp
    exact hfilter p
  calc
    (R.rep X N : ℂ) =
        ∑ p ∈ s with g p = (N : ℤ), f p := by
      rw [hsfilter]
      simp [rep, s, f, Complex.ofReal_sum, Complex.ofReal_mul]
    _ = (1 / (R.Q X P : ℂ)) *
        ∑ k ∈ range (R.Q X P),
          (∑ p ∈ s, f p * e (g p * k / R.Q X P)) *
            e (-(N * k / R.Q X P)) := hfourier.symm
    _ = (1 / (R.Q X P : ℂ)) *
        ∑ k ∈ range (R.Q X P),
          R.SI X (k / R.Q X P) * R.SJ X (k / R.Q X P) *
            e (-(N * k / R.Q X P)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [← hprod k]

/-- **Fourier inversion for the unweighted count.** -/
theorem count_eq_sum (hX : 0 ≤ X) {N : ℕ} (hN : (N : ℝ) ≤ R.B * X) :
    (R.count X N : ℂ) = (1 / (R.Q X P : ℂ)) * ∑ k ∈ range (R.Q X P),
      R.TI X (k / R.Q X P) * R.TJ X (k / R.Q X P) * e (-(N * k / R.Q X P)) := by
  let s := R.I X ×ˢ R.J X
  let g : ℕ × ℕ → ℤ := fun p => ((R.ν * p.1 + p.2 : ℕ) : ℤ)
  have hprod (k : ℕ) :
      R.TI X (k / R.Q X P) * R.TJ X (k / R.Q X P) =
        ∑ p ∈ s, (1 : ℂ) * e (g p * k / R.Q X P) := by
    simp only [s, g, TI, TJ]
    rw [Finset.sum_mul_sum, ← Finset.sum_product']
    apply Finset.sum_congr rfl
    intro p hp
    calc
      _ = (1 : ℂ) * (e (R.ν * p.1 * (k / R.Q X P)) *
          e (p.2 * (k / R.Q X P))) := by ring
      _ = (1 : ℂ) * e (((R.ν * p.1 + p.2 : ℕ) : ℝ) * (k / R.Q X P)) := by
        rw [← e_add]
        congr 2
        push_cast
        ring_nf
      _ = (1 : ℂ) * e (g p * k / R.Q X P) := by
        dsimp [g]
        congr 2
        norm_num
        ring
  have hfreq : ∀ p ∈ s, |g p - (N : ℤ)| < (R.Q X P : ℤ) := by
    intro p hp
    have hp' := Finset.mem_product.mp hp
    have hlt := R.add_lt_Q X P hX hp'.1 hp'.2
    have hNlt : N < R.Q X P := by
      exact_mod_cast R.le_Q_of_le X P hX hN
    simp only [g]
    rw [abs_lt]
    constructor <;> omega
  have hfourier := sum_mul_e_neg_eq s (fun _ => (1 : ℂ)) g (N : ℤ)
    (R.Q_pos X P) hfreq
  have hfilter : ∀ p, g p = (N : ℤ) ↔ R.ν * p.1 + p.2 = N := by
    intro p
    simp only [g]
    exact_mod_cast Int.natCast_inj
  have hsfilter :
      s.filter (fun p => g p = (N : ℤ)) =
        s.filter (fun p => R.ν * p.1 + p.2 = N) := by
    apply Finset.filter_congr
    intro p hp
    exact hfilter p
  calc
    (R.count X N : ℂ) =
        ∑ p ∈ s with g p = (N : ℤ), (1 : ℂ) := by
      rw [hsfilter]
      simp [count, s]
    _ = (1 / (R.Q X P : ℂ)) *
        ∑ k ∈ range (R.Q X P),
          (∑ p ∈ s, (1 : ℂ) * e (g p * k / R.Q X P)) *
            e (-(N * k / R.Q X P)) := hfourier.symm
    _ = (1 / (R.Q X P : ℂ)) *
        ∑ k ∈ range (R.Q X P),
          R.TI X (k / R.Q X P) * R.TJ X (k / R.Q X P) *
            e (-(N * k / R.Q X P)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [← hprod k]

/-! ### Admissibility and de-weighting -/

/-- The first interval's upper endpoint lies below `span`. -/
private theorem beta_mul_le_span (hX : 0 ≤ X) : R.β * X ≤ R.span X := by
  rw [span]
  have hν : 1 ≤ (R.ν : ℝ) := by
    exact_mod_cast R.one_le_ν
  have hβ : 0 < R.β := R.α_pos.trans R.α_lt_β
  have hδ : 0 < R.δ := R.γ_pos.trans R.γ_lt_δ
  have hνβ : 0 ≤ ((R.ν : ℝ) - 1) * R.β :=
    mul_nonneg (sub_nonneg.mpr hν) hβ.le
  have hδB : 0 ≤ R.δ + R.B := (add_pos hδ R.B_pos).le
  nlinarith [mul_nonneg hνβ hX, mul_nonneg hδB hX]

/-- The second interval's upper endpoint lies below `span`. -/
private theorem delta_mul_le_span (hX : 0 ≤ X) : R.δ * X ≤ R.span X := by
  rw [span]
  have hν : 0 ≤ (R.ν : ℝ) := by
    exact_mod_cast Nat.zero_le R.ν
  have hβ : 0 < R.β := R.α_pos.trans R.α_lt_β
  have hνβ : 0 ≤ (R.ν : ℝ) * R.β := mul_nonneg hν hβ.le
  nlinarith [mul_nonneg hνβ hX, mul_nonneg R.B_pos.le hX]

/-- If `span` is below one, the first interval is empty. -/
private theorem I_eq_empty_of_span_lt_one (hX : 1 ≤ X) (hspan : R.span X < 1) :
    R.I X = ∅ := by
  rw [I, Finset.Icc_eq_empty]
  have hαX : 0 < R.α * X := mul_pos R.α_pos (by linarith)
  have hβX : R.β * X < 1 :=
    (R.beta_mul_le_span X (by linarith)).trans_lt hspan
  have hceil : 1 ≤ ⌈R.α * X⌉₊ := Nat.one_le_ceil_iff.mpr hαX
  have hfloor : ⌊R.β * X⌋₊ = 0 := Nat.floor_eq_zero.mpr hβX
  omega

/-- Absence of a prime representation excludes prime pairs in the two intervals. -/
private theorem no_prime_pair_of_not_hasPrimeRepr (hX : 1 ≤ X) {N : ℕ}
    (hno : ¬ Conway.HasPrimeRepr R.ν (R.α * X) (R.β * X) (R.γ * X) (R.δ * X) N) :
    ∀ p ∈ R.I X, ∀ q ∈ R.J X, R.ν * p + q = N → ¬ p.Prime ∨ ¬ q.Prime := by
  simp only [Conway.HasPrimeRepr] at hno
  push Not at hno
  intro p hp q hq hpq
  by_contra hprime
  push Not at hprime
  apply hno p q
  · rw [Nat.mem_primesIcc]
    exact ⟨hprime.1, (R.mem_I X (by linarith)).mp hp⟩
  · rw [Nat.mem_primesIcc]
    exact ⟨hprime.2, (R.mem_J X (by linarith)).mp hq⟩
  · exact hpq.symm

/-- If no pair in the ranges consists of two primes, `rep` is bounded by prime powers. -/
private theorem rep_le_of_no_prime_pair (hX : 1 ≤ X) (hspan : 1 ≤ R.span X) {N : ℕ}
    (hno : ∀ p ∈ R.I X, ∀ q ∈ R.J X, R.ν * p + q = N → ¬ p.Prime ∨ ¬ q.Prime) :
    R.rep X N ≤ 2 * √(R.span X) * Real.log (R.span X) ^ 2 := by
  let L := Real.log (R.span X)
  let S : Finset (ℕ × ℕ) :=
    (R.I X ×ˢ R.J X).filter (fun p => R.ν * p.1 + p.2 = N)
  have hX0 : 0 ≤ X := by linarith
  have hL : 0 ≤ L := Real.log_nonneg hspan
  have hΛ (n : ℕ) : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  have hcoord (p : ℕ × ℕ) (hp : p ∈ S) :
      1 ≤ p.1 ∧ (p.1 : ℝ) ≤ R.span X ∧ 1 ≤ p.2 ∧ (p.2 : ℝ) ≤ R.span X := by
    rcases Finset.mem_filter.mp hp with ⟨hpij, _⟩
    rcases Finset.mem_product.mp hpij with ⟨hpi, hpj⟩
    have hpi' := (R.mem_I X hX0).mp hpi
    have hpj' := (R.mem_J X hX0).mp hpj
    have hpi_pos : 0 < (p.1 : ℝ) :=
      lt_of_lt_of_le (mul_pos R.α_pos (by linarith)) hpi'.1
    have hpj_pos : 0 < (p.2 : ℝ) :=
      lt_of_lt_of_le (mul_pos R.γ_pos (by linarith)) hpj'.1
    constructor
    · exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hpi_pos.ne')
    constructor
    · exact hpi'.2.trans (R.beta_mul_le_span X hX0)
    constructor
    · exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hpj_pos.ne')
    · exact hpj'.2.trans (R.delta_mul_le_span X hX0)
  have hterm (p : ℕ × ℕ) (hp : p ∈ S) :
      Λ p.1 * Λ p.2 ≤
        L * (if ¬ p.1.Prime then Λ p.1 else 0) +
          L * (if ¬ p.2.Prime then Λ p.2 else 0) := by
    have hc := hcoord p hp
    have hΛ1 : Λ p.1 ≤ L :=
      vonMangoldt_le_log_of_le hc.1 (by simpa [L] using hc.2.1)
    have hΛ2 : Λ p.2 ≤ L :=
      vonMangoldt_le_log_of_le hc.2.2.1 (by simpa [L] using hc.2.2.2)
    rcases Finset.mem_filter.mp hp with ⟨hpij, hpN⟩
    rcases Finset.mem_product.mp hpij with ⟨hpi, hpj⟩
    rcases hno p.1 hpi p.2 hpj hpN with hnp | hnp
    · have hright : 0 ≤ L * (if ¬ p.2.Prime then Λ p.2 else 0) := by
        split_ifs <;> positivity
      calc
        Λ p.1 * Λ p.2 ≤ Λ p.1 * L :=
          mul_le_mul_of_nonneg_left hΛ2 (hΛ _)
        _ = L * Λ p.1 := mul_comm _ _
        _ ≤ L * (if ¬ p.1.Prime then Λ p.1 else 0) +
            L * (if ¬ p.2.Prime then Λ p.2 else 0) := by
          simp only [if_pos hnp]
          linarith
    · have hleft : 0 ≤ L * (if ¬ p.1.Prime then Λ p.1 else 0) := by
        split_ifs <;> positivity
      calc
        Λ p.1 * Λ p.2 ≤ L * Λ p.2 :=
          mul_le_mul_of_nonneg_right hΛ1 (hΛ _)
        _ ≤ L * (if ¬ p.1.Prime then Λ p.1 else 0) +
            L * (if ¬ p.2.Prime then Λ p.2 else 0) := by
          simp only [if_pos hnp]
          linarith
  have hsum1_eq :
      (∑ p ∈ S, if ¬ p.1.Prime then Λ p.1 else 0) =
        ∑ p ∈ S with ¬ p.1.Prime, Λ p.1 := by
    simp only [S, Finset.sum_filter, Finset.filter_filter]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hpN : R.ν * p.1 + p.2 = N <;> by_cases hpprime : ¬ p.1.Prime <;>
      simp [hpN, hpprime]
  have hsum2_eq :
      (∑ p ∈ S, if ¬ p.2.Prime then Λ p.2 else 0) =
        ∑ p ∈ S with ¬ p.2.Prime, Λ p.2 := by
    simp only [S, Finset.sum_filter, Finset.filter_filter]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hpN : R.ν * p.1 + p.2 = N <;> by_cases hpprime : ¬ p.2.Prime <;>
      simp [hpN, hpprime]
  have hsum1 :
      (∑ p ∈ S, if ¬ p.1.Prime then Λ p.1 else 0) ≤
        √(R.span X) * L := by
    rw [hsum1_eq]
    let S' : Finset (ℕ × ℕ) := S.filter (fun p => ¬ p.1.Prime)
    have hinj : Set.InjOn Prod.fst (↑S' : Set (ℕ × ℕ)) := by
      intro p hp p' hp' hfst
      change p ∈ S' at hp
      change p' ∈ S' at hp'
      have hpS : p ∈ S := (Finset.mem_filter.mp hp).1
      have hpS' : p' ∈ S := (Finset.mem_filter.mp hp').1
      have hpN := (Finset.mem_filter.mp hpS).2
      have hpN' := (Finset.mem_filter.mp hpS').2
      rcases p with ⟨a, b⟩
      rcases p' with ⟨a', b'⟩
      change a = a' at hfst
      change R.ν * a + b = N at hpN
      change R.ν * a' + b' = N at hpN'
      subst a'
      have hsnd : b = b' := by omega
      exact Prod.ext rfl hsnd
    rw [show (∑ p ∈ S with ¬ p.1.Prime, Λ p.1) = ∑ p ∈ S', Λ p.1 by rfl,
      ← Finset.sum_image hinj]
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
    · exact sum_vonMangoldt_not_prime_le hspan
    · intro m hm
      rcases Finset.mem_image.mp hm with ⟨p, hp, rfl⟩
      change p ∈ S.filter (fun p => ¬ p.1.Prime) at hp
      have hpS : p ∈ S := (Finset.mem_filter.mp hp).1
      have hc := hcoord p hpS
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨hc.1, Nat.le_floor hc.2.1⟩, (Finset.mem_filter.mp hp).2⟩
    · intro m hm _
      exact hΛ m
  have hsum2 :
      (∑ p ∈ S, if ¬ p.2.Prime then Λ p.2 else 0) ≤
        √(R.span X) * L := by
    rw [hsum2_eq]
    let S' : Finset (ℕ × ℕ) := S.filter (fun p => ¬ p.2.Prime)
    have hinj : Set.InjOn Prod.snd (↑S' : Set (ℕ × ℕ)) := by
      intro p hp p' hp' hsnd
      change p ∈ S' at hp
      change p' ∈ S' at hp'
      have hpS : p ∈ S := (Finset.mem_filter.mp hp).1
      have hpS' : p' ∈ S := (Finset.mem_filter.mp hp').1
      have hpN := (Finset.mem_filter.mp hpS).2
      have hpN' := (Finset.mem_filter.mp hpS').2
      have hmul : R.ν * p.1 = R.ν * p'.1 := by omega
      have hfst : p.1 = p'.1 :=
        Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_of_lt R.one_le_ν) hmul
      exact Prod.ext hfst hsnd
    rw [show (∑ p ∈ S with ¬ p.2.Prime, Λ p.2) = ∑ p ∈ S', Λ p.2 by rfl,
      ← Finset.sum_image hinj]
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
    · exact sum_vonMangoldt_not_prime_le hspan
    · intro m hm
      rcases Finset.mem_image.mp hm with ⟨p, hp, rfl⟩
      change p ∈ S.filter (fun p => ¬ p.2.Prime) at hp
      have hpS : p ∈ S := (Finset.mem_filter.mp hp).1
      have hc := hcoord p hpS
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨hc.2.2.1, Nat.le_floor hc.2.2.2⟩, (Finset.mem_filter.mp hp).2⟩
    · intro m hm _
      exact hΛ m
  rw [rep]
  change (∑ p ∈ S, Λ p.1 * Λ p.2) ≤ _
  calc
    ∑ p ∈ S, Λ p.1 * Λ p.2 ≤
        ∑ p ∈ S, (L * (if ¬ p.1.Prime then Λ p.1 else 0) +
          L * (if ¬ p.2.Prime then Λ p.2 else 0)) :=
      Finset.sum_le_sum fun p hp => hterm p hp
    _ = L * (∑ p ∈ S, if ¬ p.1.Prime then Λ p.1 else 0) +
        L * (∑ p ∈ S, if ¬ p.2.Prime then Λ p.2 else 0) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ L * (√(R.span X) * L) + L * (√(R.span X) * L) :=
      add_le_add (mul_le_mul_of_nonneg_left hsum1 hL)
        (mul_le_mul_of_nonneg_left hsum2 hL)
    _ = 2 * √(R.span X) * Real.log (R.span X) ^ 2 := by
      simp only [L]
      ring

/-- An admissible target has at least `η X - 1` lattice representations. -/
theorem le_count_of_isAdmissible {N : ℕ}
    (h : Conway.IsAdmissible R.ν (R.α * X) (R.β * X) (R.γ * X) (R.δ * X) (R.η * X) N) :
    R.η * X - 1 ≤ R.count X N := by
  rcases h with ⟨s, hαs, hsβ, hv⟩
  by_cases hX : X ≤ 0
  · have hcount : (0 : ℝ) ≤ R.count X N := Nat.cast_nonneg _
    nlinarith [mul_nonpos_of_nonneg_of_nonpos R.η_pos.le hX]
  have hX0 : 0 ≤ X := le_of_lt (lt_of_not_ge hX)
  have hXpos : 0 < X := lt_of_not_ge hX
  have hs0 : 0 ≤ s := by
    exact (mul_nonneg R.α_pos.le hX0).trans hαs
  let T : Finset ℕ := Icc ⌈s⌉₊ ⌊s + R.η * X⌋₊
  let S : Finset (ℕ × ℕ) :=
    (R.I X ×ˢ R.J X).filter (fun p => R.ν * p.1 + p.2 = N)
  have hTcard : R.η * X - 1 ≤ (#T : ℝ) := by
    by_cases hle : ⌈s⌉₊ ≤ ⌊s + R.η * X⌋₊
    · rw [show #T = ⌊s + R.η * X⌋₊ + 1 - ⌈s⌉₊ by
        simp [T, Nat.card_Icc], Nat.cast_sub (Nat.le_succ_of_le hle)]
      have hfloor := Nat.lt_floor_add_one (s + R.η * X)
      have hceil := Nat.ceil_lt_add_one hs0
      norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_succ] at hfloor hceil ⊢
      linarith
    · have hlt : ⌊s + R.η * X⌋₊ < ⌈s⌉₊ := Nat.lt_of_not_ge hle
      have hsucc : ⌊s + R.η * X⌋₊ + 1 ≤ ⌈s⌉₊ := Nat.succ_le_of_lt hlt
      have hfloor := Nat.lt_floor_add_one (s + R.η * X)
      have hceil := Nat.ceil_lt_add_one hs0
      have hsmall : R.η * X - 1 < 0 := by
        have hsucc' : (⌊s + R.η * X⌋₊ : ℝ) + 1 ≤ ⌈s⌉₊ := by
          exact_mod_cast hsucc
        linarith
      have hnonneg : (0 : ℝ) ≤ #T := Nat.cast_nonneg _
      linarith
  have hTS : #T ≤ #S := by
    apply Finset.card_le_card_of_injOn (fun m => (m, N - R.ν * m))
    · intro m hm
      have hmT : ⌈s⌉₊ ≤ m ∧ m ≤ ⌊s + R.η * X⌋₊ := by
        simpa [T] using hm
      have hsm : s ≤ m := by
        rw [← Nat.ceil_le]
        exact hmT.1
      have hms : (m : ℝ) ≤ s + R.η * X := by
        have hmfloor : (m : ℝ) ≤ ⌊s + R.η * X⌋₊ := by
          exact_mod_cast hmT.2
        exact hmfloor.trans (Nat.floor_le
          (add_nonneg hs0 (mul_nonneg R.η_pos.le hX0)))
      have hmn := hv m hsm hms
      have hnm : R.ν * m < N := by
        have hnm' : (R.ν : ℝ) * m < N := by
          nlinarith [hmn.1, mul_pos R.γ_pos hXpos]
        exact_mod_cast hnm'
      have hncast : ((N - R.ν * m : ℕ) : ℝ) = N - R.ν * m := by
        rw [Nat.cast_sub (le_of_lt hnm), Nat.cast_mul]
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_product.mpr
        constructor
        · apply (R.mem_I X hX0).mpr
          constructor
          · linarith
          · linarith [hsβ]
        · apply (R.mem_J X hX0).mpr
          constructor <;> rw [hncast] <;> linarith
      · exact Nat.add_sub_of_le (le_of_lt hnm)
    · intro m hm n hn hmn
      exact congrArg Prod.fst hmn
  change R.η * X - 1 ≤ (#S : ℝ)
  exact hTcard.trans (by exact_mod_cast hTS)

/-- **De-weighting.** The pairs `(m, n)` with `m` or `n` a proper prime power contribute at most
`2 √span · (log span)²` to `rep N`; any excess forces a representation by primes. -/
theorem hasPrimeRepr_of_lt_rep (hX : 1 ≤ X) {N : ℕ}
    (h : 2 * √(R.span X) * log (R.span X) ^ 2 < R.rep X N) :
    Conway.HasPrimeRepr R.ν (R.α * X) (R.β * X) (R.γ * X) (R.δ * X) N := by
  by_contra hno
  by_cases hspan : 1 ≤ R.span X
  · have hno' := R.no_prime_pair_of_not_hasPrimeRepr X hX hno
    exact absurd h (not_lt.mpr (R.rep_le_of_no_prime_pair X hX hspan hno'))
  · have hI : R.I X = ∅ :=
      R.I_eq_empty_of_span_lt_one X hX (lt_of_not_ge hspan)
    have hrep : R.rep X N = 0 := by
      simp [rep, hI]
    rw [hrep] at h
    exact (not_lt_of_ge (mul_nonneg
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (sq_nonneg _))) h

end Ranges

end CircleMethod
