/-
Copyright (c) 2026 Romain Popescu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Romain Popescu
-/
import ConwayGolden.NumberTheory.CircleMethod.Inputs
import ConwayGolden.Subprime.Hypotheses

/-!
# Primes in proportional intervals from Siegel–Walfisz

The case `q = 1` of Siegel–Walfisz is the prime number theorem with a `(log x)⁻ᴬ` error term:
`ψ(x) = x + O(x (log x)⁻ᴬ)`. Consequently `∑_{α X < n ≤ β X} Λ n ≥ (β - α) X / 2` for large
`X`; removing the proper prime powers (`≤ √(β X) log (β X)`) and dividing by `log (β X)` gives
`≫ X / log X` primes in `[α X, β X]`.

## Main statements

* `CircleMethod.SiegelWalfisz.primesIccLower`: `SiegelWalfisz → Conway.PrimesIccLower`.
-/

namespace CircleMethod

open Filter Finset Real
open scoped ArithmeticFunction.vonMangoldt

namespace SiegelWalfisz

/-- The von Mangoldt mass of `(α X, β X]` is at least `(β - α) X / 2` for large `X`. -/
theorem eventually_le_sum_vonMangoldt_Ioc (h : SiegelWalfisz) {α β : ℝ} (hα : 0 < α)
    (hαβ : α < β) :
    ∀ᶠ X : ℝ in atTop, (β - α) * X / 2 ≤ ∑ n ∈ Ioc ⌊α * X⌋₊ ⌊β * X⌋₊, Λ n := by
  obtain ⟨C, hC, hpsi⟩ := h.abs_psi_sub_le one_pos
  have hαβpos : 0 < β - α := sub_pos.mpr hαβ
  have hlog : ∀ᶠ X : ℝ in atTop,
      2 ≤ α * X ∧ 2 ≤ β * X ∧
        2 * C * (α + β) / (β - α) ≤ log (α * X) := by
    have hXα : ∀ᶠ X : ℝ in atTop, 2 ≤ α * X :=
      (eventually_ge_atTop (2 / α)).mono fun X hX => by
        have := mul_le_mul_of_nonneg_left hX (le_of_lt hα)
        field_simp at this ⊢
        nlinarith
    have hXβ : ∀ᶠ X : ℝ in atTop, 2 ≤ β * X :=
      (eventually_ge_atTop (2 / β)).mono fun X hX => by
        have hβ : 0 < β := hα.trans hαβ
        have := mul_le_mul_of_nonneg_left hX (le_of_lt hβ)
        field_simp at this ⊢
        nlinarith
    have hlogα : Tendsto (fun X : ℝ => log (α * X)) atTop atTop := by
      apply Real.tendsto_log_atTop.comp
      simpa [mul_comm] using tendsto_id.const_mul_atTop hα
    have hbound := hlogα.eventually_ge_atTop (2 * C * (α + β) / (β - α))
    exact (hXα.and (hXβ.and hbound)).mono fun X hX => ⟨hX.1, hX.2.1, hX.2.2⟩
  filter_upwards [hlog] with X hX
  have hfloor : ⌊α * X⌋₊ ≤ ⌊β * X⌋₊ :=
    Nat.floor_mono (by nlinarith [hαβ, hX.1])
  have hsum0 (m : ℕ) :
      ∑ n ∈ Icc 1 m, Λ n = ∑ n ∈ Ioc 0 m, Λ n := by
    apply Finset.sum_congr
    · ext n
      simp only [mem_Icc, mem_Ioc]
      omega
    · intro n hn
      rfl
  have hsum : psi (β * X) - psi (α * X) =
      ∑ n ∈ Ioc ⌊α * X⌋₊ ⌊β * X⌋₊, Λ n := by
    rw [psi, psi, hsum0, hsum0]
    have hc := Finset.sum_Ioc_consecutive (fun n : ℕ => Λ n)
      (m := 0) (n := ⌊α * X⌋₊) (k := ⌊β * X⌋₊) (by omega) hfloor
    linarith
  rw [← hsum]
  have hαlog : 0 < log (α * X) := Real.log_pos (by linarith [hX.1])
  have hβlog : 0 < log (β * X) := Real.log_pos (by linarith [hX.2.1])
  have ha := (abs_le.mp (hpsi (α * X) hX.1))
  have hb := (abs_le.mp (hpsi (β * X) hX.2.1))
  have hXnonneg : 0 ≤ X := by nlinarith [hX.1]
  have hxy : α * X ≤ β * X :=
    mul_le_mul_of_nonneg_right (le_of_lt hαβ) hXnonneg
  have hlogs : log (α * X) ≤ log (β * X) :=
    Real.strictMonoOn_log.monotoneOn (by show 0 < α * X; linarith [hX.1])
      (by show 0 < β * X; linarith [hX.2.1])
      hxy
  have hcb : C * (β * X) / log (β * X) ≤
      C * (β * X) / log (α * X) := by
    apply (div_le_div_iff₀ hβlog hαlog).2
    have hβ : 0 < β := hα.trans hαβ
    have hnonneg : 0 ≤ C * (β * X) :=
      mul_nonneg hC.le (mul_nonneg hβ.le hXnonneg)
    exact mul_le_mul_of_nonneg_left hlogs hnonneg
  norm_num at ha hb
  have herror : C * (α * X) / log (α * X) + C * (β * X) / log (β * X) ≤
      (β - α) * X / 2 := by
    calc
      C * (α * X) / log (α * X) + C * (β * X) / log (β * X)
          ≤ C * (α * X) / log (α * X) + C * (β * X) / log (α * X) := by
            exact add_le_add le_rfl hcb
      _ = C * ((α + β) * X) / log (α * X) := by ring
      _ ≤ (β - α) * X / 2 := by
        apply (div_le_iff₀ hαlog).2
        have hbound := (div_le_iff₀ hαβpos).mp hX.2.2
        nlinarith
  nlinarith [ha.1, ha.2, hb.1, hb.2, herror]

private theorem sum_log_primes_Ioc_le (α β : ℝ) (X : ℝ) (_hX : 0 ≤ X) :
    ∑ n ∈ Ioc ⌊α * X⌋₊ ⌊β * X⌋₊ with n.Prime, Λ n ≤
      ∑ p ∈ Nat.primesIcc (α * X) (β * X), log p := by
  let T := (Ioc ⌊α * X⌋₊ ⌊β * X⌋₊).filter Nat.Prime
  have hsub : T ⊆ Nat.primesIcc (α * X) (β * X) := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpI, hpprime⟩
    rw [Nat.mem_primesIcc]
    refine ⟨hpprime, ?_, ?_⟩
    · have hlt := Nat.lt_floor_add_one (α * X)
      have hpIlow := (Finset.mem_Ioc.mp hpI).1
      have hle : (⌊α * X⌋₊ : ℝ) + 1 ≤ p := by
        have hleN : ⌊α * X⌋₊ + 1 ≤ p := by
          exact Nat.succ_le_of_lt hpIlow
        exact_mod_cast hleN
      linarith
    · by_cases hβX : 0 ≤ β * X
      · calc
          (p : ℝ) ≤ (⌊β * X⌋₊ : ℝ) := by
            exact_mod_cast (Finset.mem_Ioc.mp hpI).2
          _ ≤ β * X := Nat.floor_le hβX
      · have hzero : ⌊β * X⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
        rw [hzero] at hpI
        have hpupper : p ≤ 0 := (Finset.mem_Ioc.mp hpI).2
        exact ((lt_of_lt_of_le hpprime.pos hpupper).ne rfl).elim
  have hnonneg : ∀ p ∈ Nat.primesIcc (α * X) (β * X), 0 ≤ log p := by
    intro p hp
    exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primesIcc.mp hp).1.one_le)
  calc
    ∑ n ∈ Ioc ⌊α * X⌋₊ ⌊β * X⌋₊ with n.Prime, Λ n =
        ∑ p ∈ T, log p := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [ArithmeticFunction.vonMangoldt_apply_prime
            (Finset.mem_filter.mp hp).2]
    _ ≤ ∑ p ∈ Nat.primesIcc (α * X) (β * X), log p :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by
        intro p hp _
        exact hnonneg p hp)

private theorem sum_vonMangoldt_Ioc_not_prime_le {β : ℝ} (X : ℝ) (hβX : 1 ≤ β * X)
    (m : ℕ) :
    ∑ n ∈ Ioc m ⌊β * X⌋₊ with ¬ n.Prime, Λ n ≤ √(β * X) * log (β * X) := by
  let T := (Ioc m ⌊β * X⌋₊).filter (fun n => ¬n.Prime)
  have hsub : T ⊆ (Icc 1 ⌊β * X⌋₊).filter (fun n => ¬n.Prime) := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnI, hnprime⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, hnprime⟩
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at hnI ⊢
    omega
  calc
    ∑ n ∈ Ioc m ⌊β * X⌋₊ with ¬n.Prime, Λ n
        = ∑ n ∈ T, Λ n := rfl
    _ ≤ ∑ n ∈ Icc 1 ⌊β * X⌋₊ with ¬n.Prime, Λ n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by
        intro n hn _
        exact ArithmeticFunction.vonMangoldt_nonneg)
    _ ≤ √(β * X) * log (β * X) := sum_vonMangoldt_not_prime_le hβX

private theorem eventually_sqrt_mul_log_le {α β : ℝ} (hαβ : α < β) (hβ : 0 < β) :
    ∀ᶠ X : ℝ in atTop, √(β * X) * log (β * X) ≤ (β - α) * X / 4 := by
  have hδ : 0 < β - α := sub_pos.mpr hαβ
  let K := 16 * β ^ (3 / 4 : ℝ) / (β - α)
  have hK0 : 0 ≤ K := by
    dsimp [K]
    positivity
  filter_upwards [eventually_ge_atTop (max 1 (K ^ 4))] with X hX
  have hXpos : 0 < X := by
    have : 0 < max 1 (K ^ 4) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    linarith
  have hβXpos : 0 < β * X := mul_pos hβ hXpos
  have hlarge : K ≤ X ^ (1 / 4 : ℝ) := by
    calc
      K = (K ^ 4) ^ (1 / 4 : ℝ) := by
        convert (Real.pow_rpow_inv_natCast hK0 (by norm_num : (4 : ℕ) ≠ 0)).symm using 1;
          norm_num
      _ ≤ X ^ (1 / 4 : ℝ) := Real.rpow_le_rpow (pow_nonneg hK0 _) (by
        exact le_trans (le_max_right _ _) hX) (by norm_num)
  have hlog : log (β * X) ≤ (β * X) ^ (1 / 4 : ℝ) / (1 / 4 : ℝ) :=
    Real.log_le_rpow_div hβXpos.le (by norm_num)
  have hmain : 16 * β ^ (3 / 4 : ℝ) ≤ (β - α) * X ^ (1 / 4 : ℝ) :=
    by simpa [K, mul_comm] using (div_le_iff₀ hδ).mp hlarge
  have hmul : 16 * β ^ (3 / 4 : ℝ) * X ^ (3 / 4 : ℝ) ≤
      (β - α) * X ^ (1 / 4 : ℝ) * X ^ (3 / 4 : ℝ) :=
    mul_le_mul_of_nonneg_right hmain (Real.rpow_nonneg hXpos.le _)
  have hXsplit : X ^ (1 / 4 : ℝ) * X ^ (3 / 4 : ℝ) = X := by
    rw [← Real.rpow_add hXpos]
    norm_num
  calc
    √(β * X) * log (β * X) ≤
        (β * X) ^ (1 / 2 : ℝ) * ((β * X) ^ (1 / 4 : ℝ) / (1 / 4 : ℝ)) := by
          simpa [Real.sqrt_eq_rpow] using
            mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hβXpos.le _)
    _ = 4 * (β * X) ^ (3 / 4 : ℝ) := by
      calc
        (β * X) ^ (1 / 2 : ℝ) * ((β * X) ^ (1 / 4 : ℝ) / (1 / 4 : ℝ)) =
            4 * ((β * X) ^ (1 / 2 : ℝ) * (β * X) ^ (1 / 4 : ℝ)) := by ring
        _ = 4 * (β * X) ^ (3 / 4 : ℝ) := by
          rw [← Real.rpow_add hβXpos]
          norm_num
    _ = (16 * β ^ (3 / 4 : ℝ) * X ^ (3 / 4 : ℝ)) / 4 := by
      rw [Real.mul_rpow hβ.le hXpos.le]
      ring
    _ ≤ ((β - α) * X ^ (1 / 4 : ℝ) * X ^ (3 / 4 : ℝ)) / 4 :=
      div_le_div_of_nonneg_right hmul (by norm_num)
    _ = (β - α) * X / 4 := by
      rw [show (β - α) * X ^ (1 / 4 : ℝ) * X ^ (3 / 4 : ℝ) =
        (β - α) * (X ^ (1 / 4 : ℝ) * X ^ (3 / 4 : ℝ)) by ring, hXsplit]

/-- The mass carried by primes alone is at least `(β - α) X / 4` for large `X`. -/
theorem eventually_le_sum_log_primesIcc (h : SiegelWalfisz) {α β : ℝ} (hα : 0 < α)
    (hαβ : α < β) :
    ∀ᶠ X : ℝ in atTop, (β - α) * X / 4 ≤ ∑ p ∈ Nat.primesIcc (α * X) (β * X), log p := by
  have hβ : 0 < β := hα.trans hαβ
  filter_upwards [eventually_le_sum_vonMangoldt_Ioc h hα hαβ,
    eventually_sqrt_mul_log_le hαβ hβ, Filter.eventually_ge_atTop (1 / β)] with X h1 h3 hX
  have hX0 : 0 ≤ X := by
    have hXpos : 0 < X := lt_of_lt_of_le (div_pos one_pos hβ) hX
    linarith
  have hβX : 1 ≤ β * X := by
    have h := (div_le_iff₀ hβ).mp hX
    nlinarith
  rw [← Finset.sum_filter_add_sum_filter_not (Ioc ⌊α * X⌋₊ ⌊β * X⌋₊) Nat.Prime] at h1
  linarith [sum_log_primes_Ioc_le α β X hX0,
    sum_vonMangoldt_Ioc_not_prime_le X hβX ⌊α * X⌋₊]

/-- **Primes in proportional intervals.** -/
theorem primesIccLower (h : SiegelWalfisz) : Conway.PrimesIccLower := by
  intro α β hα hαβ
  have hδ : 0 < β - α := sub_pos.mpr hαβ
  refine ⟨(β - α) / 8, by positivity, ?_⟩
  have hm := eventually_le_sum_log_primesIcc h hα hαβ
  have hβ : 0 < β := hα.trans hαβ
  have hlarge : ∀ᶠ X : ℝ in atTop,
      1 < X ∧ 0 < log X ∧ log β ≤ log X ∧ 0 < β * X := by
    have hX : ∀ᶠ X : ℝ in atTop, 1 < X ∧ 0 < β * X :=
      (eventually_gt_atTop (max 2 (1 / β))).mono fun X hX => by
        have hX1 : 1 < X := by
          have : (1 : ℝ) ≤ max 2 (1 / β) := le_max_of_le_left (by norm_num)
          linarith
        have hprod : 0 < β * X := mul_pos hβ (by linarith)
        exact ⟨hX1, hprod⟩
    have hlogβ : ∀ᶠ X : ℝ in atTop, log β ≤ log X :=
      Real.tendsto_log_atTop.eventually_ge_atTop _
    filter_upwards [hX, hlogβ] with X hX hlogβ
    refine ⟨hX.1, Real.log_pos hX.1, hlogβ, hX.2⟩
  filter_upwards [hm, hlarge] with X hm hX
  let S := Nat.primesIcc (α * X) (β * X)
  have hsum : ∑ p ∈ S, log p ≤ (S.card : ℝ) * log (β * X) := by
    calc
      ∑ p ∈ S, log p ≤ S.card • log (β * X) := by
        apply Finset.sum_le_card_nsmul
        intro p hp
        apply Real.log_le_log
        · have := (Nat.mem_primesIcc.mp hp).1.one_le
          exact_mod_cast this
        · exact Nat.le_of_mem_primesIcc' hp
      _ = (S.card : ℝ) * log (β * X) := by simp [nsmul_eq_mul]
  have hlogmul : log (β * X) ≤ 2 * log X := by
    have hmul : log (β * X) = log β + log X :=
      Real.log_mul (ne_of_gt hβ) (by linarith [hX.1])
    rw [hmul]
    linarith
  have hcard : (β - α) * X / 4 ≤ (S.card : ℝ) * (2 * log X) := by
    calc
      (β - α) * X / 4 ≤ ∑ p ∈ S, log p := hm
      _ ≤ (S.card : ℝ) * log (β * X) := hsum
      _ ≤ (S.card : ℝ) * (2 * log X) := by
        gcongr
  calc
    (β - α) / 8 * (X / log X) = ((β - α) * X / 8) / log X := by ring
    _ ≤ (S.card : ℝ) := by
      apply (div_le_iff₀ hX.2.1).2
      nlinarith [hcard]

end SiegelWalfisz

end CircleMethod
