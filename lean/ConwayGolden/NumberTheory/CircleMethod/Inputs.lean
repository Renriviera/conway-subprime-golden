/-
Copyright (c) 2026 Romain Popescu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Romain Popescu
-/
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Totient
import ConwayGolden.NumberTheory.CircleMethod.ExpSum

/-!
# Standard analytic inputs: Siegel–Walfisz and Vinogradov's minor-arc bound

This file states, as `Prop`s, the two classical theorems on the von Mangoldt function that the
discrete circle method of this project takes as external inputs, and it collects the elementary
facts about `Λ` that are proved here directly.

## Main definitions

* `CircleMethod.psiMod x q a`: the Chebyshev function `ψ(x; q, a) = ∑_{n ≤ x, n ≡ a (q)} Λ n`.
* `CircleMethod.lambdaExpSum x α`: the exponential sum `∑_{n ≤ x} Λ n · e (n α)`.
* `CircleMethod.SiegelWalfisz`: for every `A > 0` there is `C_A` with
  `|ψ(x; q, a) - x / φ(q)| ≤ C_A x (log x)⁻ᴬ` for `x ≥ 2`, `q ≤ (log x)^A`, `(a, q) = 1`.
* `CircleMethod.VinogradovMinorArc`: there is `C` with
  `|∑_{n ≤ x} Λ n e (n α)| ≤ C (log x)⁴ (x q^{-1/2} + x^{4/5} + (x q)^{1/2})`
  whenever `|α - a / q| ≤ q⁻²`, `(a, q) = 1`.
* `CircleMethod.StandardInputs`: the conjunction of the two.

## Main statements

* `CircleMethod.sum_vonMangoldt_sq_le`: `∑_{n ≤ x} Λ n ² ≤ x (log x)²`.
* `CircleMethod.sum_vonMangoldt_not_prime_le`: the prime powers with exponent `≥ 2` contribute
  at most `√x · log x` to `ψ(x)`.
* `CircleMethod.sum_vonMangoldt_not_coprime_le`: the `n ≤ x` sharing a factor with `q`
  contribute at most `q · log x` to `ψ(x)`.
* `CircleMethod.SiegelWalfisz.abs_psi_sub_le`: the case `q = 1` of Siegel–Walfisz.

## References

* [H. Davenport, *Multiplicative number theory*, Chapters 22 and 25][Davenport2000]
* [R. C. Vaughan, *The Hardy–Littlewood method*, Theorem 3.1][Vaughan1997]
-/

namespace CircleMethod

open Finset Real
open scoped ArithmeticFunction.vonMangoldt

/-! ### Chebyshev functions and the von Mangoldt exponential sum -/

/-- `ψ(x; q, a) = ∑_{n ≤ x, n ≡ a [MOD q]} Λ n`. -/
noncomputable def psiMod (x : ℝ) (q a : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊ with Nat.ModEq q n a, Λ n

/-- `ψ(x) = ∑_{n ≤ x} Λ n`. -/
noncomputable def psi (x : ℝ) : ℝ := ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n

theorem psiMod_one_zero (x : ℝ) : psiMod x 1 0 = psi x := by
  simp [psiMod, psi, Nat.modEq_one]

/-- `∑_{n ≤ x} Λ n · e (n α)`. -/
noncomputable def lambdaExpSum (x α : ℝ) : ℂ := ∑ n ∈ Icc 1 ⌊x⌋₊, (Λ n : ℂ) * e (n * α)

/-! ### The two external inputs -/

/-- **Siegel–Walfisz.** For every `A > 0` there is a constant `C_A` such that
`|ψ(x; q, a) - x / φ(q)| ≤ C_A · x / (log x)^A` for all `x ≥ 2`, `1 ≤ q ≤ (log x)^A` and
`(a, q) = 1`. -/
def SiegelWalfisz : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x → ∀ q a : ℕ, 0 < q →
    (q : ℝ) ≤ log x ^ A → Nat.Coprime a q →
      |psiMod x q a - x / q.totient| ≤ C * x / log x ^ A

/-- **Vinogradov's minor-arc bound** (in Vaughan's form). There is a constant `C` such that
`‖∑_{n ≤ x} Λ n e (n α)‖ ≤ C (log x)⁴ (x / √q + x^{4/5} + √(x q))` for all `x ≥ 2` and all
`α` with `|α - a / q| ≤ 1 / q²`, `(a, q) = 1`. -/
def VinogradovMinorArc : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x → ∀ (α : ℝ) (a q : ℕ), 0 < q → Nat.Coprime a q →
    |α - a / q| ≤ 1 / (q : ℝ) ^ 2 →
      ‖lambdaExpSum x α‖ ≤ C * log x ^ 4 * (x / √q + x ^ ((4 : ℝ) / 5) + √(x * q))

/-- The two standard analytic inputs of the discrete circle method. -/
structure StandardInputs : Prop where
  /-- The Siegel–Walfisz theorem. -/
  siegelWalfisz : SiegelWalfisz
  /-- Vinogradov's bound for the von Mangoldt exponential sum on minor arcs. -/
  vinogradovMinorArc : VinogradovMinorArc

/-! ### Elementary bounds for `Λ` -/

theorem vonMangoldt_le_log_of_le {n : ℕ} {x : ℝ} (hn : 1 ≤ n) (hnx : (n : ℝ) ≤ x) :
    Λ n ≤ log x := by
  exact ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log (by positivity) hnx)

/-- `ψ(x) ≤ x log x`. -/
theorem sum_vonMangoldt_le {x : ℝ} (hx : 1 ≤ x) : ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n ≤ x * log x := by
  have hlog : 0 ≤ log x := Real.log_nonneg (by linarith)
  have hterm : ∀ n ∈ Icc 1 ⌊x⌋₊, Λ n ≤ log x := by
    intro n hn
    apply vonMangoldt_le_log_of_le (Finset.mem_Icc.mp hn).1
    exact (by
      calc
        (n : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).2
        _ ≤ x := Nat.floor_le (by linarith))
  calc
    ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n ≤ (Icc 1 ⌊x⌋₊).card • log x :=
      Finset.sum_le_card_nsmul _ _ _ hterm
    _ = ((Icc 1 ⌊x⌋₊).card : ℝ) * log x := by simp [nsmul_eq_mul]
    _ ≤ x * log x := by
      gcongr
      rw [Nat.card_Icc]
      norm_num
      exact Nat.floor_le (by linarith)

/-- `∑_{n ≤ x} Λ n ² ≤ x (log x)²`. -/
theorem sum_vonMangoldt_sq_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n ^ 2 ≤ x * log x ^ 2 := by
  have hlog : 0 ≤ log x := Real.log_nonneg (by linarith)
  have hterm : ∀ n ∈ Icc 1 ⌊x⌋₊, Λ n ^ 2 ≤ log x ^ 2 := by
    intro n hn
    have hΛ : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
    have hΛlog : Λ n ≤ log x := vonMangoldt_le_log_of_le (Finset.mem_Icc.mp hn).1 (by
      calc
        (n : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).2
        _ ≤ x := Nat.floor_le (by linarith))
    nlinarith
  calc
    ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n ^ 2 ≤ (Icc 1 ⌊x⌋₊).card • (log x ^ 2) :=
      Finset.sum_le_card_nsmul _ _ _ hterm
    _ = ((Icc 1 ⌊x⌋₊).card : ℝ) * log x ^ 2 := by simp [nsmul_eq_mul]
    _ ≤ x * log x ^ 2 := by
      gcongr
      rw [Nat.card_Icc]
      norm_num
      exact Nat.floor_le (by linarith)

/-- The `Λ`-mass of the powers of a fixed prime `p` up to `x` is at most `log x`. -/
private theorem sum_vonMangoldt_pow_fibre_le {x : ℝ} (hx : 1 ≤ x) {p : ℕ} (hp : p.Prime)
    (T : Finset ℕ) (hT : ∀ n ∈ T, n ≤ ⌊x⌋₊ ∧ ∃ k, 1 ≤ k ∧ n = p ^ k) :
    ∑ n ∈ T, Λ n ≤ log x := by
  have hfloor : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff x).mpr hx
  have hfloor_ne : ⌊x⌋₊ ≠ 0 := by omega
  let K := Nat.log p ⌊x⌋₊
  have hmaps : Set.MapsTo (fun n : ℕ => Nat.log p n) T (Icc 1 K) := by
    intro n hn
    obtain ⟨hnx, k, hk, rfl⟩ := hT n hn
    change Nat.log p (p ^ k) ∈ Icc 1 K
    simpa [K, Nat.log_pow hp.one_lt] using
      (Finset.mem_Icc.mpr ⟨hk, Nat.le_log_of_pow_le hp.one_lt hnx⟩)
  have hinj : (T : Set ℕ).InjOn (fun n : ℕ => Nat.log p n) := by
    intro m hm n hn hmn
    obtain ⟨_, k, hk, rfl⟩ := hT m hm
    obtain ⟨_, l, hl, rfl⟩ := hT n hn
    change Nat.log p (p ^ k) = Nat.log p (p ^ l) at hmn
    rw [Nat.log_pow hp.one_lt, Nat.log_pow hp.one_lt] at hmn
    exact congrArg (p ^ ·) hmn
  have hcard : T.card ≤ K := by
    calc
      T.card ≤ (Icc 1 K).card := Finset.card_le_card_of_injOn _ hmaps hinj
      _ = K := by rw [Nat.card_Icc]; omega
  have hsum : ∑ n ∈ T, Λ n = T.card * log p := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨_, k, hk, rfl⟩ := hT n hn
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega), 
      ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hlogp : 0 ≤ log p := Real.log_nonneg (by exact_mod_cast hp.one_le)
  calc
    ∑ n ∈ T, Λ n = T.card * log p := hsum
    _ ≤ K * log p := by gcongr
    _ = log (p ^ K) := by rw [Real.log_pow]
    _ ≤ log ⌊x⌋₊ := Real.log_le_log (by
      exact_mod_cast (Nat.pow_pos hp.pos : 0 < p ^ K)) (by
      exact_mod_cast Nat.pow_log_le_self p hfloor_ne)
    _ ≤ log x := Real.log_le_log (by exact_mod_cast hfloor) (Nat.floor_le (by linarith))

/-- The proper prime powers `p ^ k ≤ x`, `k ≥ 2`, contribute at most `√x · log x` to `ψ(x)`. -/
theorem sum_vonMangoldt_not_prime_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Icc 1 ⌊x⌋₊ with ¬ n.Prime, Λ n ≤ √x * log x := by
  let S := ((Icc 1 ⌊x⌋₊).filter fun n => ¬n.Prime).filter fun n => Λ n ≠ 0
  let t := Icc 2 ⌊√x⌋₊
  have hmaps : Set.MapsTo Nat.minFac S t := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hn, hΛ⟩
    rcases Finset.mem_filter.mp hn with ⟨hn, hnp⟩
    have hpp : IsPrimePow n := by
      by_contra hpp
      apply hΛ
      exact ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp
    obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff n).mp hpp
    have hk2 : 2 ≤ k := by
      by_contra hk2
      have hk1 : k = 1 := by omega
      subst k
      apply hnp
      rw [← hpk]
      simpa using hp
    have hsq : p ^ 2 ≤ n := by
      rw [← hpk]
      exact Nat.pow_le_pow_right hp.pos hk2
    have hnx : (n : ℝ) ≤ x := by
      calc
        (n : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).2
        _ ≤ x := Nat.floor_le (by linarith)
    have hp_sqrt : (p : ℝ) ≤ √x :=
      (Real.le_sqrt (by positivity : 0 ≤ (p : ℝ)) (by linarith : 0 ≤ x)).mpr (by
      exact (by exact_mod_cast hsq : (p : ℝ) ^ 2 ≤ n).trans hnx)
    have hmin : n.minFac = p := by
      rw [← hpk]
      exact hp.pow_minFac hk.ne'
    simpa [t, hmin] using Finset.mem_Icc.mpr ⟨hp.two_le, Nat.le_floor hp_sqrt⟩
  rw [← Finset.sum_filter_ne_zero]
  change ∑ n ∈ S, Λ n ≤ √x * log x
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hlog : 0 ≤ log x := Real.log_nonneg hx
  calc
    ∑ p ∈ t, ∑ n ∈ S with Nat.minFac n = p, Λ n
        ≤ ∑ p ∈ t, log x := by
          gcongr with p hp
          by_cases hempty : (S.filter fun n => Nat.minFac n = p).Nonempty
          · obtain ⟨n, hn⟩ := hempty
            rcases Finset.mem_filter.mp hn with ⟨hnS, hmin⟩
            have hpprime : p.Prime := by
              rw [← hmin]
              exact Nat.minFac_prime (IsPrimePow.ne_one (by
                have hΛ := (Finset.mem_filter.mp hnS).2
                by_contra hpp
                apply hΛ
                exact ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp))
            apply sum_vonMangoldt_pow_fibre_le (p := p) hx hpprime
            intro n hn
            rcases Finset.mem_filter.mp hn with ⟨hnS, hmin⟩
            rcases Finset.mem_filter.mp hnS with ⟨hnIcc, hΛ⟩
            rcases Finset.mem_filter.mp hnIcc with ⟨hnIcc, _⟩
            have hpp : IsPrimePow n := by
              by_contra hpp
              apply hΛ
              exact ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp
            obtain ⟨r, k, hr, hk, hrk⟩ := (isPrimePow_nat_iff n).mp hpp
            refine ⟨(Finset.mem_Icc.mp hnIcc).2, k, hk, ?_⟩
            have hrp : r = p := by
              simp only [← hmin, ← hrk, hr.pow_minFac hk.ne']
            rw [← hrk, hrp]
          · simp [Finset.not_nonempty_iff_eq_empty.mp hempty, hlog]
    _ = (t.card : ℝ) * log x := by simp [nsmul_eq_mul]
    _ ≤ √x * log x := by
      gcongr
      calc
        (t.card : ℝ) = (⌊√x⌋₊ + 1 - 2 : ℕ) := by
          simp only [t, Nat.card_Icc]
        _ ≤ ⌊√x⌋₊ := by exact_mod_cast (by omega)
        _ ≤ √x := Nat.floor_le (Real.sqrt_nonneg _)

/-- The `n ≤ x` not coprime to `q` contribute at most `q · log x` to `ψ(x)`. -/
theorem sum_vonMangoldt_not_coprime_le {x : ℝ} (hx : 1 ≤ x) {q : ℕ} (hq : 0 < q) :
    ∑ n ∈ Icc 1 ⌊x⌋₊ with ¬ Nat.Coprime n q, Λ n ≤ q * log x := by
  let S := ((Icc 1 ⌊x⌋₊).filter fun n => ¬Nat.Coprime n q).filter fun n => Λ n ≠ 0
  have hmaps : Set.MapsTo Nat.minFac S q.primeFactors := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hn, hΛ⟩
    rcases Finset.mem_filter.mp hn with ⟨hnIcc, hcop⟩
    have hpp : IsPrimePow n := by
      by_contra hpp
      apply hΛ
      exact ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp
    obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff n).mp hpp
    have hpq : p ∣ q := by
      by_contra hpq
      have hpcop : Nat.Coprime p q := hp.coprime_iff_not_dvd.mpr hpq
      apply hcop
      rw [← hpk]
      exact hpcop.pow_left k
    have hmin : n.minFac = p := by
      rw [← hpk]
      exact hp.pow_minFac hk.ne'
    rw [hmin]
    exact Nat.mem_primeFactors.mpr ⟨hp, hpq, hq.ne'⟩
  rw [← Finset.sum_filter_ne_zero]
  change ∑ n ∈ S, Λ n ≤ q * log x
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hlog : 0 ≤ log x := Real.log_nonneg hx
  calc
    ∑ p ∈ q.primeFactors, ∑ n ∈ S with Nat.minFac n = p, Λ n
        ≤ ∑ p ∈ q.primeFactors, log x := by
          gcongr with p hp
          have hpprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
          apply sum_vonMangoldt_pow_fibre_le (p := p) hx hpprime
          intro n hn
          rcases Finset.mem_filter.mp hn with ⟨hnS, hmin⟩
          rcases Finset.mem_filter.mp hnS with ⟨hnIcc, hΛ⟩
          rcases Finset.mem_filter.mp hnIcc with ⟨hnIcc, _⟩
          have hpp : IsPrimePow n := by
            by_contra hpp
            apply hΛ
            exact ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp
          obtain ⟨r, k, hr, hk, hrk⟩ := (isPrimePow_nat_iff n).mp hpp
          refine ⟨(Finset.mem_Icc.mp hnIcc).2, k, hk, ?_⟩
          have hrp : r = p := by
            simp only [← hmin, ← hrk, hr.pow_minFac hk.ne']
          rw [← hrk, hrp]
    _ = ((q.primeFactors.card : ℝ) * log x) := by simp [nsmul_eq_mul]
    _ ≤ q * log x := by
      gcongr
      calc
        q.primeFactors.card ≤ (Icc 1 q).card := by
          exact Finset.card_le_card (by
            intro p hp
            rcases Nat.mem_primeFactors.mp hp with ⟨hpp, hpq, _⟩
            exact Finset.mem_Icc.mpr ⟨hpp.one_le, Nat.le_of_dvd hq hpq⟩)
        _ = q := by rw [Nat.card_Icc]; norm_num

/-! ### First consequences of Siegel–Walfisz -/

namespace SiegelWalfisz

/-- The case `q = 1`: `|ψ(x) - x| ≤ C_A x / (log x)^A`. -/
theorem abs_psi_sub_le (h : SiegelWalfisz) {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x → |psi x - x| ≤ C * x / log x ^ A := by
  obtain ⟨C, hC, hSW⟩ := h A hA
  refine ⟨C + 2, by linarith, ?_⟩
  intro x hx
  have hx1 : 0 ≤ x := by linarith
  have hpsi : 0 ≤ psi x := by
    simp only [psi]
    exact Finset.sum_nonneg fun n _ => ArithmeticFunction.vonMangoldt_nonneg
  by_cases hlog : 1 ≤ log x
  · have hpow : (1 : ℝ) ≤ log x ^ A := Real.one_le_rpow hlog hA.le
    have hs := hSW x hx 1 0 (by norm_num) (by exact_mod_cast hpow)
      (Nat.coprime_one_right 0)
    rw [psiMod_one_zero, Nat.totient_one, Nat.cast_one, div_one] at hs
    have hpos : 0 < log x ^ A :=
      Real.rpow_pos_of_pos (lt_of_lt_of_le (by positivity) hlog) _
    calc
      |psi x - x| ≤ C * x / log x ^ A := hs
      _ ≤ (C + 2) * x / log x ^ A := by
        apply div_le_div_of_nonneg_right
        · nlinarith [mul_nonneg (le_of_lt hC) hx1]
        · exact hpos.le
  · have hlog0 : 0 ≤ log x := Real.log_nonneg (by linarith)
    have hlog' : log x ≤ 1 := le_of_not_ge hlog
    have hpow : log x ^ A ≤ (1 : ℝ) := Real.rpow_le_one hlog0 hlog' hA.le
    have hpowpos : 0 < log x ^ A :=
      Real.rpow_pos_of_pos (Real.log_pos (by linarith)) _
    have htriv : |psi x - x| ≤ 2 * x := by
      calc
        |psi x - x| ≤ |psi x| + |x| := abs_sub _ _
        _ = psi x + x := by rw [abs_of_nonneg hpsi, abs_of_nonneg hx1]
        _ ≤ x * log x + x := by
          gcongr
          exact sum_vonMangoldt_le (by linarith)
        _ ≤ 2 * x := by nlinarith
    calc
      |psi x - x| ≤ 2 * x := htriv
      _ ≤ (C + 2) * x / log x ^ A := by
        apply (le_div_iff₀ hpowpos).2
        nlinarith [mul_nonneg (by linarith : 0 ≤ C + 2) hx1]

end SiegelWalfisz

end CircleMethod
