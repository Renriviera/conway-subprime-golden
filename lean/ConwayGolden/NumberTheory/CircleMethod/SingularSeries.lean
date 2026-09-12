/-
Copyright (c) 2026 Romain Popescu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Romain Popescu
-/
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import ConwayGolden.NumberTheory.CircleMethod.RamanujanSum

/-!
# The truncated singular series for `N = ν p + q`

The major arcs of the discrete circle method contribute the main term
`𝔖_P(N) · W(N)`, where `W(N)` is the singular integral and

`𝔖_P(N) = ∑_{q ≤ P} μ(q) c_q(ν) c_q(N) / φ(q)²`

is the *truncated singular series*. This file proves that `𝔖_P(N) ≥ 1/2` for all admissible
`N ≤ Y` outside an exceptional set of size `≪ Y P^{-1/4}`, and that `|𝔖_P(N)| ≪ (log P)⁴`.

The argument is entirely finite. Writing `g(q) = μ(q) c_q(ν) c_q(N) / φ(q)²`:

* `g` is multiplicative, so `∑_{q ∣ P#} g(q) = ∏_{p ≤ P} (1 + g(p))` (with `P#` the primorial);
* for admissible `N` the local factors satisfy `1 + g(2) = 2` and `1 + g(p) ≥ 1 - (p-1)⁻²` for
  odd `p`, whence `∏_{p ≤ P} (1 + g(p)) ≥ 2 ∏_{n=2}^{P} (1 - n⁻²) ≥ 1`;
* `∑_{q ∣ P#} g(q) - 𝔖_P(N) = ∑_{q ∣ P#, q > P} g(q)`, split at `q = Y`: the part `q > Y` is
  `o(1)` uniformly in `N ≤ Y`, and the part `P < q ≤ Y` is small on average over `N ≤ Y`
  because `∑_{N ≤ Y} σ((q, N)) ≤ Y τ(q) (log q + 1)`.

## Main definitions

* `CircleMethod.arcCoeff ν N q`: `μ(q) c_q(ν) c_q(N) / φ(q)²`.
* `CircleMethod.singularSeries ν N P`: `∑_{q ≤ P} arcCoeff ν N q`.

## Main statements

* `CircleMethod.arcCoeff_prime`: the local factors at primes.
* `CircleMethod.one_le_prod_one_add_arcCoeff`: `1 ≤ ∏_{p ≤ P} (1 + arcCoeff ν N p)` for
  admissible `N`.
* `CircleMethod.card_singularSeries_lt_le`: the number of admissible `N ≤ Y` with
  `𝔖_P(N) < 1/2` is at most `4 · 10⁵ · Y / P^{1/4}` once `Y` is large.
* `CircleMethod.abs_singularSeries_le`: `|𝔖_P(N)| ≤ 4 (log P + 1)⁴`.

## Implementation notes

Only crude elementary bounds are used: `τ(q) ≤ 2 √q`, `q / φ(q) ≤ 2 (log q + 1)`,
`σ(d) ≤ d (log d + 1)` and `log x + 1 ≤ 12 x^{1/12}`. The resulting constants are far from
optimal but explicit.
-/

namespace CircleMethod

open Finset Real
open scoped ArithmeticFunction.Moebius ArithmeticFunction.sigma

/-! ### Elementary arithmetic bounds -/

/-- `log x + 1 ≤ 12 x^{1/12}` for `x ≥ 1`. -/
theorem log_add_one_le_rpow {x : ℝ} (hx : 1 ≤ x) : log x + 1 ≤ 12 * x ^ ((1 : ℝ) / 12) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hr : 0 < x ^ ((1 : ℝ) / 12) := Real.rpow_pos_of_pos hx0 _
  have hlog := Real.log_le_sub_one_of_pos hr
  have hpow : log x = 12 * log (x ^ ((1 : ℝ) / 12)) := by
    rw [Real.log_rpow hx0]
    ring
  nlinarith

/-- `τ(q) ≤ 2 √q`. -/
theorem card_divisors_le_two_mul_sqrt (q : ℕ) : (σ 0 q : ℝ) ≤ 2 * √q := by
  rw [ArithmeticFunction.sigma_zero_apply]
  by_cases hq : q = 0
  · simp [hq]
  classical
  let A := q.divisors.filter fun d => d * d ≤ q
  let B := q.divisors.filter fun d => ¬ d * d ≤ q
  have hcard : #q.divisors = #A + #B := by
    simpa [A, B] using
      (Finset.card_filter_add_card_filter_not (s := q.divisors) fun d => d * d ≤ q).symm
  have hBA : #B ≤ #A := by
    apply Finset.card_le_card_of_injOn (fun d => q / d)
    · intro d hd
      have hd' := Finset.mem_filter.mp hd
      have hdiv : d ∣ q := (Nat.mem_divisors.mp hd'.1).1
      have hpos : 0 < d := Nat.pos_of_mem_divisors hd'.1
      have hmul : (q / d) * d = q := Nat.div_mul_cancel hdiv
      have hlt : q < d * d := Nat.lt_of_not_ge hd'.2
      have hle : q / d ≤ d := by
        exact Nat.le_of_mul_le_mul_right (by
          rw [hmul]
          exact Nat.le_of_lt hlt) hpos
      exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
        ⟨Nat.div_dvd_of_dvd hdiv, hq⟩, by
          calc
            (q / d) * (q / d) ≤ (q / d) * d := Nat.mul_le_mul_left _ hle
            _ = q := hmul⟩
    · intro d hd e he hde
      have hd' := Finset.mem_filter.mp hd
      have he' := Finset.mem_filter.mp he
      have hddvd : d ∣ q := (Nat.mem_divisors.mp hd'.1).1
      have hedvd : e ∣ q := (Nat.mem_divisors.mp he'.1).1
      change q / d = q / e at hde
      calc
        d = q / (q / d) := (Nat.div_div_self hddvd hq).symm
        _ = q / (q / e) := by rw [hde]
        _ = e := Nat.div_div_self hedvd hq
  have hA : #A ≤ Nat.sqrt q := by
    calc
      #A ≤ #(Icc 1 (Nat.sqrt q)) := by
        apply Finset.card_le_card
        intro d hd
        have hd' := Finset.mem_filter.mp hd
        exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd'.1,
          Nat.le_sqrt.mpr hd'.2⟩
      _ = Nat.sqrt q := by simp
  have hnat : #q.divisors ≤ 2 * Nat.sqrt q := by omega
  have hreal : (#q.divisors : ℝ) ≤ 2 * (Nat.sqrt q : ℝ) := by
    exact_mod_cast hnat
  exact hreal.trans (mul_le_mul_of_nonneg_left Real.nat_sqrt_le_real_sqrt (by norm_num))

/-- `σ(d) ≤ d (log d + 1)` for `d ≥ 1`. -/
theorem sigma_one_le {d : ℕ} (hd : 1 ≤ d) : (σ 1 d : ℝ) ≤ d * (log d + 1) := by
  rw [ArithmeticFunction.sigma_one_apply]
  norm_cast
  -- The remaining goal is the real-valued divisor sum.
  push_cast
  calc
    (∑ x ∈ d.divisors, (x : ℝ)) =
        ∑ x ∈ d.divisors, (d : ℝ) / x := by
      rw [← Nat.sum_div_divisors d (fun x : ℕ => (x : ℝ))]
      apply Finset.sum_congr rfl
      intro x hx
      have hx0 : (x : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (Nat.pos_of_mem_divisors hx))
      rw [eq_div_iff hx0]
      exact_mod_cast Nat.div_mul_cancel (Nat.mem_divisors.mp hx).1
    _ ≤ ∑ x ∈ Icc 1 d, (d : ℝ) / x := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr
          (Nat.ne_of_gt (Nat.pos_of_mem_divisors hx)), Nat.le_of_dvd hd
          (Nat.mem_divisors.mp hx).1⟩
      · intro x hx _
        positivity
    _ = d * ∑ x ∈ Icc 1 d, (1 / (x : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      field_simp
    _ = d * (harmonic d : ℝ) := by
      simp [harmonic_eq_sum_Icc]
    _ ≤ d * (log d + 1) := by
      gcongr
      have h := harmonic_le_one_add_log d
      linarith

private theorem rpow_neg_succ_le_sub {s : ℝ} (hs : 0 < s) {r : ℕ} (hr : 2 ≤ r) :
    (r : ℝ) ^ (-(1 + s)) ≤
      (((r - 1 : ℕ) : ℝ) ^ (-s) - (r : ℝ) ^ (-s)) / s := by
  have ht : 0 < (r : ℝ) := by positivity
  have hu : 0 < ((r - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt (by omega)
  have htu : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos ht hu)
  have hinv : 1 - ((r : ℝ) / ((r - 1 : ℕ) : ℝ))⁻¹ = 1 / (r : ℝ) := by
    rw [inv_div]
    rw [htu]
    field_simp
    ring
  have hlog' : 1 / (r : ℝ) ≤ Real.log ((r : ℝ) / ((r - 1 : ℕ) : ℝ)) := by
    rw [← hinv]
    exact hlog
  have hexp := Real.add_one_le_exp
    (Real.log ((r : ℝ) / ((r - 1 : ℕ) : ℝ)) * s)
  have hrpow : 1 + s / (r : ℝ) ≤
      ((r : ℝ) / ((r - 1 : ℕ) : ℝ)) ^ s := by
    rw [Real.rpow_def_of_pos (div_pos ht hu)]
    have hlogs := mul_le_mul_of_nonneg_left hlog' hs.le
    have hlogs' : s / (r : ℝ) ≤
        s * Real.log ((r : ℝ) / ((r - 1 : ℕ) : ℝ)) := by
      simpa [div_eq_mul_inv, mul_comm] using hlogs
    nlinarith [Real.add_one_le_exp (Real.log
      ((r : ℝ) / ((r - 1 : ℕ) : ℝ)) * s)]
  have hrel : ((r - 1 : ℕ) : ℝ) ^ (-s) =
      ((r : ℝ) / ((r - 1 : ℕ) : ℝ)) ^ s * (r : ℝ) ^ (-s) := by
    rw [Real.div_rpow ht.le hu.le, Real.rpow_neg ht.le, Real.rpow_neg hu.le]
    field_simp
  rw [le_div_iff₀ hs]
  rw [show -(1 + s) = -s + (-1) by ring, Real.rpow_add ht,
    Real.rpow_neg_one, hrel]
  have hmul := mul_le_mul_of_nonneg_right hrpow
    (le_of_lt (Real.rpow_pos_of_pos ht (-s)))
  field_simp at hmul ⊢
  nlinarith

private theorem sum_Ioc_telescope_le {s : ℝ} (R : ℕ) :
    ∀ M : ℕ, ∑ r ∈ Ioc R M,
      (((r - 1 : ℕ) : ℝ) ^ (-s) - (r : ℝ) ^ (-s)) ≤ (R : ℝ) ^ (-s) := by
  intro M
  have heq : ∀ M : ℕ, ∑ r ∈ Ioc R M,
      (((r - 1 : ℕ) : ℝ) ^ (-s) - (r : ℝ) ^ (-s)) =
        (R : ℝ) ^ (-s) - (max R M : ℝ) ^ (-s) := by
    intro n
    induction n with
    | zero =>
        have hempty : Ioc R 0 = ∅ := by
          ext x
          simp
        rw [hempty]
        simp
    | succ n ih =>
        by_cases h : R ≤ n
        · rw [Finset.sum_Ioc_succ_top h, ih]
          have hmax : max (R : ℝ) (n : ℝ) = n := max_eq_right (by
            exact_mod_cast h)
          have hmax' : max (R : ℝ) ((n + 1 : ℕ) : ℝ) =
              ((n + 1 : ℕ) : ℝ) := max_eq_right (by
            exact_mod_cast (show R ≤ n + 1 by omega))
          simp only [Nat.add_sub_cancel]
          rw [hmax, hmax']
          ring
        · have hempty : Ioc R (n + 1) = ∅ := by
            ext x
            constructor
            · intro hx
              have hx' := Finset.mem_Ioc.mp hx
              omega
            · intro hx
              have : False := by simp at hx
              contradiction
          rw [hempty]
          have hmax : max (R : ℝ) (n + 1 : ℕ) = R := max_eq_left (by
            exact_mod_cast (show n + 1 ≤ R by omega))
          simp only [Finset.sum_empty]
          rw [hmax]
          ring
  rw [heq M]
  have hnonneg : 0 ≤ (max R M : ℝ) ^ (-s) := Real.rpow_nonneg (by positivity) _
  linarith

private theorem prod_div_sub_one_le (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) :
    ∏ p ∈ S, ((p : ℝ) / (p - 1)) ≤ #S + 1 := by
  revert hS
  induction S using Finset.induction_on_max with
  | empty =>
      intro _
      simp
  | insert a s ha ih =>
      intro hS
      have hnot : a ∉ s := fun h => lt_irrefl a (ha a h)
      have hS' : ∀ p ∈ s, 2 ≤ p := fun p hp => hS p (Finset.mem_insert_of_mem hp)
      have ha2 : 2 ≤ a := hS a (Finset.mem_insert_self a s)
      have hcard : #s + 2 ≤ a := by
        have hsub : s ⊆ Finset.Icc 2 (a - 1) := fun p hp =>
          Finset.mem_Icc.mpr ⟨hS' p hp, by
            have := ha p hp
            omega⟩
        have hle := Finset.card_le_card hsub
        rw [Nat.card_Icc] at hle
        omega
      rw [Finset.prod_insert hnot, Finset.card_insert_of_notMem hnot]
      have ha2R : (2 : ℝ) ≤ a := by exact_mod_cast ha2
      have hcardR : (#s : ℝ) + 2 ≤ a := by exact_mod_cast hcard
      have hprod_nonneg : 0 ≤ ∏ p ∈ s, ((p : ℝ) / (p - 1)) :=
        Finset.prod_nonneg fun p hp => by
          have hp : (2 : ℝ) ≤ p := by exact_mod_cast hS' p hp
          exact div_nonneg (by linarith) (by linarith)
      have hfrac : (a : ℝ) / (a - 1) ≤ ((#s : ℝ) + 2) / ((#s : ℝ) + 1) := by
        rw [div_le_div_iff₀ (by linarith) (by
          have : (0 : ℝ) ≤ #s := by positivity
          linarith)]
        nlinarith
      calc
        (a : ℝ) / (a - 1) * ∏ p ∈ s, ((p : ℝ) / (p - 1))
            ≤ ((#s : ℝ) + 2) / ((#s : ℝ) + 1) * ((#s : ℝ) + 1) :=
          mul_le_mul hfrac (ih hS') hprod_nonneg (by positivity)
        _ = _ := by
          push_cast
          field_simp
          ring

private theorem card_primeFactors_le_two_mul_log {q : ℕ} (hq : 1 ≤ q) :
    (#q.primeFactors : ℝ) ≤ 2 * log q := by
  have h2 : 2 ^ #q.primeFactors ≤ q :=
    (Finset.pow_card_le_prod _ _ _ fun p hp =>
      (Nat.prime_of_mem_primeFactors hp).two_le).trans
      (Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd q))
  have h2R : (2 : ℝ) ^ #q.primeFactors ≤ q := by
    exact_mod_cast h2
  have hlog := Real.log_le_log (by positivity) h2R
  rw [Real.log_pow] at hlog
  have hl2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  nlinarith

/-- `q / φ(q) ≤ ω(q) + 1 ≤ 2 (log q + 1)` for `q ≥ 1`. -/
theorem le_totient_mul {q : ℕ} (hq : 1 ≤ q) : (q : ℝ) ≤ q.totient * (2 * (log q + 1)) := by
  have hid := Nat.totient_mul_prod_primeFactors q
  have hidR : (q.totient : ℝ) * ∏ p ∈ q.primeFactors, (p : ℝ) =
      q * ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
    have hcast := congrArg (Nat.cast (R := ℝ)) hid
    push_cast at hcast
    have hsub : (∏ p ∈ q.primeFactors, ((p - 1 : ℕ) : ℝ)) =
        ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le]
      norm_num
    rw [hsub] at hcast
    exact hcast
  have hne : ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p hp => by
      have hp := (Nat.prime_of_mem_primeFactors hp).two_le
      have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
      linarith
  have hq_eq : (q : ℝ) =
      q.totient * ∏ p ∈ q.primeFactors, ((p : ℝ) / (p - 1)) := by
    rw [Finset.prod_div_distrib]
    rw [← mul_div_assoc, eq_div_iff hne]
    simpa [mul_comm] using hidR.symm
  conv_lhs => rw [hq_eq]
  have hφ : (0 : ℝ) ≤ q.totient := by positivity
  have h1 := prod_div_sub_one_le q.primeFactors fun p hp =>
    (Nat.prime_of_mem_primeFactors hp).two_le
  have h2 := card_primeFactors_le_two_mul_log hq
  calc
    (q.totient : ℝ) * ∏ p ∈ q.primeFactors, ((p : ℝ) / (p - 1))
        ≤ q.totient * (#q.primeFactors + 1) := by gcongr
    _ ≤ q.totient * (2 * (log q + 1)) := by
      gcongr
      nlinarith

/-- Tail of `∑ r^{-(1+s)}`: `∑_{R < r ≤ M} r^{-(1+s)} ≤ R^{-s} / s` for `R ≥ 1`. -/
theorem sum_Ioc_rpow_neg_le {s : ℝ} (hs : 0 < s) {R M : ℕ} (hR : 1 ≤ R) :
    ∑ r ∈ Ioc R M, (r : ℝ) ^ (-(1 + s)) ≤ (R : ℝ) ^ (-s) / s := by
  calc
    _ ≤ ∑ r ∈ Ioc R M,
        ((((r - 1 : ℕ) : ℝ) ^ (-s) - (r : ℝ) ^ (-s)) / s) := by
      apply Finset.sum_le_sum
      intro r hr
      apply rpow_neg_succ_le_sub hs
      have hr' := Finset.mem_Ioc.mp hr
      omega
    _ = (∑ r ∈ Ioc R M,
        (((r - 1 : ℕ) : ℝ) ^ (-s) - (r : ℝ) ^ (-s))) / s := by
      rw [Finset.sum_div]
    _ ≤ _ := div_le_div_of_nonneg_right (sum_Ioc_telescope_le R M) hs.le

private theorem inv_totient_sq_le {r : ℕ} (hr : 1 ≤ r) :
    1 / (r.totient : ℝ) ^ 2 ≤ 576 * (r : ℝ) ^ (-(1 + (5 : ℝ) / 6)) := by
  have hφ : 0 < (r.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hA := le_totient_mul hr
  have hB := log_add_one_le_rpow hrR
  have hr0 : 0 < (r : ℝ) := by positivity
  have hbound : (r : ℝ) ≤ (r.totient : ℝ) * (24 * (r : ℝ) ^ ((1 : ℝ) / 12)) := by
    calc
      (r : ℝ) ≤ r.totient * (2 * (log r + 1)) := hA
      _ ≤ r.totient * (2 * (12 * r ^ ((1 : ℝ) / 12))) := by gcongr
      _ = _ := by ring
  have hinv : 1 / (r.totient : ℝ) ≤ 24 * (r : ℝ) ^ ((1 : ℝ) / 12) / r := by
    rw [div_le_div_iff₀ hφ hr0]
    nlinarith [hbound]
  calc
    1 / (r.totient : ℝ) ^ 2 = (1 / (r.totient : ℝ)) ^ 2 := by field_simp
    _ ≤ (24 * (r : ℝ) ^ ((1 : ℝ) / 12) / r) ^ 2 := by gcongr
    _ = 576 * (r : ℝ) ^ (-(1 + (5 : ℝ) / 6)) := by
      rw [div_pow, mul_pow]
      norm_num
      have hp : ((r : ℝ) ^ ((1 : ℝ) / 12)) ^ 2 = (r : ℝ) ^ ((1 : ℝ) / 6) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hr0.le]
        norm_num
      rw [hp, ← Real.rpow_natCast, mul_div_assoc, ← Real.rpow_sub hr0]
      norm_num

/-- `∑_{R < r ≤ M} 1 / φ(r)² ≤ 768 R^{-3/4}` for `R ≥ 1`. -/
theorem sum_Ioc_inv_totient_sq_le {R M : ℕ} (hR : 1 ≤ R) :
    ∑ r ∈ Ioc R M, 1 / (r.totient : ℝ) ^ 2 ≤ 768 * (R : ℝ) ^ (-(3 : ℝ) / 4) := by
  have htail := sum_Ioc_rpow_neg_le (M := M) (by norm_num : (0 : ℝ) < 5 / 6) hR
  have hpow : (R : ℝ) ^ (-(5 / 6 : ℝ)) ≤ (R : ℝ) ^ (-(3 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hR) (by norm_num)
  have hnonneg : 0 ≤ (R : ℝ) ^ (-(3 : ℝ) / 4) := Real.rpow_nonneg (by positivity) _
  calc
    ∑ r ∈ Ioc R M, 1 / (r.totient : ℝ) ^ 2
        ≤ ∑ r ∈ Ioc R M, 576 * (r : ℝ) ^ (-(1 + (5 : ℝ) / 6)) := by
          apply Finset.sum_le_sum
          intro r hr
          apply inv_totient_sq_le
          have hr' := Finset.mem_Ioc.mp hr
          omega
    _ = 576 * ∑ r ∈ Ioc R M, (r : ℝ) ^ (-(1 + (5 : ℝ) / 6)) := by
      rw [Finset.mul_sum]
    _ ≤ 576 * ((R : ℝ) ^ (-(5 / 6 : ℝ)) / (5 / 6)) := by
      gcongr
    _ ≤ 768 * (R : ℝ) ^ (-(3 : ℝ) / 4) := by
      nlinarith

/-- `∏_{n=2}^{M} (1 - 1 / n²) = (M + 1) / (2 M)` for `M ≥ 1`. -/
theorem prod_Icc_one_sub_inv_sq {M : ℕ} (hM : 1 ≤ M) :
    ∏ n ∈ Icc 2 M, (1 - 1 / (n : ℝ) ^ 2) = ((M : ℝ) + 1) / (2 * M) := by
  induction M with
  | zero => omega
  | succ M ih =>
      by_cases hzero : M = 0
      · subst M
        norm_num
      · have h : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr hzero
        rw [Finset.prod_Icc_succ_top (by omega)]
        rw [ih h]
        have hM0 : (M : ℝ) ≠ 0 := by positivity
        have hM1 : (M : ℝ) + 1 ≠ 0 := by positivity
        norm_num [Nat.cast_add, Nat.cast_one]
        field_simp
        ring

/-! ### The local coefficients -/

/-- The coefficient `μ(q) c_q(ν) c_q(N) / φ(q)²` of the major arcs with denominator `q`. -/
noncomputable def arcCoeff (ν N q : ℕ) : ℝ :=
  (μ q : ℝ) * ramanujanSum q ν * ramanujanSum q N / (q.totient : ℝ) ^ 2

/-- The truncated singular series `𝔖_P(N) = ∑_{q ≤ P} arcCoeff ν N q`. -/
noncomputable def singularSeries (ν N P : ℕ) : ℝ := ∑ q ∈ Icc 1 P, arcCoeff ν N q

@[simp]
theorem arcCoeff_zero_right (ν N : ℕ) : arcCoeff ν N 0 = 0 := by
  simp [arcCoeff]

@[simp]
theorem arcCoeff_one_right (ν N : ℕ) : arcCoeff ν N 1 = 1 := by
  simp [arcCoeff, ramanujanSum_one_left]

theorem arcCoeff_of_not_squarefree {ν N q : ℕ} (hq : ¬ Squarefree q) : arcCoeff ν N q = 0 := by
  simp [arcCoeff, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hq]

theorem arcCoeff_mul_of_coprime {ν N q q' : ℕ} (h : Nat.Coprime q q') :
    arcCoeff ν N (q * q') = arcCoeff ν N q * arcCoeff ν N q' := by
  simp only [arcCoeff, ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
    ArithmeticFunction.isMultiplicative_moebius h, ramanujanSum_mul_of_coprime_left h,
    Nat.totient_mul h]
  push_cast
  field_simp

/-- `q ↦ arcCoeff ν N q` as an arithmetic function. -/
noncomputable def arcCoeffFun (ν N : ℕ) : ArithmeticFunction ℝ :=
  ⟨arcCoeff ν N, arcCoeff_zero_right ν N⟩

theorem isMultiplicative_arcCoeffFun (ν N : ℕ) :
    ArithmeticFunction.IsMultiplicative (arcCoeffFun ν N) := by
  constructor
  · simp [arcCoeffFun, arcCoeff_one_right]
  · intro m n h
    exact arcCoeff_mul_of_coprime h

/-- The local factors at primes, for `ν ∈ {1, 2}` and `N + ν` odd. -/
theorem arcCoeff_prime {ν N p : ℕ} (hp : p.Prime) (hν : ν = 1 ∨ ν = 2) (hpar : Odd (N + ν)) :
    arcCoeff ν N p =
      if p = 2 then 1 else if p ∣ N then 1 / (p - 1 : ℝ) else -1 / (p - 1 : ℝ) ^ 2 := by
  rw [arcCoeff, ArithmeticFunction.moebius_apply_prime hp, ramanujanSum_prime_left hp,
    ramanujanSum_prime_left hp, Nat.totient_prime hp]
  by_cases hp2 : p = 2
  · subst p
    simp only
    rcases hν with rfl | rfl
    · have hN : 2 ∣ N := by
        apply (even_iff_two_dvd).mp
        exact Nat.not_odd_iff_even.mp (Nat.odd_add_one.mp (by simpa using hpar))
      simp [hN]
    · have hN : ¬2 ∣ N := by
        intro hN
        have hNe : Even N := (even_iff_two_dvd).mpr hN
        have : Even (N + 2) := hNe.add even_two
        exact (Nat.not_even_iff_odd.mpr hpar) this
      simp [hN]
  · simp only [if_neg hp2]
    have hpodd : Odd p := hp.odd_of_ne_two hp2
    have hνp : ¬p ∣ ν := by
      rcases hν with rfl | rfl
      · simp [hp.ne_one]
      · intro h
        have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
          (dvd_trans h (by norm_num))
        exact hp2 this
    simp [hνp]
    by_cases hNp : p ∣ N
    · simp [hNp, Nat.cast_sub hp.one_le]
      have hp1 : (p : ℝ) - 1 ≠ 0 := by
        have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
        linarith
      field_simp [hp1]
    · simp [hNp, Nat.cast_sub hp.one_le]

/-- `|arcCoeff ν N q| ≤ σ((q, N)) / φ(q)²` for `ν ∈ {1, 2}`. -/
theorem abs_arcCoeff_le {ν N : ℕ} (hν : ν = 1 ∨ ν = 2) (q : ℕ) :
    |arcCoeff ν N q| ≤ (σ 1 (Nat.gcd q N) : ℝ) / (q.totient : ℝ) ^ 2 := by
  by_cases hq : Squarefree q
  · rw [arcCoeff, abs_div, abs_mul, abs_mul]
    have hμ : |(μ q : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have hν' := abs_ramanujanSum_le_one_of_squarefree hq hν
    have hN' := abs_ramanujanSum_le q N
    have hs : 0 ≤ (q.totient : ℝ) ^ 2 := sq_nonneg _
    have hsq : |(q.totient : ℝ) ^ 2| = (q.totient : ℝ) ^ 2 :=
      abs_of_nonneg hs
    rw [hsq]
    have hνr : |(ramanujanSum q ν : ℝ)| ≤ 1 := by exact_mod_cast hν'
    have hNr : |(ramanujanSum q N : ℝ)| ≤ (σ 1 (Nat.gcd q N) : ℝ) := by
      exact_mod_cast hN'
    have hnum :
        |(μ q : ℝ)| * |(ramanujanSum q ν : ℝ)| * |(ramanujanSum q N : ℝ)| ≤
          (σ 1 (Nat.gcd q N) : ℝ) := by
      calc
        _ ≤ 1 * 1 * |(ramanujanSum q N : ℝ)| := by
          gcongr
        _ = |(ramanujanSum q N : ℝ)| := by ring
        _ ≤ _ := hNr
    exact div_le_div_of_nonneg_right hnum (by positivity)
  · rw [arcCoeff_of_not_squarefree hq]
    simp only [abs_zero]
    positivity

/-! ### The Euler product over `p ≤ P` -/

private theorem one_sub_le_one_add_arcCoeff {ν N p : ℕ}
    (hν : ν = 1 ∨ ν = 2) (hpar : Odd (N + ν)) (hp : p.Prime) (hp2 : p ≠ 2) :
    1 - 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 + arcCoeff ν N p := by
  rw [arcCoeff_prime hp hν hpar]
  simp only [if_neg hp2]
  by_cases hpN : p ∣ N
  · simp only [if_pos hpN]
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hpos : 0 ≤ 1 / ((p : ℝ) - 1) := by positivity
    have hnonneg : 0 ≤ 1 / ((p : ℝ) - 1) ^ 2 := by positivity
    linarith
  · simp only [if_neg hpN]
    simp only [sub_eq_add_neg]
    norm_num [div_eq_mul_inv]

private theorem prod_Icc_le_prod_subset {s : Finset ℕ} {M : ℕ}
    (hs : s ⊆ Icc 2 M) :
    ∏ n ∈ Icc 2 M, (1 - 1 / (n : ℝ) ^ 2) ≤
      ∏ n ∈ s, (1 - 1 / (n : ℝ) ^ 2) := by
  apply Finset.prod_le_prod_of_subset_of_le_one hs
  · intro n hn
    have hn2 := (Finset.mem_Icc.mp hn).1
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have hsq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    have hfrac : 1 / (n : ℝ) ^ 2 ≤ 1 := by
      rw [div_le_iff₀ (by positivity)]
      simpa using hsq
    nlinarith
  · intro n hn _
    have hn2 := (Finset.mem_Icc.mp hn).1
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have hfrac : 0 ≤ 1 / (n : ℝ) ^ 2 := by positivity
    linarith

/-- For admissible `N`, `∏_{p ≤ P} (1 + arcCoeff ν N p) ≥ 1`. -/
theorem one_le_prod_one_add_arcCoeff {ν N : ℕ} (hν : ν = 1 ∨ ν = 2) (hpar : Odd (N + ν)) (P : ℕ) :
    1 ≤ ∏ p ∈ range (P + 1) with p.Prime, (1 + arcCoeff ν N p) := by
  classical
  set S := (range (P + 1)).filter Nat.Prime with hS
  change 1 ≤ ∏ p ∈ S, (1 + arcCoeff ν N p)
  rcases Nat.lt_or_ge P 2 with hP | hP
  · have h_empty : S = ∅ := by
      rw [hS, Finset.filter_eq_empty_iff]
      intro p hp hprime
      have hp2 := hprime.two_le
      rw [Finset.mem_range] at hp
      omega
    simp [h_empty]
  · have h2 : 2 ∈ S := by
      rw [hS, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, Nat.prime_two⟩
    rw [← Finset.mul_prod_erase S (fun p => 1 + arcCoeff ν N p) h2]
    have h2val : 1 + arcCoeff ν N 2 = 2 := by
      rw [arcCoeff_prime Nat.prime_two hν hpar]
      norm_num
    rw [h2val]
    set T := S.erase 2 with hT
    have hT_prime : ∀ p ∈ T, p.Prime ∧ p ≠ 2 ∧ p ≤ P := by
      intro p hp
      rw [hT, Finset.mem_erase, hS, Finset.mem_filter, Finset.mem_range] at hp
      exact ⟨hp.2.2, hp.1, by omega⟩
    have hlow : ∏ p ∈ T, (1 - 1 / ((p : ℝ) - 1) ^ 2) ≤
        ∏ p ∈ T, (1 + arcCoeff ν N p) := by
      apply Finset.prod_le_prod
      · intro p hp
        obtain ⟨hprime, hp2, -⟩ := hT_prime p hp
        have hthree : 3 ≤ p := by
          have htwo := hprime.two_le
          omega
        have hthreeR : (3 : ℝ) ≤ p := by exact_mod_cast hthree
        have hfrac : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 := by
          rw [div_le_one (by nlinarith)]
          nlinarith
        linarith
      · intro p hp
        obtain ⟨hprime, hp2, -⟩ := hT_prime p hp
        exact one_sub_le_one_add_arcCoeff hν hpar hprime hp2
    have himg : ∏ p ∈ T, (1 - 1 / ((p : ℝ) - 1) ^ 2) =
        ∏ n ∈ T.image (fun p : ℕ => p - 1), (1 - 1 / (n : ℝ) ^ 2) := by
      rw [Finset.prod_image]
      · apply Finset.prod_congr rfl
        intro p hp
        obtain ⟨hprime, -, -⟩ := hT_prime p hp
        rw [Nat.cast_sub hprime.one_le, Nat.cast_one]
      · intro p hp p' hp' heq
        have hp_one := (hT_prime p hp).1.one_le
        have hp'_one := (hT_prime p' hp').1.one_le
        change p - 1 = p' - 1 at heq
        omega
    have hsub : T.image (fun p : ℕ => p - 1) ⊆ Icc 2 P := by
      intro n hn
      rw [Finset.mem_image] at hn
      obtain ⟨p, hp, rfl⟩ := hn
      obtain ⟨hprime, hp2, hpP⟩ := hT_prime p hp
      have htwo := hprime.two_le
      have hthree : 3 ≤ p := by omega
      rw [Finset.mem_Icc]
      constructor <;> omega
    have hhalf : (1 : ℝ) / 2 ≤ ∏ n ∈ Icc 2 P, (1 - 1 / (n : ℝ) ^ 2) := by
      rw [prod_Icc_one_sub_inv_sq (by omega)]
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      have hP_one : (1 : ℝ) ≤ P := by
        exact_mod_cast (by omega : 1 ≤ P)
      nlinarith
    calc
      (1 : ℝ) = 2 * (1 / 2) := by norm_num
      _ ≤ 2 * ∏ p ∈ T, (1 + arcCoeff ν N p) := by
        gcongr
        calc
          (1 : ℝ) / 2 ≤ ∏ n ∈ Icc 2 P, (1 - 1 / (n : ℝ) ^ 2) := hhalf
          _ ≤ ∏ n ∈ T.image (fun p : ℕ => p - 1), (1 - 1 / (n : ℝ) ^ 2) :=
            prod_Icc_le_prod_subset hsub
          _ = ∏ p ∈ T, (1 - 1 / ((p : ℝ) - 1) ^ 2) := himg.symm
          _ ≤ _ := hlow

/-- The sum over the divisors of the primorial `P#` equals the Euler product over `p ≤ P`. -/
theorem sum_divisors_primorial_arcCoeff (ν N P : ℕ) :
    ∑ q ∈ (primorial P).divisors, arcCoeff ν N q =
      ∏ p ∈ range (P + 1) with p.Prime, (1 + arcCoeff ν N p) := by
  simpa [arcCoeffFun, primeFactors_primorial, Nat.primesLE_eq_filter_range] using
    (isMultiplicative_arcCoeffFun ν N).prodPrimeFactors_one_add_of_squarefree
      (squarefree_primorial P) |>.symm

/-- The truncated singular series is the primorial sum minus its part with `q > P`. -/
theorem singularSeries_eq_sub (ν N P : ℕ) :
    singularSeries ν N P = ∑ q ∈ (primorial P).divisors, arcCoeff ν N q -
      ∑ q ∈ (primorial P).divisors with P < q, arcCoeff ν N q := by
  rw [eq_sub_iff_add_eq]
  rw [← Finset.sum_filter_add_sum_filter_not (primorial P).divisors (fun q => P < q)]
  suffices singularSeries ν N P =
      ∑ q ∈ (primorial P).divisors with ¬ P < q, arcCoeff ν N q by
    rw [this, add_comm]
  unfold singularSeries
  apply (Finset.sum_subset ?_ ?_).symm
  · intro q hq
    have hq' := Finset.mem_filter.mp hq
    exact Finset.mem_Icc.mpr
      ⟨Nat.pos_of_mem_divisors hq'.1, Nat.le_of_not_gt hq'.2⟩
  · intro q hq hq'
    by_contra hzero
    have hqIcc := Finset.mem_Icc.mp hq
    have hqle : q ≤ P := hqIcc.2
    have hsq : Squarefree q := by
      by_contra hnsq
      exact hzero (arcCoeff_of_not_squarefree hnsq)
    have hdiv : q ∣ primorial P :=
      (hsq.dvd_primorial).trans (primorial_dvd_primorial hqle)
    exact hq' (Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨hdiv, primorial_ne_zero P⟩, by omega⟩)

private theorem sigma_one_gcd_eq {q N : ℕ} (hq : q ≠ 0) :
    (σ 1 (Nat.gcd q N) : ℝ) =
      ∑ d ∈ q.divisors with d ∣ N, (d : ℝ) := by
  rw [ArithmeticFunction.sigma_one_apply]
  push_cast
  apply Finset.sum_congr
  · ext d
    simp [Nat.mem_divisors, Nat.dvd_gcd_iff, hq]
  · intro d hd
    rfl

private theorem card_filter_dvd_le (d Y : ℕ) :
    (#{N ∈ Icc 1 Y | d ∣ N} : ℝ) * d ≤ Y := by
  have hcard : #{N ∈ Icc 1 Y | d ∣ N} = Y / d := by
    rw [show Icc 1 Y = Ioc 0 Y by
      ext n
      simp only [mem_Icc, mem_Ioc]
      omega]
    exact Nat.Ioc_filter_dvd_card_eq_div Y d
  rw [hcard]
  exact_mod_cast Nat.div_mul_le_self Y d

private theorem sum_sigma_one_gcd_le {q Y : ℕ} (hq : 0 < q) :
    ∑ N ∈ Icc 1 Y, (σ 1 (Nat.gcd q N) : ℝ) ≤ Y * (σ 0 q : ℝ) := by
  have hq0 : q ≠ 0 := Nat.ne_of_gt hq
  simp_rw [sigma_one_gcd_eq hq0, Finset.sum_filter]
  rw [Finset.sum_comm]
  calc
    ∑ d ∈ q.divisors, ∑ N ∈ Icc 1 Y, (if d ∣ N then (d : ℝ) else 0) ≤
        ∑ d ∈ q.divisors, (Y : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
      rw [← Finset.sum_filter]
      calc
        ∑ N ∈ Icc 1 Y with d ∣ N, (d : ℝ) =
            (#(Icc 1 Y |>.filter fun N => d ∣ N) : ℝ) * d := by
              rw [Finset.sum_const]
              simp [nsmul_eq_mul]
        _ ≤ Y := card_filter_dvd_le d Y
    _ = Y * (σ 0 q : ℝ) := by
      rw [ArithmeticFunction.sigma_zero_apply]
      rw [Finset.sum_const, nsmul_eq_mul]
      ring

/-! ### The two tails -/

/-- **First moment of the middle range.** Averaged over `N ≤ Y`, the coefficients with
`P < q ≤ Y` are small. -/
theorem sum_abs_sum_arcCoeff_Ioc_le {ν : ℕ} (hν : ν = 1 ∨ ν = 2) (P Y : ℕ) :
    ∑ N ∈ Icc 1 Y, |∑ q ∈ (primorial P).divisors with P < q ∧ q ≤ Y, arcCoeff ν N q| ≤
      Y * ∑ q ∈ Ioc P Y, (σ 0 q : ℝ) * (log q + 1) / (q.totient : ℝ) ^ 2 := by
  calc
    ∑ N ∈ Icc 1 Y,
          |∑ q ∈ (primorial P).divisors with P < q ∧ q ≤ Y, arcCoeff ν N q| ≤
        ∑ N ∈ Icc 1 Y,
          ∑ q ∈ (primorial P).divisors with P < q ∧ q ≤ Y,
            |arcCoeff ν N q| := by
      apply Finset.sum_le_sum
      intro N hN
      exact Finset.abs_sum_le_sum_abs
        (f := arcCoeff ν N)
        (s := (primorial P).divisors.filter fun q => P < q ∧ q ≤ Y)
    _ ≤ ∑ N ∈ Icc 1 Y,
          ∑ q ∈ (primorial P).divisors with P < q ∧ q ≤ Y,
            (σ 1 (Nat.gcd q N) : ℝ) / (q.totient : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro N hN
      apply Finset.sum_le_sum
      intro q hq
      exact abs_arcCoeff_le hν q
    _ = ∑ q ∈ (primorial P).divisors with P < q ∧ q ≤ Y,
          ∑ N ∈ Icc 1 Y,
            (σ 1 (Nat.gcd q N) : ℝ) / (q.totient : ℝ) ^ 2 := by
      rw [Finset.sum_comm]
    _ ≤ ∑ q ∈ (primorial P).divisors with P < q ∧ q ≤ Y,
          (Y * (σ 0 q : ℝ)) / (q.totient : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro q hq
      have hqpos : 0 < q := by
        have hq' := Finset.mem_filter.mp hq
        exact Nat.pos_of_mem_divisors hq'.1
      have hinner := sum_sigma_one_gcd_le (Y := Y) hqpos
      rw [← Finset.sum_div]
      exact div_le_div_of_nonneg_right hinner (sq_nonneg _)
    _ = Y * ∑ q ∈ (primorial P).divisors with P < q ∧ q ≤ Y,
          (σ 0 q : ℝ) / (q.totient : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ ≤ Y * ∑ q ∈ (primorial P).divisors with P < q ∧ q ≤ Y,
          (σ 0 q : ℝ) * (log q + 1) / (q.totient : ℝ) ^ 2 := by
      have hY0 : (0 : ℝ) ≤ Y := by positivity
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro q hq
        have hlog : 1 ≤ log (q : ℝ) + 1 := by
          have hqR : (1 : ℝ) ≤ q := by
            exact_mod_cast (show 1 ≤ q by
              have hq' := Finset.mem_filter.mp hq
              exact Nat.pos_of_mem_divisors hq'.1)
          linarith [Real.log_nonneg hqR]
        have hσ0 : 0 ≤ (σ 0 q : ℝ) := by positivity
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right
          (by simpa [mul_comm] using mul_le_mul_of_nonneg_right hlog hσ0) (by positivity)
      · exact hY0
    _ ≤ Y * ∑ q ∈ Ioc P Y,
          (σ 0 q : ℝ) * (log q + 1) / (q.totient : ℝ) ^ 2 := by
      have hY0 : (0 : ℝ) ≤ Y := by positivity
      apply mul_le_mul_of_nonneg_left
      · refine Finset.sum_le_sum_of_subset_of_nonneg
          (f := fun q => (σ 0 q : ℝ) * (log q + 1) / (q.totient : ℝ) ^ 2) ?_ ?_
        · intro q hq
          have hq' := Finset.mem_filter.mp hq
          exact Finset.mem_Ioc.mpr ⟨hq'.2.1, hq'.2.2⟩
        · intro q hq _
          have hq1 : 1 ≤ q := by
            have hqI := Finset.mem_Ioc.mp hq
            omega
          have hlog : 0 ≤ log (q : ℝ) + 1 := by
            have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq1
            linarith [Real.log_nonneg hqR]
          positivity
      · exact hY0

private theorem divisor_term_le {q : ℕ} (hq : 1 ≤ q) :
    (σ 0 q : ℝ) * (log q + 1) / (q.totient : ℝ) ^ 2 ≤
      13824 * (q : ℝ) ^ (-(1 + (1 : ℝ) / 4)) := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by positivity
  have hτ := card_divisors_le_two_mul_sqrt q
  have hlog := log_add_one_le_rpow hqR
  have hinv := inv_totient_sq_le hq
  have hterm :
      (σ 0 q : ℝ) * (log q + 1) / (q.totient : ℝ) ^ 2 ≤
        (2 * √q) * (12 * (q : ℝ) ^ ((1 : ℝ) / 12)) *
          (576 * (q : ℝ) ^ (-(1 + (5 : ℝ) / 6))) := by
    rw [div_eq_mul_inv]
    calc
      (σ 0 q : ℝ) * (log q + 1) * ((q.totient : ℝ) ^ 2)⁻¹ ≤
          (2 * √q) * (12 * (q : ℝ) ^ ((1 : ℝ) / 12)) *
            ((q.totient : ℝ) ^ 2)⁻¹ := by
        gcongr
      _ ≤ (2 * √q) * (12 * (q : ℝ) ^ ((1 : ℝ) / 12)) *
          (576 * (q : ℝ) ^ (-(1 + (5 : ℝ) / 6))) := by
        gcongr
        simpa [one_div] using hinv
  calc
    (σ 0 q : ℝ) * (log q + 1) / (q.totient : ℝ) ^ 2 ≤
        (2 * √q) * (12 * (q : ℝ) ^ ((1 : ℝ) / 12)) *
          (576 * (q : ℝ) ^ (-(1 + (5 : ℝ) / 6))) := hterm
    _ = 13824 * (q : ℝ) ^ (-(1 + (1 : ℝ) / 4)) := by
      rw [Real.sqrt_eq_rpow]
      calc
        2 * (q : ℝ) ^ ((1 : ℝ) / 2) * (12 * (q : ℝ) ^ ((1 : ℝ) / 12)) *
              (576 * (q : ℝ) ^ (-(1 + (5 : ℝ) / 6))) =
            13824 * ((q : ℝ) ^ ((1 : ℝ) / 2) *
              (q : ℝ) ^ ((1 : ℝ) / 12) *
              (q : ℝ) ^ (-(1 + (5 : ℝ) / 6))) := by ring
        _ = 13824 * (q : ℝ) ^ (-(1 + (1 : ℝ) / 4)) := by
          rw [← Real.rpow_add hq0, ← Real.rpow_add hq0]
          norm_num

/-- `∑_{P < q ≤ Y} τ(q) (log q + 1) / φ(q)² ≤ 10⁵ P^{-1/4}`. -/
theorem sum_Ioc_divisor_bound {P : ℕ} (hP : 1 ≤ P) (Y : ℕ) :
    ∑ q ∈ Ioc P Y, (σ 0 q : ℝ) * (log q + 1) / (q.totient : ℝ) ^ 2 ≤
      10 ^ 5 * (P : ℝ) ^ (-(1 : ℝ) / 4) := by
  have htail := sum_Ioc_rpow_neg_le (M := Y)
    (by norm_num : (0 : ℝ) < 1 / 4) hP
  calc
    ∑ q ∈ Ioc P Y, (σ 0 q : ℝ) * (log q + 1) / (q.totient : ℝ) ^ 2
        ≤ ∑ q ∈ Ioc P Y, 13824 * (q : ℝ) ^ (-(1 + (1 : ℝ) / 4)) := by
          apply Finset.sum_le_sum
          intro q hq
          exact divisor_term_le (by
            have := Finset.mem_Ioc.mp hq
            omega)
    _ = 13824 * ∑ q ∈ Ioc P Y, (q : ℝ) ^ (-(1 + (1 : ℝ) / 4)) := by
      rw [Finset.mul_sum]
    _ ≤ 13824 * ((P : ℝ) ^ (-(1 / 4 : ℝ)) / (1 / 4 : ℝ)) := by
      gcongr
    _ = 55296 * (P : ℝ) ^ (-(1 / 4 : ℝ)) := by ring
    _ ≤ 10 ^ 5 * (P : ℝ) ^ (-(1 : ℝ) / 4) := by
      have hnonneg : 0 ≤ (P : ℝ) ^ (-(1 / 4 : ℝ)) :=
        Real.rpow_nonneg (by positivity) _
      have he : -(1 / 4 : ℝ) = -(1 : ℝ) / 4 := by ring
      rw [he]
      gcongr
      norm_num

/-- For squarefree `q`, `|arcCoeff ν N q| ≤ σ(d) / (φ(d)² φ(q / d)²)` with `d = gcd q N`. -/
theorem abs_arcCoeff_le_gcd {ν N q : ℕ} (hν : ν = 1 ∨ ν = 2) (hq : Squarefree q) :
    |arcCoeff ν N q| ≤ (σ 1 (Nat.gcd q N) : ℝ) /
      ((Nat.gcd q N).totient : ℝ) ^ 2 / ((q / Nat.gcd q N).totient : ℝ) ^ 2 := by
  let d := Nat.gcd q N
  let r := q / d
  have hdvd : d ∣ q := Nat.gcd_dvd_left q N
  have hqr : q = d * r := by
    dsimp [r]
    exact (Nat.mul_div_cancel' hdvd).symm
  have hs : Squarefree (d * r) := by simpa [hqr] using hq
  have hcop : Nat.Coprime d r := (Nat.squarefree_mul_iff.mp hs).1
  have ht : q.totient = d.totient * r.totient := by
    rw [hqr, Nat.totient_mul hcop]
  have hb := abs_arcCoeff_le (N := N) hν q
  dsimp [d, r] at *
  rw [ht] at hb
  push_cast at hb
  calc
    |arcCoeff ν N q| ≤ (σ 1 (Nat.gcd q N) : ℝ) /
        ((Nat.gcd q N).totient * (q / Nat.gcd q N).totient) ^ 2 := hb
    _ = (σ 1 (Nat.gcd q N) : ℝ) /
        (Nat.gcd q N).totient ^ 2 / (q / Nat.gcd q N).totient ^ 2 := by
      rw [mul_pow]
      field_simp

/-- `σ(d) / φ(d)² ≤ 4 (log d + 1)³ / d` for `d ≥ 1`. -/
theorem sigma_div_totient_sq_le {d : ℕ} (hd : 1 ≤ d) :
    (σ 1 d : ℝ) / (d.totient : ℝ) ^ 2 ≤ 4 * (log d + 1) ^ 3 / d := by
  have hσ := sigma_one_le hd
  have hq := le_totient_mul hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hφ : (0 : ℝ) < d.totient := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hdR1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hL : 0 ≤ log (d : ℝ) + 1 := by
    have := Real.log_nonneg hdR1
    linarith
  have hnum :
      (σ 1 d : ℝ) / (d.totient : ℝ) ^ 2 ≤
        (d : ℝ) * (log d + 1) / (d.totient : ℝ) ^ 2 :=
    div_le_div_of_nonneg_right hσ (sq_nonneg _)
  calc
    (σ 1 d : ℝ) / (d.totient : ℝ) ^ 2
        ≤ (d : ℝ) * (log d + 1) / (d.totient : ℝ) ^ 2 := hnum
    _ ≤ 4 * (log d + 1) ^ 3 / d := by
      rw [div_le_div_iff₀ (sq_pos_of_pos hφ) hdR]
      have hq2 :
          (d : ℝ) ^ 2 ≤ (d.totient * (2 * (log d + 1))) ^ 2 :=
        (sq_le_sq₀ (by positivity) (by positivity)).mpr hq
      nlinarith

/-- Regrouping the squarefree `q > Y` by `d = gcd q N` and `r = q / d`. -/
theorem sum_filter_gt_le_sum_divisors {N Y M : ℕ} (hN : 1 ≤ N) (F : ℕ → ℕ → ℝ)
    (hF : ∀ d r, 0 ≤ F d r) :
    ∑ q ∈ M.divisors with Y < q, F (Nat.gcd q N) (q / Nat.gcd q N) ≤
      ∑ d ∈ N.divisors, ∑ r ∈ Ioc ⌊(Y : ℝ) / d⌋₊ M, F d r := by
  classical
  let g : ℕ → Sigma (fun _ : ℕ => ℕ) :=
    fun q => ⟨Nat.gcd q N, q / Nat.gcd q N⟩
  have hinj : Set.InjOn g ↑(M.divisors.filter fun q => Y < q) := by
    intro q hq q' hq' heq
    have heq' := Sigma.mk.inj_iff.mp heq
    have hg : Nat.gcd q N = Nat.gcd q' N := heq'.1
    have hr : q / Nat.gcd q N = q' / Nat.gcd q' N := by
      exact eq_of_heq heq'.2
    have hqeq : q = (q / Nat.gcd q N) * Nat.gcd q N :=
      (Nat.div_mul_cancel (Nat.gcd_dvd_left q N)).symm
    have hqeq' : q' = (q' / Nat.gcd q' N) * Nat.gcd q' N :=
      (Nat.div_mul_cancel (Nat.gcd_dvd_left q' N)).symm
    rw [hqeq, hqeq', hr, hg]
  have hsub : Finset.image g (M.divisors.filter fun q => Y < q) ⊆
      N.divisors.sigma (fun d => Ioc ⌊(Y : ℝ) / d⌋₊ M) := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    have hq' := Finset.mem_filter.mp hq
    have hqM := hq'.1
    have hqY := hq'.2
    have hdpos : 0 < Nat.gcd q N := Nat.gcd_pos_of_pos_right q (by omega)
    have hdmem : Nat.gcd q N ∈ N.divisors := by
      rw [Nat.mem_divisors]
      exact ⟨Nat.gcd_dvd_right q N, by omega⟩
    have hqle : q ≤ M := Nat.le_of_dvd (by
      have := (Nat.mem_divisors.mp hqM).2
      omega) (Nat.mem_divisors.mp hqM).1
    have hrle : q / Nat.gcd q N ≤ M :=
      (Nat.div_le_self q _).trans hqle
    have hfloor :
        ⌊(Y : ℝ) / Nat.gcd q N⌋₊ < q / Nat.gcd q N := by
      apply (Nat.floor_lt (by positivity)).2
      rw [div_lt_iff₀ (by exact_mod_cast hdpos)]
      have hmul : (q / Nat.gcd q N) * Nat.gcd q N = q :=
        Nat.div_mul_cancel (Nat.gcd_dvd_left q N)
      exact_mod_cast (show Y < (q / Nat.gcd q N) * Nat.gcd q N by
        simpa [hmul] using hqY)
    exact Finset.mem_sigma.mpr ⟨hdmem, Finset.mem_Ioc.mpr ⟨hfloor, hrle⟩⟩
  rw [← Finset.sum_image (f := fun p : Sigma (fun _ : ℕ => ℕ) => F p.1 p.2)
    (g := g) hinj]
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun (p : Sigma (fun _ : ℕ => ℕ)) hp _ => hF p.1 p.2)
  simpa [Finset.sum_sigma] using hle

/-- The inner tail `∑_{r > Y / d} 1 / φ(r)² ≤ 768 (2 d / Y)^{3/4}` for `1 ≤ d ≤ Y`. -/
theorem sum_Ioc_floor_inv_totient_sq_le {d Y M : ℕ} (hd : 1 ≤ d) (hdY : d ≤ Y) :
    ∑ r ∈ Ioc ⌊(Y : ℝ) / d⌋₊ M, 1 / (r.totient : ℝ) ^ 2 ≤
      768 * (2 * (d : ℝ) / Y) ^ ((3 : ℝ) / 4) := by
  let R : ℕ := ⌊(Y : ℝ) / d⌋₊
  have hY : (0 : ℝ) < Y := by
    have : 0 < Y := lt_of_lt_of_le (show 0 < d by omega) hdY
    exact_mod_cast this
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hRD : (1 : ℝ) ≤ (Y : ℝ) / d := by
    rw [le_div_iff₀ hdR]
    simpa using (show (1 : ℕ) * d ≤ Y by simpa using hdY)
  have hR : 1 ≤ R := by
    dsimp [R]
    exact Nat.le_floor (by simpa using hRD)
  have hbase := sum_Ioc_inv_totient_sq_le (M := M) hR
  have hlt : (Y : ℝ) / d < (R : ℝ) + 1 := by
    dsimp [R]
    exact Nat.lt_floor_add_one _
  have hR2 : (Y : ℝ) / d ≤ 2 * (R : ℝ) := by
    have hRr : (1 : ℝ) ≤ R := by exact_mod_cast hR
    linarith
  have hinv : (R : ℝ)⁻¹ ≤ 2 * (d : ℝ) / Y := by
    apply (le_div_iff₀ hY).2
    calc
      (R : ℝ)⁻¹ * Y = (Y : ℝ) / R := by
        rw [div_eq_mul_inv]
        ring
      _ ≤ 2 * (d : ℝ) := by
        rw [div_le_iff₀ (by positivity)]
        rw [div_le_iff₀ hdR] at hR2
        nlinarith [hR2]
  have hrpow :
      (R : ℝ) ^ (-(3 : ℝ) / 4) ≤
        (2 * (d : ℝ) / Y) ^ ((3 : ℝ) / 4) := by
    have he : -(3 : ℝ) / 4 = -((3 : ℝ) / 4) := by ring
    rw [he, Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity)]
    exact Real.rpow_le_rpow (by positivity) hinv (by norm_num)
  calc
    ∑ r ∈ Ioc ⌊(Y : ℝ) / d⌋₊ M, 1 / (r.totient : ℝ) ^ 2
        ≤ 768 * (R : ℝ) ^ (-(3 : ℝ) / 4) := by simpa [R] using hbase
    _ ≤ 768 * (2 * (d : ℝ) / Y) ^ ((3 : ℝ) / 4) := by
      gcongr

private theorem two_mul_div_rpow_eq {d Y : ℝ} (hd : 0 < d) (hY : 0 < Y) :
    (2 * d / Y) ^ ((3 : ℝ) / 4) =
      (2 : ℝ) ^ ((3 : ℝ) / 4) * d ^ ((3 : ℝ) / 4) *
        Y ^ (-(3 : ℝ) / 4) := by
  rw [div_eq_mul_inv, Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow hY.le,
    ← Real.rpow_neg hY.le]
  ring

private theorem inner_tail_le {N d Y M : ℕ} (hd : d ∈ N.divisors) (hNY : N ≤ Y) :
    ∑ r ∈ Ioc ⌊(Y : ℝ) / d⌋₊ M,
      (σ 1 d : ℝ) / (d.totient : ℝ) ^ 2 * (1 / (r.totient : ℝ) ^ 2) ≤
        4 * (log N + 1) ^ 3 * (768 * (2 : ℝ) ^ ((3 : ℝ) / 4)) *
          (Y : ℝ) ^ (-(3 : ℝ) / 4) := by
  have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
  have hdN : d ≤ N := Nat.divisor_le hd
  have hdY : d ≤ Y := hdN.trans hNY
  have hd0 : (0 : ℝ) < d := by positivity
  have hY0 : (0 : ℝ) < Y := by
    exact_mod_cast (lt_of_lt_of_le (show 0 < d by omega) hdY)
  have hd1' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hlog : log (d : ℝ) + 1 ≤ log (N : ℝ) + 1 := by
    have hdN' : (d : ℝ) ≤ N := by exact_mod_cast hdN
    linarith [Real.log_le_log hd0 hdN']
  have hlog0 : 0 ≤ log (d : ℝ) + 1 := by
    linarith [Real.log_nonneg hd1']
  have hpow : (log (d : ℝ) + 1) ^ 3 ≤ (log (N : ℝ) + 1) ^ 3 := by
    have hNlog0 : 0 ≤ log (N : ℝ) + 1 := hlog0.trans hlog
    have hdiff : 0 ≤ log (N : ℝ) + 1 - (log (d : ℝ) + 1) :=
      sub_nonneg.mpr hlog
    have hsum : 0 ≤ (log (N : ℝ) + 1) ^ 2 +
        (log (N : ℝ) + 1) * (log (d : ℝ) + 1) + (log (d : ℝ) + 1) ^ 2 :=
      add_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg hNlog0 hlog0)) (sq_nonneg _)
    nlinarith [mul_nonneg hdiff hsum]
  have hdrpow : (d : ℝ) ^ ((3 : ℝ) / 4) ≤ d := by
    have h := Real.rpow_le_rpow_of_exponent_le hd1'
      (show (3 : ℝ) / 4 ≤ 1 by norm_num)
    simpa using h
  have hdfrac : (d : ℝ) ^ ((3 : ℝ) / 4) / d ≤ 1 := by
    exact (div_le_one hd0).2 hdrpow
  rw [← Finset.mul_sum]
  calc
    (σ 1 d : ℝ) / (d.totient : ℝ) ^ 2 *
          ∑ r ∈ Ioc ⌊(Y : ℝ) / d⌋₊ M, 1 / (r.totient : ℝ) ^ 2 ≤
        (4 * (log d + 1) ^ 3 / d) *
          (768 * (2 * (d : ℝ) / Y) ^ ((3 : ℝ) / 4)) :=
      mul_le_mul (sigma_div_totient_sq_le hd1)
        (sum_Ioc_floor_inv_totient_sq_le hd1 hdY)
        (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
    _ = 4 * (log d + 1) ^ 3 * (768 * (2 : ℝ) ^ ((3 : ℝ) / 4)) *
          Y ^ (-(3 : ℝ) / 4) * (d ^ ((3 : ℝ) / 4) / d) := by
      rw [two_mul_div_rpow_eq hd0 hY0]
      ring
    _ ≤ 4 * (log N + 1) ^ 3 * (768 * (2 : ℝ) ^ ((3 : ℝ) / 4)) *
          Y ^ (-(3 : ℝ) / 4) * 1 := by
      have hdfrac0 : 0 ≤ (d : ℝ) ^ ((3 : ℝ) / 4) / d := by positivity
      have hNpow0 : 0 ≤ (log (N : ℝ) + 1) ^ 3 :=
        pow_nonneg (hlog0.trans hlog) _
      have hscale : 0 ≤ 4 * (768 * (2 : ℝ) ^ ((3 : ℝ) / 4)) *
          (Y : ℝ) ^ (-(3 : ℝ) / 4) := by positivity
      calc
        4 * (log d + 1) ^ 3 * (768 * (2 : ℝ) ^ ((3 : ℝ) / 4)) *
            Y ^ (-(3 : ℝ) / 4) * (d ^ ((3 : ℝ) / 4) / d) =
            ((log d + 1) ^ 3 * (d ^ ((3 : ℝ) / 4) / d)) *
              (4 * (768 * (2 : ℝ) ^ ((3 : ℝ) / 4)) * Y ^ (-(3 : ℝ) / 4)) := by ring
        _ ≤ ((log N + 1) ^ 3 * (d ^ ((3 : ℝ) / 4) / d)) *
              (4 * (768 * (2 : ℝ) ^ ((3 : ℝ) / 4)) * Y ^ (-(3 : ℝ) / 4)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hdfrac0) hscale
        _ ≤ ((log N + 1) ^ 3 * 1) *
              (4 * (768 * (2 : ℝ) ^ ((3 : ℝ) / 4)) * Y ^ (-(3 : ℝ) / 4)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdfrac hNpow0) hscale
        _ = _ := by ring
    _ = _ := by ring

/-- **Uniform bound for the far tail.** For `1 ≤ N ≤ Y`, the coefficients with `q > Y` sum
to at most `2 · 10⁴ √N (log N + 1)³ Y^{-3/4}` in absolute value. -/
theorem sum_abs_arcCoeff_gt_le {ν N : ℕ} (hν : ν = 1 ∨ ν = 2) {Y : ℕ} (hN : 1 ≤ N) (hNY : N ≤ Y)
    (P : ℕ) :
    ∑ q ∈ (primorial P).divisors with Y < q, |arcCoeff ν N q| ≤
      2 * 10 ^ 4 * √N * (log N + 1) ^ 3 * (Y : ℝ) ^ (-(3 : ℝ) / 4) := by
  classical
  have hsq : ∀ q ∈ (primorial P).divisors, Squarefree q := fun q hq =>
    (squarefree_primorial P).squarefree_of_dvd (Nat.dvd_of_mem_divisors hq)
  have h1 : ∑ q ∈ (primorial P).divisors with Y < q, |arcCoeff ν N q| ≤
      ∑ q ∈ (primorial P).divisors with Y < q,
        (σ 1 (Nat.gcd q N) : ℝ) / ((Nat.gcd q N).totient : ℝ) ^ 2 *
          (1 / ((q / Nat.gcd q N).totient : ℝ) ^ 2) := by
    apply Finset.sum_le_sum
    intro q hq
    have h := abs_arcCoeff_le_gcd (N := N) hν
      (hsq q (Finset.mem_filter.mp hq).1)
    calc
      |arcCoeff ν N q| ≤
          (σ 1 (Nat.gcd q N) : ℝ) / ((Nat.gcd q N).totient : ℝ) ^ 2 /
            ((q / Nat.gcd q N).totient : ℝ) ^ 2 := h
      _ = _ := by ring
  have h2 := sum_filter_gt_le_sum_divisors (M := primorial P) (Y := Y) hN
    (fun d r => (σ 1 d : ℝ) / (d.totient : ℝ) ^ 2 *
      (1 / (r.totient : ℝ) ^ 2))
    (fun d r => by positivity)
  have h3 : ∑ d ∈ N.divisors, ∑ r ∈ Ioc ⌊(Y : ℝ) / d⌋₊ (primorial P),
      (σ 1 d : ℝ) / (d.totient : ℝ) ^ 2 * (1 / (r.totient : ℝ) ^ 2) ≤
        #N.divisors * (4 * (log N + 1) ^ 3 *
          (768 * (2 : ℝ) ^ ((3 : ℝ) / 4)) * (Y : ℝ) ^ (-(3 : ℝ) / 4)) := by
    have h := Finset.sum_le_card_nsmul N.divisors
      (fun d => ∑ r ∈ Ioc ⌊(Y : ℝ) / d⌋₊ (primorial P),
        (σ 1 d : ℝ) / (d.totient : ℝ) ^ 2 * (1 / (r.totient : ℝ) ^ 2))
      (4 * (log N + 1) ^ 3 * (768 * (2 : ℝ) ^ ((3 : ℝ) / 4)) *
        (Y : ℝ) ^ (-(3 : ℝ) / 4))
      (fun d hd => inner_tail_le (M := primorial P) hd hNY)
    simpa [nsmul_eq_mul] using h
  have hcard : (#N.divisors : ℝ) ≤ 2 * √N := by
    have h := card_divisors_le_two_mul_sqrt N
    rwa [ArithmeticFunction.sigma_zero_apply] at h
  have h2pow : (2 : ℝ) ^ ((3 : ℝ) / 4) ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
      (show (3 : ℝ) / 4 ≤ 1 by norm_num)
    simpa using h
  have hlog : 0 ≤ log (N : ℝ) + 1 := by
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith [Real.log_nonneg hN']
  have hYpow : 0 ≤ (Y : ℝ) ^ (-(3 : ℝ) / 4) :=
    Real.rpow_nonneg (by positivity) _
  calc
    _ ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ _ := h3
    _ ≤ 2 * √N * (4 * (log N + 1) ^ 3 * (768 * 2) *
          (Y : ℝ) ^ (-(3 : ℝ) / 4)) := by
      gcongr
    _ ≤ _ := by
      have hfac : 0 ≤ √(N : ℝ) * (log (N : ℝ) + 1) ^ 3 *
          (Y : ℝ) ^ (-(3 : ℝ) / 4) :=
        mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg hlog 3)) hYpow
      calc
        2 * √N * (4 * (log N + 1) ^ 3 * (768 * 2) *
            (Y : ℝ) ^ (-(3 : ℝ) / 4)) =
            12288 * (√N * (log N + 1) ^ 3 * (Y : ℝ) ^ (-(3 : ℝ) / 4)) := by ring
        _ ≤ 20000 * (√N * (log N + 1) ^ 3 * (Y : ℝ) ^ (-(3 : ℝ) / 4)) :=
          mul_le_mul_of_nonneg_right (by norm_num) hfac
        _ = _ := by norm_num; ring
/- 
  classical
  have hsq : ∀ q ∈ (primorial P).divisors, Squarefree q := fun q hq =>
    (squarefree_primorial P).squarefree_of_dvd (Nat.dvd_of_mem_divisors hq)
  set F : ℕ → ℕ → ℝ := fun d r =>
    (σ 1 d : ℝ) / (d.totient : ℝ) ^ 2 * (1 / (r.totient : ℝ) ^ 2)
  have hF0 : ∀ d r, 0 ≤ F d r := fun d r => by positivity
  have h1 : ∑ q ∈ (primorial P).divisors with Y < q, |arcCoeff ν N q| ≤
      ∑ q ∈ (primorial P).divisors with Y < q,
        F (Nat.gcd q N) (q / Nat.gcd q N) := by
    apply Finset.sum_le_sum
    intro q hq
    have h := abs_arcCoeff_le_gcd (N := N) hν
      (hsq q (Finset.mem_filter.mp hq).1)
    simpa [F, div_div, div_eq_mul_one_div] using h
  have h2 := sum_filter_gt_le_sum_divisors (M := primorial P) (Y := Y) hN F hF0
  have h3 : ∀ d ∈ N.divisors, ∑ r ∈ Ioc ⌊(Y : ℝ) / d⌋₊ (primorial P),
      F d r ≤ 4 * (log N + 1) ^ 3 * 768 * (2 : ℝ) ^ ((3 : ℝ) / 4) *
        (Y : ℝ) ^ (-(3 : ℝ) / 4) := by
    intro d hd
    have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
    have hdN : d ≤ N := Nat.divisor_le hd
    have hdY : d ≤ Y := hdN.trans hNY
    rw [show (∑ r ∈ Ioc ⌊(Y : ℝ) / d⌋₊ (primorial P), F d r) =
      (σ 1 d : ℝ) / (d.totient : ℝ) ^ 2 *
        ∑ r ∈ Ioc ⌊(Y : ℝ) / d⌋₊ (primorial P),
          1 / (r.totient : ℝ) ^ 2 by simp [F, Finset.mul_sum]]
    calc
      _ ≤ (4 * (log d + 1) ^ 3 / d) *
          (768 * (2 * (d : ℝ) / Y) ^ ((3 : ℝ) / 4)) := by
        exact mul_le_mul (sigma_div_totient_sq_le hd1)
          (sum_Ioc_floor_inv_totient_sq_le hd1 hdY)
          (by positivity) (by positivity)
      _ ≤ _ := by
        have hd0 : (0 : ℝ) < d := by positivity
        have hY0 : (0 : ℝ) < Y := by
          exact_mod_cast (lt_of_lt_of_le (show 0 < d by omega) hdY)
        have hlog : log (d : ℝ) + 1 ≤ log (N : ℝ) + 1 := by
          linarith [Real.log_le_log hd0 (by exact_mod_cast hdN)]
        have hlog0 : 0 ≤ log (d : ℝ) + 1 := by
          linarith [Real.log_nonneg (by exact_mod_cast hd1 : (1 : ℝ) ≤ d)]
        have hpow : (log (d : ℝ) + 1) ^ 3 ≤ (log (N : ℝ) + 1) ^ 3 := by
          gcongr
        have hscale : (2 * (d : ℝ) / Y) ^ ((3 : ℝ) / 4) =
            2 ^ ((3 : ℝ) / 4) * d ^ ((3 : ℝ) / 4) *
              (Y : ℝ) ^ (-(3 : ℝ) / 4) := by
          rw [show 2 * (d : ℝ) / Y = 2 * d * Y⁻¹ by ring,
            Real.mul_rpow (by positivity) (by positivity),
            Real.mul_rpow (by positivity) (by positivity),
            Real.inv_rpow hY0.le, ← Real.rpow_neg hY0.le]
          ring
        rw [hscale]
        have hd_rpow : d ^ ((3 : ℝ) / 4) ≤ (d : ℝ) := by
          rw [← Real.rpow_one (d : ℝ)]
          exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hd1) (by norm_num)
        have hdfrac : d ^ ((3 : ℝ) / 4) / d ≤ 1 := by
          exact (div_le_one (by positivity)).2 hd_rpow
        have hnonneg : 0 ≤ (Y : ℝ) ^ (-(3 : ℝ) / 4) := by positivity
        have hnonneg2 : 0 ≤ (2 : ℝ) ^ ((3 : ℝ) / 4) := by positivity
        gcongr
        exact hdfrac
  have h4 : ∑ d ∈ N.divisors, ∑ r ∈ Ioc ⌊(Y : ℝ) / d⌋₊ (primorial P),
      F d r ≤ (N.divisors.card : ℝ) *
        (4 * (log N + 1) ^ 3 * 768 * (2 : ℝ) ^ ((3 : ℝ) / 4) *
          (Y : ℝ) ^ (-(3 : ℝ) / 4)) := by
    calc
      _ ≤ ∑ _d ∈ N.divisors,
          (4 * (log N + 1) ^ 3 * 768 * (2 : ℝ) ^ ((3 : ℝ) / 4) *
            (Y : ℝ) ^ (-(3 : ℝ) / 4)) :=
        Finset.sum_le_sum (fun d hd => h3 d hd)
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
  have hcard := card_divisors_le_two_mul_sqrt N
  have hpow : (2 : ℝ) ^ ((3 : ℝ) / 4) ≤ 2 := by
    rw [← Real.rpow_one (2 : ℝ)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  calc
    _ ≤ (N.divisors.card : ℝ) *
        (4 * (log N + 1) ^ 3 * 768 * (2 : ℝ) ^ ((3 : ℝ) / 4) *
          (Y : ℝ) ^ (-(3 : ℝ) / 4)) := h1.trans (h2.trans h4)
    _ ≤ _ := by
      have hcard' : (N.divisors.card : ℝ) ≤ 2 * √N := by
        simpa [ArithmeticFunction.sigma_zero_apply] using hcard
      have hsqrt : 0 ≤ √(N : ℝ) := Real.sqrt_nonneg _
      have hlog : 0 ≤ (log (N : ℝ) + 1) ^ 3 := by positivity
      have hy : 0 ≤ (Y : ℝ) ^ (-(3 : ℝ) / 4) := by positivity
      nlinarith [hcard', hpow]
 -/

/-! ### Consequences -/

open Classical in
/-- **Positivity of the singular series for almost all admissible `N`.** If the far tail is at
most `1/4` for all `N ≤ Y`, then the admissible `N ≤ Y` with `𝔖_P(N) < 1/2` number at most
`4 · 10⁵ · Y / P^{1/4}`. -/
theorem card_singularSeries_lt_le {ν : ℕ} (hν : ν = 1 ∨ ν = 2) {P Y : ℕ} (hP : 1 ≤ P)
    (hY : 2 * 10 ^ 4 * √Y * (log Y + 1) ^ 3 * (Y : ℝ) ^ (-(3 : ℝ) / 4) ≤ 1 / 4) :
    (#{N ∈ Icc 1 Y | Odd (N + ν) ∧ singularSeries ν N P < 1 / 2} : ℝ) ≤
      4 * 10 ^ 5 * Y * (P : ℝ) ^ (-(1 : ℝ) / 4) := by
  classical
  set S := {N ∈ Icc 1 Y | Odd (N + ν) ∧ singularSeries ν N P < 1 / 2}
  set mid : ℕ → ℝ := fun N =>
    ∑ q ∈ (primorial P).divisors with P < q ∧ q ≤ Y, arcCoeff ν N q
  have hmid : ∀ N ∈ S, 1 / 4 ≤ |mid N| := by
    intro N hNS
    have hNS' := Finset.mem_filter.mp hNS
    have hNI := hNS'.1
    have hodd := hNS'.2.1
    have hlt := hNS'.2.2
    have hN1 := (Finset.mem_Icc.mp hNI).1
    have hNY := (Finset.mem_Icc.mp hNI).2
    let far : ℝ := ∑ q ∈ (primorial P).divisors with P < q ∧ Y < q,
      arcCoeff ν N q
    have hsplit :
        ∑ q ∈ (primorial P).divisors with P < q, arcCoeff ν N q =
          mid N + far := by
      rw [show mid N = ∑ q ∈ (primorial P).divisors with P < q ∧ q ≤ Y,
        arcCoeff ν N q by rfl]
      rw [← Finset.sum_filter_add_sum_filter_not
        ((primorial P).divisors.filter fun q => P < q) (fun q => q ≤ Y)]
      simp [Finset.filter_filter, far, and_comm, not_le]
    have hfarabs : |far| ≤ 1 / 4 := by
      calc
        |far| ≤ ∑ q ∈ (primorial P).divisors with Y < q, |arcCoeff ν N q| := by
          dsimp [far]
          apply le_trans (Finset.abs_sum_le_sum_abs (f := arcCoeff ν N)
            (s := (primorial P).divisors.filter fun q => P < q ∧ Y < q))
            (Finset.sum_le_sum_of_subset_of_nonneg (by
              intro q hq
              have hq' := Finset.mem_filter.mp hq
              exact Finset.mem_filter.mpr ⟨hq'.1, hq'.2.2⟩) (by
              intro q hq _
              exact abs_nonneg _))
        _ ≤ 1 / 4 := by
          have ht := sum_abs_arcCoeff_gt_le hν hN1 hNY P
          have hmono :
              2 * 10 ^ 4 * √N * (log N + 1) ^ 3 *
                  (Y : ℝ) ^ (-(3 : ℝ) / 4) ≤
                2 * 10 ^ 4 * √Y * (log Y + 1) ^ 3 *
                  (Y : ℝ) ^ (-(3 : ℝ) / 4) := by
            gcongr
          exact ht.trans (hmono.trans hY)
    have hprod := one_le_prod_one_add_arcCoeff hν hodd P
    have hSS := singularSeries_eq_sub ν N P
    have hsum := sum_divisors_primorial_arcCoeff ν N P
    have hsing : 1 - (mid N + far) < 1 / 2 := by
      rw [hSS, hsum, hsplit] at hlt
      linarith [hprod]
    have hfarlo := (abs_le.mp hfarabs)
    have hmidgt : 1 / 4 < mid N := by
      linarith
    exact le_abs.mpr (Or.inl (le_of_lt hmidgt))
  have hcard :
      (#S : ℝ) * (1 / 4) ≤ ∑ N ∈ S, |mid N| := by
    have hc := Finset.card_nsmul_le_sum S (fun N => |mid N|) (1 / 4) hmid
    simpa [nsmul_eq_mul] using hc
  have hsumS :
      ∑ N ∈ S, |mid N| ≤ ∑ N ∈ Icc 1 Y, |mid N| := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro N hN _
    exact abs_nonneg _
  have hbound := sum_abs_sum_arcCoeff_Ioc_le hν P Y
  have hdiv := sum_Ioc_divisor_bound hP Y
  have hfinal :
      ∑ N ∈ Icc 1 Y, |mid N| ≤ 10 ^ 5 * Y * (P : ℝ) ^ (-(1 : ℝ) / 4) := by
    calc
      ∑ N ∈ Icc 1 Y, |mid N| ≤ Y * ∑ q ∈ Ioc P Y,
          (σ 0 q : ℝ) * (log q + 1) / (q.totient : ℝ) ^ 2 := hbound
      _ ≤ _ := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using
          (mul_le_mul_of_nonneg_left hdiv (by positivity : (0 : ℝ) ≤ Y))
  change (#S : ℝ) ≤ _
  nlinarith [hcard, hsumS, hfinal]

/-- `|𝔖_P(N)| ≤ 4 (log P + 1)⁴`. -/
theorem abs_singularSeries_le {ν : ℕ} (hν : ν = 1 ∨ ν = 2) (N : ℕ) {P : ℕ} (hP : 1 ≤ P) :
    |singularSeries ν N P| ≤ 4 * (log P + 1) ^ 4 := by
  have hP0 : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hLP : 0 ≤ log (P : ℝ) + 1 := by
    have := Real.log_nonneg hP1
    linarith
  rw [singularSeries]
  calc
    |∑ q ∈ Icc 1 P, arcCoeff ν N q| ≤
        ∑ q ∈ Icc 1 P, |arcCoeff ν N q| := by
      exact Finset.abs_sum_le_sum_abs (f := arcCoeff ν N) (s := Icc 1 P)
    _ ≤ ∑ q ∈ Icc 1 P, 4 * (log (P : ℝ) + 1) ^ 3 / q := by
      apply Finset.sum_le_sum
      intro q hq
      have hqI := Finset.mem_Icc.mp hq
      have hq1 : 1 ≤ q := hqI.1
      have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
      have hdpos : 0 < Nat.gcd q N := by
        by_cases hN0 : N = 0
        · subst N
          simpa using (Nat.zero_lt_of_lt hq1)
        · simpa [Nat.gcd_comm] using
            (Nat.gcd_pos_of_pos_left q (Nat.pos_of_ne_zero hN0))
      have hdle : Nat.gcd q N ≤ q :=
        Nat.le_of_dvd (Nat.zero_lt_of_lt hq1) (Nat.gcd_dvd_left q N)
      have hσ := sigma_one_le (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hdpos))
      have hlogd : log (Nat.gcd q N : ℝ) ≤ log (q : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast hdle)
      have hsig :
          (σ 1 (Nat.gcd q N) : ℝ) ≤ (q : ℝ) * (log q + 1) := by
        calc
          (σ 1 (Nat.gcd q N) : ℝ) ≤
              (Nat.gcd q N : ℝ) * (log (Nat.gcd q N) + 1) := hσ
          _ ≤ (q : ℝ) * (log q + 1) := by
            have hdR : (Nat.gcd q N : ℝ) ≤ q := by exact_mod_cast hdle
            have hlogd' : log (Nat.gcd q N : ℝ) + 1 ≤ log q + 1 := by linarith
            have hLq : 0 ≤ log (q : ℝ) + 1 := by
              have hqR1 : (1 : ℝ) ≤ q := by exact_mod_cast hq1
              have := Real.log_nonneg hqR1
              linarith
            nlinarith
      have hφ : (0 : ℝ) < q.totient := by
        exact_mod_cast Nat.totient_pos.mpr (by omega)
      have htot := le_totient_mul hq1
      have hLq : 0 ≤ log (q : ℝ) + 1 := by
        have hqR1 : (1 : ℝ) ≤ q := by exact_mod_cast hq1
        have := Real.log_nonneg hqR1
        linarith
      have hinv :
          1 / (q.totient : ℝ) ^ 2 ≤
            4 * (log q + 1) ^ 2 / (q : ℝ) ^ 2 := by
        rw [div_le_div_iff₀ (sq_pos_of_pos hφ) (sq_pos_of_pos hqR)]
        nlinarith
      have hterm := abs_arcCoeff_le (N := N) hν q
      calc
        |arcCoeff ν N q| ≤
            (σ 1 (Nat.gcd q N) : ℝ) / (q.totient : ℝ) ^ 2 := hterm
        _ ≤ ((q : ℝ) * (log q + 1)) / (q.totient : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right hsig (sq_nonneg _)
        _ ≤ 4 * (log q + 1) ^ 3 / q := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          calc
            (q : ℝ) * (log q + 1) * ((q.totient : ℝ) ^ 2)⁻¹ ≤
                (q : ℝ) * (log q + 1) *
                  (4 * (log q + 1) ^ 2 / (q : ℝ) ^ 2) := by
              exact mul_le_mul_of_nonneg_left (by simpa [one_div] using hinv) (by positivity)
            _ = 4 * (log q + 1) ^ 3 / q := by
              field_simp
        _ ≤ 4 * (log (P : ℝ) + 1) ^ 3 / q := by
          have hlogqP : log (q : ℝ) ≤ log (P : ℝ) :=
            Real.log_le_log (by positivity) (by exact_mod_cast hqI.2)
          have hqL : 0 ≤ log (q : ℝ) + 1 := by
            have hqR1 : (1 : ℝ) ≤ q := by exact_mod_cast hq1
            linarith [Real.log_nonneg hqR1]
          have hpow :
              (log (q : ℝ) + 1) ^ 3 ≤ (log (P : ℝ) + 1) ^ 3 := by
            gcongr
          exact div_le_div_of_nonneg_right (by nlinarith [hpow]) (by positivity)
    _ = 4 * (log (P : ℝ) + 1) ^ 3 *
          ∑ q ∈ Icc 1 P, 1 / (q : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      field_simp
    _ = 4 * (log (P : ℝ) + 1) ^ 3 * (harmonic P : ℝ) := by
      simp [harmonic_eq_sum_Icc]
    _ ≤ 4 * (log (P : ℝ) + 1) ^ 4 := by
      have hh := harmonic_le_one_add_log P
      calc
        4 * (log (P : ℝ) + 1) ^ 3 * (harmonic P : ℝ) ≤
            4 * (log (P : ℝ) + 1) ^ 3 * (log (P : ℝ) + 1) := by
          exact mul_le_mul_of_nonneg_left (by simpa [add_comm] using hh) (by positivity)
        _ = 4 * (log (P : ℝ) + 1) ^ 4 := by ring

end CircleMethod
