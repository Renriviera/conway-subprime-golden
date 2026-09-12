/-
Copyright (c) 2026 Romain Popescu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Romain Popescu
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Totient
import ConwayGolden.NumberTheory.CircleMethod.ExpSum

/-!
# Ramanujan sums

The Ramanujan sum `c_q(m) = ∑_{a < q, (a, q) = 1} e (a m / q)` is defined here in its Möbius
form `∑_{d ∣ (q, m)} d μ(q / d)`, which is an integer, and the exponential form is proved as a
theorem. These sums are the local factors of the singular series in the circle method.

## Main definitions

* `CircleMethod.coprimeRange q`: the units `{a < q | (a, q) = 1}` as a `Finset ℕ`.
* `CircleMethod.ramanujanSum q m`: the Ramanujan sum `c_q(m)`, in Möbius form.
* `CircleMethod.ramanujanSumFun m`: `q ↦ c_q(m)` as an `ArithmeticFunction ℤ`.

## Main statements

* `CircleMethod.sum_e_coprimeRange`: `∑_{a ∈ coprimeRange q} e (a m / q) = c_q(m)`.
* `CircleMethod.isMultiplicative_ramanujanSumFun`: `q ↦ c_q(m)` is multiplicative.
* `CircleMethod.ramanujanSum_prime_left`: `c_p(m) = p - 1` if `p ∣ m` and `-1` otherwise.
* `CircleMethod.abs_ramanujanSum_le`: `|c_q(m)| ≤ σ((q, m))`.
* `CircleMethod.ramanujanSum_mul_of_coprime_right`: `c_q(ν a) = c_q(ν)` for `(a, q) = 1`.

## References

* [T. M. Apostol, *Introduction to analytic number theory*, §8.3][Apostol1976]
-/

namespace CircleMethod

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.sigma

/-! ### Units modulo `q` -/

/-- The residues `a < q` coprime to `q`. -/
def coprimeRange (q : ℕ) : Finset ℕ := {a ∈ range q | Nat.Coprime a q}

theorem mem_coprimeRange {q a : ℕ} : a ∈ coprimeRange q ↔ a < q ∧ Nat.Coprime a q := by
  simp [coprimeRange]

theorem card_coprimeRange (q : ℕ) : #(coprimeRange q) = q.totient := by
  rw [Nat.totient_eq_card_coprime]
  congr 1
  ext a
  simp [coprimeRange, Nat.coprime_comm]

/-- Multiplication by a unit permutes the units. -/
theorem sum_coprimeRange_mul_mod {M : Type*} [AddCommMonoid M] {q a : ℕ} (ha : Nat.Coprime a q)
    (f : ℕ → M) :
    ∑ r ∈ coprimeRange q, f (r * a % q) = ∑ r ∈ coprimeRange q, f r := by
  classical
  by_cases hq : q = 0
  · simp [coprimeRange, hq]
  have hq_pos : 0 < q := Nat.pos_of_ne_zero hq
  let g : ℕ → ℕ := fun r ↦ r * a % q
  have h_subset : (coprimeRange q).image g ⊆ coprimeRange q := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨r, hr, rfl⟩
    change r * a % q ∈ coprimeRange q
    refine mem_coprimeRange.2 ⟨Nat.mod_lt _ hq_pos, ?_⟩
    have hr_coprime : Nat.Coprime r q := (mem_coprimeRange.mp hr).2
    have hmul : Nat.Coprime (r * a) q := by
      rw [Nat.coprime_comm, Nat.coprime_mul_iff_right]
      exact ⟨hr_coprime.symm, ha.symm⟩
    rw [Nat.coprime_iff_gcd_eq_one] at hmul ⊢
    calc
      (r * a % q).gcd q = q.gcd (r * a) := (Nat.gcd_rec q (r * a)).symm
      _ = (r * a).gcd q := Nat.gcd_comm _ _
      _ = 1 := hmul
  have h_inj : Set.InjOn g (coprimeRange q) := by
    intro r hr r' hr' hrr'
    have hmod : r * a ≡ r' * a [MOD q] := hrr'
    have hcancel := hmod.cancel_right_of_coprime
      (by simpa [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm] using ha)
    change r % q = r' % q at hcancel
    rw [Nat.mod_eq_of_lt (mem_coprimeRange.mp hr).1,
      Nat.mod_eq_of_lt (mem_coprimeRange.mp hr').1] at hcancel
    exact hcancel
  have h_image : (coprimeRange q).image g = coprimeRange q :=
    Finset.eq_of_subset_of_card_le h_subset <| by
      rw [Finset.card_image_of_injOn h_inj]
  change ∑ r ∈ coprimeRange q, f (g r) = ∑ r ∈ coprimeRange q, f r
  nth_rw 2 [← h_image]
  rw [Finset.sum_image h_inj]

/-! ### Ramanujan sums -/

/-- **Ramanujan's sum** `c_q(m)`, in Möbius form `∑_{d ∣ q, d ∣ m} d μ(q / d)`. -/
def ramanujanSum (q m : ℕ) : ℤ :=
  ∑ d ∈ q.divisors, if d ∣ m then (d : ℤ) * μ (q / d) else 0

@[simp]
theorem ramanujanSum_zero_left (m : ℕ) : ramanujanSum 0 m = 0 := by
  simp [ramanujanSum]

@[simp]
theorem ramanujanSum_one_left (m : ℕ) : ramanujanSum 1 m = 1 := by
  simp [ramanujanSum]

/-- `c_q(1) = μ(q)`. -/
theorem ramanujanSum_one_right (q : ℕ) : ramanujanSum q 1 = μ q := by
  cases q with
  | zero =>
      have hnot : ¬Squarefree 0 := by
        intro hs
        have hu := hs 2 (by norm_num)
        norm_num at hu
      simp [ramanujanSum, ArithmeticFunction.moebius, hnot]
  | succ q =>
      simp [ramanujanSum, Nat.div_one]

/-- `c_q(0) = φ(q)`. -/
theorem ramanujanSum_zero_right (q : ℕ) : ramanujanSum q 0 = q.totient := by
  classical
  cases q with
  | zero => simp
  | succ q =>
    rw [ramanujanSum]
    simp only [Nat.dvd_zero, ite_true]
    have h :=
      (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
        (f := fun n : ℕ => (n.totient : ℤ)) (g := fun n : ℕ => (n : ℤ))).mp
        (by
          intro n hn
          exact_mod_cast Nat.sum_totient n) (q + 1) (Nat.succ_pos q)
    calc
      ∑ d ∈ (q + 1).divisors, (d : ℤ) * μ ((q + 1) / d) =
          ∑ d ∈ (q + 1).divisors, (μ ((q + 1) / d) : ℤ) * d := by
        apply Finset.sum_congr rfl
        intro d hd
        ring
      _ = ∑ x ∈ (q + 1).divisorsAntidiagonal, (μ x.1 : ℤ) * x.2 := by
        rw [← Nat.sum_divisorsAntidiagonal'
          (f := fun x y : ℕ => (μ x : ℤ) * (y : ℤ))]
      _ = (q + 1).totient := by simpa using h

/-- `c_q(m)` depends only on `gcd q m`. -/
theorem ramanujanSum_eq_of_gcd_eq {q m m' : ℕ} (h : Nat.gcd q m = Nat.gcd q m') :
    ramanujanSum q m = ramanujanSum q m' := by
  classical
  simp only [ramanujanSum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdq : d ∣ q := Nat.dvd_of_mem_divisors hd
  have hdm : d ∣ m ↔ d ∣ m' := by
    constructor
    · intro hdm
      have hg : d ∣ Nat.gcd q m := (Nat.dvd_gcd_iff).2 ⟨hdq, hdm⟩
      rw [h] at hg
      exact (Nat.dvd_gcd_iff).1 hg |>.2
    · intro hdm
      have hg : d ∣ Nat.gcd q m' := (Nat.dvd_gcd_iff).2 ⟨hdq, hdm⟩
      rw [← h] at hg
      exact (Nat.dvd_gcd_iff).1 hg |>.2
  simp only [hdm]

/-- `c_q(ν a) = c_q(ν)` when `(a, q) = 1`. -/
theorem ramanujanSum_mul_of_coprime_right {q a : ℕ} (ha : Nat.Coprime a q) (ν : ℕ) :
    ramanujanSum q (ν * a) = ramanujanSum q ν := by
  apply ramanujanSum_eq_of_gcd_eq
  exact ha.gcd_mul_right_cancel_right ν

/-- Möbius inversion evaluated on the common divisors of two natural numbers. -/
private theorem sum_moebius_divisors_gcd (a q : ℕ) (hq : 0 < q) :
    ∑ d ∈ q.divisors with d ∣ a, (μ d : ℂ) = if Nat.Coprime a q then 1 else 0 := by
  classical
  have hdivisors : q.divisors.filter (· ∣ a) = (Nat.gcd q a).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdq, -⟩, hda⟩
      exact ⟨Nat.dvd_gcd hdq hda, Nat.gcd_ne_zero_left hq.ne'⟩
    · rintro ⟨hd, -⟩
      exact ⟨⟨hd.trans (Nat.gcd_dvd_left _ _), hq.ne'⟩,
        hd.trans (Nat.gcd_dvd_right _ _)⟩
  rw [hdivisors]
  have h := congrArg (fun F : ArithmeticFunction ℂ => F (Nat.gcd q a))
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  simpa [ArithmeticFunction.one_apply, Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm] using h

/-- Summing an additive character over multiples of a divisor. -/
private theorem sum_e_range_dvd {q d : ℕ} (hq : 0 < q) (hd : d ∣ q) (m : ℕ) :
    ∑ a ∈ range q with d ∣ a, e (a * m / q) =
      ∑ b ∈ range (q / d), e (b * m / (q / d)) := by
  classical
  have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd hq
  have hqd_pos : 0 < q / d :=
    Nat.div_pos (Nat.le_of_dvd hq hd) hd_pos
  have hq_eq : q = d * (q / d) := (Nat.mul_div_cancel' hd).symm
  have hfilter : (range q).filter (d ∣ ·) = (range (q / d)).image (d * ·) := by
    ext a
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨ha, ⟨b, rfl⟩⟩
      refine ⟨b, ?_, rfl⟩
      rw [hq_eq] at ha
      exact (Nat.mul_lt_mul_left hd_pos).mp ha
    · rintro ⟨b, hb, rfl⟩
      constructor
      · rw [hq_eq]
        exact (Nat.mul_lt_mul_left hd_pos).mpr hb
      · exact dvd_mul_right d b
  rw [hfilter, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro b hb
    congr 1
    push_cast
    field_simp [hqd_pos.ne']
  · intro x hx y hy hxy
    exact Nat.eq_of_mul_eq_mul_left hd_pos hxy

/-- The exponential form of Ramanujan's sum: `∑_{(a, q) = 1} e (a m / q) = c_q(m)`. -/
theorem sum_e_coprimeRange {q : ℕ} (hq : 0 < q) (m : ℕ) :
    ∑ a ∈ coprimeRange q, e (a * m / q) = (ramanujanSum q m : ℂ) := by
  classical
  have h1 : ∑ a ∈ coprimeRange q, e (a * m / q) =
      ∑ a ∈ range q, ∑ d ∈ q.divisors with d ∣ a, (μ d : ℂ) * e (a * m / q) := by
    rw [coprimeRange, Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_mul, sum_moebius_divisors_gcd a q hq]
    split_ifs <;> simp
  have h2 : ∑ a ∈ range q, ∑ d ∈ q.divisors with d ∣ a, (μ d : ℂ) * e (a * m / q) =
      ∑ d ∈ q.divisors, (μ d : ℂ) * ∑ a ∈ range q with d ∣ a, e (a * m / q) := by
    simp_rw [Finset.mul_sum]
    exact Finset.sum_comm' (fun a d => by simp only [Finset.mem_filter]; tauto)
  have h3 : ∀ d ∈ q.divisors, ∑ a ∈ range q with d ∣ a, e (a * m / q) =
      if q / d ∣ m then ((q / d : ℕ) : ℂ) else 0 := by
    intro d hd
    have hd' : d ∣ q := (Nat.mem_divisors.mp hd).1
    have hpos : 0 < q / d :=
      Nat.div_pos (Nat.le_of_dvd hq hd') (Nat.pos_of_dvd_of_pos hd' hq)
    rw [sum_e_range_dvd hq hd' m]
    have h := sum_e_mul_div hpos (m : ℤ)
    simp only [Int.cast_natCast, Int.natCast_dvd_natCast] at h
    convert h using 1
    apply Finset.sum_congr rfl
    intro b hb
    congr 1
    field_simp [hpos.ne']
    norm_cast
    calc
      b * m * d * (q / d) = b * m * (d * (q / d)) := by ac_rfl
      _ = b * m * q := by rw [Nat.mul_div_cancel' hd']
  rw [h1, h2, Finset.sum_congr rfl (fun d hd => by rw [h3 d hd])]
  have h4 : ((ramanujanSum q m : ℤ) : ℂ) =
      ∑ d ∈ q.divisors, if d ∣ m then (d : ℂ) * μ (q / d) else 0 := by
    simp [ramanujanSum, Int.cast_sum, Int.cast_ite, Int.cast_mul]
  rw [h4, ← Nat.sum_div_divisors q (fun d => if d ∣ m then (d : ℂ) * μ (q / d) else 0)]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd' : d ∣ q := (Nat.mem_divisors.mp hd).1
  rw [Nat.div_div_self hd' hq.ne']
  split_ifs <;> simp [mul_comm]

/-- The conjugate exponential form: `∑_{(a, q) = 1} e (-(a m / q)) = c_q(m)`. -/
theorem sum_e_neg_coprimeRange {q : ℕ} (hq : 0 < q) (m : ℕ) :
    ∑ a ∈ coprimeRange q, e (-(a * m / q)) = (ramanujanSum q m : ℂ) := by
  have h := congrArg (starRingEnd ℂ) (sum_e_coprimeRange hq m)
  simpa only [map_sum, e_neg, Complex.conj_conj, map_intCast] using h

/-- `c_p(m) = p - 1` if `p ∣ m`, and `-1` otherwise, for `p` prime. -/
theorem ramanujanSum_prime_left {p : ℕ} (hp : p.Prime) (m : ℕ) :
    ramanujanSum p m = if p ∣ m then (p : ℤ) - 1 else -1 := by
  classical
  rw [ramanujanSum, hp.divisors]
  rw [Finset.sum_insert]
  · rw [Finset.sum_singleton]
    simp only [Nat.one_dvd, ite_true, Nat.cast_one, one_mul,
      Nat.div_self hp.pos, ArithmeticFunction.moebius_apply_one]
    rw [Nat.div_one, ArithmeticFunction.moebius_apply_prime hp]
    split_ifs <;> ring
  · simpa using Ne.symm hp.ne_one

/-- `|c_q(m)| ≤ σ((q, m))`. -/
theorem abs_ramanujanSum_le (q m : ℕ) : |ramanujanSum q m| ≤ σ 1 (Nat.gcd q m) := by
  classical
  by_cases hq : q = 0
  · simp [hq]
  rw [ramanujanSum]
  have hdivisors : q.divisors.filter (· ∣ m) = (Nat.gcd q m).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdq, -⟩, hdm⟩
      exact ⟨Nat.dvd_gcd hdq hdm, Nat.gcd_ne_zero_left hq⟩
    · rintro ⟨hd, -⟩
      exact ⟨⟨hd.trans (Nat.gcd_dvd_left _ _), hq⟩,
        hd.trans (Nat.gcd_dvd_right _ _)⟩
  calc
    |∑ x ∈ q.divisors, if x ∣ m then (x : ℤ) * μ (q / x) else 0| ≤
        ∑ x ∈ q.divisors, |if x ∣ m then (x : ℤ) * μ (q / x) else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    ∑ x ∈ q.divisors, |if x ∣ m then (x : ℤ) * μ (q / x) else 0| ≤
        ∑ x ∈ q.divisors, if x ∣ m then (x : ℤ) else 0 := by
      gcongr with d hd
      by_cases hdm : d ∣ m
      · rw [if_pos hdm, if_pos hdm, abs_mul, abs_of_nonneg (Int.natCast_nonneg d)]
        calc
          (d : ℤ) * |μ (q / d)| ≤ (d : ℤ) * 1 :=
            mul_le_mul_of_nonneg_left ArithmeticFunction.abs_moebius_le_one
              (Int.natCast_nonneg d)
          _ = d := by simp
      · simp [hdm]
    _ = ∑ x ∈ (Nat.gcd q m).divisors, (x : ℤ) := by
      rw [← Finset.sum_filter, hdivisors]
    _ = σ 1 (Nat.gcd q m) := by
      rw [ArithmeticFunction.sigma_one_apply]
      rw [Nat.cast_sum]

/-! ### Multiplicativity -/

/-- `q ↦ c_q(m)` as an arithmetic function. -/
def ramanujanSumFun (m : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun q ↦ ramanujanSum q m, ramanujanSum_zero_left m⟩

@[simp]
theorem ramanujanSumFun_apply (m q : ℕ) : ramanujanSumFun m q = ramanujanSum q m := rfl

/-- The divisor-weighted indicator of the divisors of `m`. -/
private def dvdIndicator (m : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun d ↦ if d ∣ m then (d : ℤ) else 0, by simp⟩

/-- `q ↦ c_q(m)` is the Dirichlet convolution of `μ` with `d ↦ d · [d ∣ m]`; in particular it is
multiplicative. -/
theorem isMultiplicative_ramanujanSumFun (m : ℕ) : IsMultiplicative (ramanujanSumFun m) := by
  have h_indicator : IsMultiplicative (dvdIndicator m) := by
    constructor
    · simp [dvdIndicator]
    intro x y hxy
    simp only [dvdIndicator, ArithmeticFunction.coe_mk]
    by_cases hx : x ∣ m <;> by_cases hy : y ∣ m
    · rw [if_pos (hxy.mul_dvd_of_dvd_of_dvd hx hy), if_pos hx, if_pos hy, Nat.cast_mul]
    · have hxy' : ¬x * y ∣ m := fun h => hy (dvd_trans (by simp) h)
      simp [hxy', hx, hy]
    · have hxy' : ¬x * y ∣ m := fun h => hx (dvd_trans (dvd_mul_right x y) h)
      simp [hxy', hx, hy]
    · have hxy' : ¬x * y ∣ m := fun h => hx (dvd_trans (dvd_mul_right x y) h)
      simp [hxy', hx, hy]
  have h_conv : ramanujanSumFun m = dvdIndicator m * μ := by
    ext q
    rw [ramanujanSumFun_apply, ramanujanSum, ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal
        (f := fun x y : ℕ => dvdIndicator m x * μ y)]
    apply Finset.sum_congr rfl
    intro d hd
    simp [dvdIndicator]
  rw [h_conv]
  exact h_indicator.mul ArithmeticFunction.isMultiplicative_moebius

theorem ramanujanSum_mul_of_coprime_left {q q' : ℕ} (h : Nat.Coprime q q') (m : ℕ) :
    ramanujanSum (q * q') m = ramanujanSum q m * ramanujanSum q' m :=
  (isMultiplicative_ramanujanSumFun m).map_mul_of_coprime h

/-- For squarefree `q`, `c_q(m)` is the product of its prime local factors. -/
theorem ramanujanSum_eq_prod_primeFactors {q : ℕ} (hq : Squarefree q) (m : ℕ) :
    ramanujanSum q m = ∏ p ∈ q.primeFactors, ramanujanSum p m := by
  change ramanujanSumFun m q = _
  rw [(isMultiplicative_ramanujanSumFun m).multiplicative_factorization
    (ramanujanSumFun m) hq.ne_zero]
  rw [Finsupp.prod]
  simp only [Nat.support_factorization]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Nat.factorization_eq_one_of_squarefree hq
    (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)]
  simp

/-- For squarefree `q` and `ν ∈ {1, 2}`, `|c_q(ν)| ≤ 1`. -/
theorem abs_ramanujanSum_le_one_of_squarefree {q ν : ℕ} (hq : Squarefree q)
    (hν : ν = 1 ∨ ν = 2) : |ramanujanSum q ν| ≤ 1 := by
  rw [ramanujanSum_eq_prod_primeFactors hq ν]
  rw [Finset.abs_prod]
  apply Finset.prod_le_one
  · intro p hp
    exact abs_nonneg _
  · intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    rcases hν with rfl | rfl
    · simp [ramanujanSum_prime_left hprime, hprime.ne_one]
    · by_cases hdiv : p ∣ 2
      · have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
        have hge : 2 ≤ p := hprime.two_le
        have heq : p = 2 := by omega
        subst p
        simp [ramanujanSum_prime_left hprime]
      · simp [ramanujanSum_prime_left hprime, hdiv]

end CircleMethod
