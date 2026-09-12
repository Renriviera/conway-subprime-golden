/-
Copyright (c) 2026 Romain Popescu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Romain Popescu
-/
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import ConwayGolden.NumberTheory.CircleMethod.RamanujanSum
import ConwayGolden.NumberTheory.CircleMethod.Setup

/-!
# Major and minor arcs on the discrete circle

The frequencies `k / Q`, `k < Q`, are split into *major arcs* — those within `J₀ / Q` of a
reduced fraction `a / q` with `q ≤ P`, where `J₀ = ⌊2 P Q / X⌋₊` — and the complementary
*minor arcs*. Since `q ∣ Q` for all `q ≤ P`, every `a / q` is itself a grid point and the major
arc around it is exactly `{a / q + j / Q : |j| ≤ J₀}`; this makes the singular integral
independent of `(q, a)`.

## Main definitions

* `CircleMethod.arcIndex P`: the pairs `(q, a)` with `1 ≤ q ≤ P`, `a < q`, `(a, q) = 1`.
* `Ranges.halfWidth R X P`: `J₀ = ⌊2 P Q / X⌋₊`.
* `Ranges.arcAngle R X P (q, a) j`: the angle `a / q + j / Q`.
* `Ranges.IsMajor R X P k`: `k / Q` lies on some major arc.
* `Ranges.minorSet R X P`: the `k < Q` on minor arcs.

## Main statements

* `Ranges.sum_range_Q_eq`: for `1`-periodic `F`, `∑_{k < Q} F (k / Q)` splits as the sum over
  major arcs, indexed by `(q, a, j)`, plus the sum over `minorSet`.
* `Ranges.exists_approx_of_mem_minorSet`: every minor-arc frequency has a Dirichlet
  approximation `a / q` with `P < q ≤ X / P` and `|k / Q - a / q| ≤ q⁻²`.

## Implementation notes

The hypotheses `8 P³ ≤ X` (arcs are disjoint and do not wrap) and `X ≤ P Q` (the grid is fine
enough that `J₀ / Q ≥ P / X`) are carried explicitly; in the final assembly `P` is a power of
`log X` and both hold for large `X`.
-/

namespace CircleMethod

open Finset Real

/-- The index set of the major arcs: `(q, a)` with `1 ≤ q ≤ P`, `a < q` and `(a, q) = 1`. -/
def arcIndex (P : ℕ) : Finset (ℕ × ℕ) :=
  {qa ∈ Icc 1 P ×ˢ range P | qa.2 < qa.1 ∧ Nat.Coprime qa.2 qa.1}

theorem mem_arcIndex {P : ℕ} {qa : ℕ × ℕ} :
    qa ∈ arcIndex P ↔ 0 < qa.1 ∧ qa.1 ≤ P ∧ qa.2 < qa.1 ∧ Nat.Coprime qa.2 qa.1 := by
  simp [arcIndex, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
    Finset.mem_range]
  omega

theorem card_arcIndex_le (P : ℕ) : #(arcIndex P) ≤ P ^ 2 := by
  calc
    #(arcIndex P) ≤ #(Icc 1 P ×ˢ range P) := Finset.card_filter_le _ _
    _ = #(Icc 1 P) * #(range P) := Finset.card_product _ _
    _ = (P * P : ℕ) := by simp [Nat.card_Icc]
    _ = P ^ 2 := by ring

private theorem distInt_ge_of_pos_int_div {n : ℤ} {D : ℕ} (hD : 0 < D)
    (hn : 0 < n) (hnD : n < D) :
    1 / (D : ℝ) ≤ distInt ((n : ℝ) / D) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlt : (n : ℝ) / D < 1 := by
    rw [div_lt_iff₀ hD']
    simpa using (show (n : ℝ) < D by exact_mod_cast hnD)
  have hpos : 0 < (n : ℝ) / D := div_pos hn' hD'
  by_cases hh : (n : ℝ) / D < 1 / 2
  · have hr : round ((n : ℝ) / D) = 0 :=
      (round_eq_zero_iff).2 ⟨by linarith, hh⟩
    rw [distInt, hr]
    norm_num
    rw [abs_of_pos hpos]
    have hfrac : (1 : ℝ) / D ≤ (n : ℝ) / D :=
      (div_le_div_iff_of_pos_right hD').2 (by
        exact_mod_cast (show (1 : ℤ) ≤ n by omega))
    simpa only [one_div] using hfrac
  · have hr : round ((n : ℝ) / D) = 1 :=
      (round_eq_iff).2 (by constructor <;> linarith)
    rw [distInt, hr]
    norm_num
    rw [abs_of_neg (sub_neg.mpr hlt)]
    have hfrac : (1 : ℝ) / D ≤ ((D : ℝ) - n) / D :=
      (div_le_div_iff_of_pos_right hD').2 (by
        have : n < (D : ℤ) := by exact_mod_cast hnD
        have hdiff : (1 : ℤ) ≤ (D : ℤ) - n := by omega
        exact_mod_cast hdiff)
    have heq : ((D : ℝ) - n) / D = -((n : ℝ) / D - 1) := by
      field_simp
      ring
    rw [heq] at hfrac
    simpa only [one_div] using hfrac

private theorem distInt_ge_of_int_div {n : ℤ} {D : ℕ} (hD : 0 < D)
    (hn : n ≠ 0) (hnD : |n| < D) :
    1 / (D : ℝ) ≤ distInt ((n : ℝ) / D) := by
  rcases lt_or_gt_of_ne hn with hnneg | hnpos
  · have hpos : 0 < -n := by omega
    have hnD' : |n| < (D : ℤ) := by exact_mod_cast hnD
    have hlt : -n < (D : ℤ) := by
      rw [abs_of_neg (by omega : n < 0)] at hnD'
      exact hnD'
    have h := distInt_ge_of_pos_int_div hD hpos hlt
    simpa [distInt_neg, neg_div] using h
  · exact distInt_ge_of_pos_int_div hD hnpos (by
      have hnD' : |n| < (D : ℤ) := by exact_mod_cast hnD
      rw [abs_of_nonneg (by omega : 0 ≤ n)] at hnD'
      exact hnD')

/-- Distinct reduced fractions with denominators `≤ P` are at least `1 / P²` apart mod `1`. -/
theorem le_distInt_sub_of_ne {P : ℕ} {qa qa' : ℕ × ℕ} (h : qa ∈ arcIndex P)
    (h' : qa' ∈ arcIndex P) (hne : qa ≠ qa') :
    1 / (P : ℝ) ^ 2 ≤ distInt ((qa.2 : ℝ) / qa.1 - qa'.2 / qa'.1) := by
  rcases qa with ⟨q, a⟩
  rcases qa' with ⟨q', a'⟩
  have hqa := (mem_arcIndex.mp h)
  have hqa' := (mem_arcIndex.mp h')
  change 0 < q ∧ q ≤ P ∧ a < q ∧ Nat.Coprime a q at hqa
  change 0 < q' ∧ q' ≤ P ∧ a' < q' ∧ Nat.Coprime a' q' at hqa'
  have hq : 0 < q := hqa.1
  have hq' : 0 < q' := hqa'.1
  have hqcast : (0 : ℝ) < q := by exact_mod_cast hq
  have hq'cast : (0 : ℝ) < q' := by exact_mod_cast hq'
  let n : ℤ := (a * q' : ℕ) - a' * q
  have hn : n ≠ 0 := by
    intro hn0
    have heq : a * q' = a' * q := by
      dsimp [n] at hn0
      exact_mod_cast (Int.sub_eq_zero.mp hn0)
    have hqq : q ∣ q' := by
      apply (hqa.2.2.2.symm).dvd_of_dvd_mul_left
      rw [heq]
      exact ⟨a', by ring⟩
    have hq'q : q' ∣ q := by
      apply (hqa'.2.2.2.symm).dvd_of_dvd_mul_left
      rw [← heq]
      exact ⟨a, by ring⟩
    have hqe : q = q' := Nat.dvd_antisymm hqq hq'q
    have hae : a = a' := by
      apply Nat.eq_of_mul_eq_mul_right hq
      simpa [hqe] using heq
    apply hne
    simp [hqe, hae]
  have hnD : |n| < (q * q' : ℕ) := by
    have hu : a * q' < q * q' :=
      Nat.mul_lt_mul_of_pos_right hqa.2.2.1 hq'
    have hu' : a' * q < q * q' :=
      (Nat.mul_lt_mul_of_pos_right hqa'.2.2.1 hq).trans_eq (by ring)
    have huI : (a * q' : ℤ) < (q * q' : ℤ) := by exact_mod_cast hu
    have hu'I : (a' * q : ℤ) < (q * q' : ℤ) := by exact_mod_cast hu'
    have hlow : -(q * q' : ℤ) < (a * q' : ℤ) - a' * q := by omega
    have huI' : (a * q' : ℤ) - a' * q < q * q' := by omega
    dsimp [n]
    rw [abs_lt]
    exact ⟨hlow, huI'⟩
  have hden : 0 < q * q' := Nat.mul_pos hq hq'
  have hmain :
      1 / ((q * q' : ℕ) : ℝ) ≤
        distInt ((a : ℝ) / q - (a' : ℝ) / q') := by
    have hh := distInt_ge_of_int_div hden hn hnD
    have hrat :
        (a : ℝ) / q - (a' : ℝ) / q' =
          (n : ℝ) / (q * q') := by
      dsimp [n]
      push_cast
      field_simp
    rw [hrat]
    simpa [Nat.cast_mul] using hh
  have hqqP : q * q' ≤ P ^ 2 := by
    calc
      q * q' ≤ P * P := Nat.mul_le_mul hqa.2.1 hqa'.2.1
      _ = P ^ 2 := by ring
  have hcast : (q * q' : ℝ) ≤ (P : ℝ) ^ 2 := by exact_mod_cast hqqP
  have hPpos : (0 : ℝ) < (P : ℝ) ^ 2 := by
    have : 0 < P := lt_of_lt_of_le hq hqa.2.1
    positivity
  calc
    1 / (P : ℝ) ^ 2 ≤ 1 / (q * q' : ℝ) :=
      one_div_le_one_div_of_le (by positivity) hcast
    _ ≤ distInt ((a : ℝ) / q - (a' : ℝ) / q') := by
      simpa [Nat.cast_mul] using hmain

namespace Ranges

variable (R : Ranges) (X : ℝ) (P : ℕ)

/-- The half-width `J₀ = ⌊2 P Q / X⌋₊` of the major arcs, in grid units. -/
noncomputable def halfWidth : ℕ := ⌊2 * P * (R.Q X P : ℝ) / X⌋₊

theorem halfWidth_div_Q_le (hX : 0 < X) : (R.halfWidth X P : ℝ) / R.Q X P ≤ 2 * P / X := by
  have hQ : 0 < (R.Q X P : ℝ) := by exact_mod_cast R.Q_pos X P
  have hfloor : (R.halfWidth X P : ℝ) ≤ 2 * P * R.Q X P / X := by
    unfold halfWidth
    exact Nat.floor_le (by positivity)
  rw [div_le_iff₀ hQ]
  calc
    (R.halfWidth X P : ℝ) ≤ 2 * P * R.Q X P / X := hfloor
    _ = (2 * P / X) * R.Q X P := by ring

theorem le_halfWidth_div_Q (hX : 0 < X) (hPQ : X ≤ P * R.Q X P) :
    (P : ℝ) / X ≤ (R.halfWidth X P : ℝ) / R.Q X P := by
  have hQ : 0 < (R.Q X P : ℝ) := by exact_mod_cast R.Q_pos X P
  have hfloor :
      2 * P * R.Q X P / X < (R.halfWidth X P : ℝ) + 1 := by
    unfold halfWidth
    exact_mod_cast Nat.lt_floor_add_one (2 * P * R.Q X P / X)
  have hPQ' : (1 : ℝ) ≤ P * R.Q X P / X := by
    rw [le_div_iff₀ hX]
    have : (1 : ℝ) * X ≤ P * R.Q X P := by simpa using hPQ
    exact this
  have hrel : P * R.Q X P / X ≤ R.halfWidth X P := by
    have haux : P * R.Q X P / X ≤ 2 * P * R.Q X P / X - 1 := by
      have hrewrite : 2 * P * R.Q X P / X = 2 * (P * R.Q X P / X) := by
        ring
      rw [hrewrite]
      linarith
    linarith
  rw [le_div_iff₀ hQ]
  calc
    P / X * R.Q X P = P * R.Q X P / X := by ring
    _ ≤ R.halfWidth X P := hrel

theorem two_mul_halfWidth_add_one_le (hX : 0 < X) (hPQ : X ≤ P * R.Q X P) :
    (2 * R.halfWidth X P + 1 : ℝ) ≤ 5 * P * R.Q X P / X := by
  have hQ : 0 < (R.Q X P : ℝ) := by exact_mod_cast R.Q_pos X P
  have hfloor : (R.halfWidth X P : ℝ) ≤ 2 * P * R.Q X P / X := by
    unfold halfWidth
    exact Nat.floor_le (by positivity)
  have hPQ' : (1 : ℝ) ≤ P * R.Q X P / X := by
    rw [le_div_iff₀ hX]
    have : (1 : ℝ) * X ≤ P * R.Q X P := by simpa using hPQ
    exact this
  have hrewrite : 2 * P * R.Q X P / X = 2 * (P * R.Q X P / X) := by
    ring
  have hrewrite5 : 5 * P * R.Q X P / X = 5 * (P * R.Q X P / X) := by
    ring
  rw [hrewrite] at hfloor
  rw [hrewrite5]
  linarith

/-- The angle `a / q + j / Q` on the major arc `(q, a)`. -/
noncomputable def arcAngle (qa : ℕ × ℕ) (j : ℤ) : ℝ := (qa.2 : ℝ) / qa.1 + j / R.Q X P

/-- `k / Q` lies on a major arc. -/
def IsMajor (k : ℕ) : Prop :=
  ∃ qa ∈ arcIndex P, distInt ((k : ℝ) / R.Q X P - qa.2 / qa.1) ≤ R.halfWidth X P / R.Q X P

open Classical in
/-- The minor-arc frequencies `k < Q`. -/
noncomputable def minorSet : Finset ℕ := {k ∈ range (R.Q X P) | ¬ R.IsMajor X P k}

theorem mem_minorSet {k : ℕ} : k ∈ R.minorSet X P ↔ k < R.Q X P ∧ ¬ R.IsMajor X P k := by
  simp [minorSet, Finset.mem_filter, Finset.mem_range]

/-- The grid index `(a · (Q / q) + j) mod Q` of the arc point `a / q + j / Q`. -/
noncomputable def arcGrid (qa : ℕ × ℕ) (j : ℤ) : ℕ :=
  ((((qa.2 * (R.Q X P / qa.1) : ℕ) : ℤ) + j) % (R.Q X P : ℤ)).toNat

theorem arcGrid_lt (qa : ℕ × ℕ) (j : ℤ) : R.arcGrid X P qa j < R.Q X P := by
  unfold arcGrid
  rw [Int.toNat_lt (Int.emod_nonneg _ (by
    have : 0 < R.Q X P := R.Q_pos X P
    omega))]
  exact Int.emod_lt_of_pos _ (by exact_mod_cast R.Q_pos X P)

/-- A `1`-periodic function is invariant under all integer shifts. -/
theorem periodic_add_intCast {F : ℝ → ℂ} (hF : ∀ θ, F (θ + 1) = F θ) (θ : ℝ) (n : ℤ) :
    F (θ + n) = F θ := by
  have hp : Function.Periodic F 1 := hF
  simpa using (hp.int_mul n θ)

/-- The arc point `a / q + j / Q` differs from its grid point `arcGrid / Q` by an integer. -/
theorem arcAngle_eq_arcGrid_div_add {qa : ℕ × ℕ} (hqa : qa ∈ arcIndex P) (j : ℤ) :
    ∃ n : ℤ, R.arcAngle X P qa j = R.arcGrid X P qa j / R.Q X P + n := by
  rcases qa with ⟨q, a⟩
  have hqa' := mem_arcIndex.mp hqa
  have hq : 0 < q := hqa'.1
  have hqP : q ≤ P := hqa'.2.1
  have hdvd : q ∣ R.Q X P := R.dvd_Q X P hq hqP
  let x : ℤ := (a * (R.Q X P / q) : ℕ) + j
  let n : ℤ := x / R.Q X P
  have hQ : (0 : ℤ) < R.Q X P := by exact_mod_cast R.Q_pos X P
  have hxnonneg : 0 ≤ x % (R.Q X P : ℤ) :=
    Int.emod_nonneg _ (ne_of_gt hQ)
  have htoNat :
      ((x % (R.Q X P : ℤ)).toNat : ℝ) =
        ((x % (R.Q X P : ℤ) : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hxnonneg]
  have hmul : q * (R.Q X P / q) = R.Q X P := Nat.mul_div_cancel' hdvd
  have hdivR :
      ((R.Q X P / q : ℕ) : ℝ) = (R.Q X P : ℝ) / q := by
    rw [Nat.cast_div hdvd (by exact_mod_cast hq.ne')]
  have hfrac :
      (a : ℝ) / q = ((a * (R.Q X P / q) : ℕ) : ℝ) / R.Q X P := by
    have hmulR : (q : ℝ) * (R.Q X P / q) = R.Q X P := by
      exact_mod_cast hmul
    field_simp
    push_cast
    rw [hdivR]
    field_simp [ne_of_gt (show (0 : ℝ) < R.Q X P by exact_mod_cast R.Q_pos X P)]
  refine ⟨n, ?_⟩
  unfold arcAngle
  change (a : ℝ) / q + (j : ℝ) / R.Q X P =
    (((x % (R.Q X P : ℤ)).toNat : ℕ) : ℝ) / R.Q X P + n
  rw [htoNat, hfrac]
  have he := Int.emod_add_mul_ediv x (R.Q X P : ℤ)
  have her :
      ((x % (R.Q X P : ℤ) : ℤ) : ℝ) +
          (R.Q X P : ℝ) * ((x / (R.Q X P : ℤ) : ℤ) : ℝ) = x := by
    exact_mod_cast he
  rw [← add_div]
  apply (div_eq_iff (show (R.Q X P : ℝ) ≠ 0 by
    exact_mod_cast (ne_of_gt (R.Q_pos X P)))).2
  dsimp [n]
  rw [add_mul]
  have hmod :
      ((x % (R.Q X P : ℤ) : ℤ) : ℝ) / R.Q X P * (R.Q X P : ℝ) =
        ((x % (R.Q X P : ℤ) : ℤ) : ℝ) := by
    field_simp [ne_of_gt (show (0 : ℝ) < R.Q X P by exact_mod_cast R.Q_pos X P)]
  rw [hmod]
  rw [mul_comm ((x / (R.Q X P : ℤ) : ℤ) : ℝ) (R.Q X P : ℝ)]
  have hxcast :
      ((a * (R.Q X P / q) : ℕ) : ℝ) + (j : ℝ) = (x : ℝ) := by
    have hprod :
        ((a * (R.Q X P / q) : ℕ) : ℝ) =
          (a : ℝ) * ((R.Q X P : ℝ) / q) := by
      rw [Nat.cast_mul, hdivR]
    dsimp [x]
    change ((a * (R.Q X P / q) : ℕ) : ℝ) + (j : ℝ) =
      ((((a * (R.Q X P / q) : ℕ) : ℤ) + j : ℤ) : ℝ)
    rw [Int.cast_add, Int.cast_natCast]
  rw [hxcast]
  exact her.symm

/-- Grid points of the arc `(q, a)` with `|j| ≤ J₀` are major. -/
theorem isMajor_arcGrid {qa : ℕ × ℕ} (hqa : qa ∈ arcIndex P) {j : ℤ}
    (hj : |j| ≤ R.halfWidth X P) : R.IsMajor X P (R.arcGrid X P qa j) := by
  refine ⟨qa, hqa, ?_⟩
  obtain ⟨n, hn⟩ := R.arcAngle_eq_arcGrid_div_add X P hqa j
  have heq :
      (R.arcGrid X P qa j : ℝ) / R.Q X P - qa.2 / qa.1 =
        (j : ℝ) / R.Q X P - n := by
    dsimp [arcAngle] at hn
    linarith
  rw [heq, sub_eq_add_neg, ← Int.cast_neg, distInt_add_intCast]
  calc
    distInt ((j : ℝ) / R.Q X P) ≤ |(j : ℝ) / R.Q X P| :=
      distInt_le_abs _
    _ = |j| / R.Q X P := by
      have hQ : (0 : ℝ) < R.Q X P := by exact_mod_cast R.Q_pos X P
      rw [abs_div, abs_of_pos hQ, Int.cast_abs]
    _ ≤ R.halfWidth X P / R.Q X P := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast hj

/-- Distinct arc parameters give distinct grid points (the arcs are disjoint and do not wrap). -/
theorem arcGrid_injective (hP : 1 ≤ P) (hX : 8 * (P : ℝ) ^ 3 ≤ X)
    {qa qa' : ℕ × ℕ} (hqa : qa ∈ arcIndex P) (hqa' : qa' ∈ arcIndex P) {j j' : ℤ}
    (hj : |j| ≤ R.halfWidth X P) (hj' : |j'| ≤ R.halfWidth X P)
    (h : R.arcGrid X P qa j = R.arcGrid X P qa' j') : qa = qa' ∧ j = j' := by
  have hP0 : 0 < P := lt_of_lt_of_le Nat.zero_lt_one hP
  have hX0 : 0 < X := by
    have : (0 : ℝ) < 8 * (P : ℝ) ^ 3 := by positivity
    exact this.trans_le hX
  have hQ : (0 : ℝ) < R.Q X P := by exact_mod_cast R.Q_pos X P
  obtain ⟨n, hn⟩ := R.arcAngle_eq_arcGrid_div_add X P hqa j
  obtain ⟨n', hn'⟩ := R.arcAngle_eq_arcGrid_div_add X P hqa' j'
  rw [h] at hn
  have heq :
      R.arcAngle X P qa j - R.arcAngle X P qa' j' = (n - n' : ℤ) := by
    push_cast
    linarith
  have hJ : (R.halfWidth X P : ℝ) / R.Q X P ≤ 2 * P / X :=
    R.halfWidth_div_Q_le X P hX0
  have hjdiff : |((j - j' : ℤ) : ℝ)| ≤ 2 * R.halfWidth X P := by
    rw [Int.cast_sub]
    calc
      |(j : ℝ) - j'| = |(j : ℝ) + -(j' : ℝ)| := by rw [sub_eq_add_neg]
      _ ≤ |(j : ℝ)| + |-(j' : ℝ)| := abs_add_le _ _
      _ = |(j : ℝ)| + |(j' : ℝ)| := by rw [abs_neg]
      _ = (|j| : ℤ) + |j'| := by rw [← Int.cast_abs, ← Int.cast_abs]
      _ ≤ 2 * R.halfWidth X P := by exact_mod_cast (by omega : |j| + |j'| ≤ 2 * R.halfWidth X P)
  have hsmall : |((j - j' : ℤ) : ℝ)| / R.Q X P < 1 / (P : ℝ) ^ 2 := by
    calc
      |((j - j' : ℤ) : ℝ)| / R.Q X P ≤
          (2 * R.halfWidth X P : ℝ) / R.Q X P :=
        div_le_div_of_nonneg_right hjdiff (le_of_lt hQ)
      _ = 2 * ((R.halfWidth X P : ℝ) / R.Q X P) := by ring
      _ ≤ 2 * (2 * P / X) := mul_le_mul_of_nonneg_left hJ (by positivity)
      _ < 1 / (P : ℝ) ^ 2 := by
        have hP' : (0 : ℝ) < P := by exact_mod_cast hP0
        calc
          2 * (2 * P / X) ≤ 2 * (2 * P / (8 * P ^ 3)) :=
            mul_le_mul_of_nonneg_left
              (div_le_div_of_nonneg_left (by positivity) (by positivity) hX)
              (by positivity)
          _ < 1 / (P : ℝ) ^ 2 := by field_simp; nlinarith
  have hqa_eq : qa = qa' := by
    by_contra hne
    have hsep := le_distInt_sub_of_ne hqa hqa' hne
    have hrel :
        (qa.2 : ℝ) / qa.1 - qa'.2 / qa'.1 =
          -((j - j' : ℤ) : ℝ) / R.Q X P + (n - n' : ℤ) := by
      dsimp [arcAngle] at heq
      have hcast : ((j - j' : ℤ) : ℝ) = (j : ℝ) - j' := by
        push_cast
        rfl
      calc
        (qa.2 : ℝ) / qa.1 - qa'.2 / qa'.1 =
            (n - n' : ℤ) - ((j : ℝ) / R.Q X P - j' / R.Q X P) := by
          linarith [heq]
        _ = -((j - j' : ℤ) : ℝ) / R.Q X P + (n - n' : ℤ) := by
          rw [hcast]
          ring
    have hnear :
        distInt ((qa.2 : ℝ) / qa.1 - qa'.2 / qa'.1) <
          1 / (P : ℝ) ^ 2 := by
      rw [hrel, distInt_add_intCast]
      rw [neg_div, distInt_neg]
      calc
        distInt (((j - j' : ℤ) : ℝ) / R.Q X P) ≤
            |((j - j' : ℤ) : ℝ) / R.Q X P| := distInt_le_abs _
        _ = |((j - j' : ℤ) : ℝ)| / R.Q X P := by
          rw [abs_div, abs_of_pos hQ]
        _ < 1 / (P : ℝ) ^ 2 := hsmall
    exact (not_lt_of_ge hsep) hnear
  subst qa'
  have hjint : j - j' = R.Q X P * (n - n') := by
    dsimp [arcAngle] at heq
    have hdiv : (j : ℝ) / R.Q X P - j' / R.Q X P = (n - n' : ℤ) := by
      ring_nf at heq ⊢
      linarith [heq]
    have hreal : ((j - j' : ℤ) : ℝ) =
        R.Q X P * ((n - n' : ℤ) : ℝ) := by
      rw [Int.cast_sub]
      field_simp [ne_of_gt hQ] at hdiv ⊢
      linarith [hdiv]
    exact_mod_cast hreal
  have hdiv : (R.Q X P : ℤ) ∣ j - j' := ⟨n - n', hjint⟩
  have hwidth : (2 * R.halfWidth X P : ℤ) < R.Q X P := by
    have hfloor : (R.halfWidth X P : ℝ) ≤ 2 * P * R.Q X P / X := by
      unfold halfWidth
      exact Nat.floor_le (by positivity)
    have h8 : (8 : ℝ) * P ≤ X := by
      calc
        (8 : ℝ) * P ≤ 8 * P ^ 3 := by
          have hP' : (1 : ℝ) ≤ P := by exact_mod_cast hP
          nlinarith
        _ ≤ X := hX
    have hbound : (2 * R.halfWidth X P : ℝ) < R.Q X P := by
      calc
        (2 * R.halfWidth X P : ℝ) ≤ 4 * P * R.Q X P / X := by
          calc
            (2 * R.halfWidth X P : ℝ) ≤ 2 * (2 * P * R.Q X P / X) :=
              mul_le_mul_of_nonneg_left hfloor (by positivity)
            _ = 4 * P * R.Q X P / X := by ring
        _ ≤ R.Q X P / 2 := by
          apply (div_le_iff₀ hX0).2
          nlinarith [h8]
        _ < R.Q X P := by linarith
    exact_mod_cast hbound
  have hjlt : |j - j'| < R.Q X P := by
    apply lt_of_le_of_lt _ hwidth
    calc
      |j - j'| = |j + -j'| := by ring_nf
      _ ≤ |j| + |-j'| := abs_add_le _ _
      _ = |j| + |j'| := by rw [abs_neg]
      _ ≤ 2 * R.halfWidth X P := by omega
  have hz : j - j' = 0 := Int.eq_zero_of_abs_lt_dvd hdiv hjlt
  exact ⟨rfl, by omega⟩

/-- Every major frequency `k < Q` is a grid point of some arc with `|j| ≤ J₀`. -/
theorem exists_arcGrid_eq {k : ℕ} (hk : k < R.Q X P) (hmaj : R.IsMajor X P k) :
    ∃ qa ∈ arcIndex P, ∃ j : ℤ, |j| ≤ R.halfWidth X P ∧ R.arcGrid X P qa j = k := by
  obtain ⟨⟨q, a⟩, hqa, hdist⟩ := hmaj
  have hqa' := mem_arcIndex.mp hqa
  have hq : 0 < q := hqa'.1
  have hqP : q ≤ P := hqa'.2.1
  have hdvd : q ∣ R.Q X P := R.dvd_Q X P hq hqP
  let g : ℕ := a * (R.Q X P / q)
  let t : ℤ := (k : ℤ) - g
  let r : ℤ := round ((t : ℝ) / R.Q X P)
  let j : ℤ := t - R.Q X P * r
  refine ⟨(q, a), hqa, j, ?_, ?_⟩
  · have hQ : (0 : ℝ) < R.Q X P := by exact_mod_cast R.Q_pos X P
    have hmul : q * (R.Q X P / q) = R.Q X P := Nat.mul_div_cancel' hdvd
    have hdivR :
        ((R.Q X P / q : ℕ) : ℝ) = (R.Q X P : ℝ) / q := by
      rw [Nat.cast_div hdvd (by exact_mod_cast hq.ne')]
    have hfrac : (a : ℝ) / q = (g : ℝ) / R.Q X P := by
      have hmulR : (q : ℝ) * (R.Q X P / q) = R.Q X P := by
        exact_mod_cast hmul
      dsimp [g]
      field_simp
      push_cast
      rw [hdivR]
      field_simp [ne_of_gt hQ]
    have ht : (t : ℝ) / R.Q X P =
        (k : ℝ) / R.Q X P - (a : ℝ) / q := by
      dsimp [t]
      rw [Int.cast_sub, Int.cast_natCast]
      change ((k : ℝ) - (g : ℝ)) / R.Q X P =
        (k : ℝ) / R.Q X P - (a : ℝ) / q
      calc
        ((k : ℝ) - (g : ℝ)) / R.Q X P =
            (k : ℝ) / R.Q X P - (g : ℝ) / R.Q X P := by ring
        _ = (k : ℝ) / R.Q X P - (a : ℝ) / q := by rw [← hfrac]
    have hj : (j : ℝ) = R.Q X P * ((t : ℝ) / R.Q X P - r) := by
      dsimp [j]
      push_cast
      field_simp
    have hdist' : distInt ((t : ℝ) / R.Q X P) ≤
        R.halfWidth X P / R.Q X P := by
      rw [ht]
      exact hdist
    have hbound : |(j : ℝ)| ≤ R.halfWidth X P := by
      rw [hj, abs_mul, abs_of_pos hQ]
      change R.Q X P * distInt ((t : ℝ) / R.Q X P) ≤ R.halfWidth X P
      calc
        R.Q X P * distInt ((t : ℝ) / R.Q X P) ≤
            R.Q X P * (R.halfWidth X P / R.Q X P) :=
          mul_le_mul_of_nonneg_left hdist' (le_of_lt hQ)
        _ = R.halfWidth X P := by field_simp
    exact_mod_cast hbound
  · unfold arcGrid
    change (((g : ℤ) + j) % (R.Q X P : ℤ)).toNat = k
    have hmod : ((g : ℤ) + j) % (R.Q X P : ℤ) = k := by
      dsimp [j, t]
      have heq : (g : ℤ) + ((k : ℤ) - g - R.Q X P * r) =
          (k : ℤ) - R.Q X P * r := by ring
      rw [heq]
      rw [Int.sub_mul_emod_self_left, Int.emod_eq_of_lt] <;> omega
    rw [hmod]
    rfl

/-- **Arc decomposition.** For a `1`-periodic `F`, the sum over the discrete circle splits into
the major arcs, parametrised by `(q, a) ∈ arcIndex P` and `|j| ≤ J₀`, and the minor arcs. -/
theorem sum_range_Q_eq (F : ℝ → ℂ) (hF : ∀ θ, F (θ + 1) = F θ) (hP : 1 ≤ P)
    (hX : 8 * (P : ℝ) ^ 3 ≤ X) :
    ∑ k ∈ range (R.Q X P), F (k / R.Q X P) =
      ∑ qa ∈ arcIndex P, ∑ j ∈ Icc (-(R.halfWidth X P : ℤ)) (R.halfWidth X P),
          F (R.arcAngle X P qa j) +
        ∑ k ∈ R.minorSet X P, F (k / R.Q X P) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (range (R.Q X P)) (R.IsMajor X P)]
  congr 1
  · rw [← Finset.sum_product']
    symm
    refine Finset.sum_nbij (fun p : (ℕ × ℕ) × ℤ => R.arcGrid X P p.1 p.2) ?_ ?_ ?_ ?_
    · intro p hp
      have hp' := Finset.mem_product.mp hp
      have hqa : p.1 ∈ arcIndex P := hp'.1
      have hj := Finset.mem_Icc.mp hp'.2
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (R.arcGrid_lt X P p.1 p.2),
        R.isMajor_arcGrid X P hqa (abs_le.mpr hj)⟩
    · intro p hp p' hp' heq
      have hp_mem := Finset.mem_product.mp hp
      have hp'_mem := Finset.mem_product.mp hp'
      obtain ⟨hqa, hj⟩ := hp_mem
      obtain ⟨hqa', hj'⟩ := hp'_mem
      have hboth := R.arcGrid_injective X P hP hX hqa hqa'
        (abs_le.mpr (Finset.mem_Icc.mp hj)) (abs_le.mpr (Finset.mem_Icc.mp hj')) heq
      exact Prod.ext hboth.1 hboth.2
    · intro k hk
      obtain ⟨hkQ, hkmaj⟩ := Finset.mem_filter.mp hk
      obtain ⟨qa, hqa, j, hj, hgrid⟩ :=
        R.exists_arcGrid_eq X P (Finset.mem_range.mp hkQ) hkmaj
      refine ⟨(qa, j), Finset.mem_product.mpr ⟨hqa, ?_⟩, hgrid⟩
      exact Finset.mem_Icc.mpr (abs_le.mp hj)
    · intro p hp
      obtain ⟨hqa, hj⟩ := Finset.mem_product.mp hp
      obtain ⟨n, hn⟩ := R.arcAngle_eq_arcGrid_div_add X P hqa p.2
      rw [hn, periodic_add_intCast hF]

/-- **Dirichlet approximation on the minor arcs.** A minor-arc frequency `k / Q` has a reduced
approximation `a / q` with `P < q ≤ X / P` and `|k / Q - a / q| ≤ 1 / q²`. -/
theorem exists_approx_of_mem_minorSet (hP : 1 ≤ P) (hXP : (P : ℝ) ≤ X) (hPQ : X ≤ P * R.Q X P)
    {k : ℕ} (hk : k ∈ R.minorSet X P) :
    ∃ q a : ℕ, P < q ∧ (q : ℝ) ≤ X / P ∧ Nat.Coprime a q ∧
      |(k : ℝ) / R.Q X P - a / q| ≤ 1 / (q : ℝ) ^ 2 := by
  have hPpos : 0 < P := lt_of_lt_of_le Nat.zero_lt_one hP
  have hXpos : 0 < X := lt_of_lt_of_le (by exact_mod_cast hPpos) hXP
  have hXP' : (1 : ℝ) ≤ X / P := by
    rw [le_div_iff₀ (by exact_mod_cast hPpos)]
    simpa using hXP
  have hnpos : 0 < ⌊X / P⌋₊ := Nat.floor_pos.mpr hXP'
  obtain ⟨r, hr, hrden⟩ :=
    Real.exists_rat_abs_sub_le_and_den_le ((k : ℝ) / R.Q X P) hnpos
  let n : ℕ := ⌊X / P⌋₊
  let q : ℕ := r.den
  have hqpos : 0 < q := r.den_pos
  have hnq : q ≤ n := hrden
  have hnle : (n : ℝ) ≤ X / P := by
    dsimp [n]
    exact Nat.floor_le (by positivity)
  have hnlt : X / P < (n : ℝ) + 1 := by
    dsimp [n]
    exact_mod_cast Nat.lt_floor_add_one (X / P)
  have hqn : (q : ℝ) ≤ n := by exact_mod_cast hnq
  have hqXP : (q : ℝ) ≤ X / P := hqn.trans hnle
  have hQpos : (0 : ℝ) < R.Q X P := by
    exact_mod_cast R.Q_pos X P
  have hkQ : k < R.Q X P := (mem_minorSet (R := R) (X := X) (P := P)).mp hk |>.1
  have htheta_nonneg : 0 ≤ (k : ℝ) / R.Q X P := by positivity
  have htheta_lt_one : (k : ℝ) / R.Q X P < 1 := by
    rw [div_lt_one hQpos]
    exact_mod_cast hkQ
  have hbound : |(k : ℝ) / R.Q X P - r| ≤
      1 / (((n : ℝ) + 1) * q) := by
    simpa [n, q, Nat.cast_add, Nat.cast_one, Nat.cast_mul] using hr
  have hrnum_nonneg : 0 ≤ r.num := by
    by_contra hneg
    have hnum : r.num ≤ -1 := by omega
    have hqreal : (0 : ℝ) < q := by exact_mod_cast hqpos
    have hrle : (r : ℝ) ≤ -1 / q := by
      rw [Rat.cast_def]
      exact (div_le_div_iff_of_pos_right hqreal).2 (by exact_mod_cast hnum)
    have hrle' : (r : ℝ) ≤ -(1 / q) := by
      convert hrle using 1
      ring
    have hlarge : 1 / (((n : ℝ) + 1) * q) <
        (k : ℝ) / R.Q X P - r := by
      have hnone : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
      have : 1 / (((n : ℝ) + 1) * q) ≤ 1 / (2 * q) := by
        apply one_div_le_one_div_of_le
        · positivity
        · nlinarith
      calc
        1 / (((n : ℝ) + 1) * q) ≤ 1 / (2 * q) := this
        _ < 1 / q := by
          calc
            1 / (2 * (q : ℝ)) = ((1 : ℝ) / 2) * (1 / q) := by ring
            _ < 1 * (1 / q) :=
              mul_lt_mul_of_pos_right (by norm_num) (one_div_pos.mpr hqreal)
            _ = 1 / (q : ℝ) := by ring
        _ ≤ (k : ℝ) / R.Q X P - r := by linarith
    exact (not_lt_of_ge hbound) (hlarge.trans_le (le_abs_self _))
  let a : ℕ := r.num.toNat
  have hnum : (a : ℤ) = r.num := by
    dsimp [a]
    exact Int.toNat_of_nonneg hrnum_nonneg
  have hra : (r : ℝ) = a / q := by
    rw [Rat.cast_def]
    rw [← hnum]
    rfl
  have hcop : Nat.Coprime a q := by
    have habs : r.num.natAbs = a := by
      dsimp [a]
      have hi : (r.num.natAbs : ℤ) = r.num := Int.natAbs_of_nonneg hrnum_nonneg
      omega
    simpa [a, q, habs] using r.reduced
  have hPq : P < q := by
    by_contra hnot
    have hqP : q ≤ P := by omega
    let a' : ℕ := a % q
    have ha'lt : a' < q := by
      dsimp [a']
      exact Nat.mod_lt _ hqpos
    have hcopa' : Nat.Coprime a' q := by
      rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec]
      simpa [a'] using hcop
    have harat : (a : ℝ) / q = (a' : ℝ) / q + (a / q : ℕ) := by
      have hdiv : q * (a / q) + a % q = a := Nat.div_add_mod a q
      dsimp [a']
      field_simp
      have hdiv' : (q : ℝ) * ((a / q : ℕ) : ℝ) + ((a % q : ℕ) : ℝ) = a := by
        exact_mod_cast hdiv
      linarith
    have hdist : distInt ((k : ℝ) / R.Q X P - a' / q) =
        distInt ((k : ℝ) / R.Q X P - a / q) := by
      have heq : (k : ℝ) / R.Q X P - a' / q =
          ((k : ℝ) / R.Q X P - a / q) + (a / q : ℕ) := by
        linarith [harat]
      calc
        distInt ((k : ℝ) / R.Q X P - a' / q) =
            distInt (((k : ℝ) / R.Q X P - a / q) + (a / q : ℤ)) := by
              rw [heq]
              norm_cast
        _ = distInt ((k : ℝ) / R.Q X P - a / q) :=
          distInt_add_intCast _ (a / q : ℤ)
    have hsmall : distInt ((k : ℝ) / R.Q X P - a' / q) ≤
        R.halfWidth X P / R.Q X P := by
      rw [hdist]
      exact le_of_lt <| calc
        distInt ((k : ℝ) / R.Q X P - a / q) ≤
            |(k : ℝ) / R.Q X P - a / q| := distInt_le_abs _
        _ = |(k : ℝ) / R.Q X P - r| := by rw [hra]
        _ ≤ 1 / (((n : ℝ) + 1) * q) := hbound
        _ ≤ 1 / ((n : ℝ) + 1) := by
          have hnn : 0 < (n : ℝ) + 1 := by positivity
          apply one_div_le_one_div_of_le
          · exact hnn
          · nlinarith [show (1 : ℝ) ≤ q by exact_mod_cast hqpos]
        _ < P / X := by
          have hP : (0 : ℝ) < P := by exact_mod_cast hPpos
          have hdiv : 1 / (X / P) = P / X := by field_simp
          rw [← hdiv]
          exact one_div_lt_one_div_of_lt (div_pos hXpos hP) hnlt
        _ ≤ R.halfWidth X P / R.Q X P := R.le_halfWidth_div_Q X P hXpos hPQ
    have hmajor : R.IsMajor X P k := by
      refine ⟨(q, a'), mem_arcIndex.mpr ⟨hqpos, hqP, ha'lt, hcopa'⟩, hsmall⟩
    exact (mem_minorSet (R := R) (X := X) (P := P)).mp hk |>.2 hmajor
  refine ⟨q, a, hPq, hqXP, hcop, ?_⟩
  rw [← hra]
  calc
    |(k : ℝ) / R.Q X P - r| ≤ 1 / (((n : ℝ) + 1) * q) := hbound
    _ ≤ 1 / (q : ℝ) ^ 2 := by
      apply one_div_le_one_div_of_le
      · positivity
      · rw [pow_two]
        nlinarith [show (q : ℝ) ≤ n by exact_mod_cast hnq]

end Ranges

end CircleMethod
