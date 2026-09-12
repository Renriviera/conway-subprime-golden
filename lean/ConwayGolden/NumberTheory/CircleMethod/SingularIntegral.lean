/-
Copyright (c) 2026 Romain Popescu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Romain Popescu
-/
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.Harmonic.Bounds
import ConwayGolden.NumberTheory.CircleMethod.Arcs

/-!
# The discrete singular integral

Because every `a / q` with `q ≤ P` is a grid point of the discrete circle, the "singular
integral" attached to each major arc is the same sum

`W(N) = Q⁻¹ ∑_{|j| ≤ J₀} TI(j / Q) TJ(j / Q) e (-N j / Q)`,

independent of `(q, a)`. Completing the sum over all `j < Q` gives exactly the lattice count
`count N = #{(m, n) ∈ I × J : ν m + n = N}` by Fourier inversion, and the completed part is
small by the geometric-series bounds for `TI` and `TJ`.

## Main definitions

* `Ranges.singularIntegral R X P N`: the sum `W(N)` above.

## Main statements

* `Ranges.norm_singularIntegral_sub_count_le`: `‖W(N) - count N‖ ≤ 2 X / P + 4 (log Q + 2)`.

## Implementation notes

For `ν = 2` the bound `‖TI(j/Q)‖ ≤ 1 / (2 ‖2 j / Q‖)` degenerates near `j = Q / 2`; there the
trivial bound `‖TI‖ ≤ #I` is used instead, which is the source of the `log Q` term. Since
`log Q ≪ P log P` this is negligible against `X / P`.
-/

namespace CircleMethod

namespace Ranges

open Finset Real

variable (R : Ranges) (X : ℝ) (P : ℕ)

/-- The discrete singular integral `W(N) = Q⁻¹ ∑_{|j| ≤ J₀} TI(j/Q) TJ(j/Q) e (-N j / Q)`. -/
noncomputable def singularIntegral (N : ℕ) : ℂ :=
  (1 / (R.Q X P : ℂ)) * ∑ j ∈ Icc (-(R.halfWidth X P : ℤ)) (R.halfWidth X P),
    R.TI X (j / R.Q X P) * R.TJ X (j / R.Q X P) * e (-(N * j / R.Q X P))

/-- The completed sum over the whole circle is the lattice count. -/
theorem sum_TI_mul_TJ_eq_count (hX : 0 ≤ X) {N : ℕ} (hN : (N : ℝ) ≤ R.B * X) :
    (1 / (R.Q X P : ℂ)) * ∑ j ∈ range (R.Q X P),
      R.TI X (j / R.Q X P) * R.TJ X (j / R.Q X P) * e (-(N * j / R.Q X P)) = R.count X N :=
  R.count_eq_sum X P hX hN |>.symm

/-! ### The far grid points -/

/-- The grid indices `J₀ < k < Q - J₀` outside the central arc. -/
noncomputable def farSet : Finset ℕ :=
  {k ∈ range (R.Q X P) | R.halfWidth X P < k ∧ k + R.halfWidth X P < R.Q X P}

theorem mem_farSet {k : ℕ} :
    k ∈ R.farSet X P ↔ R.halfWidth X P < k ∧ k + R.halfWidth X P < R.Q X P := by
  simp only [farSet, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · rintro ⟨h1, h2⟩
    exact ⟨by omega, h1, h2⟩

/-- `J₀ ≤ Q / 4` once `8 P³ ≤ X`. -/
theorem four_mul_halfWidth_le (hP : 1 ≤ P) (hX : 8 * (P : ℝ) ^ 3 ≤ X) :
    4 * (R.halfWidth X P : ℝ) ≤ R.Q X P := by
  have hX0 : 0 < X := by
    have hP0 : (0 : ℝ) < P := by exact_mod_cast Nat.zero_lt_of_lt hP
    have hP3 : 0 < (P : ℝ) ^ 3 := by positivity
    nlinarith
  have h8P : (8 : ℝ) * P ≤ X := by
    have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast hP
    have hpow : (P : ℝ) ≤ P ^ 3 := by
      nlinarith [sq_nonneg ((P : ℝ) - 1)]
    nlinarith
  have hfloor := Nat.floor_le (show 0 ≤ (2 * (P : ℝ) * R.Q X P) / X by positivity)
  have hmain : 4 * ((2 * (P : ℝ) * R.Q X P) / X) ≤ R.Q X P := by
    have hQ : (0 : ℝ) ≤ R.Q X P := by positivity
    rw [show 4 * (2 * (P : ℝ) * R.Q X P / X) =
      (8 * (P : ℝ) * R.Q X P) / X by ring]
    apply (div_le_iff₀ hX0).2
    nlinarith
  exact (mul_le_mul_of_nonneg_left hfloor (by norm_num)).trans hmain

/-- `J₀ ≥ 1` once `X ≤ P Q`. -/
theorem one_le_halfWidth (hX : 0 < X) (hPQ : X ≤ P * R.Q X P) : 1 ≤ R.halfWidth X P := by
  apply Nat.le_floor
  rw [Nat.cast_one]
  apply (le_div_iff₀ hX).2
  have hP : (0 : ℝ) ≤ P := by positivity
  nlinarith

/-- A `1`-periodic function summed over the central arc and the far set exhausts one period. -/
theorem sum_Icc_halfWidth_add_sum_farSet (F : ℝ → ℂ) (hF : ∀ θ, F (θ + 1) = F θ)
    (hJ : 2 * R.halfWidth X P < R.Q X P) :
    ∑ j ∈ Icc (-(R.halfWidth X P : ℤ)) (R.halfWidth X P), F (j / R.Q X P) +
      ∑ k ∈ R.farSet X P, F (k / R.Q X P) = ∑ k ∈ range (R.Q X P), F (k / R.Q X P) := by
  classical
  let J := R.halfWidth X P
  let Q := R.Q X P
  let g : ℤ → ℕ := fun j => (j % (Q : ℤ)).toNat
  have hQ : 0 < Q := R.Q_pos X P
  have hQz : (0 : ℤ) < Q := by exact_mod_cast hQ
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hJz : (2 * (J : ℤ)) < Q := by
    exact_mod_cast hJ
  have hg_lt (j : ℤ) : g j < Q := by
    dsimp [g]
    rw [Int.toNat_lt (Int.emod_nonneg _ hQz.ne')]
    exact Int.emod_lt_of_pos _ hQz
  have hg_cast (j : ℤ) : (g j : ℤ) = j % Q := by
    dsimp [g]
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hQz.ne')]
  have hg_eq (j : ℤ) :
      (g j : ℝ) / Q = j / Q + ((-(j / Q : ℤ) : ℤ) : ℝ) := by
    rw [show ((g j : ℕ) : ℝ) = ((j % Q : ℤ) : ℝ) by
      rw [← Int.cast_natCast, hg_cast]]
    rw [Int.emod_def]
    push_cast
    field_simp
    ring
  have hFg (j : ℤ) : F (j / Q) = F (g j / Q) := by
    rw [hg_eq, periodic_add_intCast hF]
  have hinj : Set.InjOn g (↑(Icc (-(J : ℤ)) J) : Set ℤ) := by
    intro j hj j' hj' heq
    have hmod : j % Q = j' % Q := by
      rw [← hg_cast j, ← hg_cast j', heq]
    have hdvd : (Q : ℤ) ∣ j - j' := by
      rw [Int.dvd_iff_emod_eq_zero, ← Int.emod_eq_emod_iff_emod_sub_eq_zero]
      exact hmod
    have hjmem := Finset.mem_Icc.mp hj
    have hj'mem := Finset.mem_Icc.mp hj'
    have habs : |j - j'| < Q := by
      have hle : |j - j'| ≤ 2 * J := by
        rw [abs_le]
        constructor <;> omega
      exact hle.trans_lt hJz
    have hz := Int.eq_zero_of_abs_lt_dvd hdvd habs
    omega
  have himage : (Icc (-(J : ℤ)) J).image g = range Q \ R.farSet X P := by
    ext k
    simp only [Finset.mem_image, Finset.mem_sdiff, Finset.mem_range, mem_farSet]
    constructor
    · rintro ⟨j, hj, rfl⟩
      refine ⟨hg_lt j, ?_⟩
      rintro ⟨hleft, hright⟩
      have hj' := Finset.mem_Icc.mp hj
      have hmod := hg_cast j
      by_cases hj0 : 0 ≤ j
      · have hjQ : j < Q := by omega
        have he : j % Q = j := Int.emod_eq_of_lt hj0 hjQ
        have : (g j : ℤ) = j := by rw [hg_cast, he]
        omega
      · have hjneg : j < 0 := lt_of_not_ge hj0
        have hjQ : 0 ≤ j + Q := by omega
        have hjQlt : j + Q < Q := by omega
        have he : j % Q = j + Q := by
          calc
            j % Q = (j + Q * 1) % Q := (Int.add_mul_emod_self_left j Q 1).symm
            _ = (j + Q) % Q := by ring
            _ = j + Q := Int.emod_eq_of_lt hjQ hjQlt
        have : (g j : ℤ) = j + Q := by rw [hg_cast, he]
        omega
    · rintro ⟨hkQ, hkfar⟩
      by_cases hkJ : k ≤ J
      · refine ⟨k, Finset.mem_Icc.mpr ?_, ?_⟩
        · constructor <;> omega
        · dsimp [g]
          rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast hkQ)]
          simp
      · have hkJ' : Q ≤ k + J := by
          by_contra h
          apply hkfar
          constructor <;> omega
        refine ⟨(k : ℤ) - Q, Finset.mem_Icc.mpr ?_, ?_⟩
        · constructor <;> omega
        · dsimp [g]
          have he : ((k : ℤ) - (Q : ℤ)) % (Q : ℤ) = (k : ℤ) := by
            calc
              ((k : ℤ) - (Q : ℤ)) % (Q : ℤ) = (k : ℤ) % (Q : ℤ) := by
                simp only [Int.sub_emod, Int.emod_self, sub_zero, Int.emod_emod]
              _ = k := Int.emod_eq_of_lt (by omega) (by exact_mod_cast hkQ)
          rw [he]
          rfl
  have hsub : R.farSet X P ⊆ range Q := by
    intro k hk
    apply Finset.mem_range.mpr
    have hk' := (R.mem_farSet X P).mp hk
    omega
  rw [show Icc (-(R.halfWidth X P : ℤ)) (R.halfWidth X P) = Icc (-(J : ℤ)) J by rfl]
  rw [Finset.sum_congr rfl fun j _ => hFg j]
  have hsum : ∑ k ∈ (Icc (-(J : ℤ)) J).image g, F (k / Q) =
      ∑ j ∈ Icc (-(J : ℤ)) J, F (g j / Q) := Finset.sum_image hinj
  rw [← hsum, himage]
  exact Finset.sum_sdiff hsub

/-- The singular integral differs from the lattice count by the far-set sum. -/
theorem singularIntegral_sub_count_eq (hX : 0 ≤ X) (hJ : 2 * R.halfWidth X P < R.Q X P)
    {N : ℕ} (hN : (N : ℝ) ≤ R.B * X) :
    R.singularIntegral X P N - R.count X N = -((1 / (R.Q X P : ℂ)) * ∑ k ∈ R.farSet X P,
      R.TI X (k / R.Q X P) * R.TJ X (k / R.Q X P) * e (-(N * k / R.Q X P))) := by
  rw [← R.sum_TI_mul_TJ_eq_count X P hX hN]
  unfold singularIntegral
  let F : ℝ → ℂ := fun θ => R.TI X θ * R.TJ X θ * e (-(N * θ))
  have hTI (θ : ℝ) : R.TI X (θ + 1) = R.TI X θ := by
    unfold TI
    apply Finset.sum_congr rfl
    intro m hm
    rw [show (R.ν : ℝ) * m * (θ + 1) =
      R.ν * m * θ + ((R.ν * m : ℕ) : ℤ) by
        push_cast
        ring, e_add_intCast]
  have hTJ (θ : ℝ) : R.TJ X (θ + 1) = R.TJ X θ := by
    unfold TJ
    apply Finset.sum_congr rfl
    intro n hn
    rw [show (n : ℝ) * (θ + 1) = n * θ + (n : ℤ) by
      push_cast
      ring, e_add_intCast]
  have hF : ∀ θ, F (θ + 1) = F θ := by
    intro θ
    dsimp [F]
    rw [hTI, hTJ, show -(N * (θ + 1)) = -(N * θ) + ((-N : ℤ) : ℝ) by
      push_cast
      ring, e_add_intCast]
  have hkey := R.sum_Icc_halfWidth_add_sum_farSet X P F hF hJ
  have hIcc :
      ∑ j ∈ Icc (-(R.halfWidth X P : ℤ)) (R.halfWidth X P),
        R.TI X (j / R.Q X P) * R.TJ X (j / R.Q X P) *
          e (-(N * j / R.Q X P)) =
        ∑ j ∈ Icc (-(R.halfWidth X P : ℤ)) (R.halfWidth X P), F (j / R.Q X P) := by
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [F]
    congr 2
    ring
  have hfar :
      ∑ k ∈ R.farSet X P,
        R.TI X (k / R.Q X P) * R.TJ X (k / R.Q X P) *
          e (-(N * k / R.Q X P)) =
        ∑ k ∈ R.farSet X P, F (k / R.Q X P) := by
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [F]
    congr 2
    ring
  have hrange :
      ∑ k ∈ range (R.Q X P),
        R.TI X (k / R.Q X P) * R.TJ X (k / R.Q X P) *
          e (-(N * k / R.Q X P)) =
        ∑ k ∈ range (R.Q X P), F (k / R.Q X P) := by
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [F]
    congr 2
    ring
  rw [hIcc, hfar, hrange, ← mul_sub, ← mul_neg]
  congr 1
  linear_combination hkey

/-! ### Pointwise bounds on the far set -/

/-- `‖k / Q‖ = min (k, Q - k) / Q` for `0 < k < Q`. -/
theorem distInt_div_eq_min {k : ℕ} (hk0 : 0 < k) (hkQ : k < R.Q X P) :
    distInt ((k : ℝ) / R.Q X P) = (min k (R.Q X P - k) : ℕ) / R.Q X P := by
  have hQ : 0 < R.Q X P := R.Q_pos X P
  have hQ' : (0 : ℝ) < R.Q X P := by exact_mod_cast hQ
  rcases le_or_gt (2 * k) (R.Q X P) with h | h
  · have hm : min k (R.Q X P - k) = k := by
      rw [min_eq_left]
      omega
    rw [hm]
    have hhalf : |(k : ℝ) / R.Q X P| ≤ 1 / 2 := by
      rw [abs_of_nonneg (by positivity)]
      apply (div_le_iff₀ hQ').2
      have h' : (2 : ℝ) * k ≤ R.Q X P := by exact_mod_cast h
      nlinarith
    rw [distInt_eq_abs_of_abs_le_half hhalf, abs_of_nonneg (by positivity)]
  · have hm : min k (R.Q X P - k) = R.Q X P - k := by
      rw [min_eq_right]
      omega
    rw [hm]
    have hrewrite :
        (k : ℝ) / R.Q X P =
          ((k : ℝ) / R.Q X P - 1) + ((1 : ℤ) : ℝ) := by norm_num
    rw [hrewrite, distInt_add_intCast]
    have hnonpos : (k : ℝ) / R.Q X P - 1 ≤ 0 := by
      apply sub_nonpos.mpr
      apply (div_le_iff₀ hQ').2
      have hkQ' : (k : ℝ) ≤ R.Q X P := by exact_mod_cast hkQ.le
      simpa using hkQ'
    have hhalf : |(k : ℝ) / R.Q X P - 1| ≤ 1 / 2 := by
      rw [abs_of_nonpos hnonpos]
      have hkQ' : (k : ℝ) < R.Q X P := by exact_mod_cast hkQ
      rw [show -((k : ℝ) / R.Q X P - 1) =
        (R.Q X P - k) / R.Q X P by field_simp; ring]
      apply (div_le_iff₀ hQ').2
      have h' : (R.Q X P : ℝ) < 2 * k := by exact_mod_cast h
      nlinarith
    rw [distInt_eq_abs_of_abs_le_half hhalf, abs_of_nonpos hnonpos]
    rw [Nat.cast_sub hkQ.le]
    field_simp
    ring

/-- `‖TJ (k / Q)‖ ≤ Q / (2 min (k, Q - k))` for `0 < k < Q`. -/
theorem norm_TJ_div_le {k : ℕ} (hk0 : 0 < k) (hkQ : k < R.Q X P) :
    ‖R.TJ X (k / R.Q X P)‖ ≤ R.Q X P / (2 * (min k (R.Q X P - k) : ℕ)) := by
  have hm : 0 < min k (R.Q X P - k) := by omega
  have hQ' : (0 : ℝ) < R.Q X P := by exact_mod_cast R.Q_pos X P
  have hdist : distInt ((k : ℝ) / R.Q X P) ≠ 0 := by
    rw [R.distInt_div_eq_min X P hk0 hkQ]
    exact ne_of_gt (div_pos (by exact_mod_cast hm) hQ')
  have h := R.norm_TJ_le_inv X (k / R.Q X P) hdist
  rw [R.distInt_div_eq_min X P hk0 hkQ] at h
  calc
    ‖R.TJ X (k / R.Q X P)‖ ≤ 1 / (2 * ((min k (R.Q X P - k) : ℕ) / R.Q X P)) := h
    _ = R.Q X P / (2 * (min k (R.Q X P - k) : ℕ)) := by
      field_simp

/-- `‖TI (k / Q)‖ ≤ Q / (2 min (k, Q - k))` for `0 < k < Q` with `4 min (k, Q - k) ≤ Q`. -/
private theorem distInt_two_mul_div_ge_min_pre {k Q : ℕ} (hQ : 0 < Q) (hk0 : 0 < k)
    (hkQ : k < Q) (h4 : 4 * min k (Q - k) ≤ Q) :
    ((min k (Q - k) : ℕ) : ℝ) / Q ≤ distInt (2 * ((k : ℝ) / Q)) := by
  rcases le_or_gt (2 * k) Q with h | h
  · have hm : min k (Q - k) = k := by rw [min_eq_left]; omega
    rw [hm] at h4 ⊢
    have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
    have hhalf : |2 * ((k : ℝ) / Q)| ≤ 1 / 2 := by
      rw [abs_of_nonneg (by positivity)]
      rw [show 2 * ((k : ℝ) / Q) = (2 * (k : ℝ)) / Q by ring]
      apply (div_le_iff₀ hQ').2
      have h' : (4 : ℝ) * k ≤ Q := by exact_mod_cast h4
      nlinarith
    rw [distInt_eq_abs_of_abs_le_half hhalf, abs_of_nonneg (by positivity)]
    have hkQ' : 0 ≤ (k : ℝ) / Q := by positivity
    nlinarith
  · have hm : min k (Q - k) = Q - k := by rw [min_eq_right]; omega
    rw [hm] at h4 ⊢
    have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
    have heq : 2 * ((k : ℝ) / Q) =
        -(2 * ((Q - k : ℕ) : ℝ) / Q) + ((2 : ℤ) : ℝ) := by
      push_cast
      rw [Nat.cast_sub hkQ.le]
      field_simp
      ring
    rw [heq, distInt_add_intCast, distInt_neg]
    have hhalf : |2 * ((Q - k : ℕ) : ℝ) / Q| ≤ 1 / 2 := by
      rw [abs_of_nonneg (by positivity)]
      apply (div_le_iff₀ hQ').2
      have h' : (4 : ℝ) * ((Q - k : ℕ) : ℝ) ≤ Q := by exact_mod_cast h4
      nlinarith
    rw [distInt_eq_abs_of_abs_le_half hhalf, abs_of_nonneg (by positivity)]
    have hkQ' : 0 ≤ ((Q - k : ℕ) : ℝ) / Q := by positivity
    have htwo := mul_le_mul_of_nonneg_right
      (show (1 : ℝ) ≤ 2 by norm_num) hkQ'
    simpa [mul_div_assoc] using htwo

theorem norm_TI_div_le_of_four_mul_le {k : ℕ} (hk0 : 0 < k) (hkQ : k < R.Q X P)
    (h4 : 4 * min k (R.Q X P - k) ≤ R.Q X P) :
    ‖R.TI X (k / R.Q X P)‖ ≤ R.Q X P / (2 * (min k (R.Q X P - k) : ℕ)) := by
  let m := min k (R.Q X P - k)
  have hm : 0 < m := by
    dsimp [m]
    omega
  have hQ : 0 < R.Q X P := R.Q_pos X P
  have hQ' : (0 : ℝ) < R.Q X P := by exact_mod_cast hQ
  rcases R.ν_eq with hν | hν
  · have hdist : distInt (R.ν * (k / R.Q X P)) ≠ 0 := by
      rw [hν, Nat.cast_one, one_mul, R.distInt_div_eq_min X P hk0 hkQ]
      exact ne_of_gt (div_pos (by exact_mod_cast hm) hQ')
    have h := R.norm_TI_le_inv X (k / R.Q X P) hdist
    rw [hν, Nat.cast_one, one_mul, R.distInt_div_eq_min X P hk0 hkQ] at h
    calc
      ‖R.TI X (k / R.Q X P)‖ ≤ 1 / (2 * ((m : ℕ) / R.Q X P)) := h
      _ = R.Q X P / (2 * (m : ℕ)) := by field_simp
  · have hge := distInt_two_mul_div_ge_min_pre hQ hk0 hkQ h4
    have hpos : 0 < ((m : ℕ) : ℝ) / R.Q X P := div_pos (by exact_mod_cast hm) hQ'
    have hdist : distInt (R.ν * (k / R.Q X P)) ≠ 0 := by
      rw [hν, Nat.cast_ofNat, show (2 : ℝ) * (k / R.Q X P) =
        2 * ((k : ℝ) / R.Q X P) by norm_num]
      exact ne_of_gt (lt_of_lt_of_le hpos hge)
    have h := R.norm_TI_le_inv X (k / R.Q X P) hdist
    rw [hν, Nat.cast_ofNat, show (2 : ℝ) * (k / R.Q X P) =
      2 * ((k : ℝ) / R.Q X P) by norm_num] at h
    calc
      ‖R.TI X (k / R.Q X P)‖ ≤ 1 / (2 * distInt (2 * ((k : ℝ) / R.Q X P))) := h
      _ ≤ 1 / (2 * ((m : ℕ) / R.Q X P)) := by
        apply one_div_le_one_div_of_le
        · positivity
        · linarith
      _ = R.Q X P / (2 * (m : ℕ)) := by field_simp

/-- `‖TI (k / Q)‖ ≤ Q / |2 k - Q|` for `Q < 4 min (k, Q - k)` and `2 k ≠ Q`. -/
private theorem distInt_two_mul_div_eq_D_pre {k Q : ℕ} (hQ : 0 < Q) (hkQ : k < Q)
    (h4 : Q < 4 * min k (Q - k)) :
    distInt (2 * ((k : ℝ) / Q)) =
      (((2 * k - Q) + (Q - 2 * k) : ℕ) : ℝ) / Q := by
  rcases le_or_gt (2 * k) Q with h | h
  · have hm : min k (Q - k) = k := by rw [min_eq_left]; omega
    rw [hm] at h4
    have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
    rw [show 2 * ((k : ℝ) / Q) =
      (2 * ((k : ℝ) / Q) - 1) + ((1 : ℤ) : ℝ) by norm_num,
      distInt_add_intCast]
    have hn : 2 * ((k : ℝ) / Q) - 1 ≤ 0 := by
      rw [sub_nonpos, show 2 * ((k : ℝ) / Q) = (2 * (k : ℝ)) / Q by ring]
      apply (div_le_iff₀ hQ').2
      have h' : (2 : ℝ) * k ≤ Q := by exact_mod_cast h
      nlinarith
    have hh : |2 * ((k : ℝ) / Q) - 1| ≤ 1 / 2 := by
      rw [abs_of_nonpos hn]
      rw [show -(2 * ((k : ℝ) / Q) - 1) = (Q - 2 * k) / Q by
        field_simp
        ring]
      apply (div_le_iff₀ hQ').2
      have h' : (Q : ℝ) < 4 * k := by exact_mod_cast h4
      nlinarith
    rw [distInt_eq_abs_of_abs_le_half hh, abs_of_nonpos hn]
    have hcast : ((Q - 2 * k : ℕ) : ℝ) = Q - 2 * k := by
      rw [Nat.cast_sub h]
      push_cast
      ring
    rw [show -(2 * ((k : ℝ) / Q) - 1) = ((Q - 2 * k : ℕ) : ℝ) / Q by
      rw [hcast]
      field_simp
      ring, Nat.sub_eq_zero_of_le h]
    simp
  · have hm : min k (Q - k) = Q - k := by rw [min_eq_right]; omega
    rw [hm] at h4
    have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
    rw [show 2 * ((k : ℝ) / Q) =
      (2 * ((k : ℝ) / Q) - 1) + ((1 : ℤ) : ℝ) by norm_num,
      distInt_add_intCast]
    have hn : 0 ≤ 2 * ((k : ℝ) / Q) - 1 := by
      rw [sub_nonneg, show 2 * ((k : ℝ) / Q) = (2 * (k : ℝ)) / Q by ring]
      apply (le_div_iff₀ hQ').2
      have h' : (Q : ℝ) ≤ 2 * k := by exact_mod_cast h.le
      nlinarith
    have hh : |2 * ((k : ℝ) / Q) - 1| ≤ 1 / 2 := by
      rw [abs_of_nonneg hn, show 2 * ((k : ℝ) / Q) - 1 =
        (2 * k - Q) / Q by field_simp]
      apply (div_le_iff₀ hQ').2
      have h' : (4 : ℝ) * ((Q - k : ℕ) : ℝ) > Q := by exact_mod_cast h4
      rw [Nat.cast_sub hkQ.le] at h'
      nlinarith
    rw [distInt_eq_abs_of_abs_le_half hh, abs_of_nonneg hn]
    have hcast : ((2 * k - Q : ℕ) : ℝ) = 2 * k - Q := by
      rw [Nat.cast_sub (by omega : Q ≤ 2 * k)]
      push_cast
      ring
    rw [show 2 * ((k : ℝ) / Q) - 1 = ((2 * k - Q : ℕ) : ℝ) / Q by
      rw [hcast]
      field_simp, Nat.sub_eq_zero_of_le (by omega : Q ≤ 2 * k)]
    simp

theorem norm_TI_div_le_of_lt_four_mul {k : ℕ} (hkQ : k < R.Q X P)
    (h4 : R.Q X P < 4 * min k (R.Q X P - k)) (hk : 2 * k ≠ R.Q X P) :
    ‖R.TI X (k / R.Q X P)‖ ≤ R.Q X P / ((2 * k - R.Q X P) + (R.Q X P - 2 * k) : ℕ) := by
  let m := min k (R.Q X P - k)
  let D := (2 * k - R.Q X P) + (R.Q X P - 2 * k)
  have hk0 : 0 < k := by
    omega
  have hm : 0 < m := by
    dsimp [m]
    omega
  have hD : 0 < D := by
    omega
  have hDm : D ≤ 2 * m := by
    dsimp [D, m]
    omega
  have hQ : 0 < R.Q X P := R.Q_pos X P
  have hQ' : (0 : ℝ) < R.Q X P := by exact_mod_cast hQ
  rcases R.ν_eq with hν | hν
  · have hdist : distInt (R.ν * (k / R.Q X P)) ≠ 0 := by
      rw [hν, Nat.cast_one, one_mul, R.distInt_div_eq_min X P hk0 hkQ]
      exact ne_of_gt (div_pos (by exact_mod_cast hm) hQ')
    have h := R.norm_TI_le_inv X (k / R.Q X P) hdist
    rw [hν, Nat.cast_one, one_mul, R.distInt_div_eq_min X P hk0 hkQ] at h
    calc
      ‖R.TI X (k / R.Q X P)‖ ≤ R.Q X P / (2 * (m : ℕ)) := by
        calc
          ‖R.TI X (k / R.Q X P)‖ ≤ 1 / (2 * ((m : ℕ) / R.Q X P)) := h
          _ = R.Q X P / (2 * (m : ℕ)) := by field_simp
      _ ≤ R.Q X P / (D : ℕ) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact_mod_cast hDm
  · have heq := distInt_two_mul_div_eq_D_pre hQ hkQ h4
    have hdist : distInt (R.ν * (k / R.Q X P)) ≠ 0 := by
      rw [hν, Nat.cast_ofNat, show (2 : ℝ) * (k / R.Q X P) =
        2 * ((k : ℝ) / R.Q X P) by norm_num, heq]
      exact ne_of_gt (div_pos (by exact_mod_cast hD) hQ')
    have h := R.norm_TI_le_inv X (k / R.Q X P) hdist
    rw [hν, Nat.cast_ofNat, show (2 : ℝ) * (k / R.Q X P) =
      2 * ((k : ℝ) / R.Q X P) by norm_num, heq] at h
    calc
      ‖R.TI X (k / R.Q X P)‖ ≤ 1 / (2 * ((D : ℕ) / R.Q X P)) := h
      _ = R.Q X P / (2 * (D : ℕ)) := by field_simp
      _ ≤ R.Q X P / (D : ℕ) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        nlinarith [show (0 : ℝ) ≤ (D : ℕ) by positivity]

/-- `‖TI (k / Q)‖ ≤ Q + 1` always. -/
theorem norm_TI_div_le_Q_add_one (hX : 0 ≤ X) (θ : ℝ) : ‖R.TI X θ‖ ≤ R.Q X P + 1 := by
  have hβ : R.β * X ≤ R.span X := by
    rw [span]
    have hν : (1 : ℝ) ≤ R.ν := by exact_mod_cast R.one_le_ν
    have hβ0 : 0 ≤ R.β := (R.α_pos.trans R.α_lt_β).le
    have hδ0 : 0 ≤ R.δ := (R.γ_pos.trans R.γ_lt_δ).le
    have hB0 : 0 ≤ R.B := R.B_pos.le
    nlinarith [mul_nonneg (sub_nonneg.mpr hν) (mul_nonneg hβ0 hX),
      mul_nonneg (add_nonneg hδ0 hB0) hX]
  have hTI := R.norm_TI_le X hX θ
  have hspan : R.span X < R.Q X P := R.span_lt_Q X P
  nlinarith

/-! ### Summation over the far set -/

/-- A sum of `g ∘ f` over `s` is at most twice the sum over the image when the fibres of `f` have
at most two elements, each pair `k, k'` in a fibre satisfying `k + k' = Q`. -/
theorem sum_comp_le_two_mul_sum {s t : Finset ℕ} {f : ℕ → ℕ} {g : ℕ → ℝ}
    (hg : ∀ d ∈ t, 0 ≤ g d) (hf : ∀ k ∈ s, f k ∈ t)
    (hinj : ∀ k ∈ s, ∀ k' ∈ s, f k = f k' → k = k' ∨ k + k' = R.Q X P) :
    ∑ k ∈ s, g (f k) ≤ 2 * ∑ d ∈ t, g d := by
  classical
  have hcard (b : ℕ) : #(s.filter (fun a => f a = b)) ≤ 2 := by
    by_contra h
    have h' : 2 < #(s.filter (fun a => f a = b)) := by omega
    obtain ⟨a, ha, c, hc, d, hd, hac, had, hcd⟩ :=
      Finset.two_lt_card.mp h'
    have hab := hinj a (Finset.mem_filter.mp ha).1 c (Finset.mem_filter.mp hc).1
      (by simp [Finset.mem_filter.mp ha, Finset.mem_filter.mp hc])
    have had' := hinj a (Finset.mem_filter.mp ha).1 d (Finset.mem_filter.mp hd).1
      (by simp [Finset.mem_filter.mp ha, Finset.mem_filter.mp hd])
    have hcd' := hinj c (Finset.mem_filter.mp hc).1 d (Finset.mem_filter.mp hd).1
      (by simp [Finset.mem_filter.mp hc, Finset.mem_filter.mp hd])
    rcases hab with hac' | hab
    · exact hac hac'
    rcases had' with had'' | had'
    · exact had had''
    rcases hcd' with hcd'' | hcd'
    · exact hcd hcd''
    omega
  rw [Finset.sum_comp]
  calc
    ∑ b ∈ s.image f, #(s.filter (fun a => f a = b)) • g b ≤
        ∑ b ∈ s.image f, 2 * g b := by
      apply Finset.sum_le_sum
      intro b hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
      have hc : (#(s.filter (fun x => f x = f a)) : ℝ) ≤ 2 := by
        exact_mod_cast hcard (f a)
      simpa only [nsmul_eq_mul] using
        (mul_le_mul_of_nonneg_right hc (hg (f a) (hf a ha)))
    _ = 2 * ∑ b ∈ s.image f, g b := by
      rw [← Finset.mul_sum]
    _ ≤ 2 * ∑ d ∈ t, g d := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.image_subset_iff.mpr hf) (by
            intro d hd _
            exact hg d hd)) (by norm_num)

private theorem distInt_two_mul_div_ge_min {k Q : ℕ} (hQ : 0 < Q) (hk0 : 0 < k)
    (hkQ : k < Q) (h4 : 4 * min k (Q - k) ≤ Q) :
    ((min k (Q - k) : ℕ) : ℝ) / Q ≤ distInt (2 * ((k : ℝ) / Q)) := by
  rcases le_or_gt (2 * k) Q with h | h
  · have hm : min k (Q - k) = k := by rw [min_eq_left]; omega
    rw [hm]
    rw [hm] at h4
    have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
    have hhalf : |2 * ((k : ℝ) / Q)| ≤ 1 / 2 := by
      rw [abs_of_nonneg (by positivity)]
      rw [show 2 * ((k : ℝ) / Q) = (2 * (k : ℝ)) / Q by ring]
      apply (div_le_iff₀ hQ').2
      have h' : (4 : ℝ) * k ≤ Q := by exact_mod_cast h4
      nlinarith
    rw [distInt_eq_abs_of_abs_le_half hhalf, abs_of_nonneg (by positivity)]
    have hkQ' : 0 ≤ (k : ℝ) / Q := by positivity
    have := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 2 by norm_num) hkQ'
    simpa [mul_div_assoc] using this
  · have hm : min k (Q - k) = Q - k := by rw [min_eq_right]; omega
    rw [hm]
    rw [hm] at h4
    have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
    have hrewrite :
        2 * ((k : ℝ) / Q) = -(2 * ((Q - k : ℕ) : ℝ) / Q) + ((2 : ℤ) : ℝ) := by
      push_cast
      rw [Nat.cast_sub hkQ.le]
      field_simp
      ring
    rw [hrewrite, distInt_add_intCast, distInt_neg]
    have hhalf : |2 * ((Q - k : ℕ) : ℝ) / Q| ≤ 1 / 2 := by
      rw [abs_of_nonneg (by positivity)]
      apply (div_le_iff₀ hQ').2
      have hnat : 4 * (Q - k) ≤ Q := by omega
      have h' : (4 : ℝ) * ((Q - k : ℕ) : ℝ) ≤ Q := by exact_mod_cast hnat
      nlinarith
    rw [distInt_eq_abs_of_abs_le_half hhalf, abs_of_nonneg (by positivity)]
    have hkQ' : 0 ≤ ((Q - k : ℕ) : ℝ) / Q := by positivity
    have := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 2 by norm_num) hkQ'
    simpa [mul_div_assoc] using this

private theorem distInt_two_mul_div_eq_D {k Q : ℕ} (hQ : 0 < Q) (hkQ : k < Q)
    (h4 : Q < 4 * min k (Q - k)) :
    distInt (2 * ((k : ℝ) / Q)) =
      (((2 * k - Q) + (Q - 2 * k) : ℕ) : ℝ) / Q := by
  rcases le_or_gt (2 * k) Q with h | h
  · have hm : min k (Q - k) = k := by rw [min_eq_left]; omega
    rw [hm] at h4
    have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
    rw [show 2 * ((k : ℝ) / Q) =
      (2 * ((k : ℝ) / Q) - 1) + ((1 : ℤ) : ℝ) by norm_num,
      distInt_add_intCast]
    have hn : 2 * ((k : ℝ) / Q) - 1 ≤ 0 := by
      apply sub_nonpos.mpr
      rw [show 2 * ((k : ℝ) / Q) = (2 * (k : ℝ)) / Q by ring]
      apply (div_le_iff₀ hQ').2
      have h' : (2 : ℝ) * k ≤ Q := by exact_mod_cast h
      nlinarith
    have hh : |2 * ((k : ℝ) / Q) - 1| ≤ 1 / 2 := by
      rw [abs_of_nonpos hn]
      have h' : (Q : ℝ) < 4 * k := by exact_mod_cast h4
      have heq : -(2 * ((k : ℝ) / Q) - 1) = (Q - 2 * k) / Q := by
        field_simp
        ring
      rw [heq]
      apply (div_le_iff₀ hQ').2
      nlinarith
    rw [distInt_eq_abs_of_abs_le_half hh, abs_of_nonpos hn]
    have hnat : 2 * k ≤ Q := h
    have hcast : ((Q - 2 * k : ℕ) : ℝ) = Q - 2 * k := by
      rw [Nat.cast_sub hnat]
      push_cast
      ring
    have hval : -(2 * ((k : ℝ) / Q) - 1) =
        ((Q - 2 * k : ℕ) : ℝ) / Q := by
      rw [hcast]
      field_simp
      ring
    rw [hval, Nat.sub_eq_zero_of_le h]
    simp
  · have hm : min k (Q - k) = Q - k := by rw [min_eq_right]; omega
    rw [hm] at h4
    have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
    rw [show 2 * ((k : ℝ) / Q) =
      (2 * ((k : ℝ) / Q) - 1) + ((1 : ℤ) : ℝ) by norm_num,
      distInt_add_intCast]
    have hn : 0 ≤ 2 * ((k : ℝ) / Q) - 1 := by
      apply sub_nonneg.mpr
      rw [show 2 * ((k : ℝ) / Q) = (2 * (k : ℝ)) / Q by ring]
      apply (le_div_iff₀ hQ').2
      have h' : (Q : ℝ) < 2 * k := by exact_mod_cast h
      nlinarith
    have hh : |2 * ((k : ℝ) / Q) - 1| ≤ 1 / 2 := by
      rw [abs_of_nonneg hn]
      have h' : (4 : ℝ) * ((Q - k : ℕ) : ℝ) > Q := by exact_mod_cast h4
      rw [Nat.cast_sub hkQ.le] at h'
      rw [show 2 * ((k : ℝ) / Q) - 1 =
        (2 * k - Q) / Q by field_simp]
      apply (div_le_iff₀ hQ').2
      nlinarith
    rw [distInt_eq_abs_of_abs_le_half hh, abs_of_nonneg hn]
    have hcast : ((2 * k - Q : ℕ) : ℝ) = 2 * k - Q := by
      rw [Nat.cast_sub (by omega : Q ≤ 2 * k)]
      push_cast
      ring
    have hval : 2 * ((k : ℝ) / Q) - 1 =
        ((2 * k - Q : ℕ) : ℝ) / Q := by
      rw [hcast]
      field_simp
    rw [hval, Nat.sub_eq_zero_of_le (by omega : Q ≤ 2 * k)]
    simp

/-- The outer part of the far set: `∑ Q² / (4 m²) ≤ Q² / (2 J₀)`. -/
theorem sum_farSet_outer_le (hJ : 1 ≤ R.halfWidth X P) :
    ∑ k ∈ R.farSet X P with 4 * min k (R.Q X P - k) ≤ R.Q X P,
      (R.Q X P : ℝ) ^ 2 / (4 * ((min k (R.Q X P - k) : ℕ) : ℝ) ^ 2) ≤
        (R.Q X P : ℝ) ^ 2 / (2 * R.halfWidth X P) := by
  classical
  let Q := R.Q X P
  let J := R.halfWidth X P
  let m : ℕ → ℕ := fun k => min k (Q - k)
  let s := (R.farSet X P).filter fun k => 4 * m k ≤ Q
  let t := Ioc J Q
  let g : ℕ → ℝ := fun d => (Q : ℝ) ^ 2 / (4 * (d : ℝ) ^ 2)
  by_cases hQJ : J ≤ Q
  · have hg (d : ℕ) (hd : d ∈ t) : 0 ≤ g d := by
      dsimp [g]
      positivity
    have hf (k : ℕ) (hk : k ∈ s) : m k ∈ t := by
      rw [Finset.mem_Ioc]
      have hk' := (R.mem_farSet X P).mp (Finset.mem_filter.mp hk).1
      dsimp [m]
      constructor <;> omega
    have hinj (k : ℕ) (hk : k ∈ s) (k' : ℕ) (hk' : k' ∈ s)
        (heq : m k = m k') : k = k' ∨ k + k' = Q := by
      have h1 := (R.mem_farSet X P).mp (Finset.mem_filter.mp hk).1
      have h2 := (R.mem_farSet X P).mp (Finset.mem_filter.mp hk').1
      dsimp [m] at heq
      rcases le_total k (Q - k) with h | h <;>
        rcases le_total k' (Q - k') with h' | h' <;>
        simp only [min_eq_left h, min_eq_right h, min_eq_left h', min_eq_right h'] at heq <;>
        omega
    have hsum := R.sum_comp_le_two_mul_sum X P hg hf hinj
    have hseries : ∑ i ∈ Ioc J Q, ((i : ℝ) ^ 2)⁻¹ ≤
        (J : ℝ)⁻¹ - (Q : ℝ)⁻¹ :=
      sum_Ioc_inv_sq_le_sub (k := J) (n := Q) (by omega) hQJ
    have hrewrite : 2 * ∑ d ∈ t, g d =
        ((Q : ℝ) ^ 2 / 2) * ∑ d ∈ t, ((d : ℝ) ^ 2)⁻¹ := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      dsimp [g]
      field_simp
      ring
    change ∑ k ∈ s, g (m k) ≤ (Q : ℝ) ^ 2 / (2 * J)
    calc
      ∑ k ∈ s, g (m k) ≤ 2 * ∑ d ∈ t, g d := hsum
      _ = ((Q : ℝ) ^ 2 / 2) * ∑ d ∈ t, ((d : ℝ) ^ 2)⁻¹ := hrewrite
      _ ≤ ((Q : ℝ) ^ 2 / 2) * ((J : ℝ)⁻¹ - (Q : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left hseries (by positivity)
      _ ≤ ((Q : ℝ) ^ 2 / 2) * (J : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_left (sub_le_self _ (by positivity)) (by positivity)
      _ = (Q : ℝ) ^ 2 / (2 * J) := by field_simp
  · have hs : s = ∅ := by
      ext k
      simp
      intro hk
      have hk' := (R.mem_farSet X P).mp (Finset.mem_filter.mp hk).1
      omega
    change ∑ k ∈ s, g (m k) ≤ (Q : ℝ) ^ 2 / (2 * J)
    rw [hs, Finset.sum_empty]
    positivity

/-- The middle part of the far set: `∑_{2k ≠ Q} 2 Q / |2 k - Q| ≤ 4 Q (log Q + 1)`. -/
theorem sum_farSet_middle_le :
    ∑ k ∈ R.farSet X P with R.Q X P < 4 * min k (R.Q X P - k) ∧ 2 * k ≠ R.Q X P,
      2 * (R.Q X P : ℝ) / (((2 * k - R.Q X P) + (R.Q X P - 2 * k) : ℕ) : ℝ) ≤
        4 * R.Q X P * (log (R.Q X P) + 1) := by
  classical
  let Q := R.Q X P
  let D : ℕ → ℕ := fun k => (2 * k - Q) + (Q - 2 * k)
  let s := (R.farSet X P).filter fun k => Q < 4 * min k (Q - k) ∧ 2 * k ≠ Q
  let t := Icc 1 Q
  let g : ℕ → ℝ := fun d => 2 * (Q : ℝ) / d
  have hg (d : ℕ) (hd : d ∈ t) : 0 ≤ g d := by
    dsimp [g]
    positivity
  have hf (k : ℕ) (hk : k ∈ s) : D k ∈ t := by
    rw [Finset.mem_Icc]
    have hk' := (R.mem_farSet X P).mp (Finset.mem_filter.mp hk).1
    have hcond := (Finset.mem_filter.mp hk).2
    dsimp [D]
    constructor <;> omega
  have hinj (k : ℕ) (hk : k ∈ s) (k' : ℕ) (hk' : k' ∈ s)
      (heq : D k = D k') : k = k' ∨ k + k' = Q := by
    have h1 := (R.mem_farSet X P).mp (Finset.mem_filter.mp hk).1
    have h2 := (R.mem_farSet X P).mp (Finset.mem_filter.mp hk').1
    dsimp [D] at heq
    rcases le_total (2 * k) Q with h | h <;>
      rcases le_total (2 * k') Q with h' | h' <;>
      omega
  have hsum := R.sum_comp_le_two_mul_sum X P hg hf hinj
  have hharmonic : ∑ d ∈ t, (d : ℝ)⁻¹ ≤ log Q + 1 := by
    calc
      ∑ d ∈ t, (d : ℝ)⁻¹ = (harmonic Q : ℝ) := by
        simp [t, harmonic_eq_sum_Icc]
      _ ≤ 1 + log Q := by exact_mod_cast harmonic_le_one_add_log Q
      _ = log Q + 1 := by ring
  have hrewrite : 2 * ∑ d ∈ t, g d = 4 * Q * ∑ d ∈ t, (d : ℝ)⁻¹ := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    dsimp [g]
    ring
  change ∑ k ∈ s, g (D k) ≤ 4 * Q * (log Q + 1)
  calc
    ∑ k ∈ s, g (D k) ≤ 2 * ∑ d ∈ t, g d := hsum
    _ = 4 * Q * ∑ d ∈ t, (d : ℝ)⁻¹ := hrewrite
    _ ≤ 4 * Q * (log Q + 1) :=
      mul_le_mul_of_nonneg_left hharmonic (by positivity)

/-- The far-set sum is bounded by `Q² / (2 J₀) + 2 (Q + 1) + 4 Q (log Q + 1)`. -/
theorem norm_sum_farSet_le (hX : 0 ≤ X) (hJ : 1 ≤ R.halfWidth X P) (N : ℕ) :
    ‖∑ k ∈ R.farSet X P, R.TI X (k / R.Q X P) * R.TJ X (k / R.Q X P) * e (-(N * k / R.Q X P))‖ ≤
      (R.Q X P : ℝ) ^ 2 / (2 * R.halfWidth X P) + 2 * (R.Q X P + 1) +
        4 * R.Q X P * (log (R.Q X P) + 1) := by
  classical
  have hQ : 0 < R.Q X P := R.Q_pos X P
  have hQ' : (0 : ℝ) < R.Q X P := by exact_mod_cast hQ
  have hterm (k : ℕ) (_ : k ∈ R.farSet X P) :
      ‖R.TI X (k / R.Q X P) * R.TJ X (k / R.Q X P) * e (-(N * k / R.Q X P))‖ =
        ‖R.TI X (k / R.Q X P)‖ * ‖R.TJ X (k / R.Q X P)‖ := by
    rw [norm_mul, norm_mul, norm_e, mul_one]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_congr rfl hterm]
  rw [← Finset.sum_filter_add_sum_filter_not (R.farSet X P)
    (fun k => 4 * min k (R.Q X P - k) ≤ R.Q X P)]
  rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.filter (fun k => ¬ 4 * min k (R.Q X P - k) ≤ R.Q X P) (R.farSet X P))
    (fun k => 2 * k ≠ R.Q X P)]
  rw [Finset.filter_filter, Finset.filter_filter]
  have hA : ∑ k ∈ (R.farSet X P).filter
      (fun k => 4 * min k (R.Q X P - k) ≤ R.Q X P),
      ‖R.TI X (k / R.Q X P)‖ * ‖R.TJ X (k / R.Q X P)‖ ≤
        (R.Q X P : ℝ) ^ 2 / (2 * R.halfWidth X P) := by
    calc
      _ ≤ ∑ k ∈ (R.farSet X P).filter
          (fun k => 4 * min k (R.Q X P - k) ≤ R.Q X P),
          (R.Q X P : ℝ) ^ 2 / (4 * ((min k (R.Q X P - k) : ℕ) : ℝ) ^ 2) := by
        apply Finset.sum_le_sum
        intro k hk
        have hkfar := (R.mem_farSet X P).mp (Finset.mem_filter.mp hk).1
        have hk0 : 0 < k := by omega
        have hkQ : k < R.Q X P := by omega
        have h4 := (Finset.mem_filter.mp hk).2
        have hTI := R.norm_TI_div_le_of_four_mul_le X P hk0 hkQ h4
        have hTJ := R.norm_TJ_div_le X P hk0 hkQ
        have hm : 0 < min k (R.Q X P - k) := by omega
        calc
          _ ≤ (R.Q X P / (2 * ((min k (R.Q X P - k) : ℕ) : ℝ))) *
              (R.Q X P / (2 * ((min k (R.Q X P - k) : ℕ) : ℝ))) :=
            mul_le_mul hTI hTJ (norm_nonneg _) (by positivity)
          _ = (R.Q X P : ℝ) ^ 2 / (4 * ((min k (R.Q X P - k) : ℕ) : ℝ) ^ 2) := by
            field_simp
            ring
      _ ≤ _ := R.sum_farSet_outer_le X P hJ
  have hB : ∑ k ∈ (R.farSet X P).filter
      (fun k => ¬ 4 * min k (R.Q X P - k) ≤ R.Q X P ∧ 2 * k ≠ R.Q X P),
      ‖R.TI X (k / R.Q X P)‖ * ‖R.TJ X (k / R.Q X P)‖ ≤
        4 * R.Q X P * (log (R.Q X P) + 1) := by
    have hs : (R.farSet X P).filter
        (fun k => ¬ 4 * min k (R.Q X P - k) ≤ R.Q X P ∧ 2 * k ≠ R.Q X P) =
        (R.farSet X P).filter
          (fun k => R.Q X P < 4 * min k (R.Q X P - k) ∧ 2 * k ≠ R.Q X P) :=
      Finset.filter_congr fun k _ => by rw [not_le]
    rw [hs]
    calc
      _ ≤ ∑ k ∈ (R.farSet X P).filter
          (fun k => R.Q X P < 4 * min k (R.Q X P - k) ∧ 2 * k ≠ R.Q X P),
          2 * (R.Q X P : ℝ) /
            (((2 * k - R.Q X P) + (R.Q X P - 2 * k) : ℕ) : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        have hkfar := (R.mem_farSet X P).mp (Finset.mem_filter.mp hk).1
        have hcond := (Finset.mem_filter.mp hk).2
        have hk0 : 0 < k := by omega
        have hkQ : k < R.Q X P := by omega
        have hTI := R.norm_TI_div_le_of_lt_four_mul X P hkQ hcond.1 hcond.2
        have hTJ := R.norm_TJ_div_le X P hk0 hkQ
        have hm : 0 < min k (R.Q X P - k) := by omega
        have htj : R.Q X P / (2 * ((min k (R.Q X P - k) : ℕ) : ℝ)) ≤ 2 := by
          rw [div_le_iff₀ (by positivity)]
          have hcast : (R.Q X P : ℝ) <
              4 * ((min k (R.Q X P - k) : ℕ) : ℝ) := by
            exact_mod_cast hcond.1
          norm_num at hcast ⊢
          linarith
        calc
          _ ≤ (R.Q X P / (((2 * k - R.Q X P) + (R.Q X P - 2 * k) : ℕ) : ℝ)) *
              (R.Q X P / (2 * ((min k (R.Q X P - k) : ℕ) : ℝ))) :=
            mul_le_mul hTI hTJ (norm_nonneg _) (by positivity)
          _ ≤ (R.Q X P / (((2 * k - R.Q X P) + (R.Q X P - 2 * k) : ℕ) : ℝ)) * 2 :=
            mul_le_mul_of_nonneg_left htj (by positivity)
          _ = 2 * (R.Q X P : ℝ) /
              (((2 * k - R.Q X P) + (R.Q X P - 2 * k) : ℕ) : ℝ) := by ring
      _ ≤ _ := R.sum_farSet_middle_le X P
  have hC : ∑ k ∈ (R.farSet X P).filter
      (fun k => ¬ 4 * min k (R.Q X P - k) ≤ R.Q X P ∧ ¬ 2 * k ≠ R.Q X P),
      ‖R.TI X (k / R.Q X P)‖ * ‖R.TJ X (k / R.Q X P)‖ ≤ 2 * (R.Q X P + 1) := by
    have hcard : #((R.farSet X P).filter
        (fun k => ¬ 4 * min k (R.Q X P - k) ≤ R.Q X P ∧ ¬ 2 * k ≠ R.Q X P)) ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      omega
    calc
      _ ≤ #((R.farSet X P).filter
          (fun k => ¬ 4 * min k (R.Q X P - k) ≤ R.Q X P ∧ ¬ 2 * k ≠ R.Q X P)) *
          ((R.Q X P : ℝ) + 1) := by
        rw [← nsmul_eq_mul]
        apply Finset.sum_le_card_nsmul
        intro k hk
        have hkfar := (R.mem_farSet X P).mp (Finset.mem_filter.mp hk).1
        have hcond := (Finset.mem_filter.mp hk).2
        have heq : 2 * k = R.Q X P := by omega
        have hk0 : 0 < k := by omega
        have hkQ : k < R.Q X P := by omega
        have hm : min k (R.Q X P - k) = k := by omega
        have hTI := R.norm_TI_div_le_Q_add_one X P hX (k / R.Q X P)
        have hTJ := R.norm_TJ_div_le X P hk0 hkQ
        rw [hm] at hTJ
        have hTJ' : ‖R.TJ X (k / R.Q X P)‖ ≤ 1 := by
          calc
            _ ≤ R.Q X P / (2 * (k : ℝ)) := hTJ
            _ = 1 := by
              rw [show (R.Q X P : ℝ) = 2 * k by
                exact_mod_cast heq.symm]
              field_simp
        nlinarith [mul_le_mul hTI hTJ' (norm_nonneg _) (by positivity)]
      _ ≤ 2 * ((R.Q X P : ℝ) + 1) := by
        have : (#((R.farSet X P).filter
          (fun k => ¬ 4 * min k (R.Q X P - k) ≤ R.Q X P ∧ ¬ 2 * k ≠ R.Q X P)) : ℝ) ≤ 1 := by
          exact_mod_cast hcard
        nlinarith
  linarith

/-- **Singular integral versus lattice count.** -/
theorem norm_singularIntegral_sub_count_le (hP : 1 ≤ P) (hX : 8 * (P : ℝ) ^ 3 ≤ X)
    (hPQ : X ≤ P * R.Q X P) {N : ℕ} (hN : (N : ℝ) ≤ R.B * X) :
    ‖R.singularIntegral X P N - R.count X N‖ ≤ 2 * X / P + 4 * (log (R.Q X P) + 2) := by
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hX0 : 0 < X := lt_of_lt_of_le (by positivity) hX
  have hQ' : (0 : ℝ) < R.Q X P := by exact_mod_cast R.Q_pos X P
  have hJ1 := R.one_le_halfWidth X P hX0 hPQ
  have h4 := R.four_mul_halfWidth_le X P hP hX
  have hJ1' : (1 : ℝ) ≤ R.halfWidth X P := by exact_mod_cast hJ1
  have h4' : 4 * R.halfWidth X P ≤ R.Q X P := by
    exact_mod_cast h4
  have hJ2 : 2 * R.halfWidth X P < R.Q X P := by omega
  rw [R.singularIntegral_sub_count_eq X P hX0.le hJ2 hN, norm_neg, norm_mul, norm_div,
    norm_one, Complex.norm_natCast]
  have hfar := R.norm_sum_farSet_le X P hX0.le hJ1 N
  have hratio : (R.Q X P : ℝ) / (2 * R.halfWidth X P) ≤ 2 * X / P := by
    have h := R.le_halfWidth_div_Q X P hX0 hPQ
    rw [div_le_div_iff₀ hX0 hQ'] at h
    rw [div_le_div_iff₀ (by positivity) hP0]
    nlinarith [hJ1', hQ', hX0]
  have hmid : 2 * ((R.Q X P : ℝ) + 1) / R.Q X P ≤ 4 := by
    rw [div_le_iff₀ hQ']
    nlinarith
  calc
    1 / (R.Q X P : ℝ) *
        ‖∑ k ∈ R.farSet X P,
          R.TI X (k / R.Q X P) * R.TJ X (k / R.Q X P) * e (-(N * k / R.Q X P))‖ ≤
        1 / R.Q X P *
          ((R.Q X P : ℝ) ^ 2 / (2 * R.halfWidth X P) + 2 * (R.Q X P + 1) +
            4 * R.Q X P * (log (R.Q X P) + 1)) :=
      mul_le_mul_of_nonneg_left hfar (by positivity)
    _ = R.Q X P / (2 * R.halfWidth X P) + 2 * (R.Q X P + 1) / R.Q X P +
          4 * (log (R.Q X P) + 1) := by
      field_simp
    _ ≤ 2 * X / P + 4 + 4 * (log (R.Q X P) + 1) := by
      linarith
    _ = 2 * X / P + 4 * (log (R.Q X P) + 2) := by ring

end Ranges

end CircleMethod
