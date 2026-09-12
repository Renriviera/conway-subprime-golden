/-
Copyright (c) 2026 Romain Popescu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Romain Popescu
-/
import ConwayGolden.NumberTheory.CircleMethod.MajorArcs

/-!
# The minor arcs

The minor-arc contribution `minorSum N` is controlled in mean square over `N`: by Parseval,

`∑_{N < Q} ‖minorSum N‖² = Q⁻¹ ∑_{k minor} ‖SI(k/Q)‖² ‖SJ(k/Q)‖²
  ≤ (sup_{k minor} ‖SJ(k/Q)‖)² · ∑_{m ∈ I} Λ(m)²`,

and Vinogradov's bound gives `sup_{k minor} ‖SJ(k/Q)‖ ≪ (log X)⁴ X / √P` because every minor
frequency has a Dirichlet approximation with denominator in `(P, X / P]`. Hence the number of
`N` with `‖minorSum N‖ ≥ ε X` is `≪ X (log X)¹⁰ / (ε² P)`.

## Main statements

* `Ranges.sum_norm_sq_minorSum_le`: the Parseval bound.
* `Ranges.exists_norm_SJ_le_of_mem_minorSet`: Vinogradov's bound on the minor arcs.
* `Ranges.exists_card_minor_exceptional_le`: the mean-square exceptional set bound.

## References

* [R. C. Vaughan, *The Hardy–Littlewood method*, §3.2][Vaughan1997]
-/

namespace CircleMethod

namespace Ranges

open Filter Finset Real
open scoped ArithmeticFunction.vonMangoldt

variable (R : Ranges) (X : ℝ) (P : ℕ)

/-- **Parseval bound for the minor arcs.** If `‖SJ(k/Q)‖ ≤ M` on the minor arcs, then
`∑_{N < Q} ‖minorSum N‖² ≤ M² ∑_{m ∈ I} Λ(m)²`. -/
theorem sum_norm_sq_minorSum_le (hX : 0 ≤ X) {M : ℝ}
    (hM : ∀ k ∈ R.minorSet X P, ‖R.SJ X (k / R.Q X P)‖ ≤ M) :
    ∑ N ∈ range (R.Q X P), ‖R.minorSum X P N‖ ^ 2 ≤ M ^ 2 * ∑ m ∈ R.I X, Λ m ^ 2 := by
  classical
  let F : ℕ → ℂ := fun k =>
    if k ∈ R.minorSet X P then
      R.SI X (k / R.Q X P) * R.SJ X (k / R.Q X P)
    else 0
  have hsub : ∀ k ∈ R.minorSet X P, k ∈ range (R.Q X P) := by
    intro k hk
    exact Finset.mem_range.mpr ((R.mem_minorSet X P).mp hk |>.1)
  have hminor :
      ∀ N, R.minorSum X P N =
        (1 / (R.Q X P : ℂ)) *
          ∑ k ∈ range (R.Q X P), F k * e (-(N * k / R.Q X P)) := by
    intro N
    rw [minorSum]
    congr 1
    have hminor' :
        ∑ k ∈ R.minorSet X P,
            R.SI X (k / R.Q X P) * R.SJ X (k / R.Q X P) *
              e (-(N * k / R.Q X P)) =
          ∑ k ∈ R.minorSet X P, F k * e (-(N * k / R.Q X P)) := by
      apply Finset.sum_congr rfl
      intro k hk
      change R.SI X (k / R.Q X P) * R.SJ X (k / R.Q X P) *
          e (-(N * k / R.Q X P)) =
        (if k ∈ R.minorSet X P then
          R.SI X (k / R.Q X P) * R.SJ X (k / R.Q X P) else 0) *
          e (-(N * k / R.Q X P))
      rw [if_pos hk]
    symm
    calc
      ∑ k ∈ range (R.Q X P), F k * e (-(N * k / R.Q X P)) =
          ∑ k ∈ range (R.Q X P),
            (if k ∈ R.minorSet X P then
                R.SI X (k / R.Q X P) * R.SJ X (k / R.Q X P)
              else 0) * e (-(N * k / R.Q X P)) := by
        apply Finset.sum_congr rfl
        intro k hk
        simp [F]
      _ = ∑ k ∈ (range (R.Q X P)).filter (fun k => k ∈ R.minorSet X P),
          (R.SI X (k / R.Q X P) * R.SJ X (k / R.Q X P)) *
            e (-(N * k / R.Q X P)) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro k hk
        by_cases hkm : k ∈ R.minorSet X P <;> simp [hkm]
      _ = ∑ k ∈ R.minorSet X P,
          (R.SI X (k / R.Q X P) * R.SJ X (k / R.Q X P)) *
            e (-(N * k / R.Q X P)) := by
        congr 1
        ext k
        simp only [Finset.mem_filter, Finset.mem_range]
        constructor
        · exact fun h => h.2
        · intro hk
          exact ⟨Finset.mem_range.mp (hsub k hk), hk⟩
  have hparse := sum_norm_sq_sum_mul_e_neg (R.Q_pos X P) F
  rw [show (∑ N ∈ range (R.Q X P), ‖R.minorSum X P N‖ ^ 2) =
      ∑ N ∈ range (R.Q X P),
        ‖(1 / (R.Q X P : ℂ)) *
          ∑ k ∈ range (R.Q X P), F k * e (-(N * k / R.Q X P))‖ ^ 2 by
    apply Finset.sum_congr rfl
    intro N hN
    rw [hminor]]
  rw [hparse]
  have hterm (k : ℕ) (hk : k ∈ range (R.Q X P)) :
      ‖F k‖ ^ 2 ≤ M ^ 2 * ‖R.SI X (k / R.Q X P)‖ ^ 2 := by
    by_cases hmk : k ∈ R.minorSet X P
    · simp only [F, hmk, ↓reduceIte]
      rw [norm_mul, mul_pow]
      have hsj := hM k hmk
      have hsj0 : 0 ≤ ‖R.SJ X (k / R.Q X P)‖ := norm_nonneg _
      have hM0 : 0 ≤ M := le_trans hsj0 hsj
      have hsq := (sq_le_sq₀ hsj0 hM0).mpr hsj
      simpa [mul_comm] using mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    · simp [F, hmk]
      positivity
  have hsumF :
      ∑ k ∈ range (R.Q X P), ‖F k‖ ^ 2 ≤
        M ^ 2 * ∑ k ∈ range (R.Q X P), ‖R.SI X (k / R.Q X P)‖ ^ 2 := by
    calc
      ∑ k ∈ range (R.Q X P), ‖F k‖ ^ 2 ≤
          ∑ k ∈ range (R.Q X P),
            M ^ 2 * ‖R.SI X (k / R.Q X P)‖ ^ 2 :=
        Finset.sum_le_sum fun k hk => hterm k hk
      _ = M ^ 2 * ∑ k ∈ range (R.Q X P), ‖R.SI X (k / R.Q X P)‖ ^ 2 := by
        rw [Finset.mul_sum]
  have hdistinct (m : ℕ) (hm : m ∈ R.I X) (m' : ℕ) (hm' : m' ∈ R.I X)
      (hd : (R.Q X P : ℤ) ∣ (R.ν * m : ℤ) - R.ν * m') : m = m' := by
    have hνm (u : ℕ) (hu : u ∈ R.I X) : (R.ν * u : ℝ) < R.Q X P := by
      have hν : (R.ν : ℝ) ≤ 2 := by exact_mod_cast R.ν_le_two
      have hu' := (R.mem_I X hX).mp hu
      have hβ : 0 ≤ R.β * X :=
        mul_nonneg (R.α_pos.trans R.α_lt_β).le hX
      have hspan := R.span_lt_Q X P
      calc
        (R.ν * u : ℝ) ≤ (R.ν : ℝ) * (R.β * X) := by
          exact mul_le_mul_of_nonneg_left hu'.2 (by positivity)
        _ ≤ (R.ν * R.β + R.δ + R.B) * X := by
          nlinarith [mul_nonneg (R.γ_pos.trans R.γ_lt_δ).le hX,
            mul_nonneg R.B_pos.le hX]
        _ < R.Q X P := hspan
    have hνm' := hνm m' hm'
    have hνm0 := hνm m hm
    have habs : |(R.ν * m : ℤ) - R.ν * m'| < (R.Q X P : ℤ) := by
      rw [abs_lt]
      constructor
      · have hmnat : R.ν * m < R.Q X P := by exact_mod_cast hνm0
        have hm'nat : R.ν * m' < R.Q X P := by exact_mod_cast hνm'
        have hmI : (R.ν * m : ℤ) < (R.Q X P : ℤ) := by exact_mod_cast hmnat
        have hm'I : (R.ν * m' : ℤ) < (R.Q X P : ℤ) := by exact_mod_cast hm'nat
        omega
      · have hmnat : R.ν * m < R.Q X P := by exact_mod_cast hνm0
        have hm'nat : R.ν * m' < R.Q X P := by exact_mod_cast hνm'
        have hmI : (R.ν * m : ℤ) < (R.Q X P : ℤ) := by exact_mod_cast hmnat
        have hm'I : (R.ν * m' : ℤ) < (R.Q X P : ℤ) := by exact_mod_cast hm'nat
        omega
    have hz := Int.eq_zero_of_abs_lt_dvd hd habs
    have hmul : R.ν * m = R.ν * m' := by omega
    exact Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_of_lt R.one_le_ν) hmul
  have hparseSI :
      ∑ k ∈ range (R.Q X P),
          ‖∑ m ∈ R.I X, (Λ m : ℂ) * e ((R.ν * m : ℤ) * k / R.Q X P)‖ ^ 2 =
        (R.Q X P : ℝ) * ∑ m ∈ R.I X, ‖(Λ m : ℂ)‖ ^ 2 :=
    sum_norm_sq_sum_mul_e (R.I X) (fun m => (Λ m : ℂ))
      (fun m => (R.ν * m : ℤ)) (R.Q_pos X P) (by
        intro m hm m' hm' hd
        exact hdistinct m hm m' hm' hd)
  have hmatch :
      ∑ k ∈ range (R.Q X P), ‖R.SI X (k / R.Q X P)‖ ^ 2 =
        (R.Q X P : ℝ) * ∑ m ∈ R.I X, Λ m ^ 2 := by
    calc
      _ = ∑ k ∈ range (R.Q X P),
          ‖∑ m ∈ R.I X, (Λ m : ℂ) * e ((R.ν * m : ℤ) * k / R.Q X P)‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro k hk
        congr 2
        rw [SI]
        apply Finset.sum_congr rfl
        intro m hm
        congr 2
        push_cast
        ring
      _ = (R.Q X P : ℝ) * ∑ m ∈ R.I X, ‖(Λ m : ℂ)‖ ^ 2 := hparseSI
      _ = (R.Q X P : ℝ) * ∑ m ∈ R.I X, Λ m ^ 2 := by
        congr 1
        apply Finset.sum_congr rfl
        intro m hm
        simp only [Complex.norm_real, Real.norm_eq_abs]
        rw [sq_abs]
  rw [hmatch] at hsumF
  calc
    (1 / (R.Q X P : ℝ)) * ∑ k ∈ range (R.Q X P), ‖F k‖ ^ 2 ≤
        (1 / (R.Q X P : ℝ)) *
          (M ^ 2 * ((R.Q X P : ℝ) * ∑ m ∈ R.I X, Λ m ^ 2)) :=
      mul_le_mul_of_nonneg_left hsumF (by positivity)
    _ = M ^ 2 * ∑ m ∈ R.I X, Λ m ^ 2 := by
      field_simp [show (R.Q X P : ℝ) ≠ 0 by
        exact_mod_cast (R.Q_pos X P).ne']

/-! ### Vinogradov's bound on the minor arcs -/

/-- `SJ θ` is the difference of the two complete sums `∑_{n ≤ δX}` and `∑_{n ≤ ⌈γX⌉ - 1}`. -/
theorem SJ_eq_lambdaExpSum_sub (hX : 0 < X) (θ : ℝ) :
    R.SJ X θ = lambdaExpSum (R.δ * X) θ - lambdaExpSum ((⌈R.γ * X⌉₊ - 1 : ℕ) : ℝ) θ := by
  unfold SJ J lambdaExpSum
  rw [Nat.floor_natCast]
  set c := ⌈R.γ * X⌉₊
  have hc1 : 1 ≤ c := by
    dsimp [c]
    exact Nat.one_le_ceil_iff.mpr (mul_pos R.γ_pos hX)
  have hcF : c ≤ ⌊R.δ * X⌋₊ + 1 := by
    apply Nat.ceil_le.mpr
    have hlt : R.δ * X < (⌊R.δ * X⌋₊ : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have hγδ : R.γ * X ≤ R.δ * X := by
      gcongr
      exact le_of_lt R.γ_lt_δ
    exact hγδ.trans (by
      norm_num only [Nat.cast_add, Nat.cast_one]
      exact hlt.le)
  have hsum :
      (∑ x ∈ Icc c ⌊R.δ * X⌋₊, (Λ x : ℂ) * e (x * θ)) +
          ∑ x ∈ Icc 1 (c - 1), (Λ x : ℂ) * e (x * θ) =
        ∑ x ∈ Icc 1 ⌊R.δ * X⌋₊, (Λ x : ℂ) * e (x * θ) := by
    rw [← Finset.Ico_add_one_right_eq_Icc,
      ← Finset.Ico_add_one_right_eq_Icc 1 (c - 1),
      ← Finset.Ico_add_one_right_eq_Icc]
    rw [Nat.sub_add_cancel hc1]
    simpa [add_comm] using (Finset.sum_Ico_consecutive
      (fun x => (Λ x : ℂ) * e (x * θ)) hc1 hcF)
  rw [show Icc c ⌊R.δ * X⌋₊ = Ico c (⌊R.δ * X⌋₊ + 1) by
    rw [Finset.Ico_add_one_right_eq_Icc]]
  rw [show Icc 1 (c - 1) = Ico 1 c by
    rw [← Finset.Ico_add_one_right_eq_Icc]
    simp [Nat.sub_add_cancel hc1]]
  exact eq_sub_of_add_eq hsum

/-- `P ≤ X^{1/5}` when `P⁵ ≤ X`. -/
theorem le_rpow_one_div_five_of_pow_five_le {P : ℕ} {X : ℝ} (hP5 : (P : ℝ) ^ 5 ≤ X) :
    (P : ℝ) ≤ X ^ ((1 : ℝ) / 5) := by
  calc
    (P : ℝ) = ((P : ℝ) ^ (5 : ℕ)) ^ ((1 : ℝ) / 5) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    _ ≤ X ^ ((1 : ℝ) / 5) :=
      Real.rpow_le_rpow (by positivity) hP5 (by norm_num)

/-- `X^{4/5} ≤ X / √P` when `1 ≤ P` and `P⁵ ≤ X`. -/
theorem rpow_four_div_five_le_div_sqrt {P : ℕ} {X : ℝ} (hP : 1 ≤ P) (hP5 : (P : ℝ) ^ 5 ≤ X) :
    X ^ ((4 : ℝ) / 5) ≤ X / √P := by
  have hX0 : 0 ≤ X := by
    exact le_trans (by positivity) hP5
  have hsP : 0 < √(P : ℝ) := by positivity
  have hsqrtP : √(P : ℝ) ≤ (P : ℝ) := by
    have hP' : (1 : ℝ) ≤ P := by exact_mod_cast hP
    calc
      √(P : ℝ) ≤ √((P : ℝ) ^ 2) := by
        apply Real.sqrt_le_sqrt
        nlinarith
      _ = (P : ℝ) := by rw [Real.sqrt_sq (by positivity)]
  rw [le_div_iff₀ hsP]
  calc
    X ^ ((4 : ℝ) / 5) * √P ≤ X ^ ((4 : ℝ) / 5) * X ^ ((1 : ℝ) / 5) := by
      gcongr
      exact hsqrtP.trans (le_rpow_one_div_five_of_pow_five_le hP5)
    _ = X := by
      rw [← Real.rpow_add' hX0 (by norm_num)]
      norm_num

/-- **Vinogradov's bound in the minor-arc range.** If `2 ≤ x ≤ (δ + 1) X`, `P⁵ ≤ X` and
`α` is approximated by `a / q` with `P < q ≤ X / P`, then
`‖∑_{n ≤ x} Λ n e(nα)‖ ≤ 3 (δ + 1) C log((δ + 1) X)⁴ X / √P`. -/
theorem norm_lambdaExpSum_le_of_approx (hVM : VinogradovMinorArc) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x X : ℝ) (P q a : ℕ) (α : ℝ), 2 ≤ x → x ≤ (R.δ + 1) * X →
      1 ≤ P → (P : ℝ) ^ 5 ≤ X → P < q → (q : ℝ) ≤ X / P → Nat.Coprime a q →
      |α - a / q| ≤ 1 / (q : ℝ) ^ 2 →
        ‖lambdaExpSum x α‖ ≤ C * log ((R.δ + 1) * X) ^ 4 * X / √P := by
  obtain ⟨C, hC, h⟩ := hVM
  have hδ0 : 0 < R.δ := R.γ_pos.trans R.γ_lt_δ
  refine ⟨3 * (R.δ + 1) * C, by positivity, ?_⟩
  intro x X P q a α hx hxX hP hP5 hPq hqX hcop hα
  have hq0 : 0 < q := by omega
  have hb := h x hx α a q hq0 hcop hα
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hX0 : 0 < X := lt_of_lt_of_le (by positivity) hP5
  have hsP : 0 < √(P : ℝ) := Real.sqrt_pos.mpr hP0
  have hx0 : 0 < x := by linarith
  have hδ1 : (1 : ℝ) ≤ R.δ + 1 := by linarith
  have hPq' : (P : ℝ) ≤ q := by exact_mod_cast hPq.le
  have h1 : x / √(q : ℝ) ≤ (R.δ + 1) * X / √P := by
    calc
      x / √(q : ℝ) ≤ x / √(P : ℝ) :=
        div_le_div_of_nonneg_left hx0.le hsP (Real.sqrt_le_sqrt hPq')
      _ ≤ (R.δ + 1) * X / √P :=
        div_le_div_of_nonneg_right hxX hsP.le
  have h2 : x ^ ((4 : ℝ) / 5) ≤ (R.δ + 1) * X / √P := by
    calc
      x ^ ((4 : ℝ) / 5) ≤ ((R.δ + 1) * X) ^ ((4 : ℝ) / 5) :=
        Real.rpow_le_rpow hx0.le hxX (by norm_num)
      _ = (R.δ + 1) ^ ((4 : ℝ) / 5) * X ^ ((4 : ℝ) / 5) :=
        Real.mul_rpow (by positivity) hX0.le
      _ ≤ (R.δ + 1) * (X / √P) := by
        apply mul_le_mul _ (rpow_four_div_five_le_div_sqrt hP hP5)
          (by positivity) (by linarith)
        calc
          (R.δ + 1) ^ ((4 : ℝ) / 5) ≤ (R.δ + 1) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hδ1 (by norm_num)
          _ = R.δ + 1 := Real.rpow_one _
      _ = (R.δ + 1) * X / √P := by ring
  have h3 : √(x * q) ≤ (R.δ + 1) * X / √P := by
    have hxq : x * q ≤ ((R.δ + 1) * X) * (X / P) :=
      mul_le_mul hxX hqX (by positivity) (by positivity)
    have hsq :
        ((R.δ + 1) * X) * (X / P) =
          (√(R.δ + 1) * X / √P) ^ 2 := by
      field_simp [ne_of_gt hsP]
      rw [Real.sq_sqrt hP0.le, Real.sq_sqrt (by positivity)]
      ring
    calc
      √(x * q) ≤ √(((R.δ + 1) * X) * (X / P)) :=
        Real.sqrt_le_sqrt hxq
      _ = √(R.δ + 1) * X / √P := by
        rw [hsq, Real.sqrt_sq (by positivity)]
      _ ≤ (R.δ + 1) * X / √P := by
        gcongr
        calc
          √(R.δ + 1) ≤ √((R.δ + 1) ^ 2) := by
            apply Real.sqrt_le_sqrt
            nlinarith
          _ = R.δ + 1 := Real.sqrt_sq (by linarith)
  have hlog : log x ^ 4 ≤ log ((R.δ + 1) * X) ^ 4 :=
    pow_le_pow_left₀ (Real.log_nonneg (by linarith))
      (Real.log_le_log hx0 hxX) 4
  calc
    ‖lambdaExpSum x α‖ ≤
        C * log x ^ 4 * (x / √q + x ^ ((4 : ℝ) / 5) + √(x * q)) := hb
    _ ≤ C * log ((R.δ + 1) * X) ^ 4 *
        (3 * ((R.δ + 1) * X / √P)) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hlog hC.le) _ (by positivity)
        (by positivity)
      linarith
    _ = 3 * (R.δ + 1) * C * log ((R.δ + 1) * X) ^ 4 * X / √P := by ring

/-- **Vinogradov's bound on the minor arcs.** For `P⁵ ≤ X` and `X` large,
`‖SJ(k/Q)‖ ≤ C (log X)⁴ X / √P` for every minor-arc frequency `k`. -/
theorem exists_norm_SJ_le_of_mem_minorSet (hVM : VinogradovMinorArc) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop, ∀ P : ℕ, 1 ≤ P → (P : ℝ) ^ 5 ≤ X →
      X ≤ P * R.Q X P → ∀ k ∈ R.minorSet X P,
        ‖R.SJ X (k / R.Q X P)‖ ≤ C * log X ^ 4 * X / √P := by
  obtain ⟨C, hC, h⟩ := R.norm_lambdaExpSum_le_of_approx hVM
  refine ⟨32 * C, by positivity, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ),
    Filter.eventually_ge_atTop (3 / R.γ),
    Filter.eventually_ge_atTop (2 / R.δ),
    Real.tendsto_log_atTop.eventually_ge_atTop (Real.log (R.δ + 1))] with
    X hX1 hXγ hXδ hlog
  intro P hP hP5 hXPQ k hk
  have hδ0 : 0 < R.δ := R.γ_pos.trans R.γ_lt_δ
  have hX0 : 0 < X := lt_of_lt_of_le (by positivity) hP5
  have hP0 : (0 : ℝ) < P := by exact_mod_cast (Nat.zero_lt_of_lt hP)
  have hP_le_pow : (P : ℝ) ≤ (P : ℝ) ^ 5 := by
    exact le_self_pow₀ (by exact_mod_cast hP) (by norm_num)
  have hXP : (P : ℝ) ≤ X := hP_le_pow.trans hP5
  obtain ⟨q, a, hPq, hqX, hcop, happ⟩ :=
    R.exists_approx_of_mem_minorSet X P hP hXP hXPQ hk
  have hc1 : 1 ≤ ⌈R.γ * X⌉₊ := by
    exact Nat.one_le_ceil_iff.mpr (mul_pos R.γ_pos hX0)
  have hc3 : (3 : ℝ) ≤ R.γ * X := by
    have := (div_le_iff₀ R.γ_pos).mp hXγ
    nlinarith
  have hcminus : (2 : ℝ) ≤ (⌈R.γ * X⌉₊ - 1 : ℕ) := by
    rw [Nat.cast_sub hc1, Nat.cast_one]
    have hceil : R.γ * X ≤ (⌈R.γ * X⌉₊ : ℝ) := by
      exact_mod_cast Nat.le_ceil (R.γ * X)
    linarith
  have hδX : 2 ≤ R.δ * X := by
    have := (div_le_iff₀ hδ0).mp hXδ
    nlinarith
  have hbound (x : ℝ) (hx : 2 ≤ x) (hxupper : x ≤ (R.δ + 1) * X) :
      ‖lambdaExpSum x (k / R.Q X P)‖ ≤
        C * log ((R.δ + 1) * X) ^ 4 * X / √P := by
    apply h x X P q a (k / R.Q X P) hx hxupper hP hP5 hPq hqX hcop
    exact happ
  rw [R.SJ_eq_lambdaExpSum_sub X hX0]
  have hupper1 : R.δ * X ≤ (R.δ + 1) * X := by
    nlinarith [mul_nonneg (le_of_lt hδ0) hX0.le]
  have hceilupper : (⌈R.γ * X⌉₊ - 1 : ℕ) ≤ (R.δ + 1) * X := by
    rw [Nat.cast_sub hc1]
    have hceil : (⌈R.γ * X⌉₊ : ℝ) < R.γ * X + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have hγupper : R.γ * X ≤ (R.δ + 1) * X := by
      have hγδ : R.γ * X ≤ R.δ * X :=
        mul_le_mul_of_nonneg_right (le_of_lt R.γ_lt_δ) hX0.le
      exact hγδ.trans hupper1
    have hceilminus : (⌈R.γ * X⌉₊ : ℝ) - (1 : ℝ) < R.γ * X := by
      linarith [hceil]
    simpa only [Nat.cast_one] using le_of_lt (hceilminus.trans_le hγupper)
  have hb1 := hbound (R.δ * X) hδX hupper1
  have hb2 := hbound ((⌈R.γ * X⌉₊ - 1 : ℕ) : ℝ) hcminus hceilupper
  calc
    ‖lambdaExpSum (R.δ * X) (k / R.Q X P) -
          lambdaExpSum ((⌈R.γ * X⌉₊ - 1 : ℕ) : ℝ) (k / R.Q X P)‖ ≤
        ‖lambdaExpSum (R.δ * X) (k / R.Q X P)‖ +
          ‖lambdaExpSum ((⌈R.γ * X⌉₊ - 1 : ℕ) : ℝ)
            (k / R.Q X P)‖ := norm_sub_le _ _
    _ ≤ 2 * (C * log ((R.δ + 1) * X) ^ 4 * X / √P) := by
      linarith
    _ ≤ 32 * C * log X ^ 4 * X / √P := by
      have hlogX : 0 ≤ log X := Real.log_nonneg hX1
      have hlogD : 0 ≤ log (R.δ + 1) :=
        Real.log_nonneg (by linarith)
      have hDX1 : (1 : ℝ) ≤ (R.δ + 1) * X := by
        have hD1 : (1 : ℝ) ≤ R.δ + 1 := by linarith
        simpa using mul_le_mul hD1 hX1 (by positivity) (by linarith)
      have hlogDX0 : 0 ≤ log ((R.δ + 1) * X) :=
        Real.log_nonneg hDX1
      have hlogDX : log ((R.δ + 1) * X) ≤ 2 * log X := by
        rw [Real.log_mul (by linarith) (by linarith)]
        linarith
      have hpow : log ((R.δ + 1) * X) ^ 4 ≤ 16 * log X ^ 4 := by
        calc
          log ((R.δ + 1) * X) ^ 4 ≤ (2 * log X) ^ 4 :=
            pow_le_pow_left₀ hlogDX0 hlogDX 4
          _ = 16 * log X ^ 4 := by ring
      calc
        2 * (C * log ((R.δ + 1) * X) ^ 4 * X / √P) ≤
            2 * (C * (16 * log X ^ 4) * X / √P) := by
          gcongr
        _ = 32 * C * log X ^ 4 * X / √P := by ring

/-! ### The exceptional set of the minor arcs -/

/-- **Chebyshev/Markov for a finite family.** `#{N ∈ s | t ≤ f N} · t² ≤ ∑_{N ∈ s} f N ²`
for `t ≥ 0` and `f ≥ 0`. -/
theorem card_filter_le_mul_sq_le_sum_sq {s : Finset ℕ} {f : ℕ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hf : ∀ N ∈ s, 0 ≤ f N) :
    (#{N ∈ s | t ≤ f N} : ℝ) * t ^ 2 ≤ ∑ N ∈ s, f N ^ 2 := by
  calc
    (#{N ∈ s | t ≤ f N} : ℝ) * t ^ 2 =
        ∑ N ∈ s.filter (fun N => t ≤ f N), t ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ N ∈ s.filter (fun N => t ≤ f N), f N ^ 2 := by
      apply Finset.sum_le_sum
      intro N hN
      have hfN : 0 ≤ f N := hf N ((Finset.filter_subset _ _) hN)
      exact (sq_le_sq₀ ht hfN).mpr (Finset.mem_filter.mp hN).2
    _ ≤ ∑ N ∈ s, f N ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro N hN _
      exact sq_nonneg _

/-- `∑_{m ∈ I} Λ m ² ≤ βX (log (βX))²`. -/
theorem sum_I_vonMangoldt_sq_le (hX : 1 ≤ R.β * X) :
    ∑ m ∈ R.I X, Λ m ^ 2 ≤ R.β * X * log (R.β * X) ^ 2 := by
  have hβ : 0 < R.β := R.α_pos.trans R.α_lt_β
  have hX0 : 0 < X := by nlinarith
  have hα : 1 ≤ ⌈R.α * X⌉₊ :=
    Nat.one_le_ceil_iff.mpr (mul_pos R.α_pos hX0)
  have hsub : R.I X ⊆ Icc 1 ⌊R.β * X⌋₊ := by
    intro m hm
    have hm' : m ∈ Icc ⌈R.α * X⌉₊ ⌊R.β * X⌋₊ := by
      simpa [I] using hm
    exact Finset.mem_Icc.mpr ⟨hα.trans (Finset.mem_Icc.mp hm').1,
      (Finset.mem_Icc.mp hm').2⟩
  calc
    ∑ m ∈ R.I X, Λ m ^ 2 ≤
        ∑ m ∈ Icc 1 ⌊R.β * X⌋₊, Λ m ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro m hm _
      positivity
    _ ≤ R.β * X * log (R.β * X) ^ 2 :=
      sum_vonMangoldt_sq_le hX

/-- **Exceptional set of the minor arcs.** For `P⁵ ≤ X` and `X` large, the number of `N < Q`
with `‖minorSum N‖ ≥ ε X` is at most `C X (log X)¹⁰ / (ε² P)`. -/
theorem exists_card_minor_exceptional_le (hVM : VinogradovMinorArc) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop, ∀ P : ℕ, 1 ≤ P → (P : ℝ) ^ 5 ≤ X →
      X ≤ P * R.Q X P → ∀ ε : ℝ, 0 < ε →
        (#{N ∈ range (R.Q X P) | ε * X ≤ ‖R.minorSum X P N‖} : ℝ) ≤
          C * X * log X ^ 10 / (ε ^ 2 * P) := by
  obtain ⟨C₀, hC₀, hSJ⟩ := R.exists_norm_SJ_le_of_mem_minorSet hVM
  have hβ : 0 < R.β := R.α_pos.trans R.α_lt_β
  refine ⟨4 * R.β * C₀ ^ 2, by positivity, ?_⟩
  filter_upwards [hSJ, Filter.eventually_ge_atTop (1 : ℝ),
    Filter.eventually_ge_atTop (1 / R.β),
    Real.tendsto_log_atTop.eventually_ge_atTop (log R.β)] with X hSJX hX1 hXβ hlogβ
  intro P hP hP5 hPQ ε hε
  have hX0 : 0 < X := by linarith
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hβX : 1 ≤ R.β * X := by
    rw [div_le_iff₀ hβ] at hXβ
    linarith
  have hlogX : 0 ≤ log X := Real.log_nonneg hX1
  have hlogβX : log (R.β * X) ≤ 2 * log X := by
    rw [Real.log_mul hβ.ne' hX0.ne']
    linarith
  have hlogβX0 : 0 ≤ log (R.β * X) := Real.log_nonneg hβX
  have hlogsq : log (R.β * X) ^ 2 ≤ 4 * log X ^ 2 := by
    nlinarith
  set M : ℝ := C₀ * log X ^ 4 * X / √P with hMdef
  have hM0 : 0 ≤ M := by positivity
  have hpar := R.sum_norm_sq_minorSum_le X P hX0.le (hSJX P hP hP5 hPQ)
  have hmk := card_filter_le_mul_sq_le_sum_sq (s := range (R.Q X P))
    (f := fun N => ‖R.minorSum X P N‖) (t := ε * X) (by positivity)
    (fun _ _ => norm_nonneg _)
  have hΛ := R.sum_I_vonMangoldt_sq_le X hβX
  have hMsq : M ^ 2 = C₀ ^ 2 * log X ^ 8 * X ^ 2 / P := by
    rw [hMdef, div_pow, Real.sq_sqrt hP0.le]
    ring
  have hchain : (#{N ∈ range (R.Q X P) | ε * X ≤ ‖R.minorSum X P N‖} : ℝ) *
      (ε * X) ^ 2 ≤
      C₀ ^ 2 * log X ^ 8 * X ^ 2 / P * (R.β * X * (4 * log X ^ 2)) := by
    calc
      _ ≤ ∑ N ∈ range (R.Q X P), ‖R.minorSum X P N‖ ^ 2 := hmk
      _ ≤ M ^ 2 * ∑ m ∈ R.I X, Λ m ^ 2 := hpar
      _ ≤ M ^ 2 * (R.β * X * log (R.β * X) ^ 2) := by
        exact mul_le_mul_of_nonneg_left hΛ (sq_nonneg M)
      _ ≤ M ^ 2 * (R.β * X * (4 * log X ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg M)
        exact mul_le_mul_of_nonneg_left hlogsq
          (mul_nonneg hβ.le hX0.le)
      _ = _ := by rw [hMsq]
  rw [le_div_iff₀ (by positivity)]
  have hεX : 0 < (ε * X) ^ 2 := by positivity
  have hcard : (#{N ∈ range (R.Q X P) | ε * X ≤ ‖R.minorSum X P N‖} : ℝ) ≤
      C₀ ^ 2 * log X ^ 8 * X ^ 2 / P * (R.β * X * (4 * log X ^ 2)) /
        (ε * X) ^ 2 :=
    (le_div_iff₀ hεX).mpr hchain
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 4 * R.β * C₀ ^ 2 * X * log X ^ 10 := by
      field_simp [hP0.ne', hε.ne', hX0.ne']

end Ranges

end CircleMethod
