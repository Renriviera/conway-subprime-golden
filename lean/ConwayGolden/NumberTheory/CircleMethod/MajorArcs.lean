/-
Copyright (c) 2026 Romain Popescu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Romain Popescu
-/
import ConwayGolden.NumberTheory.CircleMethod.SingularIntegral
import ConwayGolden.NumberTheory.CircleMethod.SingularSeries

/-!
# The major arcs

On the major arc around `a / q` (with `q ≤ P`, `(a, q) = 1`), Siegel–Walfisz and summation by
parts give

`SJ(a/q + β) = μ(q) / φ(q) · TJ(β) + O(q P X (log X)⁻ᴬ)`,
`SI(a/q + β) = c_q(ν) / φ(q) · TI(β) + O(q P X (log X)⁻ᴬ)`,

uniformly for `|β| ≤ 2 P / X`. Summing the products of the main terms over the arcs and using
`∑_{(a, q) = 1} e (-N a / q) = c_q(N)` yields exactly `𝔖_P(N) · W(N)`, where `𝔖_P` is the
truncated singular series and `W` the discrete singular integral.

## Main definitions

* `Ranges.majorSum R X P N`: the contribution of the major arcs to `rep N`.
* `Ranges.minorSum R X P N`: the contribution of the minor arcs to `rep N`.

## Main statements

* `Ranges.rep_eq_majorSum_add_minorSum`: `rep N = majorSum N + minorSum N`.
* `Ranges.exists_SJ_approx`, `Ranges.exists_SI_approx`: the Siegel–Walfisz approximations.
* `Ranges.sum_main_eq`: the exact evaluation of the main terms as `𝔖_P(N) · W(N)`.
* `Ranges.exists_norm_majorSum_sub_le`:
  `‖majorSum N - 𝔖_P(N) W(N)‖ ≤ C P⁵ X (log X + 1) / (log X)^A` for large `X`.

## References

* [H. Davenport, *Multiplicative number theory*, Chapter 26][Davenport2000]
-/

namespace CircleMethod

namespace Ranges

open Filter Finset Real
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt

variable (R : Ranges) (X : ℝ) (P : ℕ)

/-! ### Splitting `rep` into arcs -/

/-- The contribution of the major arcs to `rep N`. -/
noncomputable def majorSum (N : ℕ) : ℂ :=
  (1 / (R.Q X P : ℂ)) * ∑ qa ∈ arcIndex P,
    ∑ j ∈ Icc (-(R.halfWidth X P : ℤ)) (R.halfWidth X P),
      R.SI X (R.arcAngle X P qa j) * R.SJ X (R.arcAngle X P qa j) *
        e (-(N * R.arcAngle X P qa j))

/-- The contribution of the minor arcs to `rep N`. -/
noncomputable def minorSum (N : ℕ) : ℂ :=
  (1 / (R.Q X P : ℂ)) * ∑ k ∈ R.minorSet X P,
    R.SI X (k / R.Q X P) * R.SJ X (k / R.Q X P) * e (-(N * k / R.Q X P))

theorem rep_eq_majorSum_add_minorSum (hP : 1 ≤ P) (hX : 8 * (P : ℝ) ^ 3 ≤ X)
    {N : ℕ} (hN : (N : ℝ) ≤ R.B * X) :
    (R.rep X N : ℂ) = R.majorSum X P N + R.minorSum X P N := by
  have hX0 : 0 ≤ X := by
    have hP0 : (0 : ℝ) < P := by exact_mod_cast (Nat.zero_lt_of_lt hP)
    nlinarith [pow_pos hP0 3]
  rw [R.rep_eq_sum X P hX0 hN]
  let F : ℝ → ℂ := fun θ => R.SI X θ * R.SJ X θ * e (-(N * θ))
  have hF : ∀ θ, F (θ + 1) = F θ := by
    intro θ
    simp only [F, R.SI_add_one, R.SJ_add_one]
    rw [show -(N * (θ + 1)) = -(N * θ) + ((-N : ℤ) : ℝ) by
      push_cast
      ring, e_add_intCast]
  have hsum :
      (∑ k ∈ range (R.Q X P),
          R.SI X (k / R.Q X P) * R.SJ X (k / R.Q X P) *
            e (-(N * k / R.Q X P))) =
        ∑ k ∈ range (R.Q X P), F (k / R.Q X P) := by
    apply Finset.sum_congr rfl
    intro k hk
    simp only [F, mul_div_assoc]
  rw [hsum, R.sum_range_Q_eq X P F hF hP hX, mul_add]
  unfold majorSum minorSum
  simp only [F, mul_div_assoc]

/-! ### Residue-class decomposition -/

/-- Splitting a weighted exponential sum `∑ h n · e (n a / q)` by the residue of `n` mod `q`. -/
theorem sum_mul_e_div_eq_sum_range {q : ℕ} (hq : 0 < q) (a : ℕ) (s : Finset ℕ) (h : ℕ → ℂ) :
    ∑ n ∈ s, h n * e (n * a / q) =
      ∑ r ∈ range q, e (r * a / q) * ∑ n ∈ s with n % q = r, h n := by
  classical
  have hmaps : ∀ n ∈ s, n % q ∈ range q := by
    intro n hn
    exact mem_range.mpr (Nat.mod_lt _ hq)
  have hfiber :
      ∑ r ∈ range q, ∑ n ∈ s with n % q = r, h n * e (n * a / q) =
        ∑ n ∈ s, h n * e (n * a / q) :=
    Finset.sum_fiberwise_of_maps_to hmaps _
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnr : n % q = r := (Finset.mem_filter.mp hn).2
  let k : ℕ := (n / q) * a
  have heq : (n * a / q : ℝ) =
      r * a / q + (k : ℝ) := by
    have hmod : n % q + q * (n / q) = n := Nat.mod_add_div n q
    rw [hnr] at hmod
    have hmodR : (n : ℝ) = r + q * (n / q : ℕ) := by
      exact_mod_cast hmod.symm
    rw [hmodR]
    dsimp [k]
    field_simp
    norm_num [Nat.cast_mul]
    ring
  rw [heq]
  change h n * e (r * a / q + (k : ℝ)) = _
  have hk : (k : ℝ) = ((k : ℤ) : ℝ) := by norm_num
  rw [hk, e_add_intCast]
  ring

/-- The residue classes `r` with `(r, q) > 1` carry mass at most `q log x`. -/
theorem sum_not_coprime_norm_le {x : ℝ} (hx : 1 ≤ x) {q : ℕ} (hq : 0 < q) {s : Finset ℕ}
    (hs : s ⊆ Icc 1 ⌊x⌋₊) (h : ℕ → ℂ) (hh : ∀ n, ‖h n‖ ≤ 1) :
    ∑ r ∈ range q with ¬ Nat.Coprime r q, ‖∑ n ∈ s with n % q = r, (Λ n : ℂ) * h n‖ ≤
      q * log x := by
  classical
  let t := s.filter (fun n => ¬ Nat.Coprime (n % q) q)
  have hmaps : ∀ n ∈ t, n % q ∈ range q := by
    intro n hn
    exact mem_range.mpr (Nat.mod_lt _ hq)
  have hterm (r : ℕ) (hr : r ∈ range q) (hrc : ¬ Nat.Coprime r q) :
      ‖∑ n ∈ s with n % q = r, (Λ n : ℂ) * h n‖ ≤
        ∑ n ∈ s with n % q = r, Λ n := by
    calc
      _ ≤ ∑ n ∈ s with n % q = r, ‖(Λ n : ℂ) * h n‖ :=
        norm_sum_le _ _
      _ = ∑ n ∈ s with n % q = r, Λ n * ‖h n‖ := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [norm_mul, Complex.norm_real]
        simp [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro n hn
        exact mul_le_of_le_one_right (ArithmeticFunction.vonMangoldt_nonneg) (hh n)
  calc
    _ ≤ ∑ r ∈ range q with ¬ Nat.Coprime r q,
        ∑ n ∈ s with n % q = r, Λ n := by
      apply Finset.sum_le_sum
      intro r hr
      exact hterm r (Finset.mem_filter.mp hr).1 (Finset.mem_filter.mp hr).2
    _ = ∑ n ∈ t, Λ n := by
      rw [← Finset.sum_fiberwise_of_maps_to hmaps]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro r hr
      by_cases hrc : Nat.Coprime r q
      · have heq : t.filter (fun n => n % q = r) = ∅ := by
          ext n
          simp only [Finset.mem_filter]
          simp
          intro hn
          rcases Finset.mem_filter.mp hn with ⟨hns, hnc⟩
          intro hnr
          exact hnc (by simpa [hnr] using hrc)
        rw [if_neg (not_not.mpr hrc)]
        rw [heq]
        simp
      · rw [if_pos hrc]
        have heq :
            s.filter (fun n => n % q = r) =
              t.filter (fun n => n % q = r) := by
          ext n
          simp only [Finset.mem_filter, t]
          constructor
          · rintro ⟨hns, hnr⟩
            exact ⟨⟨hns, by simpa [hnr] using hrc⟩, hnr⟩
          · rintro ⟨⟨hns, hnc⟩, hnr⟩
            exact ⟨hns, hnr⟩
        rw [heq]
    _ ≤ ∑ n ∈ Icc 1 ⌊x⌋₊ with ¬ Nat.Coprime n q, Λ n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        rcases Finset.mem_filter.mp hn with ⟨hns, hnc⟩
        refine Finset.mem_filter.mpr ⟨hs hns, ?_⟩
        rw [Nat.coprime_iff_gcd_eq_one] at hnc ⊢
        rw [Nat.gcd_comm n q, Nat.gcd_rec q n]
        exact hnc
      · intro n hn _
        exact ArithmeticFunction.vonMangoldt_nonneg
    _ ≤ q * log x := sum_vonMangoldt_not_coprime_le hx hq

/-- **Abel summation against `ψ(n; q, r) - n / φ(q)`.** If `|ψ(n; q, r) - n / φ(q)| ≤ D` for
`lo - 1 ≤ n ≤ hi`, the residue class `r` of `∑_{lo ≤ n ≤ hi} Λ n · e (c n β)` differs from
`φ(q)⁻¹ ∑_{lo ≤ n ≤ hi} e (c n β)` by at most `2 D (1 + 2 π c |β| (hi + 1 - lo))`. -/
theorem norm_sum_filter_sub_le {q r : ℕ} (hr : r < q) {lo hi : ℕ} (hlo : 1 ≤ lo)
    (hlohi : lo ≤ hi + 1) {D : ℝ}
    (hD : ∀ n ∈ Icc (lo - 1) hi, |psiMod n q r - n / q.totient| ≤ D) (c : ℕ) (β : ℝ) :
    ‖∑ n ∈ Icc lo hi with n % q = r, (Λ n : ℂ) * e (c * n * β) -
        (1 / (q.totient : ℂ)) * ∑ n ∈ Icc lo hi, e (c * n * β)‖ ≤
      2 * D * (1 + 2 * π * c * |β| * (hi + 1 - lo)) := by
  let f : ℕ → ℂ := fun n => if n % q = r then (Λ n : ℂ) else 0
  let g : ℕ → ℂ := fun _ => 1 / (q.totient : ℂ)
  let v : ℕ → ℂ := fun n => e (c * n * β)
  have hIcc : Icc lo hi = Ioc (lo - 1) hi := by
    ext n
    simp only [mem_Icc, mem_Ioc]
    omega
  have hrewrite :
      (∑ n ∈ Icc lo hi with n % q = r, (Λ n : ℂ) * e (c * n * β)) -
          (1 / (q.totient : ℂ)) * ∑ n ∈ Icc lo hi, e (c * n * β) =
        ∑ n ∈ Icc lo hi, (f n - g n) * v n := by
    rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [f, g, v]
    split_ifs <;> ring
  have hpartial (n : ℕ) (hn : n ∈ Icc (lo - 1) hi) :
      ‖∑ m ∈ Icc 1 n, f m - ∑ m ∈ Icc 1 n, g m‖ ≤ D := by
    have hpsi :
        ∑ m ∈ Icc 1 n, f m = ((psiMod n q r : ℝ) : ℂ) := by
      unfold psiMod
      rw [Nat.floor_natCast, Finset.sum_filter]
      push_cast
      apply Finset.sum_congr rfl
      intro m hm
      simp only [f, Nat.ModEq, Nat.mod_eq_of_lt hr]
      split_ifs <;> simp
    have hg :
        ∑ m ∈ Icc 1 n, g m = (n : ℂ) / q.totient := by
      simp only [g, Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
      rw [Nat.add_sub_cancel]
      ring
    rw [hpsi, hg]
    have hcast :
        ((psiMod n q r : ℝ) : ℂ) - (n : ℂ) / q.totient =
          ((psiMod n q r - n / q.totient : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs]
    exact hD n hn
  have habel := norm_sum_Ioc_sub_mul_le f g v (by omega) hpartial
  rw [hrewrite, hIcc]
  calc
    _ ≤ 2 * D * (‖v hi‖ + ∑ n ∈ Ico (lo - 1) hi, ‖v (n + 1) - v n‖) := habel
    _ = 2 * D * (1 + ∑ n ∈ Ico (lo - 1) hi,
        ‖e (c * β) - 1‖) := by
      apply congrArg (fun z : ℝ => 2 * D * z)
      rw [show v hi = e (c * hi * β) by rfl, norm_e]
      apply congrArg₂ (· + ·) rfl
      apply Finset.sum_congr rfl
      intro n hn
      dsimp [v]
      push_cast
      rw [show c * (n + 1) * β = c * n * β + c * β by ring, e_add]
      rw [show e (c * n * β) * e (c * β) - e (c * n * β) =
          e (c * n * β) * (e (c * β) - 1) by ring]
      rw [norm_mul, norm_e, one_mul]
  have hvar : ∀ n ∈ Ico (lo - 1) hi, ‖e (c * β) - 1‖ ≤
      2 * π * c * |β| := by
    intro n hn
    calc
      ‖e (c * β) - 1‖ ≤ 2 * π * |c * β| := norm_e_sub_one_le _
      _ = 2 * π * c * |β| := by
        rw [abs_mul, Nat.abs_cast]
        ring
  have hsum :
      (∑ n ∈ Ico (lo - 1) hi, ‖e (c * β) - 1‖ : ℝ) ≤
        2 * π * c * |β| * (hi + 1 - lo) := by
    calc
      _ ≤ (Ico (lo - 1) hi).card • (2 * π * c * |β|) :=
        Finset.sum_le_card_nsmul _ _ _ hvar
      _ = (2 * π * c * |β|) * (hi + 1 - lo) := by
        simp [nsmul_eq_mul, Nat.card_Ico]
        rw [Nat.cast_sub (by omega)]
        rw [Nat.cast_sub hlo]
        push_cast
        ring
  have hD0 : 0 ≤ D := by
    exact (abs_nonneg _).trans (hD (lo - 1) (mem_Icc.mpr ⟨le_rfl, by omega⟩))
  calc
    2 * D * (1 + ∑ n ∈ Ico (lo - 1) hi, ‖e (c * β) - 1‖) ≤
        2 * D * (1 + 2 * π * c * |β| * (hi + 1 - lo)) :=
      mul_le_mul_of_nonneg_left (by simpa [add_comm] using add_le_add_left hsum 1)
        (by positivity)
    _ = 2 * D * (1 + 2 * π * c * |β| * (hi + 1 - lo)) := rfl

/-- **Generic major-arc approximation.** For `(a, q) = 1` and an interval `[lo, hi] ⊆ [1, x]`,
`∑_{lo ≤ n ≤ hi} Λ n · e (n c a / q) · e (c n β)` equals `c_q(c)/φ(q) · ∑ e (c n β)` up to
`q log x + q · 2 D (1 + 2 π c |β| (hi + 1 - lo))`, where `D` bounds the Siegel–Walfisz error on
the coprime residue classes. -/
theorem norm_sum_Icc_sub_le {q a : ℕ} (hq : 0 < q) (ha : Nat.Coprime a q) {lo hi : ℕ}
    (hlo : 1 ≤ lo) (hlohi : lo ≤ hi + 1) {x : ℝ} (hx : 1 ≤ x) (hhi : (hi : ℝ) ≤ x) {D : ℝ}
    (hD : ∀ r, r < q → Nat.Coprime r q →
      ∀ n ∈ Icc (lo - 1) hi, |psiMod n q r - n / q.totient| ≤ D) (c : ℕ) (β : ℝ) :
    ‖∑ n ∈ Icc lo hi, (Λ n : ℂ) * e (n * (c * a) / q) * e (c * n * β) -
        ((ramanujanSum q c / q.totient : ℝ) : ℂ) * ∑ n ∈ Icc lo hi, e (c * n * β)‖ ≤
      q * log x + q * (2 * D * (1 + 2 * π * c * |β| * (hi + 1 - lo))) := by
  classical
  let T : ℂ := ∑ n ∈ Icc lo hi, e (c * n * β)
  let h : ℕ → ℂ := fun n => (Λ n : ℂ) * e (c * n * β)
  have hfirst :
      ∑ n ∈ Icc lo hi, (Λ n : ℂ) * e (n * (c * a) / q) * e (c * n * β) =
        ∑ r ∈ range q, e (r * (c * a) / q) *
          ∑ n ∈ Icc lo hi with n % q = r, h n := by
    calc
      _ = ∑ n ∈ Icc lo hi, h n * e (n * (c * a) / q) := by
        apply Finset.sum_congr rfl
        intro n hn
        dsimp [h]
        ring
      _ = _ := by
        convert sum_mul_e_div_eq_sum_range hq (c * a) (Icc lo hi) h using 1 <;>
          push_cast <;> ring
  have hram :
      ∑ r ∈ coprimeRange q, e (r * (c * a) / q) =
        (ramanujanSum q c : ℂ) := by
    calc
      _ = ∑ r ∈ coprimeRange q, e (r * (c * a : ℕ) / q) := by
        apply Finset.sum_congr rfl
        intro r hr
        congr 1
        push_cast
        ring
      _ = (ramanujanSum q (c * a) : ℂ) := sum_e_coprimeRange hq (c * a)
      _ = (ramanujanSum q c : ℂ) := by
        rw [show c * a = c * a by rfl, ramanujanSum_mul_of_coprime_right ha c]
  have hcoef :
      ((ramanujanSum q c / q.totient : ℝ) : ℂ) =
        (1 / (q.totient : ℂ)) * ∑ r ∈ coprimeRange q, e (r * (c * a) / q) := by
    rw [hram]
    push_cast
    ring
  have hcoefT :
      ((ramanujanSum q c / q.totient : ℝ) : ℂ) * T =
        ∑ r ∈ coprimeRange q, e (r * (c * a) / q) *
          ((1 / (q.totient : ℂ)) * T) := by
    rw [hcoef]
    calc
      (1 / (q.totient : ℂ) * ∑ r ∈ coprimeRange q,
          e (r * (c * a) / q)) * T =
          (1 / (q.totient : ℂ)) *
            (∑ r ∈ coprimeRange q, e (r * (c * a) / q) * T) := by
        calc
          _ = (1 / (q.totient : ℂ)) *
              ((∑ r ∈ coprimeRange q, e (r * (c * a) / q)) * T) := by ring
          _ = _ := by rw [Finset.sum_mul]
      _ = ∑ r ∈ coprimeRange q,
            (1 / (q.totient : ℂ) * e (r * (c * a) / q)) * T := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        ring
      _ = _ := by
        apply Finset.sum_congr rfl
        intro r hr
        ring
  have heq :
      (∑ r ∈ range q, e (r * (c * a) / q) *
          ∑ n ∈ Icc lo hi with n % q = r, h n) -
          ((ramanujanSum q c / q.totient : ℝ) : ℂ) * T =
        (∑ r ∈ coprimeRange q, e (r * (c * a) / q) *
            (∑ n ∈ Icc lo hi with n % q = r, h n - (1 / (q.totient : ℂ)) * T)) +
          ∑ r ∈ range q with ¬ Nat.Coprime r q,
            e (r * (c * a) / q) * ∑ n ∈ Icc lo hi with n % q = r, h n := by
    have hcomm :
        ∑ r ∈ range q with Nat.Coprime r q, e (r * (c * a) / q) *
            (1 / (q.totient : ℂ) * T) =
          ∑ r ∈ range q with Nat.Coprime r q, e (r * (c * a) / q) *
            (1 / (q.totient : ℂ)) * T := by
      apply Finset.sum_congr rfl
      intro r hr
      ring
    rw [← Finset.sum_filter_add_sum_filter_not (range q)
      (fun r => Nat.Coprime r q)]
    rw [hcoefT]
    simp only [coprimeRange]
    calc
      _ = (∑ r ∈ range q with Nat.Coprime r q,
            e (r * (c * a) / q) * ∑ n ∈ Icc lo hi with n % q = r, h n -
              ∑ r ∈ range q with Nat.Coprime r q,
                e (r * (c * a) / q) * (1 / (q.totient : ℂ)) * T) +
          ∑ r ∈ range q with ¬ Nat.Coprime r q,
            e (r * (c * a) / q) * ∑ n ∈ Icc lo hi with n % q = r, h n := by
        rw [hcomm]
        ring
      _ = _ := by
        rw [← Finset.sum_sub_distrib]
        apply congrArg₂ (· + ·)
        · apply Finset.sum_congr rfl
          intro r hr
          ring
        · rfl
  rw [hfirst, heq]
  have hcop :
      ∑ r ∈ coprimeRange q, ‖∑ n ∈ Icc lo hi with n % q = r, h n -
          (1 / (q.totient : ℂ)) * T‖ ≤
        q * (2 * D * (1 + 2 * π * c * |β| * (hi + 1 - lo))) := by
    calc
      _ ≤ ∑ r ∈ coprimeRange q, 2 * D * (1 + 2 * π * c * |β| *
          (hi + 1 - lo)) := by
        apply Finset.sum_le_sum
        intro r hr
        exact norm_sum_filter_sub_le (mem_coprimeRange.mp hr).1 hlo hlohi
          (hD r (mem_coprimeRange.mp hr).1 (mem_coprimeRange.mp hr).2) c β
      _ = (q.totient : ℝ) * (2 * D * (1 + 2 * π * c * |β| *
          (hi + 1 - lo))) := by simp [nsmul_eq_mul, card_coprimeRange]
      _ ≤ q * (2 * D * (1 + 2 * π * c * |β| * (hi + 1 - lo))) := by
        apply mul_le_mul_of_nonneg_right
          (by exact_mod_cast Nat.totient_le q)
        have hr : 1 % q < q := Nat.mod_lt _ hq
        have hrc : Nat.Coprime (1 % q) q :=
          (ZMod.coprime_mod_iff_coprime 1 q).2 (Nat.coprime_one_left q)
        have hb := norm_sum_filter_sub_le hr hlo hlohi
          (hD (1 % q) hr hrc) c β
        exact (norm_nonneg _).trans hb
  have hs : Icc lo hi ⊆ Icc 1 ⌊x⌋₊ := by
    intro n hn
    refine mem_Icc.mpr ⟨hlo.trans (mem_Icc.mp hn).1, ?_⟩
    apply Nat.le_floor
    calc
      (n : ℝ) ≤ hi := by exact_mod_cast (mem_Icc.mp hn).2
      _ ≤ x := hhi
  have hnon :
      ∑ r ∈ range q with ¬ Nat.Coprime r q,
          ‖∑ n ∈ Icc lo hi with n % q = r, h n‖ ≤ q * log x := by
    apply sum_not_coprime_norm_le hx hq hs
      (fun n => e (c * n * β))
    intro n
    simp [norm_e]
  calc
    ‖(∑ r ∈ coprimeRange q, e (r * (c * a) / q) *
          (∑ n ∈ Icc lo hi with n % q = r, h n -
            (1 / (q.totient : ℂ)) * T)) +
        ∑ r ∈ range q with ¬ Nat.Coprime r q,
          e (r * (c * a) / q) * ∑ n ∈ Icc lo hi with n % q = r, h n‖ ≤
      ∑ r ∈ coprimeRange q, ‖∑ n ∈ Icc lo hi with n % q = r, h n -
          (1 / (q.totient : ℂ)) * T‖ +
        ∑ r ∈ range q with ¬ Nat.Coprime r q,
          ‖∑ n ∈ Icc lo hi with n % q = r, h n‖ := by
      calc
        _ ≤ ‖∑ r ∈ coprimeRange q, e (r * (c * a) / q) *
            (∑ n ∈ Icc lo hi with n % q = r, h n -
              (1 / (q.totient : ℂ)) * T)‖ +
            ‖∑ r ∈ range q with ¬ Nat.Coprime r q,
              e (r * (c * a) / q) * ∑ n ∈ Icc lo hi with n % q = r, h n‖ :=
          norm_add_le _ _
        _ ≤ _ := by
          gcongr
          · calc
              _ ≤ ∑ r ∈ coprimeRange q,
                  ‖e (r * (c * a) / q) *
                    (∑ n ∈ Icc lo hi with n % q = r, h n -
                      (1 / (q.totient : ℂ)) * T)‖ := norm_sum_le _ _
              _ ≤ _ := by
                apply Finset.sum_le_sum
                intro r hr
                rw [norm_mul, norm_e, one_mul]
          · calc
              _ ≤ ∑ r ∈ range q with ¬ Nat.Coprime r q,
                  ‖e (r * (c * a) / q) *
                    ∑ n ∈ Icc lo hi with n % q = r, h n‖ := norm_sum_le _ _
              _ ≤ _ := by
                apply Finset.sum_le_sum
                intro r hr
                rw [norm_mul, norm_e, one_mul]
    _ ≤ q * (2 * D * (1 + 2 * π * c * |β| * (hi + 1 - lo))) + q * log x :=
      add_le_add hcop hnon
    _ = q * log x + q * (2 * D * (1 + 2 * π * c * |β| * (hi + 1 - lo))) := by
      ring

/-! ### Siegel–Walfisz on a major arc -/

private theorem eventually_log_pow_le (n : ℕ) :
    ∀ᶠ X : ℝ in atTop, log X ^ n ≤ X := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := n)).def one_pos
  filter_upwards [h, Filter.eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (0 : ℝ)] with X hX hXpos hlog
  simpa [Real.norm_eq_abs, abs_pow, abs_of_nonneg hlog, abs_of_pos hXpos] using hX

private theorem eventually_log_mul_rpow_le {c A : ℝ} (hc : 0 < c) :
    ∀ᶠ X : ℝ in atTop, log (c * X) * log X ^ A ≤ X := by
  let n := ⌈A⌉₊ + 2
  filter_upwards [eventually_log_pow_le n,
    Real.tendsto_log_atTop.eventually_ge_atTop (max 2 (log c)),
    Filter.eventually_gt_atTop (0 : ℝ)] with X hpow hlog hX
  have hlogX : 2 ≤ log X := le_max_left _ _ |>.trans hlog
  have hlogc : log c ≤ log X := le_trans (le_max_right _ _) hlog
  have hcx : 0 < c * X := mul_pos hc hX
  have hlogmul : log (c * X) ≤ 2 * log X := by
    rw [Real.log_mul (ne_of_gt hc) (ne_of_gt hX)]
    linarith
  have hAceil : A ≤ (⌈A⌉₊ : ℝ) := by exact_mod_cast Nat.le_ceil A
  have hpowA : log X ^ A ≤ log X ^ (⌈A⌉₊ : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) hAceil
  rw [Real.rpow_natCast] at hpowA
  have hmul : log (c * X) * log X ^ A ≤
      2 * log X ^ (⌈A⌉₊ + 1) := by
    calc
      _ ≤ (2 * log X) * log X ^ A :=
        mul_le_mul_of_nonneg_right hlogmul (Real.rpow_nonneg (by linarith) _)
      _ ≤ (2 * log X) * log X ^ ⌈A⌉₊ :=
        mul_le_mul_of_nonneg_left hpowA (by linarith)
      _ = 2 * log X ^ (⌈A⌉₊ + 1) := by
        rw [pow_succ]
        ring
  have hpow' : 2 * log X ^ (⌈A⌉₊ + 1) ≤ log X ^ n := by
    dsimp [n]
    have hp : 0 ≤ log X ^ (⌈A⌉₊ + 1) := by positivity
    calc
      2 * log X ^ (⌈A⌉₊ + 1) ≤ log X ^ (⌈A⌉₊ + 1) * log X := by
        nlinarith
      _ = log X ^ (⌈A⌉₊ + 2) := by
        rw [pow_succ]
        ring
  exact hmul.trans (hpow'.trans hpow)

/-- **Siegel–Walfisz on `[c₀ X, c₁ X]` with `q ≤ (log X)^A`.** The loss from `log n` versus
`log X` is absorbed by applying the hypothesis with exponent `2 A`. -/
theorem exists_psiMod_sub_le (hSW : SiegelWalfisz) {A : ℝ} (hA : 0 < A) {c₀ c₁ : ℝ}
    (hc₀ : 0 < c₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop, ∀ q r : ℕ, 0 < q → (q : ℝ) ≤ log X ^ A →
      Nat.Coprime r q → ∀ n : ℕ, c₀ * X ≤ n → (n : ℝ) ≤ c₁ * X →
        |psiMod n q r - n / q.totient| ≤ C * X / log X ^ A := by
  obtain ⟨C₂, hC₂, hSW'⟩ := hSW (2 * A) (by positivity)
  refine ⟨C₂ * max c₁ 1, by positivity, ?_⟩
  have hlog : ∀ᶠ X : ℝ in atTop, 4 ≤ log X ∧ -2 * log c₀ ≤ log X := by
    filter_upwards [
      (Real.tendsto_log_atTop.eventually_ge_atTop 4),
      (Real.tendsto_log_atTop.eventually_ge_atTop (-2 * log c₀))] with X hX₁ hX₂
    exact ⟨hX₁, hX₂⟩
  have hmain : ∀ᶠ X : ℝ in atTop, 2 ≤ c₀ * X ∧ 1 ≤ X := by
    filter_upwards [
      (eventually_ge_atTop (2 / c₀)),
      (eventually_ge_atTop (1 : ℝ))] with X hX₁ hX₂
    constructor
    · have : 2 / c₀ ≤ X := hX₁
      calc
        2 = c₀ * (2 / c₀) := by field_simp
        _ ≤ c₀ * X := mul_le_mul_of_nonneg_left this hc₀.le
    · exact hX₂
  filter_upwards [hlog, hmain] with X hlogX hmainX
  intro q r hq hqX hr n hnl hnu
  have hX0 : 0 ≤ X := by nlinarith [hmainX.2]
  have hcn : 2 ≤ (n : ℝ) := by
    have : 2 ≤ c₀ * X := hmainX.1
    nlinarith [hc₀]
  have hlogn : log (c₀ * X) ≤ log (n : ℝ) := by
    apply Real.log_le_log
    · exact mul_pos hc₀ (by nlinarith [hmainX.2])
    · exact_mod_cast hnl
  have hlogX0 : 0 ≤ log X := Real.log_nonneg (by nlinarith [hmainX.2])
  have hlogc : log (c₀ * X) = log c₀ + log X := by
    rw [Real.log_mul (ne_of_gt hc₀) (ne_of_gt (by nlinarith : 0 < X))]
  have hsqrt : √(log X) ≤ log (c₀ * X) := by
    rw [hlogc]
    rw [Real.sqrt_le_iff]
    constructor
    · nlinarith [hlogX.1, Real.sqrt_nonneg (log X)]
    · nlinarith [hlogX.1, hlogX.2]
  have hsqrt_n : √(log X) ≤ log (n : ℝ) := hsqrt.trans hlogn
  have hlogn0 : 0 ≤ log (n : ℝ) := Real.log_nonneg (by nlinarith [hcn])
  have hlog_sq : log X ≤ log (n : ℝ) ^ 2 := by
    nlinarith [Real.sq_sqrt hlogX0, sq_nonneg (√(log X) - log (n : ℝ))]
  have hpow : log X ^ A ≤ log (n : ℝ) ^ (2 * A) := by
    have hlogn_pos : 0 < log (n : ℝ) := Real.log_pos (by nlinarith [hcn])
    calc
      log X ^ A ≤ (log (n : ℝ) ^ 2) ^ A :=
        Real.rpow_le_rpow hlogX0 hlog_sq hA.le
      _ = log (n : ℝ) ^ (2 * A) := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul hlogn_pos.le]
        norm_num
  have hqXn : (q : ℝ) ≤ log (n : ℝ) ^ (2 * A) := hqX.trans hpow
  have hSWn := hSW' (n : ℝ) hcn q r hq hqXn hr
  have hnupper : (n : ℝ) ≤ max c₁ 1 * X := by
    calc
      (n : ℝ) ≤ c₁ * X := hnu
      _ ≤ max c₁ 1 * X := by
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) hX0
  have hdenX : 0 < log X ^ A :=
    Real.rpow_pos_of_pos (by nlinarith [hlogX.1]) _
  have hdenn : 0 < log (n : ℝ) ^ (2 * A) :=
    Real.rpow_pos_of_pos (Real.log_pos (by nlinarith [hcn])) _
  calc
    |psiMod (n : ℝ) q r - n / q.totient| ≤ C₂ * n / log (n : ℝ) ^ (2 * A) := hSWn
    _ ≤ C₂ * (max c₁ 1 * X) / log X ^ A := by
      apply (div_le_div_iff₀ hdenn hdenX).2
      have hnum : C₂ * (n : ℝ) ≤ C₂ * (max c₁ 1 * X) :=
        mul_le_mul_of_nonneg_left hnupper hC₂.le
      calc
        C₂ * (n : ℝ) * log X ^ A ≤ C₂ * (max c₁ 1 * X) * log X ^ A :=
          mul_le_mul_of_nonneg_right hnum hdenX.le
        _ ≤ C₂ * (max c₁ 1 * X) * log (n : ℝ) ^ (2 * A) := by
          apply mul_le_mul_of_nonneg_left hpow
          positivity
    _ = C₂ * max c₁ 1 * X / log X ^ A := by ring

/-- **Major-arc approximation of `SJ`.** For `q ≤ (log X)^A`, `(a, q) = 1` and `|β| ≤ b / X`,
`SJ(a/q + β) = μ(q)/φ(q) · TJ(β) + O(q (1 + b) X (log X)⁻ᴬ)`. -/
theorem exists_SJ_approx (hSW : SiegelWalfisz) {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop, ∀ (q a : ℕ) (b β : ℝ), 0 < q → (q : ℝ) ≤ log X ^ A →
      Nat.Coprime a q → 0 ≤ b → |β| ≤ b / X →
        ‖R.SJ X (a / q + β) - ((μ q / q.totient : ℝ) : ℂ) * R.TJ X β‖ ≤
          C * q * (1 + b) * X / log X ^ A := by
  obtain ⟨C₁, hC₁, hψ⟩ := exists_psiMod_sub_le hSW hA
    (c₀ := R.γ / 2) (c₁ := R.δ) (by exact div_pos R.γ_pos (by norm_num))
  have hδ : 0 < R.δ := R.γ_pos.trans R.γ_lt_δ
  refine ⟨1 + 2 * C₁ * (9 + 8 * R.δ), by nlinarith, ?_⟩
  have hlogsmall := eventually_log_mul_rpow_le (A := A) hδ
  filter_upwards [hψ, hlogsmall, Filter.eventually_ge_atTop (2 / R.γ),
    Filter.eventually_ge_atTop (1 : ℝ), Filter.eventually_gt_atTop (1 : ℝ)] with
    X hψ hlogsmall hγX hX hXgt
  intro q a b β hq hqA ha hb hβ
  let lo : ℕ := ⌈R.γ * X⌉₊
  let hi : ℕ := ⌊R.δ * X⌋₊
  have hγX' : 2 ≤ R.γ * X := by
    calc
      2 = R.γ * (2 / R.γ) := by field_simp [ne_of_gt R.γ_pos]
      _ ≤ R.γ * X := mul_le_mul_of_nonneg_left hγX R.γ_pos.le
  have hlo : 1 ≤ lo := by
    dsimp [lo]
    exact Nat.ceil_pos.mpr (mul_pos R.γ_pos (lt_of_lt_of_le zero_lt_one hX))
  have hlohi : lo ≤ hi + 1 := by
    dsimp [lo, hi]
    have h₁ : (⌈R.γ * X⌉₊ : ℝ) < R.γ * X + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have h₂ : R.δ * X + 1 < (⌊R.δ * X⌋₊ : ℝ) + 2 := by
      linarith [Nat.lt_floor_add_one (R.δ * X)]
    have h₃ : (⌈R.γ * X⌉₊ : ℝ) < (⌊R.δ * X⌋₊ : ℝ) + 2 := by
      have hgd : R.γ * X < R.δ * X :=
        mul_lt_mul_of_pos_right R.γ_lt_δ (lt_of_lt_of_le zero_lt_one hX)
      linarith
    have h₄ : ⌈R.γ * X⌉₊ < ⌊R.δ * X⌋₊ + 2 := by exact_mod_cast h₃
    omega
  have hx : 1 ≤ R.δ * X := by
    have hgd : R.γ * X < R.δ * X :=
      mul_lt_mul_of_pos_right R.γ_lt_δ (lt_of_lt_of_le zero_lt_one hX)
    linarith
  have hhi : (hi : ℝ) ≤ R.δ * X := by
    dsimp [hi]
    exact Nat.floor_le (mul_nonneg hδ.le (by linarith [hX]))
  have hD : ∀ r, r < q → Nat.Coprime r q →
      ∀ n ∈ Icc (lo - 1) hi, |psiMod n q r - n / q.totient| ≤ C₁ * X / log X ^ A := by
    intro r hr hrc n hn
    have hnlo : R.γ / 2 * X ≤ (n : ℝ) := by
      have hnceil : R.γ * X ≤ (lo : ℝ) := by
        exact Nat.le_ceil _
      have hnsub : (lo : ℝ) - 1 ≤ (n : ℝ) := by
        exact_mod_cast (mem_Icc.mp hn).1
      nlinarith [R.γ_pos]
    have hnhi : (n : ℝ) ≤ R.δ * X := by
      calc
        (n : ℝ) ≤ hi := by exact_mod_cast (mem_Icc.mp hn).2
        _ ≤ R.δ * X := hhi
    exact hψ q r hq hqA hrc n hnlo hnhi
  have hmain := norm_sum_Icc_sub_le hq ha hlo hlohi hx hhi hD 1 β
  have hsum :
      R.SJ X (a / q + β) =
        ∑ n ∈ Icc lo hi, (Λ n : ℂ) * e (n * (1 * a) / q) * e (1 * n * β) := by
    unfold SJ J
    dsimp [lo, hi]
    apply Finset.sum_congr rfl
    intro n hn
    have he : e (n * (a / q + β)) =
        e (n * (1 * a) / q) * e (1 * n * β) := by
      rw [← e_add]
      congr 1
      ring
    rw [he]
    ring
  rw [hsum]
  calc
    _ ≤ q * log (R.δ * X) +
        q * (2 * (C₁ * X / log X ^ A) *
          (1 + 2 * π * 1 * |β| * (hi + 1 - lo))) := by
      simpa [one_mul, TJ, J, ramanujanSum_one_right] using hmain
    _ ≤ (1 + 2 * C₁ * (9 + 8 * R.δ)) * q * (1 + b) * X / log X ^ A := by
      have hden : 0 < log X ^ A := Real.rpow_pos_of_pos (Real.log_pos hXgt) _
      have hlog : log (R.δ * X) ≤ X / log X ^ A := by
        apply (le_div_iff₀ hden).2
        nlinarith [hlogsmall]
      have hwidth : (hi : ℝ) + 1 - lo ≤ R.δ * X + 1 := by
        have hlo0 : (0 : ℝ) ≤ lo := by positivity
        linarith [hhi]
      have hwidth0 : 0 ≤ (hi : ℝ) + 1 - lo := by
        have : lo ≤ hi + 1 := hlohi
        have hnat : 0 ≤ hi + 1 - lo := by omega
        exact_mod_cast hnat
      have hbeta : |β| * ((hi : ℝ) + 1 - lo) ≤ b * (R.δ + 1) := by
        calc
          |β| * ((hi : ℝ) + 1 - lo) ≤ |β| * (R.δ * X + 1) :=
            mul_le_mul_of_nonneg_left hwidth (abs_nonneg β)
          _ ≤ (b / X) * (R.δ * X + 1) :=
            mul_le_mul_of_nonneg_right hβ (by positivity)
          _ ≤ b * (R.δ + 1) := by
            field_simp
            nlinarith
      have hvar : 1 + 2 * π * |β| * ((hi : ℝ) + 1 - lo) ≤
          (9 + 8 * R.δ) * (1 + b) := by
        have hp : 2 * π ≤ (8 : ℝ) := by nlinarith [Real.pi_le_four]
        have hpw : 2 * π * (|β| * ((hi : ℝ) + 1 - lo)) ≤
            8 * (|β| * ((hi : ℝ) + 1 - lo)) := by
          exact mul_le_mul_of_nonneg_right hp
            (mul_nonneg (abs_nonneg β) hwidth0)
        calc
          _ ≤ 1 + 8 * (|β| * ((hi : ℝ) + 1 - lo)) := by
            nlinarith [hpw]
          _ ≤ (9 + 8 * R.δ) * (1 + b) := by
            have h8 := mul_le_mul_of_nonneg_left hbeta (by norm_num : (0 : ℝ) ≤ 8)
            ring_nf at h8 ⊢
            nlinarith [h8, hδ, hb]
      have hq0 : (0 : ℝ) ≤ q := by positivity
      calc
        q * log (R.δ * X) +
              q * (2 * (C₁ * X / log X ^ A) *
                (1 + 2 * π * 1 * |β| * ((hi : ℝ) + 1 - lo))) ≤
            q * (1 + b) * X / log X ^ A +
              q * (2 * (C₁ * X / log X ^ A) *
                ((9 + 8 * R.δ) * (1 + b))) := by
          have hlog' : log (R.δ * X) ≤ (1 + b) * X / log X ^ A := by
            apply (le_div_iff₀ hden).2
            have hX0 : 0 ≤ X := by linarith
            have hbX : 0 ≤ b * X := mul_nonneg hb hX0
            nlinarith [hlogsmall, hbX]
          apply add_le_add
          · calc
              q * log (R.δ * X) ≤ q * ((1 + b) * X / log X ^ A) :=
                mul_le_mul_of_nonneg_left hlog' hq0
              _ = q * (1 + b) * X / log X ^ A := by ring
          · apply mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (by simpa [one_mul] using hvar) (by positivity))
              hq0
        _ = (1 + 2 * C₁ * (9 + 8 * R.δ)) * q * (1 + b) * X / log X ^ A := by
          field_simp

/-- **Major-arc approximation of `SI`.** For `q ≤ (log X)^A`, `(a, q) = 1` and `|β| ≤ b / X`,
`SI(a/q + β) = c_q(ν)/φ(q) · TI(β) + O(q (1 + b) X (log X)⁻ᴬ)`. -/
theorem exists_SI_approx (hSW : SiegelWalfisz) {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop, ∀ (q a : ℕ) (b β : ℝ), 0 < q → (q : ℝ) ≤ log X ^ A →
      Nat.Coprime a q → 0 ≤ b → |β| ≤ b / X →
        ‖R.SI X (a / q + β) - ((ramanujanSum q R.ν / q.totient : ℝ) : ℂ) * R.TI X β‖ ≤
          C * q * (1 + b) * X / log X ^ A := by
  obtain ⟨C₁, hC₁, hψ⟩ := exists_psiMod_sub_le hSW hA
    (c₀ := R.α / 2) (c₁ := R.β) (by exact div_pos R.α_pos (by norm_num))
  have hβpos : 0 < R.β := R.α_pos.trans R.α_lt_β
  refine ⟨1 + 2 * C₁ * (17 + 16 * R.β), by nlinarith, ?_⟩
  have hlogsmall := eventually_log_mul_rpow_le (A := A) hβpos
  filter_upwards [hψ, hlogsmall, Filter.eventually_ge_atTop (2 / R.α),
    Filter.eventually_ge_atTop (1 : ℝ), Filter.eventually_gt_atTop (1 : ℝ)] with
    X hψ hlogsmall hαX hX hXgt
  intro q a b β hq hqA ha hb hβ
  let lo : ℕ := ⌈R.α * X⌉₊
  let hi : ℕ := ⌊R.β * X⌋₊
  have hαX' : 2 ≤ R.α * X := by
    calc
      2 = R.α * (2 / R.α) := by field_simp [ne_of_gt R.α_pos]
      _ ≤ R.α * X := mul_le_mul_of_nonneg_left hαX R.α_pos.le
  have hlo : 1 ≤ lo := by
    dsimp [lo]
    exact Nat.ceil_pos.mpr (mul_pos R.α_pos (lt_of_lt_of_le zero_lt_one hX))
  have hlohi : lo ≤ hi + 1 := by
    dsimp [lo, hi]
    have h₁ : (⌈R.α * X⌉₊ : ℝ) < R.α * X + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have h₂ : R.β * X + 1 < (⌊R.β * X⌋₊ : ℝ) + 2 := by
      linarith [Nat.lt_floor_add_one (R.β * X)]
    have h₃ : (⌈R.α * X⌉₊ : ℝ) < (⌊R.β * X⌋₊ : ℝ) + 2 := by
      have hgd : R.α * X < R.β * X :=
        mul_lt_mul_of_pos_right R.α_lt_β (lt_of_lt_of_le zero_lt_one hX)
      linarith
    have h₄ : ⌈R.α * X⌉₊ < ⌊R.β * X⌋₊ + 2 := by exact_mod_cast h₃
    omega
  have hx : 1 ≤ R.β * X := by
    have hgd : R.α * X < R.β * X :=
      mul_lt_mul_of_pos_right R.α_lt_β (lt_of_lt_of_le zero_lt_one hX)
    linarith
  have hhi : (hi : ℝ) ≤ R.β * X := by
    dsimp [hi]
    exact Nat.floor_le (mul_nonneg hβpos.le (by linarith [hX]))
  have hD : ∀ r, r < q → Nat.Coprime r q →
      ∀ n ∈ Icc (lo - 1) hi, |psiMod n q r - n / q.totient| ≤ C₁ * X / log X ^ A := by
    intro r hr hrc n hn
    have hnlo : R.α / 2 * X ≤ (n : ℝ) := by
      have hnceil : R.α * X ≤ (lo : ℝ) := by
        exact Nat.le_ceil _
      have hnsub : (lo : ℝ) - 1 ≤ (n : ℝ) := by
        exact_mod_cast (mem_Icc.mp hn).1
      nlinarith [R.α_pos]
    have hnhi : (n : ℝ) ≤ R.β * X := by
      calc
        (n : ℝ) ≤ hi := by exact_mod_cast (mem_Icc.mp hn).2
        _ ≤ R.β * X := hhi
    exact hψ q r hq hqA hrc n hnlo hnhi
  have hmain := norm_sum_Icc_sub_le hq ha hlo hlohi hx hhi hD R.ν β
  have hsum :
      R.SI X (a / q + β) =
        ∑ n ∈ Icc lo hi, (Λ n : ℂ) * e (n * (R.ν * a) / q) * e (R.ν * n * β) := by
    unfold SI I
    dsimp [lo, hi]
    apply Finset.sum_congr rfl
    intro n hn
    have he : e (R.ν * n * (a / q + β)) =
        e (n * (R.ν * a) / q) * e (R.ν * n * β) := by
      rw [← e_add]
      congr 1
      ring
    rw [he]
    ring
  rw [hsum]
  calc
    _ ≤ q * log (R.β * X) +
        q * (2 * (C₁ * X / log X ^ A) *
          (1 + 2 * π * R.ν * |β| * (hi + 1 - lo))) := by
      simpa [TI, I] using hmain
    _ ≤ (1 + 2 * C₁ * (17 + 16 * R.β)) * q * (1 + b) * X / log X ^ A := by
      have hden : 0 < log X ^ A := Real.rpow_pos_of_pos (Real.log_pos hXgt) _
      have hlog : log (R.β * X) ≤ X / log X ^ A := by
        apply (le_div_iff₀ hden).2
        nlinarith [hlogsmall]
      have hwidth : (hi : ℝ) + 1 - lo ≤ R.β * X + 1 := by
        have hlo0 : (0 : ℝ) ≤ lo := by positivity
        linarith [hhi]
      have hwidth0 : 0 ≤ (hi : ℝ) + 1 - lo := by
        have : lo ≤ hi + 1 := hlohi
        have hnat : 0 ≤ hi + 1 - lo := by omega
        exact_mod_cast hnat
      have hbeta : |β| * ((hi : ℝ) + 1 - lo) ≤ b * (R.β + 1) := by
        calc
          |β| * ((hi : ℝ) + 1 - lo) ≤ |β| * (R.β * X + 1) :=
            mul_le_mul_of_nonneg_left hwidth (abs_nonneg β)
          _ ≤ (b / X) * (R.β * X + 1) :=
            mul_le_mul_of_nonneg_right hβ (by positivity)
          _ ≤ b * (R.β + 1) := by
            field_simp
            nlinarith
      have hvar : 1 + 2 * π * R.ν * |β| * ((hi : ℝ) + 1 - lo) ≤
          (17 + 16 * R.β) * (1 + b) := by
        have hp : 2 * π * (R.ν : ℝ) ≤ (16 : ℝ) := by
          calc
            2 * π * (R.ν : ℝ) ≤ 2 * π * 2 := by
              apply mul_le_mul_of_nonneg_left
              · exact_mod_cast R.ν_le_two
              · positivity
            _ ≤ 16 := by nlinarith [Real.pi_le_four]
        have hpw : 2 * π * (R.ν : ℝ) * (|β| * ((hi : ℝ) + 1 - lo)) ≤
            16 * (|β| * ((hi : ℝ) + 1 - lo)) := by
          exact mul_le_mul_of_nonneg_right hp
            (mul_nonneg (abs_nonneg β) hwidth0)
        calc
          _ ≤ 1 + 16 * (|β| * ((hi : ℝ) + 1 - lo)) := by
            nlinarith [hpw]
          _ ≤ (17 + 16 * R.β) * (1 + b) := by
            have h8 := mul_le_mul_of_nonneg_left hbeta (by norm_num : (0 : ℝ) ≤ 16)
            ring_nf at h8 ⊢
            nlinarith [h8, hβpos, hb]
      have hq0 : (0 : ℝ) ≤ q := by positivity
      calc
        q * log (R.β * X) +
              q * (2 * (C₁ * X / log X ^ A) *
                (1 + 2 * π * R.ν * |β| * ((hi : ℝ) + 1 - lo))) ≤
            q * (1 + b) * X / log X ^ A +
              q * (2 * (C₁ * X / log X ^ A) *
                ((17 + 16 * R.β) * (1 + b))) := by
          have hlog' : log (R.β * X) ≤ (1 + b) * X / log X ^ A := by
            apply (le_div_iff₀ hden).2
            have hX0 : 0 ≤ X := by linarith
            have hbX : 0 ≤ b * X := mul_nonneg hb hX0
            nlinarith [hlogsmall, hbX]
          apply add_le_add
          · calc
              q * log (R.β * X) ≤ q * ((1 + b) * X / log X ^ A) :=
                mul_le_mul_of_nonneg_left hlog' hq0
              _ = q * (1 + b) * X / log X ^ A := by ring
          · apply mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (by simpa [one_mul] using hvar) (by positivity))
              hq0
        _ = (1 + 2 * C₁ * (17 + 16 * R.β)) * q * (1 + b) * X / log X ^ A := by
          field_simp


/-! ### The main term -/

/-- **Evaluation of the main terms.** Replacing `SI`, `SJ` by their major-arc approximations
in `majorSum` gives exactly `𝔖_P(N) · W(N)`. -/
theorem sum_main_eq (N : ℕ) :
    (1 / (R.Q X P : ℂ)) * ∑ qa ∈ arcIndex P,
      ∑ j ∈ Icc (-(R.halfWidth X P : ℤ)) (R.halfWidth X P),
        (((ramanujanSum qa.1 R.ν / qa.1.totient : ℝ) : ℂ) * R.TI X (j / R.Q X P)) *
          (((μ qa.1 / qa.1.totient : ℝ) : ℂ) * R.TJ X (j / R.Q X P)) *
            e (-(N * R.arcAngle X P qa j)) =
      (singularSeries R.ν N P : ℂ) * R.singularIntegral X P N := by
  classical
  let K : ℕ → ℝ := fun q =>
    (μ q : ℝ) * ramanujanSum q R.ν / (q.totient : ℝ) ^ 2
  let S : ℂ :=
    ∑ j ∈ Icc (-(R.halfWidth X P : ℤ)) (R.halfWidth X P),
      R.TI X (j / R.Q X P) * R.TJ X (j / R.Q X P) *
        e (-(N * j / R.Q X P))
  have hterm (qa : ℕ × ℕ) (j : ℤ) :
      (((ramanujanSum qa.1 R.ν / qa.1.totient : ℝ) : ℂ) *
          R.TI X (j / R.Q X P)) *
        (((μ qa.1 / qa.1.totient : ℝ) : ℂ) * R.TJ X (j / R.Q X P)) *
          e (-(N * R.arcAngle X P qa j)) =
        (((K qa.1 : ℝ) : ℂ) * e (-(qa.2 * N / qa.1))) *
          (R.TI X (j / R.Q X P) * R.TJ X (j / R.Q X P) *
            e (-(N * j / R.Q X P))) := by
    unfold arcAngle
    have hearg : -(N * (↑qa.2 / qa.1 + (j : ℝ) / R.Q X P)) =
        -(qa.2 * N / qa.1) + -(N * j / R.Q X P) := by
      simp only [mul_div_assoc]
      ring
    rw [hearg, e_add]
    simp only [K]
    push_cast
    ring
  have hinner (qa : ℕ × ℕ) :
      ∑ j ∈ Icc (-(R.halfWidth X P : ℤ)) (R.halfWidth X P),
          (((ramanujanSum qa.1 R.ν / qa.1.totient : ℝ) : ℂ) *
              R.TI X (j / R.Q X P)) *
            (((μ qa.1 / qa.1.totient : ℝ) : ℂ) * R.TJ X (j / R.Q X P)) *
              e (-(N * R.arcAngle X P qa j)) =
        (((K qa.1 : ℝ) : ℂ) * e (-(qa.2 * N / qa.1))) * S := by
    calc
      _ = ∑ j ∈ Icc (-(R.halfWidth X P : ℤ)) (R.halfWidth X P),
          (((K qa.1 : ℝ) : ℂ) * e (-(qa.2 * N / qa.1))) *
            (R.TI X (j / R.Q X P) * R.TJ X (j / R.Q X P) *
              e (-(N * j / R.Q X P))) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hterm qa j
      _ = (((K qa.1 : ℝ) : ℂ) * e (-(qa.2 * N / qa.1))) * S := by
        rw [show S = ∑ j ∈ Icc (-(R.halfWidth X P : ℤ)) (R.halfWidth X P),
            R.TI X (j / R.Q X P) * R.TJ X (j / R.Q X P) *
              e (-(N * j / R.Q X P)) by rfl]
        rw [← Finset.mul_sum]
  rw [show (∑ qa ∈ arcIndex P,
      ∑ j ∈ Icc (-(R.halfWidth X P : ℤ)) (R.halfWidth X P),
        (((ramanujanSum qa.1 R.ν / qa.1.totient : ℝ) : ℂ) *
            R.TI X (j / R.Q X P)) *
          (((μ qa.1 / qa.1.totient : ℝ) : ℂ) * R.TJ X (j / R.Q X P)) *
            e (-(N * R.arcAngle X P qa j))) =
      ∑ qa ∈ arcIndex P, (((K qa.1 : ℝ) : ℂ) * e (-(qa.2 * N / qa.1))) * S by
    apply Finset.sum_congr rfl
    intro qa hqa
    rw [hinner]]
  rw [← Finset.sum_mul]
  have hprod :
      ∑ qa ∈ arcIndex P, (((K qa.1 : ℝ) : ℂ) * e (-(qa.2 * N / qa.1))) =
        ∑ q ∈ Icc 1 P, ∑ a ∈ coprimeRange q,
          (((K q : ℝ) : ℂ) * e (-(a * N / q))) := by
    apply Finset.sum_finset_product (r := arcIndex P) (s := Icc 1 P)
      (t := coprimeRange)
    intro qa
    rw [mem_arcIndex, mem_coprimeRange]
    simp only [Finset.mem_Icc]
    omega
  rw [hprod]
  have hqsum (q : ℕ) (hq : q ∈ Icc 1 P) :
      ∑ a ∈ coprimeRange q, (((K q : ℝ) : ℂ) * e (-(a * N / q))) =
        (arcCoeff R.ν N q : ℝ) := by
    have hqpos : 0 < q := (Finset.mem_Icc.mp hq).1
    rw [← Finset.mul_sum, sum_e_neg_coprimeRange hqpos N]
    simp only [K]
    unfold arcCoeff
    push_cast
    ring
  rw [show (∑ q ∈ Icc 1 P, ∑ a ∈ coprimeRange q,
      (((K q : ℝ) : ℂ) * e (-(a * N / q)))) =
      ∑ q ∈ Icc 1 P, (arcCoeff R.ν N q : ℂ) by
    apply Finset.sum_congr rfl
    intro q hq
    exact hqsum q hq]
  unfold singularSeries singularIntegral
  dsimp [S]
  push_cast
  ring

private theorem abs_ramanujanSum_le_three (q : ℕ) :
    |ramanujanSum q R.ν| ≤ (3 : ℤ) := by
  have h := abs_ramanujanSum_le q R.ν
  rcases R.ν_eq with hν | hν
  · rw [hν] at h ⊢
    have hg : Nat.gcd q 1 = 1 := Nat.dvd_one.mp (Nat.gcd_dvd_right q 1)
    rw [hg] at h
    exact h.trans (by norm_num)
  · rw [hν] at h ⊢
    have hd : Nat.gcd q 2 ∣ 2 := Nat.gcd_dvd_right q 2
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with hg | hg
    · rw [hg] at h
      exact h.trans (by norm_num)
    · rw [hg] at h
      rw [ArithmeticFunction.sigma_one_apply] at h
      have hdv : Nat.divisors 2 = {1, 2} := by decide
      rw [hdv] at h
      norm_num at h ⊢
      exact h.trans (by norm_num)

/-- **The major arcs.** For `P ≤ (log X)^A` and `X` large,
`‖majorSum N - 𝔖_P(N) W(N)‖ ≤ C P⁵ X (log X + 1) / (log X)^A`, uniformly in `N`. -/
theorem exists_norm_majorSum_sub_le (hSW : SiegelWalfisz) {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop, ∀ P : ℕ, 1 ≤ P → (P : ℝ) ≤ log X ^ A →
      8 * (P : ℝ) ^ 3 ≤ X → X ≤ P * R.Q X P → ∀ N : ℕ,
        ‖R.majorSum X P N - (singularSeries R.ν N P : ℂ) * R.singularIntegral X P N‖ ≤
          C * P ^ 5 * X * (log X + 1) / log X ^ A := by
  obtain ⟨CJ, hCJ, hJ⟩ := R.exists_SJ_approx hSW hA
  obtain ⟨CI, hCI, hI⟩ := R.exists_SI_approx hSW hA
  let KI : ℝ := 6 * CI * (R.δ + 1)
  let KJ : ℝ := 9 * CJ * (R.β + 1)
  let C : ℝ := 5 * (KI + KJ)
  have hβpos : 0 < R.β := R.α_pos.trans R.α_lt_β
  have hδpos : 0 < R.δ := R.γ_pos.trans R.γ_lt_δ
  refine ⟨C, by dsimp [C, KI, KJ]; positivity, ?_⟩
  have hlogδ : ∀ᶠ X : ℝ in atTop,
      log (R.δ * X + 1) ≤ 2 * (log X + 1) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop (log (R.δ + 1) - 2)] with X hX hlog
    have hδ0 : 0 ≤ R.δ := (R.γ_pos.trans R.γ_lt_δ).le
    have hX0 : 0 ≤ X := zero_le_one.trans hX
    have hmul : R.δ * X + 1 ≤ (R.δ + 1) * X := by nlinarith
    have hpos1 : 0 < R.δ * X + 1 := by nlinarith
    have hpos2 : 0 < (R.δ + 1) * X := by positivity
    have hlogmul : log ((R.δ + 1) * X) =
        log (R.δ + 1) + log X := by
      rw [Real.log_mul (by positivity) (by positivity)]
    calc
      log (R.δ * X + 1) ≤ log ((R.δ + 1) * X) :=
        Real.log_le_log hpos1 hmul
      _ = log (R.δ + 1) + log X := hlogmul
      _ ≤ 2 * (log X + 1) := by linarith
  filter_upwards [hJ, hI, Filter.eventually_ge_atTop (1 : ℝ),
    Filter.eventually_gt_atTop (1 : ℝ), hlogδ] with X hJX hIX hX1 hX1' hδ
  intro P hP1 hPA hP8 hPQ N
  have hX0 : 0 < X := lt_of_lt_of_le (by positivity) hX1
  have hQ : 0 < (R.Q X P : ℝ) := by exact_mod_cast R.Q_pos X P
  have hden : 0 < log X ^ A := Real.rpow_pos_of_pos (Real.log_pos hX1') _
  have hbeta : ∀ (j : ℤ), j ∈ Icc (-(R.halfWidth X P : ℤ)) (R.halfWidth X P) →
      |(j : ℝ) / R.Q X P| ≤ 2 * P / X := by
    intro j hj
    have hj' := (Finset.mem_Icc.mp hj)
    have habs : |j| ≤ (R.halfWidth X P : ℤ) :=
      (abs_le).mpr ⟨hj'.1, hj'.2⟩
    calc
      |(j : ℝ) / R.Q X P| = |j| / R.Q X P := by
        rw [abs_div, abs_of_pos hQ, Int.cast_abs]
      _ ≤ (R.halfWidth X P : ℝ) / R.Q X P := by
        apply div_le_div_of_nonneg_right _ hQ.le
        exact_mod_cast habs
      _ ≤ 2 * P / X := R.halfWidth_div_Q_le X P hX0
  have hterm : ∀ (qa : ℕ × ℕ) (j : ℤ), qa ∈ arcIndex P →
      j ∈ Icc (-(R.halfWidth X P : ℤ)) (R.halfWidth X P) →
      ‖R.SI X (R.arcAngle X P qa j) * R.SJ X (R.arcAngle X P qa j) *
          e (-(N * R.arcAngle X P qa j)) -
        (((ramanujanSum qa.1 R.ν / qa.1.totient : ℝ) : ℂ) *
            R.TI X (j / R.Q X P)) *
          (((μ qa.1 / qa.1.totient : ℝ) : ℂ) * R.TJ X (j / R.Q X P)) *
            e (-(N * R.arcAngle X P qa j))‖ ≤
        (KI + KJ) * P ^ 2 * X ^ 2 * (log X + 1) / log X ^ A := by
    intro qa j hqa hj
    rcases mem_arcIndex.mp hqa with ⟨hq0, hqP, ha, hcop⟩
    have hqA : (qa.1 : ℝ) ≤ log X ^ A := by
      have hqP' : (qa.1 : ℝ) ≤ P := by exact_mod_cast hqP
      exact hqP'.trans hPA
    have hb : 0 ≤ (2 * P : ℝ) := by positivity
    have hjb := hbeta j hj
    have hsj := hJX qa.1 qa.2 (2 * P) (j / R.Q X P) hq0 hqA hcop hb hjb
    have hsi := hIX qa.1 qa.2 (2 * P) (j / R.Q X P) hq0 hqA hcop hb hjb
    have hqle : (qa.1 : ℝ) ≤ P := by exact_mod_cast hqP
    have hone : (1 : ℝ) + 2 * P ≤ 3 * P := by
      have hp : (1 : ℝ) ≤ P := by exact_mod_cast hP1
      linarith
    have hsj' : ‖R.SJ X (R.arcAngle X P qa j) -
          ((μ qa.1 / qa.1.totient : ℝ) : ℂ) * R.TJ X (j / R.Q X P)‖ ≤
        3 * CJ * P ^ 2 * X / log X ^ A := by
      apply le_trans hsj
      apply div_le_div_of_nonneg_right _ hden.le
      calc
        CJ * qa.1 * (1 + 2 * P) * X =
            CJ * X * (qa.1 * (1 + 2 * P)) := by ring
        _ ≤ CJ * X * (P * (3 * P)) := by gcongr
        _ = 3 * CJ * P ^ 2 * X := by ring
    have hsi' : ‖R.SI X (R.arcAngle X P qa j) -
          ((ramanujanSum qa.1 R.ν / qa.1.totient : ℝ) : ℂ) *
            R.TI X (j / R.Q X P)‖ ≤
        3 * CI * P ^ 2 * X / log X ^ A := by
      apply le_trans hsi
      apply div_le_div_of_nonneg_right _ hden.le
      calc
        CI * qa.1 * (1 + 2 * P) * X =
            CI * X * (qa.1 * (1 + 2 * P)) := by ring
        _ ≤ CI * X * (P * (3 * P)) := by gcongr
        _ = 3 * CI * P ^ 2 * X := by ring
    have hsj_norm : ‖R.SJ X (R.arcAngle X P qa j)‖ ≤
        2 * (R.δ + 1) * X * (log X + 1) := by
      calc
        ‖R.SJ X (R.arcAngle X P qa j)‖ ≤
            (R.δ * X + 1) * log (R.δ * X + 1) :=
          R.norm_SJ_le X hX1 _
        _ ≤ (R.δ + 1) * X * (2 * (log X + 1)) := by
          apply mul_le_mul
          · nlinarith [hδpos]
          · exact hδ
          · exact Real.log_nonneg (by nlinarith [hδpos])
          · positivity
        _ = 2 * (R.δ + 1) * X * (log X + 1) := by ring
    have hram : |(ramanujanSum qa.1 R.ν : ℝ)| ≤ 3 := by
      exact_mod_cast abs_ramanujanSum_le_three R qa.1
    have hphi : 1 ≤ (qa.1.totient : ℝ) := by
      exact_mod_cast Nat.succ_le_iff.mpr (Nat.totient_pos.mpr hq0)
    have hmi : ‖((ramanujanSum qa.1 R.ν / qa.1.totient : ℝ) : ℂ) *
          R.TI X (j / R.Q X P)‖ ≤ 3 * (R.β + 1) * X := by
      have hβ0 : 0 ≤ R.β := hβpos.le
      have hφpos : (0 : ℝ) < qa.1.totient := by
        exact_mod_cast Nat.totient_pos.mpr hq0
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div,
        abs_of_pos hφpos]
      calc
        |(ramanujanSum qa.1 R.ν : ℝ)| / qa.1.totient *
            ‖R.TI X (j / R.Q X P)‖ ≤
            3 * (R.β * X + 1) := by
          apply mul_le_mul
          · exact (div_le_iff₀ hφpos).mpr (by nlinarith [hram, hphi])
          · exact R.norm_TI_le X hX0.le _
          · exact norm_nonneg _
          · norm_num
        _ ≤ 3 * (R.β + 1) * X := by nlinarith
    have hsplit :
        ‖(R.SI X (R.arcAngle X P qa j) -
            ((ramanujanSum qa.1 R.ν / qa.1.totient : ℝ) : ℂ) *
              R.TI X (j / R.Q X P)) *
            R.SJ X (R.arcAngle X P qa j) +
          (((ramanujanSum qa.1 R.ν / qa.1.totient : ℝ) : ℂ) *
            R.TI X (j / R.Q X P)) *
            (R.SJ X (R.arcAngle X P qa j) -
              ((μ qa.1 / qa.1.totient : ℝ) : ℂ) *
                R.TJ X (j / R.Q X P))‖ ≤
        (3 * CI * P ^ 2 * X / log X ^ A) *
            (2 * (R.δ + 1) * X * (log X + 1)) +
          (3 * (R.β + 1) * X) *
            (3 * CJ * P ^ 2 * X / log X ^ A) := by
      calc
        _ ≤ ‖(R.SI X (R.arcAngle X P qa j) -
            ((ramanujanSum qa.1 R.ν / qa.1.totient : ℝ) : ℂ) *
              R.TI X (j / R.Q X P)) *
            R.SJ X (R.arcAngle X P qa j)‖ +
          ‖(((ramanujanSum qa.1 R.ν / qa.1.totient : ℝ) : ℂ) *
            R.TI X (j / R.Q X P)) *
            (R.SJ X (R.arcAngle X P qa j) -
              ((μ qa.1 / qa.1.totient : ℝ) : ℂ) *
                R.TJ X (j / R.Q X P))‖ := norm_add_le _ _
        _ = ‖R.SI X (R.arcAngle X P qa j) -
              ((ramanujanSum qa.1 R.ν / qa.1.totient : ℝ) : ℂ) *
                R.TI X (j / R.Q X P)‖ *
              ‖R.SJ X (R.arcAngle X P qa j)‖ +
            ‖((ramanujanSum qa.1 R.ν / qa.1.totient : ℝ) : ℂ) *
                R.TI X (j / R.Q X P)‖ *
              ‖R.SJ X (R.arcAngle X P qa j) -
                ((μ qa.1 / qa.1.totient : ℝ) : ℂ) *
                  R.TJ X (j / R.Q X P)‖ := by rw [norm_mul, norm_mul]
        _ ≤ _ := add_le_add
          (mul_le_mul hsi' hsj_norm (norm_nonneg _) (by positivity))
          (mul_le_mul hmi hsj' (norm_nonneg _) (by positivity))
    have hfac :
        R.SI X (R.arcAngle X P qa j) * R.SJ X (R.arcAngle X P qa j) *
            e (-(N * R.arcAngle X P qa j)) -
          (((ramanujanSum qa.1 R.ν / qa.1.totient : ℝ) : ℂ) *
              R.TI X (j / R.Q X P)) *
            (((μ qa.1 / qa.1.totient : ℝ) : ℂ) *
              R.TJ X (j / R.Q X P)) *
            e (-(N * R.arcAngle X P qa j)) =
          ((R.SI X (R.arcAngle X P qa j) -
              ((ramanujanSum qa.1 R.ν / qa.1.totient : ℝ) : ℂ) *
                R.TI X (j / R.Q X P)) *
              R.SJ X (R.arcAngle X P qa j) +
            (((ramanujanSum qa.1 R.ν / qa.1.totient : ℝ) : ℂ) *
              R.TI X (j / R.Q X P)) *
              (R.SJ X (R.arcAngle X P qa j) -
                ((μ qa.1 / qa.1.totient : ℝ) : ℂ) *
                  R.TJ X (j / R.Q X P))) *
            e (-(N * R.arcAngle X P qa j)) := by ring
    rw [hfac, norm_mul, norm_e, mul_one]
    apply le_trans hsplit
    have hlog : 0 ≤ log X := Real.log_nonneg hX1
    have hlogone : 1 ≤ log X + 1 := by linarith
    have hkj0 : 0 ≤ 9 * CJ * (R.β + 1) := by positivity
    have hkj := mul_le_mul_of_nonneg_left hlogone hkj0
    dsimp [KI, KJ]
    field_simp
    ring_nf at hkj ⊢
    linarith
  rw [← R.sum_main_eq X P N]
  unfold majorSum
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  apply le_trans (norm_mul_le _ _)
  rw [norm_div, norm_one, Complex.norm_natCast]
  have hcqa : (#(arcIndex P) : ℝ) ≤ P ^ 2 := by
    exact_mod_cast card_arcIndex_le P
  have hcj : (#(Icc (-(R.halfWidth X P : ℤ)) (R.halfWidth X P)) : ℝ) ≤
      5 * P * R.Q X P / X := by
    have hw : 0 ≤ (R.halfWidth X P : ℤ) := by exact_mod_cast Nat.zero_le _
    rw [Int.card_Icc]
    rw [show ((R.halfWidth X P : ℤ) + 1 - -(R.halfWidth X P : ℤ)) =
      2 * (R.halfWidth X P : ℤ) + 1 by ring]
    have hwi : 0 ≤ 2 * (R.halfWidth X P : ℤ) + 1 := by omega
    have hcast : ((2 * (R.halfWidth X P : ℤ) + 1).toNat : ℝ) =
        2 * (R.halfWidth X P : ℤ) + 1 := by
      norm_cast
    rw [hcast]
    exact R.two_mul_halfWidth_add_one_le X P hX0 hPQ
  have hsum : (#(arcIndex P) : ℝ) *
      (#(Icc (-(R.halfWidth X P : ℤ)) (R.halfWidth X P)) : ℝ) *
      ((KI + KJ) * P ^ 2 * X ^ 2 * (log X + 1) / log X ^ A) ≤
      P ^ 2 * (5 * P * R.Q X P / X) *
        ((KI + KJ) * P ^ 2 * X ^ 2 * (log X + 1) / log X ^ A) := by
    have hT0 : 0 ≤ (KI + KJ) * P ^ 2 * X ^ 2 * (log X + 1) / log X ^ A := by
      apply div_nonneg
      apply mul_nonneg
      · apply mul_nonneg
        · apply mul_nonneg
          · dsimp [KI, KJ]
            positivity
          · positivity
        · positivity
      · linarith [Real.log_nonneg hX1]
      · exact hden.le
    gcongr
  have houter :
      ∑ qa ∈ arcIndex P, ‖∑ j ∈ Icc (-(R.halfWidth X P : ℤ)) (R.halfWidth X P),
        (R.SI X (R.arcAngle X P qa j) * R.SJ X (R.arcAngle X P qa j) *
            e (-(N * R.arcAngle X P qa j)) -
          (((ramanujanSum qa.1 R.ν / qa.1.totient : ℝ) : ℂ) *
              R.TI X (j / R.Q X P)) *
            (((μ qa.1 / qa.1.totient : ℝ) : ℂ) *
              R.TJ X (j / R.Q X P)) *
            e (-(N * R.arcAngle X P qa j)))‖ ≤
        (#(arcIndex P) : ℝ) *
          (#(Icc (-(R.halfWidth X P : ℤ)) (R.halfWidth X P)) : ℝ) *
          ((KI + KJ) * P ^ 2 * X ^ 2 * (log X + 1) / log X ^ A) := by
    calc
      _ ≤ ∑ qa ∈ arcIndex P,
          ∑ j ∈ Icc (-(R.halfWidth X P : ℤ)) (R.halfWidth X P),
            ‖(R.SI X (R.arcAngle X P qa j) * R.SJ X (R.arcAngle X P qa j) *
                e (-(N * R.arcAngle X P qa j)) -
              (((ramanujanSum qa.1 R.ν / qa.1.totient : ℝ) : ℂ) *
                  R.TI X (j / R.Q X P)) *
                (((μ qa.1 / qa.1.totient : ℝ) : ℂ) *
                  R.TJ X (j / R.Q X P)) *
                e (-(N * R.arcAngle X P qa j)))‖ := by
        apply Finset.sum_le_sum
        intro qa hqa
        exact norm_sum_le _ _
      _ ≤ ∑ _qa ∈ arcIndex P,
          ∑ _j ∈ Icc (-(R.halfWidth X P : ℤ)) (R.halfWidth X P),
            (KI + KJ) * P ^ 2 * X ^ 2 * (log X + 1) / log X ^ A :=
        Finset.sum_le_sum fun qa hqa => Finset.sum_le_sum fun j hj => hterm qa j hqa hj
      _ = _ := by simp [nsmul_eq_mul, mul_assoc]
  calc
    _ ≤ (1 / (R.Q X P : ℝ)) *
        ∑ qa ∈ arcIndex P, ‖∑ j ∈ Icc (-(R.halfWidth X P : ℤ)) (R.halfWidth X P),
          (R.SI X (R.arcAngle X P qa j) * R.SJ X (R.arcAngle X P qa j) *
              e (-(N * R.arcAngle X P qa j)) -
            (((ramanujanSum qa.1 R.ν / qa.1.totient : ℝ) : ℂ) *
                R.TI X (j / R.Q X P)) *
              (((μ qa.1 / qa.1.totient : ℝ) : ℂ) *
                R.TJ X (j / R.Q X P)) *
              e (-(N * R.arcAngle X P qa j)))‖ := by
      apply mul_le_mul_of_nonneg_left
      apply le_trans (norm_sum_le _ _)
      apply Finset.sum_le_sum
      intro qa hqa
      rw [Finset.sum_sub_distrib]
      positivity
    _ ≤ (1 / (R.Q X P : ℝ)) *
        ((#(arcIndex P) : ℝ) *
          (#(Icc (-(R.halfWidth X P : ℤ)) (R.halfWidth X P)) : ℝ) *
          ((KI + KJ) * P ^ 2 * X ^ 2 * (log X + 1) / log X ^ A)) := by
      gcongr
    _ ≤ C * P ^ 5 * X * (log X + 1) / log X ^ A := by
      apply le_trans (mul_le_mul_of_nonneg_left hsum (by positivity))
      dsimp [C]
      convert le_rfl using 1
      field_simp

end Ranges

end CircleMethod
