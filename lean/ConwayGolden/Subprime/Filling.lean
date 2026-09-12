/-
Copyright (c) 2026 Romain Popescu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Romain Popescu
-/
import ConwayGolden.Analysis.SelfDivLog
import ConwayGolden.Subprime.Hypotheses
import ConwayGolden.Subprime.Pigeonhole
import ConwayGolden.Subprime.PrimePrefix

/-!
# Buffered filling

If every prime up to `X` lies in `gen n`, then every integer `m ≥ 2` which is the midpoint of two
primes `p, q ≤ X` lies in `gen (n + 1)`, since `subprime (p + q) = subprime (2 * m) = m`. The
restricted Goldbach hypothesis `Conway.RestrictedBinary 1` says that, at every scale `Y`, all but
`o(Y / log Y)` admissible even targets `2 * m` have such a representation with `p, q ∈ [c Y, Y]`
for a fixed `c > 0`. Applying it at the scales `X, X / 2, X / 4, …` fills all of `[1, (1 - θ) X]`
except `o(X / log X)` integers, uniformly in the generation `n`.

The buffer `θ > 0` is essential: with prime ranges of fixed proportional length, the midpoints
close to `X` are not admissible.

## Main statements

* `Conway.RestrictedBinary.eventually_holes_le`: for fixed `0 < θ < 1` and `ε > 0`, for all
  sufficiently large `X` and every `n` with `PrimePrefix n X`,
  `holes (n + 1) ⌊(1 - θ) X⌋₊ ≤ ε X / log X`.

## Implementation notes

The dyadic descent is organised as a strong induction on `⌊Y⌋₊`: the number of holes below
`(1 - θ) Y` is at most the number below `(1 - θ) (Y / 2)` plus the size of the exceptional set at
scale `Y`. Below a fixed threshold `Y₀` the trivial bound `holes ≤ Y < Y₀` is used, and above it
the inequality `2 log Y ≤ 3 log (Y / 2)` (valid for `Y ≥ 8`) absorbs the new error into the
inductive bound `Y₀ + 4 ε' Y / log Y`.
-/

namespace Conway

open Filter Finset Real Topology

variable {θ : ℝ}

/-- Lower endpoint of the prime ranges `[fillLower θ * Y, Y]` used at scale `Y`. -/
private noncomputable def fillLower (θ : ℝ) : ℝ := (1 - θ) / 4

/-- Admissibility margin `fillMargin θ * Y` used at scale `Y`. -/
private noncomputable def fillMargin (θ : ℝ) : ℝ := min ((1 - θ) / 2) (2 * θ)

/-- The exceptional set of the restricted Goldbach problem at scale `Y`, with the parameters of
the filling argument. -/
private noncomputable def fillExceptional (θ Y : ℝ) : Finset ℕ :=
  exceptionalSet 1 (fillLower θ) 1 (fillLower θ) 1 (fillMargin θ) 2 Y

private theorem fillMargin_pos (hθ0 : 0 < θ) (hθ1 : θ < 1) : 0 < fillMargin θ :=
  lt_min (by linarith) (by linarith)

/-- An even target `2 * m` with `(1 - θ) Y / 2 < m ≤ (1 - θ) Y` is admissible for the ranges
`[fillLower θ * Y, Y]` with margin `fillMargin θ * Y`. -/
private theorem isAdmissible_two_mul (hθ0 : 0 < θ) (hθ1 : θ < 1) {Y : ℝ} (hY : 0 < Y) {m : ℕ}
    (hm1 : (1 - θ) * Y / 2 < m) (hm2 : (m : ℝ) ≤ (1 - θ) * Y) :
    IsAdmissible 1 (fillLower θ * Y) (1 * Y) (fillLower θ * Y) (1 * Y) (fillMargin θ * Y)
      (2 * m) := by
  have hη1 : fillMargin θ ≤ (1 - θ) / 2 := min_le_left _ _
  have hη2 : fillMargin θ ≤ 2 * θ := min_le_right _ _
  have hη0 : 0 < fillMargin θ := fillMargin_pos hθ0 hθ1
  have hα : fillLower θ = (1 - θ) / 4 := rfl
  -- The four endpoint inequalities behind `max (α Y) (2 m - Y) + η Y ≤ min Y (2 m - α Y)`.
  have h1 : fillLower θ * Y + fillMargin θ * Y ≤ Y := by rw [hα]; nlinarith
  have h2 : fillLower θ * Y + fillMargin θ * Y ≤ 2 * m - fillLower θ * Y := by rw [hα]; nlinarith
  have h3 : 2 * m - Y + fillMargin θ * Y ≤ Y := by nlinarith
  have h4 : 2 * m - Y + fillMargin θ * Y ≤ 2 * m - fillLower θ * Y := by rw [hα]; nlinarith
  have hs1 : fillLower θ * Y ≤ max (fillLower θ * Y) (2 * m - Y) := le_max_left _ _
  have hs2 : 2 * (m : ℝ) - Y ≤ max (fillLower θ * Y) (2 * m - Y) := le_max_right _ _
  have hs3 : max (fillLower θ * Y) (2 * m - Y) ≤ 2 * m - fillLower θ * Y - fillMargin θ * Y :=
    max_le (by linarith) (by linarith)
  have hs4 : max (fillLower θ * Y) (2 * m - Y) ≤ Y - fillMargin θ * Y :=
    max_le (by linarith) (by linarith)
  refine ⟨max (fillLower θ * Y) (2 * m - Y), le_max_left _ _, ?_, ?_⟩
  · rw [one_mul]
    linarith
  · intro v hv1 hv2
    push_cast
    rw [one_mul, one_mul]
    constructor <;> linarith

/-- At a single scale `Y`, the integers in `((1 - θ) Y / 2, (1 - θ) Y]` missing from `gen (n + 1)`
inject into the exceptional set via `m ↦ 2 m`. -/
private theorem card_missing_le_card_fillExceptional (hθ0 : 0 < θ) (hθ1 : θ < 1) {Y : ℝ}
    (hY : 4 ≤ (1 - θ) * Y) {n : ℕ} (hn : PrimePrefix n Y) :
    #{m ∈ Icc 1 ⌊(1 - θ) * Y⌋₊ | m ∉ gen (n + 1) ∧ (1 - θ) * Y / 2 < m} ≤
      #(fillExceptional θ Y) := by
  have hY0 : 0 < Y := by nlinarith
  refine card_le_card_of_injOn (fun m ↦ 2 * m) ?_ ?_
  · intro m hm
    show 2 * m ∈ fillExceptional θ Y
    rw [mem_coe, mem_filter, mem_Icc] at hm
    obtain ⟨⟨hm1, hm2⟩, hmn, hmlt⟩ := hm
    have hm2' : (m : ℝ) ≤ (1 - θ) * Y :=
      (Nat.cast_le.mpr hm2).trans (Nat.floor_le (by nlinarith))
    have hm3 : 2 ≤ m := by
      have : (2 : ℝ) < m := by linarith
      exact_mod_cast this.le
    rw [fillExceptional, mem_exceptionalSet]
    refine ⟨mem_Icc.mpr ⟨by omega, Nat.le_floor ?_⟩, ?_, isAdmissible_two_mul hθ0 hθ1 hY0 hmlt hm2',
      ?_⟩
    · push_cast
      nlinarith
    · exact odd_two_mul_add_one m
    · rintro ⟨p, q, hp, hq, hpq⟩
      have hp' : p ∈ gen n := hn.primesIcc_subset (by rw [one_mul]) hp
      have hq' : q ∈ gen n := hn.primesIcc_subset (by rw [one_mul]) hq
      exact hmn (mem_gen_succ_of_add_eq_two_mul hp' hq' hm3 (by omega))
  · intro a _ b _ hab
    simpa using hab

/-- One step of the dyadic descent. -/
private theorem holes_floor_le_holes_floor_half (hθ0 : 0 < θ) (hθ1 : θ < 1) {Y : ℝ}
    (hY : 4 ≤ (1 - θ) * Y) {n : ℕ} (hn : PrimePrefix n Y) :
    holes (n + 1) ⌊(1 - θ) * Y⌋₊ ≤
      holes (n + 1) ⌊(1 - θ) * (Y / 2)⌋₊ + #(fillExceptional θ Y) := by
  refine (holes_le_holes_add_card _ ⌊(1 - θ) * (Y / 2)⌋₊ _).trans (Nat.add_le_add_left ?_ _)
  refine (card_le_card ?_).trans (card_missing_le_card_fillExceptional hθ0 hθ1 hY hn)
  intro m hm
  simp only [mem_filter] at hm ⊢
  refine ⟨hm.1, hm.2.1, ?_⟩
  have h1 : (1 - θ) * (Y / 2) < ⌊(1 - θ) * (Y / 2)⌋₊ + 1 := Nat.lt_floor_add_one _
  have h2 : (⌊(1 - θ) * (Y / 2)⌋₊ : ℝ) + 1 ≤ m := by exact_mod_cast hm.2.2
  linarith

/-- The inequality `2 log Y ≤ 3 log (Y / 2)` for `Y ≥ 8`, in the form used to absorb the error of
one dyadic step: `4 ε' (Y / 2) / log (Y / 2) + ε' Y / log Y ≤ 4 ε' Y / log Y`. -/
private theorem absorb_step {ε' Y : ℝ} (hε' : 0 ≤ ε') (hY : 8 ≤ Y) :
    4 * ε' * (Y / 2 / log (Y / 2)) + ε' * (Y / log Y) ≤ 4 * ε' * (Y / log Y) := by
  have hY0 : 0 < Y := by linarith
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  have hlogY : 3 * log 2 ≤ log Y := by
    have h8 : log ((2 : ℝ) ^ 3) = 3 * log 2 := by rw [log_pow]; norm_num
    rw [← h8]
    exact log_le_log (by norm_num) (by norm_num; linarith)
  have hlogY0 : 0 < log Y := by linarith
  have hhalf : log (Y / 2) = log Y - log 2 := log_div hY0.ne' (by norm_num)
  have hlogh0 : 0 < log (Y / 2) := by rw [hhalf]; linarith
  have key : Y / 2 / log (Y / 2) ≤ 3 / 4 * (Y / log Y) := by
    rw [hhalf, div_div, div_le_iff₀ (by linarith : 0 < 2 * (log Y - log 2))]
    have : 3 / 4 * (Y / log Y) * (2 * (log Y - log 2)) =
        Y * (3 * (log Y - log 2) / (2 * log Y)) := by
      field_simp
      ring
    rw [this]
    refine le_mul_of_one_le_right hY0.le ?_
    rw [le_div_iff₀ (by positivity)]
    linarith
  nlinarith

/-- The inductive bound of the dyadic descent: if the exceptional set is at most
`ε' Y / log Y` for all `Y ≥ Y₀`, then `holes (n + 1) ⌊(1 - θ) Y⌋₊ ≤ Y₀ + 4 ε' Y / log Y` for all
`Y ≥ 16` and every generation `n` with `PrimePrefix n Y`. -/
private theorem holes_floor_le_of_forall (hθ0 : 0 < θ) (hθ1 : θ < 1) {ε' Y₀ : ℝ} (hε' : 0 ≤ ε')
    (hY₀ : 32 ≤ Y₀) (hY₀' : 4 ≤ (1 - θ) * Y₀)
    (hE : ∀ Y : ℝ, Y₀ ≤ Y → (#(fillExceptional θ Y) : ℝ) ≤ ε' * (Y / log Y)) :
    ∀ k : ℕ, ∀ Y : ℝ, ⌊Y⌋₊ = k → 16 ≤ Y → ∀ n : ℕ, PrimePrefix n Y →
      (holes (n + 1) ⌊(1 - θ) * Y⌋₊ : ℝ) ≤ Y₀ + 4 * ε' * (Y / log Y) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro Y hk hY n hn
    have hY0 : 0 < Y := by linarith
    have hlogY : 0 < log Y := log_pos (by linarith)
    have hnonneg : 0 ≤ 4 * ε' * (Y / log Y) := by positivity
    rcases lt_or_ge Y Y₀ with hlt | hge
    · -- Below the threshold: the trivial bound `holes ≤ (1 - θ) Y ≤ Y < Y₀`.
      have h1 : (holes (n + 1) ⌊(1 - θ) * Y⌋₊ : ℝ) ≤ ⌊(1 - θ) * Y⌋₊ := by
        exact_mod_cast holes_le _ _
      have h2 : (⌊(1 - θ) * Y⌋₊ : ℝ) ≤ (1 - θ) * Y := Nat.floor_le (by nlinarith)
      have h3 : (1 - θ) * Y ≤ Y := by nlinarith
      linarith
    · -- Above the threshold: one dyadic step and the inductive hypothesis at `Y / 2`.
      have hhalf : ⌊Y / 2⌋₊ < k := by
        rw [← hk]
        have h1 : (⌊Y / 2⌋₊ : ℝ) ≤ Y / 2 := Nat.floor_le (by positivity)
        have h2 : Y < ⌊Y⌋₊ + 1 := Nat.lt_floor_add_one Y
        exact_mod_cast (show (⌊Y / 2⌋₊ : ℝ) < ⌊Y⌋₊ by linarith)
      have hY4 : 4 ≤ (1 - θ) * Y := hY₀'.trans (by nlinarith)
      have hstep := holes_floor_le_holes_floor_half hθ0 hθ1 hY4 hn
      have hih := ih _ hhalf (Y / 2) rfl (by linarith) n (hn.anti (by linarith))
      have hEY := hE Y hge
      have habs := absorb_step (Y := Y) hε' (by linarith)
      have hstep' : (holes (n + 1) ⌊(1 - θ) * Y⌋₊ : ℝ) ≤
          holes (n + 1) ⌊(1 - θ) * (Y / 2)⌋₊ + #(fillExceptional θ Y) := by exact_mod_cast hstep
      linarith

/-- **Buffered filling.** Under the restricted Goldbach hypothesis, for fixed `0 < θ < 1` and
`ε > 0`, for all sufficiently large `X`: if every prime up to `X` lies in `gen n`, then at most
`ε X / log X` integers in `[1, (1 - θ) X]` are missing from `gen (n + 1)`. The threshold on `X`
does not depend on `n`. -/
theorem RestrictedBinary.eventually_holes_le (h : RestrictedBinary 1) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, ∀ n : ℕ, PrimePrefix n X →
      (holes (n + 1) ⌊(1 - θ) * X⌋₊ : ℝ) ≤ ε * (X / log X) := by
  have hα : 0 < fillLower θ := by unfold fillLower; linarith
  have hα1 : fillLower θ < 1 := by unfold fillLower; linarith
  have htend := h (fillLower θ) 1 (fillLower θ) 1 (fillMargin θ) 2 hα hα1 hα hα1
    (fillMargin_pos hθ0 hθ1) two_pos
  -- Choose the threshold `Y₀` beyond which the exceptional set is at most `(ε / 8) Y / log Y`.
  have hev : ∀ᶠ Y : ℝ in atTop, (#(fillExceptional θ Y) : ℝ) ≤ ε / 8 * (Y / log Y) := by
    have h8 : (0 : ℝ) < ε / 8 := by positivity
    filter_upwards [(tendsto_order.mp htend).2 _ h8, eventually_gt_atTop 1] with Y hY hY1
    have hpos : 0 < Y / log Y := div_pos (by linarith) (log_pos hY1)
    rw [fillExceptional]
    exact (div_le_iff₀ hpos).mp hY.le
  obtain ⟨Y₁, hY₁⟩ := eventually_atTop.mp hev
  set Y₀ : ℝ := max (max Y₁ 32) (4 / (1 - θ)) with hY₀def
  have hY₀32 : 32 ≤ Y₀ := (le_max_right _ _).trans (le_max_left _ _)
  have hY₀θ : 4 ≤ (1 - θ) * Y₀ := by
    have : 4 / (1 - θ) ≤ Y₀ := le_max_right _ _
    rw [div_le_iff₀ (by linarith)] at this
    linarith
  have hE : ∀ Y : ℝ, Y₀ ≤ Y → (#(fillExceptional θ Y) : ℝ) ≤ ε / 8 * (Y / log Y) := fun Y hY ↦
    hY₁ Y (((le_max_left _ _).trans (le_max_left _ _)).trans hY)
  have hmain := holes_floor_le_of_forall hθ0 hθ1 (by positivity) hY₀32 hY₀θ hE
  -- Finally `Y₀ ≤ (ε / 2) X / log X` for large `X`.
  have hfin : ∀ᶠ X : ℝ in atTop, Y₀ ≤ ε / 2 * (X / log X) := by
    have := tendsto_self_div_log_atTop.const_mul_atTop (by positivity : (0 : ℝ) < ε / 2)
    exact this.eventually_ge_atTop Y₀
  filter_upwards [hfin, eventually_ge_atTop 16] with X hX hX16 n hn
  have := hmain ⌊X⌋₊ X rfl hX16 n hn
  linarith

end Conway
