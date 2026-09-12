/-
Copyright (c) 2026 Romain Popescu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Romain Popescu
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import ConwayGolden.NumberTheory.PrimesIcc
import ConwayGolden.Subprime.Basic

/-!
# Analytic hypotheses for the golden-ratio limit of Conway's closure

The proof that `#(gen (n + 1)) / #(gen n)` tends to the golden ratio is a *conditional
reduction*: it takes as input a small number of statements from analytic number theory, none of
which is currently available in Mathlib. This file states those inputs precisely, in the form in
which they appear in the literature, as the `Prop`-valued structure `Conway.Hypotheses`.

## Main definitions

* `Conway.HasPrimeRepr ν a b c d N`: `N = ν * p + q` for primes `p ∈ [a, b]`, `q ∈ [c, d]`.
* `Conway.IsAdmissible ν a b c d η N`: the set of real `v ∈ [a, b]` with `N - ν * v ∈ [c, d]`
  contains an interval of length `η`.
* `Conway.exceptionalSet ν α β γ δ η B X`: the admissible targets `N ≤ B * X` of the right
  parity without a representation `N = ν * p + q`, `p ∈ [α X, β X]`, `q ∈ [γ X, δ X]`.
* `Conway.RestrictedBinary ν`: for all fixed parameters, the exceptional set has
  `o(X / log X)` elements.
* `Conway.Hypotheses`: the analytic hypotheses of the reduction.

## Implementation notes

`IsAdmissible` replaces the length of the real solution set `{v ∈ [a, b] : N - ν v ∈ [c, d]}`
(an interval) by the existence of a subinterval of the required length. The two formulations are
equivalent, and the existential one is far easier to verify in applications.

The hypothesis `RestrictedBinary ν` asserts no uniformity in the interval parameters: every
parameter is fixed before the limit is taken. Only finitely many parameter tuples are used in the
proof.

## References

* [T. Tao, *254A, Notes 8: The Hardy–Littlewood circle method and Vinogradov's theorem*][Tao2015]
  for the classical analytic source of `RestrictedBinary`.
-/

namespace Conway

open Filter Finset Topology

/-- `N` is a sum `ν * p + q` of primes with `p ∈ [a, b]` and `q ∈ [c, d]`. -/
def HasPrimeRepr (ν : ℕ) (a b c d : ℝ) (N : ℕ) : Prop :=
  ∃ p q : ℕ, p ∈ Nat.primesIcc a b ∧ q ∈ Nat.primesIcc c d ∧ N = ν * p + q

/-- `N` is *admissible* for the ranges `[a, b]`, `[c, d]` with margin `η`: some subinterval
`[s, s + η]` of `[a, b]` consists of real numbers `v` with `N - ν * v ∈ [c, d]`. -/
def IsAdmissible (ν : ℕ) (a b c d η : ℝ) (N : ℕ) : Prop :=
  ∃ s : ℝ, a ≤ s ∧ s + η ≤ b ∧
    ∀ v : ℝ, s ≤ v → v ≤ s + η → c ≤ N - ν * v ∧ N - ν * v ≤ d

open scoped Classical in
/-- The targets `N ∈ [1, B * X]` of the parity of `ν + 1` that are admissible for the ranges
`[α X, β X]`, `[γ X, δ X]` with margin `η X`, yet have no representation `N = ν * p + q` with primes
in those ranges. -/
noncomputable def exceptionalSet (ν : ℕ) (α β γ δ η B X : ℝ) : Finset ℕ :=
  {N ∈ Icc 1 ⌊B * X⌋₊ | Odd (N + ν) ∧
    IsAdmissible ν (α * X) (β * X) (γ * X) (δ * X) (η * X) N ∧
    ¬ HasPrimeRepr ν (α * X) (β * X) (γ * X) (δ * X) N}

theorem mem_exceptionalSet {ν : ℕ} {α β γ δ η B X : ℝ} {N : ℕ} :
    N ∈ exceptionalSet ν α β γ δ η B X ↔
      N ∈ Icc 1 ⌊B * X⌋₊ ∧ Odd (N + ν) ∧
        IsAdmissible ν (α * X) (β * X) (γ * X) (δ * X) (η * X) N ∧
        ¬ HasPrimeRepr ν (α * X) (β * X) (γ * X) (δ * X) N := by
  classical
  simp only [exceptionalSet, mem_filter]

/-- **Restricted almost-all binary representations.** For every choice of fixed proportional
ranges and margin, the exceptional set at scale `X` has `o(X / log X)` elements. The case `ν = 1`
is the almost-all binary Goldbach problem with summands in fixed ranges; `ν = 2` is the analogous
problem for `N = 2 * p + q`. -/
def RestrictedBinary (ν : ℕ) : Prop :=
  ∀ α β γ δ η B : ℝ, 0 < α → α < β → 0 < γ → γ < δ → 0 < η → 0 < B →
    Tendsto (fun X : ℝ ↦ (#(exceptionalSet ν α β γ δ η B X) : ℝ) / (X / Real.log X))
      atTop (𝓝 0)

/-- **Primes in proportional intervals.** For fixed `0 < α < β`, the interval `[α X, β X]`
contains `≫ X / log X` primes. This is a consequence of the prime number theorem without error
term; no uniformity in `α, β` is asserted. -/
def PrimesIccLower : Prop :=
  ∀ α β : ℝ, 0 < α → α < β → ∃ c : ℝ, 0 < c ∧
    ∀ᶠ X : ℝ in atTop, c * (X / Real.log X) ≤ #(Nat.primesIcc (α * X) (β * X))

/-- The analytic hypotheses of the conditional reduction.

* `exhaustion` is Theorem 1 of Caragiu–Vicol–Zaki: every initial segment of `ℕ` lies in some
  generation.
* `primesIcc_lower` is the lower bound `#(ℙ ∩ [α X, β X]) ≫ X / log X` for fixed
  `0 < α < β`, a consequence of the prime number theorem without error term.
* `restrictedBinary_one` and `restrictedBinary_two` are `RestrictedBinary 1` and
  `RestrictedBinary 2`. -/
structure Hypotheses : Prop where
  /-- Every initial segment `[1, k]` is contained in some generation. -/
  exhaustion : ∀ k : ℕ, ∃ n : ℕ, Icc 1 k ⊆ gen n
  /-- For fixed `0 < α < β`, the interval `[α X, β X]` contains `≫ X / log X` primes. -/
  primesIcc_lower : PrimesIccLower
  /-- Almost all admissible even targets are sums `p + q` of primes in fixed ranges. -/
  restrictedBinary_one : RestrictedBinary 1
  /-- Almost all admissible odd targets are sums `2 * p + q` of primes in fixed ranges. -/
  restrictedBinary_two : RestrictedBinary 2

/-! ### Elementary consequences of `PrimesIccLower` -/

namespace PrimesIccLower

variable {α β : ℝ}

/-- Eventually, `[α X, β X]` contains a prime. -/
theorem eventually_nonempty (h : PrimesIccLower) (hα : 0 < α) (hαβ : α < β) :
    ∀ᶠ X : ℝ in atTop, (Nat.primesIcc (α * X) (β * X)).Nonempty := by
  obtain ⟨c, hc, hev⟩ := h α β hα hαβ
  filter_upwards [hev, eventually_gt_atTop 1] with X hX hX1
  have hpos : 0 < X / Real.log X := div_pos (by linarith) (Real.log_pos hX1)
  rw [← Finset.card_pos]
  exact_mod_cast (mul_pos hc hpos).trans_le hX

end PrimesIccLower

end Conway
