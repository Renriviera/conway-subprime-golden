/-
Copyright (c) 2026 Romain Popescu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Romain Popescu
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Tauto

/-!
# Primes in a real interval

This file defines `Nat.primesIcc a b`, the finite set of primes in the real interval `[a, b]`,
and records its basic membership and monotonicity properties. It is the natural object for
stating prime-number estimates in intervals with real endpoints such as `[α * X, β * X]`.

## Main definitions

* `Nat.primesIcc a b`: the primes `p` with `a ≤ p ≤ b`, for real `a b`.

## Main statements

* `Nat.mem_primesIcc`: `p ∈ primesIcc a b ↔ p.Prime ∧ a ≤ p ∧ p ≤ b`.
* `Nat.primesIcc_subset_primesLE`: `primesIcc a b ⊆ primesLE ⌊b⌋₊`.
-/

namespace Nat

open Finset

/-- The finite set of primes in the real interval `[a, b]`. -/
noncomputable def primesIcc (a b : ℝ) : Finset ℕ := {p ∈ Icc ⌈a⌉₊ ⌊b⌋₊ | p.Prime}

variable {a b : ℝ} {p : ℕ}

theorem mem_primesIcc : p ∈ primesIcc a b ↔ p.Prime ∧ a ≤ p ∧ (p : ℝ) ≤ b := by
  simp only [primesIcc, mem_filter, mem_Icc, Nat.ceil_le]
  rcases le_or_gt 0 b with hb | hb
  · rw [Nat.le_floor_iff hb]
    tauto
  · have h0 : ⌊b⌋₊ = 0 := Nat.floor_of_nonpos hb.le
    rw [h0]
    constructor
    · rintro ⟨⟨-, hp0⟩, hp⟩
      exact absurd (Nat.le_zero.mp hp0) hp.ne_zero
    · rintro ⟨-, -, hpb⟩
      have : (0 : ℝ) ≤ p := Nat.cast_nonneg p
      linarith

theorem prime_of_mem_primesIcc (hp : p ∈ primesIcc a b) : p.Prime := (mem_primesIcc.mp hp).1

theorem le_of_mem_primesIcc (hp : p ∈ primesIcc a b) : a ≤ p := (mem_primesIcc.mp hp).2.1

theorem le_of_mem_primesIcc' (hp : p ∈ primesIcc a b) : (p : ℝ) ≤ b := (mem_primesIcc.mp hp).2.2

theorem primesIcc_subset_primesIcc {a' b' : ℝ} (ha : a' ≤ a) (hb : b ≤ b') :
    primesIcc a b ⊆ primesIcc a' b' := by
  intro p hp
  rw [mem_primesIcc] at hp ⊢
  exact ⟨hp.1, ha.trans hp.2.1, hp.2.2.trans hb⟩

theorem primesIcc_subset_primesLE : primesIcc a b ⊆ primesLE ⌊b⌋₊ := by
  intro p hp
  rw [mem_primesIcc] at hp
  rw [mem_primesLE]
  refine ⟨Nat.le_floor hp.2.2, hp.1⟩

theorem card_primesIcc_le_primeCounting : #(primesIcc a b) ≤ primeCounting ⌊b⌋₊ := by
  rw [← primesLE_card_eq_primeCounting]
  exact card_le_card primesIcc_subset_primesLE

/-- The number of primes in a natural interval `[m, k]` is at most `π k`. -/
theorem card_filter_prime_Icc_le_primeCounting (m k : ℕ) :
    #{p ∈ Icc m k | p.Prime} ≤ primeCounting k := by
  rw [← primesLE_card_eq_primeCounting]
  refine card_le_card fun p hp ↦ ?_
  rw [mem_filter, mem_Icc] at hp
  exact mem_primesLE.mpr ⟨hp.1.2, hp.2⟩

/-- The primes in `[a, b]` are the primes in `[1, ⌊b⌋₊]` that are at least `a`. -/
theorem primesIcc_eq_filter : primesIcc a b = {p ∈ primesLE ⌊b⌋₊ | a ≤ ((p : ℕ) : ℝ)} := by
  ext p
  simp only [mem_primesIcc, mem_filter, mem_primesLE]
  rcases le_or_gt 0 b with hb | hb
  · rw [Nat.le_floor_iff hb]
    tauto
  · have h0 : ⌊b⌋₊ = 0 := Nat.floor_of_nonpos hb.le
    rw [h0]
    constructor
    · rintro ⟨-, -, hpb⟩
      have : (0 : ℝ) ≤ p := Nat.cast_nonneg p
      linarith
    · rintro ⟨⟨hp0, hp⟩, -⟩
      exact absurd (Nat.le_zero.mp hp0) hp.ne_zero

end Nat
