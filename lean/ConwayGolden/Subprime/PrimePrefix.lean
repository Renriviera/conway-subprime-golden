/-
Copyright (c) 2026 Romain Popescu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Romain Popescu
-/
import ConwayGolden.NumberTheory.PrimesIcc
import ConwayGolden.Subprime.Basic

/-!
# Complete prime prefixes of a generation

The asymptotic analysis of Conway's closure is organised around the predicate
`Conway.PrimePrefix n L`: every prime `p ≤ L` belongs to `gen n`. The real parameter `L` is a
*cutoff*; the analysis propagates cutoffs from one generation to the next.

## Main definitions

* `Conway.PrimePrefix n L`: every prime at most `L` lies in `gen n`.

## Main statements

* `Conway.PrimePrefix.mono`, `Conway.PrimePrefix.anti`: monotonicity in the generation and
  antitonicity in the cutoff.
* `Conway.PrimePrefix.primesIcc_subset`: primes in a real interval below the cutoff lie in `gen n`.
* `Conway.PrimePrefix.le_genMax`: a prime `p ≤ L` bounds `genMax n` from below.
-/

namespace Conway

open Finset

/-- `PrimePrefix n L` means that every prime `p ≤ L` lies in the generation `gen n`. -/
def PrimePrefix (n : ℕ) (L : ℝ) : Prop := ∀ p : ℕ, p.Prime → (p : ℝ) ≤ L → p ∈ gen n

namespace PrimePrefix

variable {n m : ℕ} {L L' : ℝ}

theorem mem (h : PrimePrefix n L) {p : ℕ} (hp : p.Prime) (hpL : (p : ℝ) ≤ L) : p ∈ gen n :=
  h p hp hpL

theorem mono (h : PrimePrefix n L) (hnm : n ≤ m) : PrimePrefix m L :=
  fun p hp hpL ↦ gen_mono hnm (h p hp hpL)

theorem anti (h : PrimePrefix n L) (hL : L' ≤ L) : PrimePrefix n L' :=
  fun p hp hpL ↦ h p hp (hpL.trans hL)

theorem of_Icc_subset {k : ℕ} (h : Icc 1 k ⊆ gen n) : PrimePrefix n k := fun p hp hpk ↦
  h (mem_Icc.mpr ⟨hp.one_le, by exact_mod_cast hpk⟩)

/-- The primes of a real interval `[a, b]` with `b ≤ L` lie in `gen n`. -/
theorem primesIcc_subset (h : PrimePrefix n L) {a b : ℝ} (hb : b ≤ L) :
    Nat.primesIcc a b ⊆ gen n := fun p hp ↦
  h p (Nat.prime_of_mem_primesIcc hp) ((Nat.le_of_mem_primesIcc' hp).trans hb)

/-- A prime `p ≤ L` bounds the maximum of `gen n` from below. -/
theorem le_genMax (h : PrimePrefix n L) {p : ℕ} (hp : p.Prime) (hpL : (p : ℝ) ≤ L) :
    (p : ℝ) ≤ genMax n := by
  exact_mod_cast Conway.le_genMax (h p hp hpL)

/-- If the prime interval `[a, L]` is nonempty, then `a ≤ genMax n`. -/
theorem le_genMax_of_nonempty (h : PrimePrefix n L) {a : ℝ} (hne : (Nat.primesIcc a L).Nonempty) :
    a ≤ genMax n := by
  obtain ⟨p, hp⟩ := hne
  rw [Nat.mem_primesIcc] at hp
  exact hp.2.1.trans (h.le_genMax hp.1 hp.2.2)

end PrimePrefix

end Conway
