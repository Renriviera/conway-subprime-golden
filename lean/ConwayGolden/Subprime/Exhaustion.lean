/-
Copyright (c) 2026 Romain Popescu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Romain Popescu
-/
import Mathlib.NumberTheory.Bertrand
import ConwayGolden.Subprime.Pigeonhole

/-!
# Exhaustion: every integer eventually appears in Conway's closure

We prove that every initial segment `[1, k]` of `ℕ` is contained in some generation `gen n`
(Theorem 1 of Caragiu–Vicol–Zaki). The proof is a strong induction on `m` using Bertrand's
postulate: if `[1, m - 1] ⊆ gen n` and `m ≥ 3`, pick a prime `p` with `m - 1 < p ≤ 2 (m - 1)`.
If `p = m` then `m = (m - 1) + 1` is a prime sum and lies in `gen (n + 1)`. Otherwise
`p = (m - 1) + (p - m + 1)` with both summands in `[1, m - 1]`, so `p ∈ gen (n + 1)`, and then
`p + (2 m - p) = 2 m` with `2 m - p ∈ [2, m - 1]` gives `m = subprime (2 m) ∈ gen (n + 2)`.

## Main statements

* `Conway.Icc_subset_gen_of_Icc_subset`: `[1, m - 1] ⊆ gen n → [1, m] ⊆ gen (n + 2)`.
* `Conway.exhaustion`: `∀ k, ∃ n, Icc 1 k ⊆ gen n`.

## References

* [M. Caragiu, A. Vicol, M. Zaki, *Conway's subprime Fibonacci sequences*][CaragiuVicolZaki]
-/

namespace Conway

open Finset

/-- If `[1, m - 1] ⊆ gen n` and `m - 1 < p ≤ 2 m - 2` is prime, then `p ∈ gen (n + 1)`. -/
theorem prime_mem_gen_succ_of_Icc_subset {n m p : ℕ} (h : Icc 1 (m - 1) ⊆ gen n)
    (hp : p.Prime) (hlo : m - 1 < p) (hhi : p ≤ 2 * (m - 1)) : p ∈ gen (n + 1) := by
  have ha : m - 1 ∈ gen n := h (mem_Icc.mpr ⟨by omega, by omega⟩)
  have hb : p - (m - 1) ∈ gen n := h (mem_Icc.mpr ⟨by omega, by omega⟩)
  have hab : (m - 1) + (p - (m - 1)) = p := by omega
  have hp' : ((m - 1) + (p - (m - 1))).Prime := by simpa [hab] using hp
  have hgen := add_mem_gen_succ_of_prime ha hb hp'
  simpa [hab] using hgen

/-- The inductive step of exhaustion. -/
theorem Icc_subset_gen_of_Icc_subset {n m : ℕ} (hm : 2 ≤ m) (h : Icc 1 (m - 1) ⊆ gen n) :
    Icc 1 m ⊆ gen (n + 2) := by
  obtain ⟨p, hp, hlo, hhi⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (m - 1) (by omega)
  by_cases hpm : p = m
  · have hmgen : m ∈ gen (n + 1) := by
      have ha : m - 1 ∈ gen n := h (mem_Icc.mpr ⟨by omega, by omega⟩)
      have hb : 1 ∈ gen n := h (mem_Icc.mpr ⟨by omega, by omega⟩)
      have hp_m : m.Prime := hpm ▸ hp
      have hsum : (m - 1) + 1 = m := by omega
      have hp' : ((m - 1) + 1).Prime := by rw [hsum]; exact hp_m
      simpa [hsum] using (add_mem_gen_succ_of_prime ha hb hp')
    intro x hx
    rcases mem_Icc.mp hx with ⟨hx1, hxm⟩
    by_cases hxm' : x ≤ m - 1
    · exact gen_mono (by omega) (h (mem_Icc.mpr ⟨hx1, hxm'⟩))
    · have : x = m := by omega
      subst x
      exact gen_mono (by omega) hmgen
  · have hmp : m < p := by omega
    have hpgen : p ∈ gen (n + 1) :=
      prime_mem_gen_succ_of_Icc_subset h hp hlo hhi
    have hbgen : 2 * m - p ∈ gen (n + 1) := by
      apply gen_mono (Nat.le_succ n)
      apply h
      apply mem_Icc.mpr
      omega
    have hmgen : m ∈ gen (n + 2) :=
      mem_gen_succ_of_add_eq_two_mul hpgen hbgen hm (by omega)
    intro x hx
    rcases mem_Icc.mp hx with ⟨hx1, hxm⟩
    by_cases hxm' : x ≤ m - 1
    · exact gen_mono (by omega) (h (mem_Icc.mpr ⟨hx1, hxm'⟩))
    · have : x = m := by omega
      subst x
      exact hmgen

/-- **Exhaustion** (Caragiu–Vicol–Zaki, Theorem 1): every initial segment `[1, k]` of `ℕ` lies
in some generation. -/
theorem exhaustion (k : ℕ) : ∃ n : ℕ, Icc 1 k ⊆ gen n := by
  induction k with
  | zero =>
      refine ⟨0, ?_⟩
      intro x hx
      simp at hx
  | succ k ih =>
      by_cases hk : k = 0
      · refine ⟨0, ?_⟩
        intro x hx
        have : x = 1 := by
          have hx' := mem_Icc.mp hx
          omega
        simpa [this] using one_mem_gen 0
      · obtain ⟨n, hn⟩ := ih
        exact ⟨n + 2, Icc_subset_gen_of_Icc_subset (by omega) hn⟩

end Conway
