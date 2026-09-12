/-
Copyright (c) 2026 Romain Popescu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Romain Popescu
-/
import ConwayGolden.Subprime.Basic

/-!
# Generation steps and pigeonhole principles for Conway's closure

The asymptotic analysis of Conway's closure uses analytic number theory only to *count*
(primes in intervals, integers missing from a generation, exceptional targets of a binary
additive problem). Once the counts are known, every step is either a direct bookkeeping check
of how a specific number is generated, or a finite pigeonhole argument. This file isolates
those finite steps, with the counts as explicit hypotheses.

## Main statements

* `Conway.mem_gen_succ_of_add_eq_two_mul`: if `a + b = 2 * m` with `a, b ∈ gen n` and `2 ≤ m`,
  then `m ∈ gen (n + 1)`.
* `Conway.mem_gen_add_two_of_two_mul_eq`: if `t, q ∈ gen n` are odd, `p ∈ gen (n + 1)`, and
  `u` is a prime with `2 * u = t + q + 2 * p`, then `u ∈ gen (n + 2)`.
* `Conway.exists_apply_mem_gen_of_holes_lt`: if an injective image of a candidate set in
  `[1, Y]` has more elements than `gen n` has holes in `[1, Y]`, some image point lies in `gen n`.
* `Conway.exists_mem_gen_and_apply_mem_gen_of_lt`: the variant with two exclusions, where
  the candidate itself and its image must both lie in `gen n`.
-/

namespace Conway

open Finset

/-! ### Generation steps -/

/-- Two elements of `gen n` summing to `2 * m` with `2 ≤ m` produce `m` in the next generation. -/
theorem mem_gen_succ_of_add_eq_two_mul {n a b m : ℕ} (ha : a ∈ gen n) (hb : b ∈ gen n)
    (hm : 2 ≤ m) (h : a + b = 2 * m) : m ∈ gen (n + 1) := by
  have := subprime_add_mem_gen_succ ha hb
  rwa [h, subprime_two_mul hm] at this

/-- Two odd elements of `gen n` produce half their sum in the next generation. -/
theorem add_div_two_mem_gen_succ_of_odd {n t q : ℕ} (ht : t ∈ gen n) (hq : q ∈ gen n)
    (htodd : Odd t) (hqodd : Odd q) (ht3 : 3 ≤ t) : (t + q) / 2 ∈ gen (n + 1) := by
  obtain ⟨m, hm⟩ := htodd.add_odd hqodd
  have hm2 : 2 ≤ m := by have := one_le_of_mem_gen hq; omega
  rw [hm, show (m + m) / 2 = m by omega]
  exact mem_gen_succ_of_add_eq_two_mul ht hq hm2 (by omega)

/-- From odd `t, q ∈ gen n` with `3 ≤ t` and `p ∈ gen (n + 1)`, the even number `t + q` produces
`(t + q) / 2 ∈ gen (n + 1)`, and if `u = p + (t + q) / 2` is prime then `u ∈ gen (n + 2)`. -/
theorem mem_gen_add_two_of_two_mul_eq {n t q p u : ℕ} (ht : t ∈ gen n) (hq : q ∈ gen n)
    (hp : p ∈ gen (n + 1)) (htodd : Odd t) (hqodd : Odd q) (ht3 : 3 ≤ t) (hu : u.Prime)
    (heq : 2 * u = t + q + 2 * p) : u ∈ gen (n + 2) := by
  have hb := add_div_two_mem_gen_succ_of_odd ht hq htodd hqodd ht3
  have h2 : (2 : ℕ) ∣ t + q := (htodd.add_odd hqodd).two_dvd
  have hsum : p + (t + q) / 2 = u := by omega
  exact hsum ▸ add_mem_gen_succ_of_prime hp hb (hsum ▸ hu)

/-! ### Pigeonhole principles -/

/-- **Pigeonhole.** If `f` is injective on a finite set `U` of candidates, maps `U` into `[1, Y]`,
and `U` has more elements than `gen n` has holes in `[1, Y]`, then some `f u` lies in `gen n`. -/
theorem exists_apply_mem_gen_of_holes_lt {n Y : ℕ} {U : Finset ℕ} {f : ℕ → ℕ}
    (hf : Set.InjOn f U) (hfU : ∀ u ∈ U, f u ∈ Icc 1 Y) (h : holes n Y < #U) :
    ∃ u ∈ U, f u ∈ gen n := by
  by_contra hcon
  push Not at hcon
  have hsub : U.image f ⊆ {m ∈ Icc 1 Y | m ∉ gen n} := by
    intro m hm
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hm
    exact mem_filter.mpr ⟨hfU u hu, hcon u hu⟩
  have := card_le_card hsub
  rw [card_image_of_injOn hf] at this
  exact absurd h (not_lt.mpr this)

/-- **Pigeonhole with two exclusions.** If the candidates of `U` outside `gen n`, together with
the holes of `gen n` in `[1, Y]`, are fewer than the candidates, then some candidate `u` and its
image `f u` both lie in `gen n`. -/
theorem exists_mem_gen_and_apply_mem_gen_of_lt {n Y : ℕ} {U : Finset ℕ} {f : ℕ → ℕ}
    (hf : Set.InjOn f U) (hfU : ∀ u ∈ U, f u ∈ Icc 1 Y)
    (h : #{u ∈ U | u ∉ gen n} + holes n Y < #U) :
    ∃ u ∈ U, u ∈ gen n ∧ f u ∈ gen n := by
  have hcard := card_filter_add_card_filter_not (s := U) (fun u ↦ u ∈ gen n)
  have hlt : holes n Y < #{u ∈ U | u ∈ gen n} := by omega
  obtain ⟨u, hu, hfu⟩ := exists_apply_mem_gen_of_holes_lt (hf.mono (filter_subset _ _))
    (fun u hu ↦ hfU u (mem_filter.mp hu).1) hlt
  exact ⟨u, (mem_filter.mp hu).1, (mem_filter.mp hu).2, hfu⟩

end Conway
