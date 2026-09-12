/-
Copyright (c) 2026 Romain Popescu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Romain Popescu
-/
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Conway's subprime function and its additive closure

Conway's *subprime function* sends a prime to itself and a composite number `m` to
`m / minFac m`. Starting from `{1}` and repeatedly adjoining the values `subprime (a + b)` for
all pairs `a, b` of elements already present produces an increasing sequence of finite sets
`Conway.gen n`, which exhausts `ℕ` by a theorem of Caragiu, Vicol and Zaki [CaragiuVicolZaki2017].

This file contains the definitions and the elementary structure of these sets, none of which
uses any input from analytic number theory.

## Main definitions

* `Conway.subprime`: Conway's subprime function.
* `Conway.gen n`: the `n`-th generation of the closure, `gen 0 = {1}` and
  `gen (n + 1) = gen n ∪ subprime (gen n + gen n)`.
* `Conway.genMax n`: the largest element of `gen n`.
* `Conway.holes n Y`: the number of integers in `[1, Y]` missing from `gen n`.

## Main statements

* `Conway.le_genMax_or_prime_of_mem_gen_succ`: every element of `gen (n + 1)` is at most
  `genMax n` or is prime.
* `Conway.genMax_prime`: for `1 ≤ n` the maximum `genMax n` is prime.
* `Conway.genMax_add_two_le`: the Fibonacci inequality `genMax (n + 2) ≤ genMax (n + 1) + genMax n`.
* `Conway.genMax_le_two_mul`: `genMax (n + 1) ≤ 2 * genMax n`.
* `Conway.genMax_le_fib`: `genMax n ≤ fib (n + 2)`.
* `Conway.card_gen_succ_le`, `Conway.le_card_gen_add_holes`: the two-sided cardinality
  estimate `Y - holes n Y ≤ #(gen n) ≤ genMax (n - 1) + π (genMax n)`.

## References

* [M. Caragiu, P. A. Vicol, M. Zaki, *On Conway's subprime function, a covering of `ℕ` and an
  unexpected appearance of the golden ratio*][CaragiuVicolZaki2017]

## Tags

Conway, subprime function, golden ratio
-/

namespace Conway

open Finset

/-- **Conway's subprime function**: `subprime m = m` if `m` is prime, and
`subprime m = m / minFac m` otherwise. -/
def subprime (m : ℕ) : ℕ := if m.Prime then m else m / m.minFac

/-- The `n`-th generation of Conway's closure: `gen 0 = {1}` and
`gen (n + 1) = gen n ∪ {subprime (a + b) | a, b ∈ gen n}`. Repeated inputs `a = b` are allowed. -/
def gen : ℕ → Finset ℕ
  | 0 => {1}
  | n + 1 => gen n ∪ ((gen n ×ˢ gen n).image fun ab : ℕ × ℕ ↦ subprime (ab.1 + ab.2))

/-- The largest element of the `n`-th generation. -/
def genMax (n : ℕ) : ℕ := (gen n).sup id

/-- The number of integers in `[1, Y]` that are missing from `gen n`. -/
def holes (n Y : ℕ) : ℕ := #{m ∈ Icc 1 Y | m ∉ gen n}

/-! ### The subprime function -/

theorem subprime_of_prime {p : ℕ} (hp : p.Prime) : subprime p = p := by simp [subprime, hp]

theorem subprime_of_not_prime {m : ℕ} (hm : ¬ m.Prime) : subprime m = m / m.minFac := by
  simp [subprime, hm]

theorem subprime_le (m : ℕ) : subprime m ≤ m := by
  unfold subprime
  split_ifs
  · exact le_rfl
  · exact Nat.div_le_self _ _

/-- A composite input is at least halved. -/
theorem two_mul_subprime_le {m : ℕ} (hm : ¬ m.Prime) (h2 : 2 ≤ m) : 2 * subprime m ≤ m := by
  rw [subprime_of_not_prime hm]
  have hmin : 2 ≤ m.minFac := (Nat.minFac_prime (by omega)).two_le
  exact (Nat.mul_le_mul_left 2 (Nat.div_le_div_left hmin (by norm_num))).trans
    (Nat.mul_div_le m 2)

theorem one_le_subprime {m : ℕ} (hm : 1 ≤ m) : 1 ≤ subprime m := by
  unfold subprime
  split_ifs
  · exact hm
  · exact Nat.div_pos (Nat.minFac_le hm) (Nat.minFac_pos m)

/-- The halving branch: `subprime (2 * m) = m` for `2 ≤ m`. -/
theorem subprime_two_mul {m : ℕ} (hm : 2 ≤ m) : subprime (2 * m) = m := by
  have hnp : ¬ (2 * m).Prime := Nat.not_prime_mul (by norm_num) (by omega)
  rw [subprime_of_not_prime hnp, (Nat.minFac_eq_two_iff _).mpr (dvd_mul_right 2 m)]
  exact Nat.mul_div_cancel_left m (by norm_num)

/-! ### Membership in the generations -/

theorem mem_gen_succ_iff {n x : ℕ} :
    x ∈ gen (n + 1) ↔ x ∈ gen n ∨ ∃ a ∈ gen n, ∃ b ∈ gen n, subprime (a + b) = x := by
  simp only [gen, mem_union, mem_image, mem_product, Prod.exists]
  constructor
  · rintro (h | ⟨a, b, ⟨ha, hb⟩, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨a, ha, b, hb, rfl⟩
  · rintro (h | ⟨a, ha, b, hb, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨a, b, ⟨ha, hb⟩, rfl⟩

theorem gen_subset_succ (n : ℕ) : gen n ⊆ gen (n + 1) := fun _ h ↦ mem_gen_succ_iff.mpr (Or.inl h)

theorem gen_mono : Monotone gen := monotone_nat_of_le_succ gen_subset_succ

/-- Inputs at generation `n` give an output at generation `n + 1`. -/
theorem subprime_add_mem_gen_succ {n a b : ℕ} (ha : a ∈ gen n) (hb : b ∈ gen n) :
    subprime (a + b) ∈ gen (n + 1) :=
  mem_gen_succ_iff.mpr (Or.inr ⟨a, ha, b, hb, rfl⟩)

/-- If `a, b ∈ gen n` and `a + b` is prime, then `a + b ∈ gen (n + 1)`. -/
theorem add_mem_gen_succ_of_prime {n a b : ℕ} (ha : a ∈ gen n) (hb : b ∈ gen n)
    (hp : (a + b).Prime) : a + b ∈ gen (n + 1) :=
  subprime_of_prime hp ▸ subprime_add_mem_gen_succ ha hb

theorem gen_zero : gen 0 = {1} := rfl

theorem one_mem_gen (n : ℕ) : 1 ∈ gen n := gen_mono (Nat.zero_le n) (by simp [gen])

theorem one_le_of_mem_gen {n x : ℕ} (hx : x ∈ gen n) : 1 ≤ x := by
  induction n generalizing x with
  | zero => simp [gen] at hx; omega
  | succ n ih =>
    rcases mem_gen_succ_iff.mp hx with h | ⟨a, ha, b, hb, rfl⟩
    · exact ih h
    · exact one_le_subprime (by have := ih ha; omega)

theorem two_mem_gen_one : 2 ∈ gen 1 :=
  add_mem_gen_succ_of_prime (one_mem_gen 0) (one_mem_gen 0) Nat.prime_two

theorem two_mem_gen {n : ℕ} (hn : 1 ≤ n) : 2 ∈ gen n := gen_mono hn two_mem_gen_one

theorem gen_one : gen 1 = {1, 2} := by
  ext x
  simp only [mem_insert, mem_singleton]
  constructor
  · intro hx
    rcases mem_gen_succ_iff.mp hx with h | ⟨a, ha, b, hb, rfl⟩
    · simp [gen] at h; exact Or.inl h
    · simp only [gen_zero, mem_singleton] at ha hb
      subst ha; subst hb
      exact Or.inr (subprime_of_prime Nat.prime_two)
  · rintro (rfl | rfl)
    · exact one_mem_gen 1
    · exact two_mem_gen_one

theorem gen_nonempty (n : ℕ) : (gen n).Nonempty := ⟨1, one_mem_gen n⟩

/-! ### The maximum -/

theorem le_genMax {n x : ℕ} (hx : x ∈ gen n) : x ≤ genMax n := Finset.le_sup (f := id) hx

theorem genMax_le_iff {n k : ℕ} : genMax n ≤ k ↔ ∀ x ∈ gen n, x ≤ k := Finset.sup_le_iff

theorem genMax_mono : Monotone genMax := fun _ _ h ↦ Finset.sup_mono (gen_mono h)

theorem one_le_genMax (n : ℕ) : 1 ≤ genMax n := le_genMax (one_mem_gen n)

theorem genMax_pos (n : ℕ) : 0 < genMax n := one_le_genMax n

theorem genMax_mem (n : ℕ) : genMax n ∈ gen n := by
  obtain ⟨x, hx, hxeq⟩ := Finset.exists_mem_eq_sup (gen n) (gen_nonempty n) id
  simpa [genMax, hxeq] using hx

theorem genMax_zero : genMax 0 = 1 := by simp [genMax, gen]

theorem genMax_one : genMax 1 = 2 := by
  apply le_antisymm
  · rw [genMax_le_iff, gen_one]
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    omega
  · exact le_genMax two_mem_gen_one

theorem three_mem_gen_two : 3 ∈ gen 2 :=
  add_mem_gen_succ_of_prime (one_mem_gen 1) two_mem_gen_one Nat.prime_three

theorem genMax_two : genMax 2 = 3 := by
  refine le_antisymm ?_ (le_genMax three_mem_gen_two)
  rw [genMax_le_iff]
  intro r hr
  rcases mem_gen_succ_iff.mp hr with h | ⟨a, ha, b, hb, rfl⟩
  · have := le_genMax h
    rw [genMax_one] at this
    omega
  · rw [gen_one] at ha hb
    simp only [mem_insert, mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · have := subprime_le (1 + 1); omega
    · have := subprime_le (1 + 2); omega
    · have := subprime_le (2 + 1); omega
    · have := two_mul_subprime_le (m := 2 + 2) (by decide) (by omega); omega

/-- A composite output formed from `gen n` is at most `genMax n`. -/
theorem subprime_add_le_genMax_of_not_prime {n a b : ℕ} (ha : a ∈ gen n) (hb : b ∈ gen n)
    (h : ¬ (a + b).Prime) : subprime (a + b) ≤ genMax n := by
  have h1 := le_genMax ha
  have h2 := le_genMax hb
  have := two_mul_subprime_le h
    (by have := one_le_of_mem_gen ha; have := one_le_of_mem_gen hb; omega)
  omega

/-- Every element of `gen (n + 1)` is at most `genMax n` or is prime. -/
theorem le_genMax_or_prime_of_mem_gen_succ {n x : ℕ} (hx : x ∈ gen (n + 1)) :
    x ≤ genMax n ∨ x.Prime := by
  rcases mem_gen_succ_iff.mp hx with h | ⟨a, ha, b, hb, rfl⟩
  · exact Or.inl (le_genMax h)
  · by_cases hp : (a + b).Prime
    · exact Or.inr ((subprime_of_prime hp).symm ▸ hp)
    · exact Or.inl (subprime_add_le_genMax_of_not_prime ha hb hp)

/-- An element of `gen (n + 1)` above `genMax n` is prime. -/
theorem prime_of_mem_gen_succ_of_genMax_lt {n r : ℕ} (hr : r ∈ gen (n + 1)) (hM : genMax n < r) :
    r.Prime :=
  (le_genMax_or_prime_of_mem_gen_succ hr).resolve_left (not_le.mpr hM)

/-- An element of `gen (n + 1)` above `genMax n` is a sum of two elements of `gen n`. -/
theorem exists_add_eq_of_mem_gen_succ_of_genMax_lt {n r : ℕ} (hr : r ∈ gen (n + 1))
    (hM : genMax n < r) : ∃ a ∈ gen n, ∃ b ∈ gen n, a + b = r := by
  rcases mem_gen_succ_iff.mp hr with h | ⟨a, ha, b, hb, rfl⟩
  · exact absurd (le_genMax h) (not_le.mpr hM)
  · by_cases hp : (a + b).Prime
    · exact ⟨a, ha, b, hb, (subprime_of_prime hp).symm⟩
    · exact absurd (subprime_add_le_genMax_of_not_prime ha hb hp) (not_le.mpr hM)

/-- Every even element of `gen (n + 1)` is `2` or at most `genMax n`. -/
theorem eq_two_or_le_genMax_of_even {n e : ℕ} (he : e ∈ gen (n + 1)) (hev : Even e) :
    e = 2 ∨ e ≤ genMax n := by
  induction n generalizing e with
  | zero =>
    rcases mem_gen_succ_iff.mp he with h | ⟨a, ha, b, hb, rfl⟩
    · simp only [gen_zero, mem_singleton] at h
      subst h
      exact absurd hev Nat.not_even_one
    · by_cases hp : (a + b).Prime
      · left
        rw [subprime_of_prime hp] at hev ⊢
        exact hp.even_iff.mp hev
      · exact Or.inr (subprime_add_le_genMax_of_not_prime ha hb hp)
  | succ n ih =>
    rcases mem_gen_succ_iff.mp he with h | ⟨a, ha, b, hb, rfl⟩
    · rcases ih h hev with h2 | h2
      · exact Or.inl h2
      · exact Or.inr (h2.trans (genMax_mono (Nat.le_succ n)))
    · by_cases hp : (a + b).Prime
      · left
        rw [subprime_of_prime hp] at hev ⊢
        exact hp.even_iff.mp hev
      · exact Or.inr (subprime_add_le_genMax_of_not_prime ha hb hp)

/-- The **Fibonacci inequality** `genMax (n + 2) ≤ genMax (n + 1) + genMax n`. -/
theorem genMax_add_two_le (n : ℕ) : genMax (n + 2) ≤ genMax (n + 1) + genMax n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [genMax_one, genMax_zero, genMax_two]
  rw [genMax_le_iff]
  intro r hr
  by_cases hle : r ≤ genMax (n + 1)
  · omega
  have hlt : genMax (n + 1) < r := lt_of_not_ge hle
  have hp := prime_of_mem_gen_succ_of_genMax_lt hr hlt
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_add_eq_of_mem_gen_succ_of_genMax_lt hr hlt
  have h2lt : 2 < a + b := by
    have : 2 ≤ genMax (n + 1) := genMax_one ▸ genMax_mono (le_trans hn (Nat.le_succ n))
    omega
  have hodd : Odd (a + b) := hp.odd_of_ne_two (ne_of_gt h2lt)
  have h2M : 2 ≤ genMax n := le_genMax (two_mem_gen hn)
  have hA := le_genMax ha
  have hB := le_genMax hb
  rcases Nat.even_or_odd a with hae | hao
  · rcases eq_two_or_le_genMax_of_even ha hae with h2 | h2 <;> omega
  · have hbe : Even b := by
      rcases Nat.even_or_odd b with h | h
      · exact h
      · exact absurd (hao.add_odd h) (Nat.not_even_iff_odd.mpr hodd)
    rcases eq_two_or_le_genMax_of_even hb hbe with h2 | h2 <;> omega

/-- Consecutive maxima differ by at most a factor of two. -/
theorem genMax_le_two_mul (n : ℕ) : genMax (n + 1) ≤ 2 * genMax n := by
  cases n with
  | zero => rw [genMax_one, genMax_zero]
  | succ n =>
    show genMax (n + 2) ≤ 2 * genMax (n + 1)
    have h1 := genMax_add_two_le n
    have h2 : genMax n ≤ genMax (n + 1) := genMax_mono (Nat.le_succ n)
    omega

/-- `genMax n ≤ fib (n + 2)`. -/
theorem genMax_le_fib (n : ℕ) : genMax n ≤ Nat.fib (n + 2) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rw [genMax_zero]; decide
    | 1 => rw [genMax_one]; decide
    | n + 2 =>
      have h1 := ih (n + 1) (by omega)
      have h2 := ih n (by omega)
      calc
        genMax (n + 2) ≤ genMax (n + 1) + genMax n := genMax_add_two_le n
        _ ≤ Nat.fib (n + 3) + Nat.fib (n + 2) := Nat.add_le_add h1 h2
        _ = Nat.fib (n + 4) := by
          rw [add_comm]
          exact (Nat.fib_add_two (n := n + 2)).symm

/-- Every maximum after the initial stage is prime. -/
theorem genMax_prime {n : ℕ} (hn : 1 ≤ n) : (genMax n).Prime := by
  induction n, hn using Nat.le_induction with
  | base => rw [genMax_one]; exact Nat.prime_two
  | succ n hn ih =>
    by_cases h : genMax (n + 1) ≤ genMax n
    · rwa [le_antisymm h (genMax_mono (Nat.le_succ n))]
    · exact prime_of_mem_gen_succ_of_genMax_lt (genMax_mem (n + 1)) (lt_of_not_ge h)

theorem three_le_genMax {n : ℕ} (hn : 2 ≤ n) : 3 ≤ genMax n := genMax_two ▸ genMax_mono hn

theorem genMax_odd {n : ℕ} (hn : 2 ≤ n) : Odd (genMax n) :=
  (genMax_prime (by omega)).odd_of_ne_two (by have := three_le_genMax hn; omega)

/-! ### Cardinality bounds -/

/-- Holes below `y` are at most the holes below `q ≤ y` plus the length of `(q, y]`. -/
theorem holes_le_add {n q y : ℕ} (h : q ≤ y) : holes n y ≤ (y - q) + holes n q := by
  have hsub : {m ∈ Icc 1 y | m ∉ gen n} ⊆ {m ∈ Icc 1 q | m ∉ gen n} ∪ Icc (q + 1) y := by
    intro m hm
    have hm' := mem_filter.mp hm
    have hmI := mem_Icc.mp hm'.1
    by_cases hq : m ≤ q
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_Icc.mpr ⟨hmI.1, hq⟩, hm'.2⟩)
    · exact mem_union_right _ (mem_Icc.mpr ⟨by omega, hmI.2⟩)
  calc
    holes n y ≤ #({m ∈ Icc 1 q | m ∉ gen n} ∪ Icc (q + 1) y) := card_le_card hsub
    _ ≤ holes n q + #(Icc (q + 1) y) := card_union_le _ _
    _ = holes n q + (y + 1 - (q + 1)) := by rw [Nat.card_Icc]
    _ = (y - q) + holes n q := by omega

theorem holes_mono_right (n : ℕ) : Monotone (holes n) := by
  intro y y' h
  exact card_le_card (filter_subset_filter _ (Icc_subset_Icc_right h))

theorem holes_le (n Y : ℕ) : holes n Y ≤ Y := by
  unfold holes
  simpa using card_le_card (filter_subset (fun m ↦ m ∉ gen n) (Icc 1 Y))

/-- Holes below `y` are at most the holes below `q` plus the holes in `(q, y]`. -/
theorem holes_le_holes_add_card (n q y : ℕ) :
    holes n y ≤ holes n q + #{m ∈ Icc 1 y | m ∉ gen n ∧ q < m} := by
  have hsub : {m ∈ Icc 1 y | m ∉ gen n} ⊆
      {m ∈ Icc 1 q | m ∉ gen n} ∪ {m ∈ Icc 1 y | m ∉ gen n ∧ q < m} := by
    intro m hm
    have hm' := mem_filter.mp hm
    have hmI := mem_Icc.mp hm'.1
    by_cases hq : m ≤ q
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_Icc.mpr ⟨hmI.1, hq⟩, hm'.2⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hm'.1, hm'.2, not_le.mp hq⟩)
  exact (card_le_card hsub).trans (card_union_le _ _)

/-- `#(gen (n + 1)) ≤ genMax n + π (genMax (n + 1))`: the region above the previous maximum
contains only primes. -/
theorem card_gen_succ_le (n : ℕ) :
    #(gen (n + 1)) ≤ genMax n + #{p ∈ Icc 1 (genMax (n + 1)) | p.Prime} := by
  have hsub : gen (n + 1) ⊆ Icc 1 (genMax n) ∪ {p ∈ Icc 1 (genMax (n + 1)) | p.Prime} := by
    intro x hx
    have h1 := one_le_of_mem_gen hx
    rcases le_genMax_or_prime_of_mem_gen_succ hx with h | h
    · exact mem_union_left _ (mem_Icc.mpr ⟨h1, h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_Icc.mpr ⟨h1, le_genMax hx⟩, h⟩)
  calc
    #(gen (n + 1)) ≤ #(Icc 1 (genMax n) ∪ {p ∈ Icc 1 (genMax (n + 1)) | p.Prime}) :=
      card_le_card hsub
    _ ≤ #(Icc 1 (genMax n)) + #{p ∈ Icc 1 (genMax (n + 1)) | p.Prime} := card_union_le _ _
    _ = genMax n + #{p ∈ Icc 1 (genMax (n + 1)) | p.Prime} := by simp

/-- `Y ≤ #(gen n) + holes n Y`. -/
theorem le_card_gen_add_holes (n Y : ℕ) : Y ≤ #(gen n) + holes n Y := by
  have hsub : Icc 1 Y ⊆ gen n ∪ {m ∈ Icc 1 Y | m ∉ gen n} := by
    intro m hm
    by_cases h : m ∈ gen n
    · exact mem_union_left _ h
    · exact mem_union_right _ (mem_filter.mpr ⟨hm, h⟩)
  have := (card_le_card hsub).trans (card_union_le _ _)
  simpa [holes] using this

end Conway
