import ConwayGolden.Basic

/-!
# The three combinatorial mechanisms of the proof

`prime-completeness.md` uses analytic number theory only to *count* things (primes in
intervals, holes below a complete prime prefix, exceptional sets of a binary problem).
Once the counts are known, each step of the argument is a finite pigeonhole or a direct
generation-bookkeeping check.  This file proves those finite steps in full generality, with
the counts as explicit hypotheses, so that the analytic inputs enter only through numerical
inequalities between cardinalities of finite sets.

* `bootstrap_step` — Section 2: if all primes `≤ X` are in `C n` and `[1, Y]` has fewer holes
  in `C n` than there are primes in `[X - h, X]`, then every prime in `(X, X + Y - h]` is in
  `C (n+1)`.
* `outlier_step` — Section 3, equation (8): an odd prime `t` and odd prime `q` in `C n` together
  with a prime `p ∈ C (n+1)` and a prime `u` with `2u = t + q + 2p` force `u ∈ C (n+2)`.
* `closing_step` / `final_step` — Section 4: the target prime `r` is generated as soon as one
  candidate `u` survives the two exclusions.
-/

namespace Conway

open Finset

/-- **Bootstrap step** (Section 2).  Pigeonhole on the injective map `p ↦ r - p`. -/
theorem bootstrap_step {n X Y h : ℕ} (hhX : h ≤ X)
    (hX : ∀ p, p.Prime → p ≤ X → p ∈ C n)
    (hcount : ((Icc 1 Y).filter (fun m => m ∉ C n)).card
        < ((Icc (X - h) X).filter Nat.Prime).card)
    {r : ℕ} (hr : r.Prime) (hrX : X < r) (hrY : r ≤ X + Y - h) :
    r ∈ C (n + 1) := by
  set Pr := (Icc (X - h) X).filter Nat.Prime with hPr
  have hex : ∃ p ∈ Pr, r - p ∈ C n := by
    by_contra hcon
    push Not at hcon
    have hsub : Pr.image (fun p => r - p) ⊆ (Icc 1 Y).filter (fun m => m ∉ C n) := by
      intro m hm
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hm
      have hp' := mem_filter.mp hp
      have hp'' := mem_Icc.mp hp'.1
      refine mem_filter.mpr ⟨mem_Icc.mpr ⟨?_, ?_⟩, hcon p hp⟩ <;> omega
    have hinj : Set.InjOn (fun p => r - p) Pr := by
      intro p hp q hq hpq
      have := (mem_Icc.mp (mem_filter.mp hp).1).2
      have := (mem_Icc.mp (mem_filter.mp hq).1).2
      simp only at hpq
      omega
    have := card_le_card hsub
    rw [card_image_of_injOn hinj] at this
    omega
  obtain ⟨p, hp, hrp⟩ := hex
  have hp' := mem_filter.mp hp
  have hpC : p ∈ C n := hX p hp'.2 (mem_Icc.mp hp'.1).2
  have := s_add_mem hpC hrp
  have hpX : p ≤ X := (mem_Icc.mp hp'.1).2
  have hpr : p ≤ r := le_of_lt (lt_of_le_of_lt hpX hrX)
  rwa [Nat.add_sub_of_le hpr, s_of_prime hr] at this

/-- **Outlier step** (Section 3, display (8)).  From odd primes `t, q ∈ C n` (only oddness and
`t ≥ 3` are used) and `p ∈ C (n+1)`, the even number `b = (t + q)/2` lies in `C (n+1)`, and if
`u = p + b` is prime then `u ∈ C (n+2)`. -/
theorem outlier_step {n t q p u : ℕ} (ht : t ∈ C n) (hq : q ∈ C n) (hp : p ∈ C (n + 1))
    (htodd : Odd t) (hqodd : Odd q) (ht3 : 3 ≤ t) (hu : u.Prime)
    (heq : 2 * u = t + q + 2 * p) : u ∈ C (n + 2) := by
  obtain ⟨m, hm⟩ := htodd.add_odd hqodd
  have hm2 : 2 ≤ m := by have := mem_C_pos hq; omega
  have hb : m ∈ C (n + 1) := by
    have := s_add_mem ht hq
    rwa [hm, ← two_mul, s_two_mul hm2] at this
  have := s_add_mem hp hb
  rwa [show p + m = u by omega, s_of_prime hu] at this

/-- **Closing step** (Section 4). -/
theorem closing_step {n u a r : ℕ} (hu : u ∈ C n) (ha : a ∈ C n) (hr : r.Prime)
    (h : u + a = r) : r ∈ C (n + 1) := by
  have := s_add_mem hu ha
  rwa [h, s_of_prime hr] at this

/-- **Final counting step** (Section 4).  Let `U` be a finite set of candidates `u < r` with
`r - u ∈ [1, Y]`.  If the candidates absent from `C n`, together with the holes of `C n` in
`[1, Y]`, are fewer than the candidates, then some candidate `u` and its complement `r - u`
both lie in `C n`, so the prime `r` lies in `C (n+1)`. -/
theorem final_step {n Y : ℕ} {U : Finset ℕ} {r : ℕ} (hr : r.Prime)
    (hUr : ∀ u ∈ U, 1 ≤ r - u ∧ r - u ≤ Y)
    (hcount : (U.filter (fun u => u ∉ C n)).card
        + ((Icc 1 Y).filter (fun m => m ∉ C n)).card < U.card) :
    r ∈ C (n + 1) := by
  have hex : ∃ u ∈ U, u ∈ C n ∧ r - u ∈ C n := by
    by_contra hcon
    push Not at hcon
    have hsub : U ⊆ U.filter (fun u => u ∉ C n) ∪ U.filter (fun u => r - u ∉ C n) := by
      intro u hu
      by_cases h1 : u ∈ C n
      · exact mem_union_right _ (mem_filter.mpr ⟨hu, hcon u hu h1⟩)
      · exact mem_union_left _ (mem_filter.mpr ⟨hu, h1⟩)
    have h2 : (U.filter (fun u => r - u ∉ C n)).card
        ≤ ((Icc 1 Y).filter (fun m => m ∉ C n)).card := by
      have hinj : Set.InjOn (fun u => r - u) (U.filter (fun u => r - u ∉ C n)) := by
        intro a ha b hb hab
        have := hUr a (mem_filter.mp ha).1
        have := hUr b (mem_filter.mp hb).1
        simp only at hab
        omega
      rw [← card_image_of_injOn hinj]
      apply card_le_card
      intro m hm
      obtain ⟨u, hu, rfl⟩ := mem_image.mp hm
      have := mem_filter.mp hu
      exact mem_filter.mpr ⟨mem_Icc.mpr (hUr u this.1), this.2⟩
    have := card_le_card hsub
    have := card_union_le (U.filter (fun u => u ∉ C n)) (U.filter (fun u => r - u ∉ C n))
    omega
  obtain ⟨u, hu, huC, hruC⟩ := hex
  exact closing_step huC hruC hr (by have := (hUr u hu).1; omega)

end Conway
