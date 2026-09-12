import Mathlib

/-!
# Conway's subprime closure: definitions and elementary structure

This file formalizes the objects of `prime-completeness.md`:

* `Conway.s` — Conway's subprime function, `s m = m` for prime `m`, otherwise `m / minFac m`;
* `Conway.C n` — the closure sets, `C 0 = {1}`, `C (n+1) = C n ∪ s (C n + C n)`;
* `Conway.M n` — the maximum of `C n`;
* `Conway.P n` — the first prime absent from `C n` (all primes below `P n` lie in `C n`).

Everything here is proved without any analytic input.  The main structural facts are:

* composite outputs are bounded by the previous maximum (`composite_output_le`);
* a new maximum is a prime equal to a sum of two elements (`new_max`);
* even elements of `C (n+1)` are `2` or at most `M n` (`even_mem_C_succ`);
* the Fibonacci inequality `M (n+2) ≤ M (n+1) + M n` for `n ≥ 1` (`M_succ_succ_le`)
  and `M n ≤ fib (n+2)` (`M_le_fib`);
* the inclusion `C (n+1) ⊆ [1, M n] ∪ {primes ≤ M (n+1)}` (`mem_C_succ_le_or_prime`)
  and the resulting cardinality bound (`card_C_succ_le`).
-/

namespace Conway

open Finset

/-- Conway's subprime function. -/
def s (m : ℕ) : ℕ := if m.Prime then m else m / m.minFac

/-- The closure sets `C n`. Repeated inputs `a = b` are allowed. -/
def C : ℕ → Finset ℕ
  | 0 => {1}
  | n + 1 => C n ∪ ((C n ×ˢ C n).image fun ab : ℕ × ℕ => s (ab.1 + ab.2))

/-- The maximum `M n = max C n`. -/
def M (n : ℕ) : ℕ := (C n).sup id

/-! ### The subprime function -/

theorem s_of_prime {p : ℕ} (hp : p.Prime) : s p = p := by simp [s, hp]

theorem s_of_not_prime {m : ℕ} (hm : ¬ m.Prime) : s m = m / m.minFac := by simp [s, hm]

theorem s_le (m : ℕ) : s m ≤ m := by
  unfold s
  split_ifs
  · exact le_rfl
  · exact Nat.div_le_self _ _

/-- A composite input is at least halved. -/
theorem two_mul_s_le {m : ℕ} (hm : ¬ m.Prime) (h2 : 2 ≤ m) : 2 * s m ≤ m := by
  rw [s_of_not_prime hm]
  have hmin : 2 ≤ m.minFac := (Nat.minFac_prime (by omega)).two_le
  exact (Nat.mul_le_mul_left 2 (Nat.div_le_div_left hmin (by norm_num))).trans
    (Nat.mul_div_le m 2)

theorem s_pos {m : ℕ} (hm : 1 ≤ m) : 1 ≤ s m := by
  unfold s
  split_ifs
  · exact hm
  · exact Nat.div_pos (Nat.minFac_le hm) (Nat.minFac_pos m)

/-- The division-by-two branch: `s (2 m) = m` for `m ≥ 2`. -/
theorem s_two_mul {m : ℕ} (hm : 2 ≤ m) : s (2 * m) = m := by
  have hnp : ¬ (2 * m).Prime := Nat.not_prime_mul (by norm_num) (by omega)
  rw [s_of_not_prime hnp, (Nat.minFac_eq_two_iff _).mpr (dvd_mul_right 2 m)]
  exact Nat.mul_div_cancel_left m (by norm_num)

/-! ### Membership in the closure sets -/

theorem mem_C_succ_iff {n x : ℕ} :
    x ∈ C (n + 1) ↔ x ∈ C n ∨ ∃ a ∈ C n, ∃ b ∈ C n, s (a + b) = x := by
  simp only [C, mem_union, mem_image, mem_product, Prod.exists]
  constructor
  · rintro (h | ⟨a, b, ⟨ha, hb⟩, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨a, ha, b, hb, rfl⟩
  · rintro (h | ⟨a, ha, b, hb, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨a, b, ⟨ha, hb⟩, rfl⟩

theorem C_subset_succ (n : ℕ) : C n ⊆ C (n + 1) := fun _ h => mem_C_succ_iff.mpr (Or.inl h)

theorem C_mono : Monotone C := monotone_nat_of_le_succ C_subset_succ

/-- Generation bookkeeping: inputs at generation `n` give an output at generation `n+1`. -/
theorem s_add_mem {n a b : ℕ} (ha : a ∈ C n) (hb : b ∈ C n) : s (a + b) ∈ C (n + 1) :=
  mem_C_succ_iff.mpr (Or.inr ⟨a, ha, b, hb, rfl⟩)

theorem C_zero : C 0 = {1} := rfl

theorem one_mem_C (n : ℕ) : 1 ∈ C n := C_mono (Nat.zero_le n) (by simp [C])

theorem mem_C_pos {n x : ℕ} (hx : x ∈ C n) : 1 ≤ x := by
  induction n generalizing x with
  | zero => simp [C] at hx; omega
  | succ n ih =>
    rcases mem_C_succ_iff.mp hx with h | ⟨a, ha, b, hb, rfl⟩
    · exact ih h
    · exact s_pos (by have := ih ha; omega)

theorem two_mem_C_one : 2 ∈ C 1 := by
  have := s_add_mem (one_mem_C 0) (one_mem_C 0)
  rwa [show (1 : ℕ) + 1 = 2 from rfl, s_of_prime Nat.prime_two] at this

theorem two_mem_C {n : ℕ} (hn : 1 ≤ n) : 2 ∈ C n := C_mono hn two_mem_C_one

theorem C_one : C 1 = {1, 2} := by
  ext x
  simp only [mem_insert, mem_singleton]
  constructor
  · intro hx
    rcases mem_C_succ_iff.mp hx with h | ⟨a, ha, b, hb, rfl⟩
    · simp [C] at h; exact Or.inl h
    · simp [C] at ha hb
      subst ha; subst hb
      right
      rw [show (1 : ℕ) + 1 = 2 from rfl, s_of_prime Nat.prime_two]
  · rintro (rfl | rfl)
    · exact one_mem_C 1
    · exact two_mem_C_one

/-! ### The maximum -/

theorem le_M {n x : ℕ} (hx : x ∈ C n) : x ≤ M n := Finset.le_sup (f := id) hx

theorem M_le_iff {n k : ℕ} : M n ≤ k ↔ ∀ x ∈ C n, x ≤ k := Finset.sup_le_iff

theorem M_mono : Monotone M := fun _ _ h => Finset.sup_mono (C_mono h)

theorem M_pos (n : ℕ) : 1 ≤ M n := le_M (one_mem_C n)

theorem M_zero : M 0 = 1 := by simp [M, C]

theorem M_one : M 1 = 2 := by
  apply le_antisymm
  · rw [M_le_iff, C_one]; intro x hx; simp at hx; omega
  · exact le_M two_mem_C_one

theorem three_mem_C_two : 3 ∈ C 2 := by
  have h := s_add_mem (one_mem_C 1) two_mem_C_one
  have : (1 : ℕ) + 2 = 3 := rfl
  rwa [this, s_of_prime Nat.prime_three] at h

theorem M_two_le : M 2 ≤ 3 := by
  rw [M_le_iff]
  intro r hr
  rcases mem_C_succ_iff.mp hr with h | ⟨a, ha, b, hb, rfl⟩
  · have := le_M h; rw [M_one] at this; omega
  · rw [C_one] at ha hb
    simp only [mem_insert, mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · have := s_le (1 + 1); omega
    · have := s_le (1 + 2); omega
    · have := s_le (2 + 1); omega
    · have := two_mul_s_le (m := 2 + 2) (by norm_num) (by norm_num); omega

theorem M_two : M 2 = 3 :=
  le_antisymm M_two_le (le_M three_mem_C_two)

theorem C_nonempty (n : ℕ) : (C n).Nonempty := ⟨1, one_mem_C n⟩

/-- A composite output formed from `C n` is at most `M n`. -/
theorem composite_output_le {n a b : ℕ} (ha : a ∈ C n) (hb : b ∈ C n) (h : ¬ (a + b).Prime) :
    s (a + b) ≤ M n := by
  have h1 := le_M ha
  have h2 := le_M hb
  have := two_mul_s_le h (by have := mem_C_pos ha; have := mem_C_pos hb; omega)
  omega

/-- Inclusion (4): `C (n+1) ⊆ [1, M n] ∪ {primes}`. -/
theorem mem_C_succ_le_or_prime {n x : ℕ} (hx : x ∈ C (n + 1)) : x ≤ M n ∨ x.Prime := by
  rcases mem_C_succ_iff.mp hx with h | ⟨a, ha, b, hb, rfl⟩
  · exact Or.inl (le_M h)
  · by_cases hp : (a + b).Prime
    · right; rw [s_of_prime hp]; exact hp
    · left; exact composite_output_le ha hb hp

/-- A new maximum is a prime and is a direct sum of two elements of the previous generation. -/
theorem new_max {n r : ℕ} (hr : r ∈ C (n + 1)) (hM : M n < r) :
    r.Prime ∧ ∃ a ∈ C n, ∃ b ∈ C n, a + b = r := by
  rcases mem_C_succ_iff.mp hr with h | ⟨a, ha, b, hb, rfl⟩
  · exact absurd (le_M h) (not_le.mpr hM)
  · by_cases hp : (a + b).Prime
    · rw [s_of_prime hp]; exact ⟨hp, a, ha, b, hb, rfl⟩
    · exact absurd (composite_output_le ha hb hp) (not_le.mpr hM)

/-- Every even element of `C (n+1)` is `2` or at most `M n`. -/
theorem even_mem_C_succ {n e : ℕ} (he : e ∈ C (n + 1)) (hev : Even e) : e = 2 ∨ e ≤ M n := by
  induction n generalizing e with
  | zero =>
    rcases mem_C_succ_iff.mp he with h | ⟨a, ha, b, hb, rfl⟩
    · simp [C] at h; subst h; exact absurd hev Nat.not_even_one
    · by_cases hp : (a + b).Prime
      · left; rw [s_of_prime hp] at hev ⊢; exact hp.even_iff.mp hev
      · right; exact composite_output_le ha hb hp
  | succ n ih =>
    rcases mem_C_succ_iff.mp he with h | ⟨a, ha, b, hb, rfl⟩
    · rcases ih h hev with h2 | h2
      · exact Or.inl h2
      · exact Or.inr (h2.trans (M_mono (Nat.le_succ n)))
    · by_cases hp : (a + b).Prime
      · left; rw [s_of_prime hp] at hev ⊢; exact hp.even_iff.mp hev
      · right; exact composite_output_le ha hb hp

/-- The Fibonacci inequality (5): `M (n+2) ≤ M (n+1) + M n` for `n ≥ 1`. -/
theorem M_succ_succ_le {n : ℕ} (hn : 1 ≤ n) : M (n + 2) ≤ M (n + 1) + M n := by
  rw [M_le_iff]
  intro r hr
  by_cases hle : r ≤ M (n + 1)
  · omega
  · have hlt : M (n + 1) < r := lt_of_not_ge hle
    obtain ⟨hp, a, ha, b, hb, rfl⟩ := new_max hr hlt
    have h2lt : 2 < a + b := by
      have : 2 ≤ M (n + 1) := M_one ▸ M_mono (le_trans hn (Nat.le_succ n))
      omega
    have hodd : Odd (a + b) := hp.odd_of_ne_two (ne_of_gt h2lt)
    have h2M : 2 ≤ M n := le_M (two_mem_C hn)
    have hA := le_M ha
    have hB := le_M hb
    rcases Nat.even_or_odd a with hae | hao
    · rcases even_mem_C_succ ha hae with h2 | h2 <;> omega
    · have hbe : Even b := by
        rcases Nat.even_or_odd b with h | h
        · exact h
        · exact absurd (hao.add_odd h) (Nat.not_even_iff_odd.mpr hodd)
      rcases even_mem_C_succ hb hbe with h2 | h2 <;> omega

/-- `M (n+2) ≤ M (n+1) + M n` for every `n`, including the directly checked `n = 0`. -/
theorem M_succ_succ_le' (n : ℕ) : M (n + 2) ≤ M (n + 1) + M n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [M_one, M_zero]; exact M_two_le
  · exact M_succ_succ_le hn

theorem M_mem (n : ℕ) : M n ∈ C n := by
  obtain ⟨x, hx, hxeq⟩ := Finset.exists_mem_eq_sup (C n) (C_nonempty n) id
  simpa [M, hxeq] using hx

/-- Every maximum after the initial stage is prime. -/
theorem M_prime {n : ℕ} (hn : 1 ≤ n) : (M n).Prime := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [M_one]
    exact Nat.prime_two
  | succ n hn ih =>
    by_cases h : M (n + 1) ≤ M n
    · have : M (n + 1) = M n := le_antisymm h (M_mono (Nat.le_succ n))
      rwa [this]
    · exact (new_max (M_mem (n + 1)) (lt_of_not_ge h)).1

theorem M_odd {n : ℕ} (hn : 2 ≤ n) : Odd (M n) :=
  (M_prime (by omega)).odd_of_ne_two (by
    have h3 : 3 ≤ M n := by
      rw [← M_two]
      exact M_mono hn
    omega)

/-- Number of integers in `[1, Y]` missing from `C n`. -/
def holes (n Y : ℕ) : ℕ := ((Icc 1 Y).filter (fun m => m ∉ C n)).card

/-- Number of primes in `[1, Y]`. -/
def primesLE (Y : ℕ) : ℕ := ((Icc 1 Y).filter Nat.Prime).card

theorem holes_split {n q y : ℕ} (h : q ≤ y) :
    holes n y ≤ (y - q) + holes n q := by
  have hsub :
      (Icc 1 y).filter (fun m => m ∉ C n) ⊆
        (Icc 1 q).filter (fun m => m ∉ C n) ∪ Icc (q + 1) y := by
    intro m hm
    have hm' := mem_filter.mp hm
    have hmI := mem_Icc.mp hm'.1
    by_cases hq : m ≤ q
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_Icc.mpr ⟨hmI.1, hq⟩, hm'.2⟩)
    · exact mem_union_right _ (mem_Icc.mpr ⟨by omega, hmI.2⟩)
  calc
    holes n y ≤ ((Icc 1 q).filter (fun m => m ∉ C n) ∪ Icc (q + 1) y).card :=
      card_le_card hsub
    _ ≤ holes n q + (Icc (q + 1) y).card := card_union_le _ _
    _ = holes n q + (y + 1 - (q + 1)) := by rw [Nat.card_Icc]
    _ = (y - q) + holes n q := by omega

/-- `M n ≤ F (n+2)`. -/
theorem M_le_fib (n : ℕ) : M n ≤ Nat.fib (n + 2) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rw [M_zero]; decide
    | 1 => rw [M_one]; decide
    | n + 2 =>
      have h1 := ih (n + 1) (by omega)
      have h2 := ih n (by omega)
      have h3 := M_succ_succ_le' n
      calc
        M (n + 2) ≤ M (n + 1) + M n := h3
        _ ≤ Nat.fib (n + 3) + Nat.fib (n + 2) := Nat.add_le_add h1 h2
        _ = Nat.fib (n + 4) := by
          rw [add_comm]
          exact (Nat.fib_add_two (n := n + 2)).symm

/-! ### The first missing prime -/

theorem exists_prime_not_mem (n : ℕ) : ∃ p, p.Prime ∧ p ∉ C n := by
  obtain ⟨p, hle, hp⟩ := Nat.exists_infinite_primes (M n + 1)
  exact ⟨p, hp, fun h => by have := le_M h; omega⟩

/-- The first prime absent from `C n`.  In the text, `Q n` is the prime immediately before
`P n`; every prime `< P n` lies in `C n`. -/
noncomputable def P (n : ℕ) : ℕ := Nat.find (exists_prime_not_mem n)

theorem P_prime (n : ℕ) : (P n).Prime := (Nat.find_spec (exists_prime_not_mem n)).1

theorem P_not_mem (n : ℕ) : P n ∉ C n := (Nat.find_spec (exists_prime_not_mem n)).2

theorem mem_of_prime_lt_P {n p : ℕ} (hp : p.Prime) (h : p < P n) : p ∈ C n := by
  by_contra hc
  exact Nat.find_min (exists_prime_not_mem n) h ⟨hp, hc⟩

theorem P_mono : Monotone P := by
  intro m n hmn
  exact Nat.find_min' (exists_prime_not_mem m) ⟨P_prime n, fun h => P_not_mem n (C_mono hmn h)⟩

theorem two_lt_P {n : ℕ} (hn : 1 ≤ n) : 2 < P n := by
  have h2 : 2 ∈ C n := two_mem_C hn
  have hne : P n ≠ 2 := fun h => P_not_mem n (h ▸ h2)
  have hle : 2 ≤ P n := (P_prime n).two_le
  omega

theorem primes_below_P_nonempty {n : ℕ} (hn : 1 ≤ n) :
    ((Icc 1 (P n - 1)).filter Nat.Prime).Nonempty := by
  refine ⟨2, mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, ?_⟩, Nat.prime_two⟩⟩
  have := two_lt_P hn
  omega

/-- The complete prime prefix: the prime immediately before the first missing prime.
For `n = 0` this is a dummy value `1`, since `C 0 = {1}` contains no prime. -/
noncomputable def Q : ℕ → ℕ
  | 0 => 1
  | n + 1 => ((Icc 1 (P (n + 1) - 1)).filter Nat.Prime).max'
      (primes_below_P_nonempty (Nat.succ_le_succ (Nat.zero_le n)))

theorem Q_eq {n : ℕ} (hn : 1 ≤ n) :
    Q n = ((Icc 1 (P n - 1)).filter Nat.Prime).max' (primes_below_P_nonempty hn) := by
  cases n with
  | zero => exact (Nat.not_succ_le_zero 0 hn).elim
  | succ n => rfl

theorem Q_prime {n : ℕ} (hn : 1 ≤ n) : (Q n).Prime := by
  rw [Q_eq hn]
  exact (mem_filter.mp (max'_mem _ (primes_below_P_nonempty hn))).2

theorem Q_lt_P {n : ℕ} (hn : 1 ≤ n) : Q n < P n := by
  rw [Q_eq hn]
  have hmem := max'_mem _ (primes_below_P_nonempty hn)
  have hle : _ ≤ P n - 1 := (mem_Icc.mp (mem_filter.mp hmem).1).2
  exact Nat.lt_of_le_pred (P_prime n).pos hle

theorem Q_mem {n : ℕ} (hn : 1 ≤ n) : Q n ∈ C n :=
  mem_of_prime_lt_P (Q_prime hn) (Q_lt_P hn)

theorem Q_le_M {n : ℕ} (hn : 1 ≤ n) : Q n ≤ M n := le_M (Q_mem hn)

theorem le_Q_of_prime_lt_P {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime) (h : p < P n) :
    p ≤ Q n := by
  rw [Q_eq hn]
  refine le_max' _ p (mem_filter.mpr ⟨mem_Icc.mpr ⟨hp.pos, ?_⟩, hp⟩)
  omega

theorem mem_of_prime_le_Q {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime) (h : p ≤ Q n) :
    p ∈ C n :=
  mem_of_prime_lt_P hp (h.trans_lt (Q_lt_P hn))

/-! ### Cardinality bounds -/

/-- `|C (n+1)| ≤ M n + #{primes ≤ M (n+1)}`; the second term is the region above the
previous maximum, which contains only primes. -/
theorem card_C_succ_le (n : ℕ) :
    (C (n + 1)).card ≤ M n + ((Icc 1 (M (n + 1))).filter Nat.Prime).card := by
  have hsub : C (n + 1) ⊆ Icc 1 (M n) ∪ (Icc 1 (M (n + 1))).filter Nat.Prime := by
    intro x hx
    have h1 := mem_C_pos hx
    rcases mem_C_succ_le_or_prime hx with h | h
    · exact mem_union_left _ (mem_Icc.mpr ⟨h1, h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_Icc.mpr ⟨h1, le_M hx⟩, h⟩)
  calc (C (n + 1)).card ≤ (Icc 1 (M n) ∪ (Icc 1 (M (n + 1))).filter Nat.Prime).card :=
        card_le_card hsub
    _ ≤ (Icc 1 (M n)).card + ((Icc 1 (M (n + 1))).filter Nat.Prime).card := card_union_le _ _
    _ = M n + ((Icc 1 (M (n + 1))).filter Nat.Prime).card := by simp

/-- `|C n| ≥ Y − #holes`, where the holes are the integers in `[1, Y]` missing from `C n`. -/
theorem card_C_ge (n Y : ℕ) :
    Y ≤ (C n).card + ((Icc 1 Y).filter (fun m => m ∉ C n)).card := by
  have hsub : Icc 1 Y ⊆ C n ∪ (Icc 1 Y).filter (fun m => m ∉ C n) := by
    intro m hm
    by_cases h : m ∈ C n
    · exact mem_union_left _ h
    · exact mem_union_right _ (mem_filter.mpr ⟨hm, h⟩)
  have := (card_le_card hsub).trans (card_union_le _ _)
  simpa using this

end Conway
