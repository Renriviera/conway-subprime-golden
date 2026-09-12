import ConwayGolden.Main

/-!
# Interfaces and elementary checks for the weaker-input research variant

This file does NOT formalize the full revised proof. It states its proposed
analytic interfaces, proves the prime-scale pigeonhole comparison, and checks
the two new interval margins. The restricted binary theorems, their implication
of buffered filling, the profile-increase construction, and the bounded-step
iteration remain to be formalized. There are no `sorry` or new axiom declarations.

Check using the existing (unmodified) Lean project's environment:
  cd lean
  lake env lean ../proof-variants/lean-friendly/WeakInputs.lean
-/

namespace Conway.Weak

open Filter Topology Finset

def PrimePrefix (j : ℕ) (L : ℝ) : Prop :=
  ∀ p : ℕ, p.Prime → (p : ℝ) ≤ L → p ∈ Conway.C j

noncomputable def primeIntervalCount (α β X : ℝ) : ℕ :=
  ((Icc ⌈α * X⌉₊ ⌊β * X⌋₊).filter Nat.Prime).card

/-- Only proportional-interval lower bounds and sublinear prime counting. -/
structure PrimeInputs : Prop where
  proportional_lower :
    ∀ α β : ℝ, 0 < α → α < β →
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop,
        c * (X / Real.log X) ≤ (primeIntervalCount α β X : ℝ)
  primes_sublinear :
    Tendsto (fun X : ℕ => (Conway.primesLE X : ℝ) / (X : ℝ)) atTop (𝓝 0)

/-- A positive fixed buffer; the little-o bound is uniform in the generation. -/
structure BufferedFilling : Prop where
  holes_small :
    ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ ε : ℝ, 0 < ε →
      ∃ X₀ : ℝ, 2 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X → ∀ j : ℕ,
        PrimePrefix j X →
        (Conway.holes (j + 1) ⌊(1 - θ) * X⌋₊ : ℝ) ≤ ε * (X / Real.log X)

/-- Real solution length for `N = ν p + q`; used only for ν = 1 or 2. -/
noncomputable def binaryOverlap (ν : ℕ) (α β γ δ X N : ℝ) : ℝ :=
  max 0 (min (β * X) ((N - γ * X) / ν) -
         max (α * X) ((N - δ * X) / ν))

def HasRestrictedRepresentation (ν : ℕ) (α β γ δ X : ℝ) (N : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧
    α * X ≤ p ∧ (p : ℝ) ≤ β * X ∧
    γ * X ≤ q ∧ (q : ℝ) ≤ δ * X ∧ N = ν * p + q

noncomputable def binaryBadCount (ν : ℕ) (α β γ δ η B X : ℝ) : ℕ := by
  classical
  exact ((Icc 1 ⌊B * X⌋₊).filter (fun N =>
    N % 2 = (ν + 1) % 2 ∧
    η * X ≤ binaryOverlap ν α β γ δ X N ∧
    ¬ HasRestrictedRepresentation ν α β γ δ X N)).card

/-- Prime-scale exceptions; this is stronger than natural density zero. -/
structure RestrictedBinary (ν : ℕ) : Prop where
  almost_all :
    ∀ α β γ δ η B : ℝ,
      0 < α → α < β → 0 < γ → γ < δ → 0 < η → 0 < B →
      Tendsto (fun X : ℝ =>
        (binaryBadCount ν α β γ δ η B X : ℝ) / (X / Real.log X))
        atTop (𝓝 0)

/-- Raw analytic boundary of the manuscript. Buffered filling is to be derived
from `goldbach`, not added as an independent raw assumption. -/
structure RawInputs : Prop where
  exhaustion : Conway.Exhaustion
  primes : PrimeInputs
  goldbach : RestrictedBinary 1
  coefficient_two : RestrictedBinary 2

/-- Two errors that are little-o on the candidate scale cannot remove all candidates. -/
theorem eventually_two_errors_lt_candidates
    {ι : Type*} {l : Filter ι} {scale candidates e₁ e₂ : ι → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hs : ∀ᶠ n in l, 0 < scale n)
    (hcan : ∀ᶠ n in l, c ≤ candidates n / scale n)
    (he₁ : Tendsto (fun n => e₁ n / scale n) l (𝓝 0))
    (he₂ : Tendsto (fun n => e₂ n / scale n) l (𝓝 0)) :
    ∀ᶠ n in l, e₁ n + e₂ n < candidates n := by
  have hsum : Tendsto (fun n => e₁ n / scale n + e₂ n / scale n) l (𝓝 0) := by
    simpa using he₁.add he₂
  have hsmall : ∀ᶠ n in l, e₁ n / scale n + e₂ n / scale n < c :=
    (tendsto_order.mp hsum).2 c hc
  filter_upwards [hs, hcan, hsmall] with n hn hcn hen
  have hdiv : (e₁ n + e₂ n) / scale n < candidates n / scale n := by
    rw [add_div]
    exact lt_of_lt_of_le hen hcn
  exact (div_lt_div_iff_of_pos_right hn).mp hdiv

/-- The upper interval margin in the profile-increase lemma, after dividing by L. -/
theorem boost_difference_upper {lam δ T r u : ℝ}
    (hpoly : lam ^ 3 - 2 * lam - 1 ≤ 0)
    (hT : 1 + δ - δ / 400 ≤ T)
    (hr : r ≤ lam ^ 3 + δ / 8)
    (hu : lam + (T + 1) / 2 - 3 * (δ / 100) ≤ u) :
    r - u ≤ lam - 11 * δ / 32 := by
  linarith

/-- The lower interval margin in the same lemma. -/
theorem boost_difference_lower {lam δ T r u : ℝ}
    (hδ1 : δ ≤ 1 / 10)
    (hpoly : (312 : ℝ) / 125 ≤ lam ^ 3 - lam)
    (hT : T ≤ 2 + 2 * δ + δ / 400)
    (hr : lam ^ 3 ≤ r)
    (hu : u ≤ lam + (T + 1) / 2 - 5 * (δ / 100) / 2) :
    (1 : ℝ) / 2 ≤ r - u := by
  linarith

#print axioms eventually_two_errors_lt_candidates
#print axioms boost_difference_upper
#print axioms boost_difference_lower

end Conway.Weak
