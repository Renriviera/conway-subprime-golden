import ConwayGolden.Basic

/-!
# Analytic inputs used by the Conway cardinality argument

These are the external facts consumed by `prime-completeness.md` / the TeX draft.
None of them is currently in Mathlib, so they are packaged as hypotheses rather than
kernel axioms: every subsequent theorem takes an `AnalyticInputs` bundle.

* `Exhaustion` — Caragiu–Vicol–Zaki, Theorem 1: every finite initial segment of `ℕ`
  appears in some `C N`.
* `GoldbachFilling` — Coppola–Laporta almost-all Goldbach with almost equal summands,
  applied as in the draft's filling lemma.
* `PrimeEstimates` — prime-number theorem with a power-saving error, in the four
  forms used in the draft (short intervals, proportional intervals, previous prime,
  following prime).
* `BinaryLemma` — the appendix's almost-all statement for `N = 2p + q` with `p, q`
  restricted to two fixed positive-length intervals.
-/

namespace Conway

open Filter Topology Finset

/-- Caragiu–Vicol–Zaki, Theorem 1. -/
structure Exhaustion : Prop where
  finite_interval : ∀ M : ℕ, ∃ N : ℕ, Icc 1 M ⊆ C N

/-- Filling lemma: a complete prime prefix up to `X` in `C j` produces
`O_A(X / log^A X)` holes in `C (j+1)` below `X`. -/
structure GoldbachFilling : Prop where
  holes_bound :
    ∀ A : ℝ, 0 < A →
      ∃ C : ℝ, 0 < C ∧
        ∀ (j X : ℕ), 2 ≤ X →
          (∀ p : ℕ, p.Prime → p ≤ X → p ∈ Conway.C j) →
          (holes (j + 1) X : ℝ) ≤ C * X / Real.log X ^ A

/-- Length of `{v ∈ [αX, βX] : N - 2v ∈ [γX, δX]}`. -/
noncomputable def overlap (α β γ δ X N : ℝ) : ℝ :=
  max 0 (min (β * X) ((N - γ * X) / 2) - max (α * X) ((N - δ * X) / 2))

/-- Failure of the restricted representation `N = 2p + q`. -/
def BinaryExceptional (α β γ δ : ℝ) (X N : ℕ) : Prop :=
  ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧
      α * X ≤ p ∧ p ≤ β * X ∧ γ * X ≤ q ∧ q ≤ δ * X ∧ N = 2 * p + q

/-- Odd targets with large overlap that still lack a representation. -/
def BinaryBad (α β γ δ η : ℝ) (X N : ℕ) : Prop :=
  Odd N ∧ η * (X : ℝ) ≤ overlap α β γ δ X N ∧ BinaryExceptional α β γ δ X N

/-- Almost-all binary representations in two fixed intervals. -/
structure BinaryLemma : Prop where
  almost_all :
    ∀ (α β γ δ η B A : ℝ),
      0 < α → α < β → 0 < γ → γ < δ → 0 < η → 0 < B → 0 < A →
      ∃ C : ℝ, 0 < C ∧
        ∀ᶠ X : ℕ in atTop,
          (Nat.card {N : ℕ | N ≤ ⌊B * (X : ℝ)⌋₊ ∧ BinaryBad α β γ δ η X N} : ℝ)
            ≤ C * (X : ℝ) / Real.log X ^ A

/-- Prime-number estimates used in the draft. -/
structure PrimeEstimates : Prop where
  /-- `#(ℙ ∩ [X - X/log²X, X]) ∼ X / log³ X`. -/
  short_interval :
    Tendsto (fun X : ℕ =>
        (((Icc (X - ⌊(X : ℝ) / Real.log X ^ 2⌋₊) X).filter Nat.Prime).card : ℝ)
          / ((X : ℝ) / Real.log X ^ 3))
      atTop (𝓝 1)
  /-- For fixed `0 < α < β`, `#(ℙ ∩ [αX, βX]) ∼ (β-α)X / log X`. -/
  proportional :
    ∀ α β : ℝ, 0 < α → α < β →
      Tendsto (fun X : ℕ =>
          (((Icc ⌈α * X⌉₊ ⌊β * X⌋₊).filter Nat.Prime).card : ℝ)
            / ((β - α) * X / Real.log X))
        atTop (𝓝 1)
  /-- The prime immediately preceding a large `X` is at least `X - X/log² X`. -/
  prev_prime :
    ∀ᶠ X : ℕ in atTop,
      3 ≤ X → ∃ p : ℕ, p.Prime ∧ (X : ℝ) - X / Real.log X ^ 2 ≤ p ∧ p ≤ X
  /-- The prime immediately following a large `X` is `X + o(X)`. -/
  next_prime :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℕ in atTop,
      ∃ p : ℕ, p.Prime ∧ (X : ℝ) < p ∧ p ≤ (1 + ε) * X

/-- The four analytic inputs of the draft. -/
structure AnalyticInputs : Prop where
  exhaustion : Exhaustion
  filling : GoldbachFilling
  primes : PrimeEstimates
  binary : BinaryLemma

/-- Short-interval width `⌊X / log² X⌋`. -/
noncomputable def shortH (X : ℕ) : ℕ := ⌊(X : ℝ) / Real.log X ^ 2⌋₊

end Conway
