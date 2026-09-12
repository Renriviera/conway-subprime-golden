/-
Copyright (c) 2026 Romain Popescu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Romain Popescu
-/
import ConwayGolden.NumberTheory.CircleMethod.RestrictedBinary
import ConwayGolden.NumberTheory.CircleMethod.PrimesIccLower
import ConwayGolden.Subprime.Exhaustion
import ConwayGolden.Subprime.Limit

/-!
# The golden-ratio limit from the standard analytic inputs

This file discharges the hypotheses of the conditional reduction from the two standard analytic
inputs `CircleMethod.StandardInputs` (Siegel–Walfisz and Vinogradov's minor-arc bound):

* `exhaustion` is proved outright (`Conway.exhaustion`);
* `primesIcc_lower` follows from Siegel–Walfisz at `q = 1`;
* `restrictedBinary_one` and `restrictedBinary_two` are the output of the discrete circle
  method.

## Main statements

* `Conway.Hypotheses.of_standardInputs`: `StandardInputs → Hypotheses`.
* `Conway.tendsto_card_gen_succ_div_of_standardInputs`: assuming only `StandardInputs`,
  `#(gen (n + 1)) / #(gen n) → φ`.
-/

namespace Conway

open CircleMethod Filter Finset Real Topology
open scoped goldenRatio

/-- The analytic hypotheses of the reduction follow from the standard inputs. -/
theorem Hypotheses.of_standardInputs (h : StandardInputs) : Hypotheses where
  exhaustion := _root_.Conway.exhaustion
  primesIcc_lower := h.siegelWalfisz.primesIccLower
  restrictedBinary_one := h.restrictedBinary (Or.inl rfl)
  restrictedBinary_two := h.restrictedBinary (Or.inr rfl)

/-- **Main theorem, from the standard inputs.** Assuming Siegel–Walfisz and Vinogradov's
minor-arc bound, the ratio of consecutive generation sizes of Conway's closure tends to the
golden ratio. -/
theorem tendsto_card_gen_succ_div_of_standardInputs (h : StandardInputs) :
    Tendsto (fun n : ℕ ↦ (#(gen (n + 1)) : ℝ) / #(gen n)) atTop (𝓝 φ) :=
  tendsto_card_gen_succ_div (Hypotheses.of_standardInputs h)

end Conway
