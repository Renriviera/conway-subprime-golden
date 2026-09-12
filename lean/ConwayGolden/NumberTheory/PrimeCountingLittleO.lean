/-
Copyright (c) 2026 Romain Popescu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Romain Popescu
-/
import Mathlib.NumberTheory.Chebyshev

/-!
# The primes have density zero

Chebyshev's upper bound `π x ≤ (log 4 + ε) x / log x` (`Chebyshev.eventually_primeCounting_le`)
implies that the prime counting function is `o(x)`. This file records that consequence in the
two forms that are convenient downstream: as a limit `π ⌊x⌋₊ / x → 0` and as an `IsLittleO`
statement.

## Main statements

* `Chebyshev.tendsto_primeCounting_div`: `π ⌊x⌋₊ / x → 0` as `x → ∞`.
* `Chebyshev.primeCounting_isLittleO`: `π ⌊x⌋₊ = o(x)`.
-/

namespace Chebyshev

open Asymptotics Filter Real Topology
open scoped Nat.Prime

/-- The primes have natural density zero: `π ⌊x⌋₊ / x → 0`. -/
theorem tendsto_primeCounting_div :
    Tendsto (fun x : ℝ ↦ (π ⌊x⌋₊ : ℝ) / x) atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℝ ↦ (log 4 + 1) * (log x)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_log_atTop.inv_tendsto_atTop).const_mul (log 4 + 1)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlog ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with x hx
    positivity
  · filter_upwards [eventually_primeCounting_le one_pos, eventually_gt_atTop 1] with x hx hx1
    have hxpos : 0 < x := by linarith
    have hlogpos : 0 < log x := log_pos hx1
    rw [div_le_iff₀ hxpos]
    calc (π ⌊x⌋₊ : ℝ) ≤ (log 4 + 1) * x / log x := hx
      _ = (log 4 + 1) * (log x)⁻¹ * x := by ring

/-- The prime counting function is `o(x)`. -/
theorem primeCounting_isLittleO : (fun x : ℝ ↦ (π ⌊x⌋₊ : ℝ)) =o[atTop] fun x ↦ x := by
  refine (isLittleO_iff_tendsto' ?_).mpr tendsto_primeCounting_div
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx h
  exact absurd h hx.ne'

end Chebyshev
