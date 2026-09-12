/-
Copyright (c) 2026 Romain Popescu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Romain Popescu
-/
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

/-!
# Asymptotics of `x / log x`

The function `x ↦ x / log x` is the natural scale for counting primes. This file records the two
elementary facts about it that are used repeatedly: it tends to infinity, and it is monotone on
`[e, ∞)`. Both follow from Mathlib's `Real.isLittleO_log_id_atTop` and
`Real.log_div_self_antitoneOn`.

## Main statements

* `Real.tendsto_self_div_log_atTop`: `x / log x → ∞`.
* `Real.monotoneOn_self_div_log`: `x ↦ x / log x` is monotone on `[e, ∞)`.
* `Real.self_div_log_le_self_div_log`: the pointwise form of monotonicity.
-/

namespace Real

open Filter Set Topology

theorem tendsto_self_div_log_atTop : Tendsto (fun x : ℝ ↦ x / log x) atTop atTop := by
  have h0 : Tendsto (fun x : ℝ ↦ log x / x) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨isLittleO_log_id_atTop.tendsto_div_nhds_zero, ?_⟩
    filter_upwards [eventually_gt_atTop 1] with x hx
    exact div_pos (log_pos hx) (by linarith)
  refine (h0.inv_tendsto_nhdsGT_zero).congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  simp [inv_div]

theorem monotoneOn_self_div_log : MonotoneOn (fun x : ℝ ↦ x / log x) (Ici (exp 1)) := by
  intro x hx y hy hxy
  have hx1 : 1 < x := (one_lt_exp_iff.mpr one_pos).trans_le hx
  have hlogx : 0 < log x := log_pos hx1
  have hlogy : 0 < log y := log_pos (hx1.trans_le hxy)
  have h := log_div_self_antitoneOn hx hy hxy
  simp only at h ⊢
  rw [div_le_div_iff₀ hlogx hlogy]
  rw [div_le_div_iff₀ (by linarith) (by linarith)] at h
  linarith

theorem self_div_log_le_self_div_log {x y : ℝ} (hx : exp 1 ≤ x) (hxy : x ≤ y) :
    x / log x ≤ y / log y :=
  monotoneOn_self_div_log hx (hx.trans hxy) hxy

end Real
