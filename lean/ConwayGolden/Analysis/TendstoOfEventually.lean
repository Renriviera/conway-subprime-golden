/-
Copyright (c) 2026 Romain Popescu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Romain Popescu
-/
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Two elementary convergence criteria for real sequences

* `tendsto_nhds_of_eventually_le_of_eventually_ge`: a real-valued function converges to `c`
  along a filter if, for every `ε > 0`, it is eventually at most `c + ε` and eventually at least
  `c - ε`. This is a convenient repackaging of `tendsto_order`.
* `tendsto_zero_of_le_mul_add`: a nonnegative sequence satisfying the *contractive* recursion
  `d (n + 1) ≤ ρ * d n + e n` with `0 ≤ ρ < 1` and `e n → 0` tends to `0`.
-/

open Filter Topology

variable {α : Type*} {l : Filter α}

/-- A real-valued function converges to `c` if, for each `ε > 0`, it is eventually within `ε`
of `c` from above and from below. -/
theorem tendsto_nhds_of_eventually_le_of_eventually_ge {f : α → ℝ} {c : ℝ}
    (hle : ∀ ε : ℝ, 0 < ε → ∀ᶠ x in l, f x ≤ c + ε)
    (hge : ∀ ε : ℝ, 0 < ε → ∀ᶠ x in l, c - ε ≤ f x) :
    Tendsto f l (𝓝 c) := by
  rw [tendsto_order]
  refine ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩
  · filter_upwards [hge ((c - a) / 2) (by linarith)] with x hx
    linarith
  · filter_upwards [hle ((b - c) / 2) (by linarith)] with x hx
    linarith

/-- **Contractive recursion.** If `0 ≤ d n`, `d (n + 1) ≤ ρ * d n + e n` for all `n`, with
`0 ≤ ρ < 1` and `e n → 0`, then `d n → 0`. -/
theorem tendsto_zero_of_le_mul_add {d e : ℕ → ℝ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hd : ∀ n, 0 ≤ d n) (hrec : ∀ n, d (n + 1) ≤ ρ * d n + e n) (he : Tendsto e atTop (𝓝 0)) :
    Tendsto d atTop (𝓝 0) := by
  refine tendsto_nhds_of_eventually_le_of_eventually_ge (fun ε hε ↦ ?_)
    (fun ε hε ↦ Eventually.of_forall fun n ↦ by linarith [hd n])
  -- Beyond `N`, the error term is at most `ε (1 - ρ) / 2`.
  have hη : 0 < ε * (1 - ρ) / 2 := by
    have := sub_pos.mpr hρ1
    positivity
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.mp he).2 _ hη)
  -- Then `d (N + k) ≤ ρ ^ k * d N + ε / 2` for every `k`.
  have key : ∀ k : ℕ, d (N + k) ≤ ρ ^ k * d N + ε / 2 := by
    intro k
    induction k with
    | zero => simp; positivity
    | succ k ih =>
      have h2 := (hN (N + k) (Nat.le_add_right N k)).le
      calc d (N + (k + 1)) = d (N + k + 1) := by rw [add_assoc]
        _ ≤ ρ * d (N + k) + e (N + k) := hrec _
        _ ≤ ρ * (ρ ^ k * d N + ε / 2) + ε * (1 - ρ) / 2 := by gcongr
        _ = ρ ^ (k + 1) * d N + ε / 2 := by ring
  -- Finally `ρ ^ k * d N → 0`.
  have hpow : Tendsto (fun k : ℕ ↦ ρ ^ k * d N + ε / 2) atTop (𝓝 (0 * d N + ε / 2)) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const _).add_const _
  rw [zero_mul, zero_add] at hpow
  obtain ⟨K, hK⟩ := eventually_atTop.mp ((tendsto_order.mp hpow).2 (ε / 2 + ε / 2) (by linarith))
  filter_upwards [eventually_ge_atTop (N + K)] with n hn
  have h1 := key (n - N)
  rw [Nat.add_sub_cancel' (by omega)] at h1
  have h2 := hK (n - N) (by omega)
  linarith
