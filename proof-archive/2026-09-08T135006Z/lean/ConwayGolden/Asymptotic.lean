import ConwayGolden.Basic

/-!
# The maximum has a golden-ratio limit (unconditional part of Section 2)

From the Fibonacci inequality `M (n+2) ≤ M (n+1) + M n` alone we prove that
`M n / φ^n` converges.  Positivity of the limit is *not* proved here: it needs the
analytic bootstrap of Section 2.

The argument is the one in the text: with

  `T n = (M n + M (n-1) / φ) / φ^n`,

the identity `φ - φ⁻¹ = 1` gives `T (n+1) - T n = (M (n+1) - M n - M (n-1)) / φ^(n+1) ≤ 0`,
so `T` is eventually antitone and bounded below, hence convergent; and

  `M (n+1) / φ^(n+1) = T (n+1) - φ⁻² · M n / φ^n`

is a contraction with ratio `φ⁻² < 1`, so `M n / φ^n` converges to `lim T / (1 + φ⁻²)`.
-/

namespace Conway

open Filter Topology Real

local notation "φ" => Real.goldenRatio

/-- A stable first-order linear recurrence `x (n+1) = e (n+1) - k * x n`, `0 ≤ k < 1`, with
convergent forcing `e → t`, has `x → t / (1 + k)`. -/
theorem tendsto_of_contraction {x e : ℕ → ℝ} {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hrec : ∀ n, x (n + 1) = e (n + 1) - k * x n) {t : ℝ}
    (he : Tendsto e atTop (𝓝 t)) :
    Tendsto x atTop (𝓝 (t / (1 + k))) := by
  set L := t / (1 + k) with hLdef
  have hk1' : (0 : ℝ) < 1 + k := by linarith
  have hL : L = t - k * L := by
    rw [hLdef]; field_simp; ring
  have hy : ∀ n, x (n + 1) - L = (e (n + 1) - t) - k * (x n - L) := by
    intro n; rw [hrec]; linarith [hL]
  have hd : Tendsto (fun n => e n - t) atTop (𝓝 0) := by
    simpa using he.sub_const t
  rw [← tendsto_sub_nhds_zero_iff]
  rw [Metric.tendsto_atTop] at hd ⊢
  intro ε hε
  have hε' : 0 < ε * (1 - k) / 2 := by
    have : 0 < 1 - k := by linarith
    positivity
  obtain ⟨N, hN⟩ := hd _ hε'
  have hstep : ∀ n, N ≤ n → |x (n + 1) - L| ≤ ε * (1 - k) / 2 + k * |x n - L| := by
    intro n hn
    have h1 : |e (n + 1) - t| < ε * (1 - k) / 2 := by
      have := hN (n + 1) (by omega)
      simpa [Real.dist_eq] using this
    rw [hy]
    calc |(e (n + 1) - t) - k * (x n - L)|
        ≤ |e (n + 1) - t| + |k * (x n - L)| := abs_sub _ _
      _ = |e (n + 1) - t| + k * |x n - L| := by rw [abs_mul, abs_of_nonneg hk0]
      _ ≤ ε * (1 - k) / 2 + k * |x n - L| := by linarith
  have hiter : ∀ m, |x (N + m) - L| ≤ k ^ m * |x N - L| + ε / 2 := by
    intro m
    induction m with
    | zero => simp; linarith
    | succ m ih =>
      have := hstep (N + m) (by omega)
      rw [show N + (m + 1) = N + m + 1 by ring]
      calc |x (N + m + 1) - L| ≤ ε * (1 - k) / 2 + k * |x (N + m) - L| := this
        _ ≤ ε * (1 - k) / 2 + k * (k ^ m * |x N - L| + ε / 2) := by gcongr
        _ = k ^ (m + 1) * |x N - L| + ε / 2 := by ring
  have hgeom : Tendsto (fun m : ℕ => k ^ m * |x N - L|) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hk0 hk1).mul_const |x N - L|
  obtain ⟨m0, hm0⟩ := (Metric.tendsto_atTop.mp hgeom) (ε / 2) (by positivity)
  refine ⟨N + m0, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = N + m := ⟨n - N, by omega⟩
  have h1 := hiter m
  have h2 : k ^ m * |x N - L| < ε / 2 := by
    have := hm0 m (by omega)
    rw [Real.dist_eq, sub_zero] at this
    exact lt_of_abs_lt this
  rw [Real.dist_eq, sub_zero]
  linarith

/-- The auxiliary sequence `T n = (M n + M (n-1)/φ) / φ^n` (with `M (-1)` read as `0`). -/
noncomputable def T (n : ℕ) : ℝ :=
  match n with
  | 0 => (M 0 : ℝ)
  | n + 1 => ((M (n + 1) : ℝ) + (M n : ℝ) / φ) / φ ^ (n + 1)

theorem gold_sub_inv : φ - φ⁻¹ = 1 := by
  rw [Real.inv_goldenRatio]
  linarith [Real.goldenRatio_add_goldenConj]

/-- The recursion `M (n+1)/φ^(n+1) = T (n+1) - φ⁻² · M n/φ^n`. -/
theorem M_div_gold_pow_succ (n : ℕ) :
    (M (n + 1) : ℝ) / φ ^ (n + 1) = T (n + 1) - (φ ^ 2)⁻¹ * ((M n : ℝ) / φ ^ n) := by
  simp only [T]
  have hφ : (0 : ℝ) < φ := Real.goldenRatio_pos
  field_simp
  ring

/-- `T (n+2) ≤ T (n+1)` for `n ≥ 1`: the Fibonacci inequality in the `T`-coordinate. -/
theorem T_succ_le {n : ℕ} (hn : 1 ≤ n) : T (n + 2) ≤ T (n + 1) := by
  have h5 := M_succ_succ_le hn
  have hφ : (0 : ℝ) < φ := Real.goldenRatio_pos
  have h5' : (M (n + 2) : ℝ) ≤ (M (n + 1) : ℝ) + (M n : ℝ) := by exact_mod_cast h5
  have hginv := gold_sub_inv
  simp only [T]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hpow : φ ^ (n + 2) = φ ^ (n + 1) * φ := by ring
  rw [hpow]
  have key : (M (n + 2) : ℝ) + (M (n + 1) : ℝ) / φ ≤ ((M (n + 1) : ℝ) + (M n : ℝ) / φ) * φ := by
    have hinv : (M (n + 1) : ℝ) / φ = (M (n + 1) : ℝ) * φ⁻¹ := div_eq_mul_inv _ _
    have hmul : ((M n : ℝ) / φ) * φ = (M n : ℝ) := by field_simp
    rw [add_mul, hmul, hinv]
    nlinarith [hginv, (Nat.cast_nonneg (M (n + 1)) : (0 : ℝ) ≤ M (n + 1))]
  calc ((M (n + 2) : ℝ) + (M (n + 1) : ℝ) / φ) * φ ^ (n + 1)
      ≤ (((M (n + 1) : ℝ) + (M n : ℝ) / φ) * φ) * φ ^ (n + 1) := by gcongr
    _ = ((M (n + 1) : ℝ) + (M n : ℝ) / φ) * (φ ^ (n + 1) * φ) := by ring

theorem T_nonneg (n : ℕ) : 0 ≤ T n := by
  cases n with
  | zero => simp [T]
  | succ n =>
    simp only [T]
    have hφ : (0 : ℝ) < φ := Real.goldenRatio_pos
    positivity

/-- `T` converges (it is eventually antitone and bounded below). -/
theorem exists_tendsto_T : ∃ t : ℝ, Tendsto T atTop (𝓝 t) := by
  have hanti : Antitone (fun n => T (n + 2)) := by
    apply antitone_nat_of_succ_le
    intro n
    exact T_succ_le (n := n + 1) (by omega)
  have hbdd : BddBelow (Set.range fun n => T (n + 2)) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact T_nonneg _⟩
  refine ⟨⨅ n, T (n + 2), ?_⟩
  have := tendsto_atTop_ciInf hanti hbdd
  exact (Filter.tendsto_add_atTop_iff_nat 2).mp this

/-- **Unconditional golden-ratio limit for the maximum.**  `M n / φ^n` converges. -/
theorem exists_tendsto_M_div_gold_pow :
    ∃ c : ℝ, Tendsto (fun n => (M n : ℝ) / φ ^ n) atTop (𝓝 c) := by
  obtain ⟨t, ht⟩ := exists_tendsto_T
  have hk0 : (0 : ℝ) ≤ (φ ^ 2)⁻¹ := by positivity
  have hk1 : (φ ^ 2)⁻¹ < 1 := by
    have h1 : (1 : ℝ) < φ := Real.one_lt_goldenRatio
    have : (1 : ℝ) < φ ^ 2 := by nlinarith
    exact inv_lt_one_of_one_lt₀ this
  exact ⟨_, tendsto_of_contraction hk0 hk1 M_div_gold_pow_succ ht⟩

/-- Consequently `M (n+1) / M n → φ`, provided the limit `c` is positive. -/
theorem tendsto_M_ratio_of_pos {c : ℝ} (hc : 0 < c)
    (h : Tendsto (fun n => (M n : ℝ) / φ ^ n) atTop (𝓝 c)) :
    Tendsto (fun n => (M (n + 1) : ℝ) / M n) atTop (𝓝 φ) := by
  have hφ : (0 : ℝ) < φ := Real.goldenRatio_pos
  have h1 : Tendsto (fun n => (M (n + 1) : ℝ) / φ ^ (n + 1)) atTop (𝓝 c) :=
    (Filter.tendsto_add_atTop_iff_nat 1).mpr h
  have h2 := h1.div h hc.ne'
  have heq : ∀ n, (M (n + 1) : ℝ) / M n
      = ((M (n + 1) : ℝ) / φ ^ (n + 1)) / ((M n : ℝ) / φ ^ n) * φ := by
    intro n
    have hM : (0 : ℝ) < M n := by exact_mod_cast M_pos n
    field_simp
    ring
  simp_rw [heq]
  simpa [div_self hc.ne'] using h2.mul_const φ

end Conway
