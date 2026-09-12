import ConwayGolden.Combinatorial
import ConwayGolden.Asymptotic
import ConwayGolden.Analytic

/-!
# Sections 2–4: scale selection, interval coefficients, and constant equality
-/

namespace Conway

open Filter Topology Finset

local notation "φ" => Real.goldenRatio

/-! ### Golden-ratio identities -/

theorem inv_gold_eq : φ⁻¹ = φ - 1 := by
  apply inv_eq_of_mul_eq_one_right
  have := Real.goldenRatio_sq
  linarith

theorem gold_sq_sub : φ ^ 2 - φ = 1 := by
  rw [Real.goldenRatio_sq]
  ring

theorem gold_cube_sub : φ ^ 3 - φ ^ 2 = φ := by
  simpa using Real.goldenRatio_pow_sub_goldenRatio_pow 1

theorem two_phi_sq_sub (d : ℝ) :
    2 * (φ ^ 2 * d) - 2 * (φ * d) = 2 * d := by
  calc
    2 * (φ ^ 2 * d) - 2 * (φ * d) = 2 * d * (φ ^ 2 - φ) := by ring
    _ = 2 * d * 1 := by rw [gold_sq_sub]
    _ = 2 * d := by ring

/-! ### Scale selection when `d < c` -/

theorem exists_scale {c d : ℝ} (hd : 0 < d) (hdc : d < c) :
    ∃ k : ℕ, d < c / φ ^ k ∧ c / φ ^ k ≤ φ * d := by
  have hφ : (1 : ℝ) < φ := Real.one_lt_goldenRatio
  have hφ0 : (0 : ℝ) < φ := Real.goldenRatio_pos
  have hc : 0 < c := lt_trans hd hdc
  have hinv0 : 0 < φ⁻¹ := inv_pos.mpr hφ0
  have hinv1 : φ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hφ
  have htend : Tendsto (fun k : ℕ => c / φ ^ k) atTop (𝓝 0) := by
    have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt hinv0) hinv1
    simpa [div_eq_mul_inv, ← inv_pow] using hpow.const_mul c
  by_cases h0 : c ≤ φ * d
  · refine ⟨0, ?_, ?_⟩
    · simpa using hdc
    · simpa using h0
  · have hex : ∃ k, c / φ ^ k ≤ φ * d := by
      have hφd : 0 < φ * d := mul_pos hφ0 hd
      obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp htend (φ * d) hφd
      refine ⟨K, ?_⟩
      have := hK K le_rfl
      rw [Real.dist_eq, sub_zero] at this
      exact (abs_lt.mp this).2.le
    set k := Nat.find hex
    have hk : c / φ ^ k ≤ φ * d := Nat.find_spec hex
    have hkpos : 0 < k := by
      by_contra hk0
      have hk00 : k = 0 := Nat.eq_zero_of_not_pos hk0
      have : c / φ ^ 0 ≤ φ * d := by simpa [k, hk00] using hk
      simp at this
      exact h0 this
    have hpred : ¬ c / φ ^ (k - 1) ≤ φ * d :=
      Nat.find_min hex (Nat.sub_one_lt (Nat.pos_iff_ne_zero.mp hkpos))
    replace hpred : φ * d < c / φ ^ (k - 1) := lt_of_not_ge hpred
    refine ⟨k, ?_, hk⟩
    have hrec : c / φ ^ k = c / φ ^ (k - 1) / φ := by
      have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel hkpos
      rw [← hk1, pow_succ]
      exact div_mul_eq_div_div _ _ _
    rw [hrec]
    have : φ * d / φ < c / φ ^ (k - 1) / φ :=
      div_lt_div_of_pos_right hpred hφ0
    have hsimp : φ * d / φ = d := by field_simp
    rwa [hsimp] at this

/-! ### Interval coefficients of Section 3 -/

noncomputable def eps (T d : ℝ) : ℝ := (T - d) / 16

theorem J_upper_coeff (T d : ℝ) :
    2 * d - T + 9 * eps T d = d - 7 * eps T d := by
  unfold eps
  ring

theorem J_upper_lt_d {T d : ℝ} (hTd : d < T) :
    2 * d - T + 9 * eps T d < d := by
  rw [J_upper_coeff]
  unfold eps
  linarith

theorem I_lower_pos {T d : ℝ} (hd : 0 < d) (hTφ : T ≤ φ * d) :
    0 < φ * d - 2 * eps T d := by
  unfold eps
  have hφ : (1 : ℝ) < φ := Real.one_lt_goldenRatio
  have : T - d ≤ φ * d - d := sub_le_sub_right hTφ _
  nlinarith

theorem J_lower_pos {T d : ℝ} (hd : 0 < d) (hTφ : T ≤ φ * d) :
    0 < 2 * d - T + 3 * eps T d := by
  have hφ : φ < 2 := Real.goldenRatio_lt_two
  unfold eps
  nlinarith

theorem U_beyond_prefix {T d : ℝ} (hTd : d < T) : 0 < eps T d := by
  unfold eps
  linarith

/-! ### Packaged Fibonacci-scale lower bound -/

/-- Output of the `L k` bootstrap: `Q n ≫ φ^n`. -/
structure RoughScales : Prop where
  Q_ge : ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, 1 ≤ n → δ * φ ^ n ≤ (Q n : ℝ)

theorem exists_pos_M_limit (h : RoughScales) :
    ∃ c : ℝ, 0 < c ∧ Tendsto (fun n => (M n : ℝ) / φ ^ n) atTop (𝓝 c) := by
  obtain ⟨c0, hc0⟩ := exists_tendsto_M_div_gold_pow
  obtain ⟨δ, hδ, hge⟩ := h.Q_ge
  have hφ : (0 : ℝ) < φ := Real.goldenRatio_pos
  have hle : ∀ᶠ n : ℕ in atTop, δ ≤ (M n : ℝ) / φ ^ n :=
    eventually_atTop.mpr ⟨1, fun n hn => by
      have hQ := hge n hn
      have hQM : (Q n : ℝ) ≤ M n := by exact_mod_cast Q_le_M hn
      have hpow : 0 < φ ^ n := pow_pos hφ _
      rw [le_div_iff₀ hpow]
      linarith⟩
  have : δ ≤ c0 := ge_of_tendsto hc0 hle
  exact ⟨c0, lt_of_lt_of_le hδ this, hc0⟩

theorem d_le_c {c d : ℝ} (hc : 0 < c)
    (hM : Tendsto (fun n => (M n : ℝ) / φ ^ n) atTop (𝓝 c))
    (hQ : Tendsto (fun n => (Q n : ℝ) / φ ^ n) atTop (𝓝 d)) :
    d ≤ c := by
  have hφ : (0 : ℝ) < φ := Real.goldenRatio_pos
  have hdiv : Tendsto (fun n => (Q n : ℝ) / M n) atTop (𝓝 (d / c)) := by
    have h := hQ.div hM hc.ne'
    convert h using 1
    ext n
    simp only [Pi.div_apply]
    have hMpos : 0 < (M n : ℝ) := by exact_mod_cast M_pos n
    have hpow : 0 < φ ^ n := pow_pos hφ _
    field_simp
  have hle : ∀ᶠ n : ℕ in atTop, (Q n : ℝ) / M n ≤ 1 :=
    eventually_atTop.mpr ⟨1, fun n hn => by
      have hMpos : 0 < (M n : ℝ) := by exact_mod_cast M_pos n
      exact div_le_one_of_le₀ (by exact_mod_cast Q_le_M hn) (le_of_lt hMpos)⟩
  exact (div_le_one hc).mp (le_of_tendsto hdiv hle)

theorem tendsto_Q_div_M {c d : ℝ} (hc : 0 < c)
    (hM : Tendsto (fun n => (M n : ℝ) / φ ^ n) atTop (𝓝 c))
    (hQ : Tendsto (fun n => (Q n : ℝ) / φ ^ n) atTop (𝓝 d))
    (heq : d = c) :
    Tendsto (fun n => (Q n : ℝ) / M n) atTop (𝓝 1) := by
  have hφ : (0 : ℝ) < φ := Real.goldenRatio_pos
  have h := hQ.div hM hc.ne'
  rw [heq, div_self hc.ne'] at h
  convert h using 1
  ext n
  simp only [Pi.div_apply]
  have hMpos : 0 < (M n : ℝ) := by exact_mod_cast M_pos n
  have hpow : 0 < φ ^ n := pow_pos hφ _
  field_simp

theorem tendsto_P_div_M {c d : ℝ} (hc : 0 < c)
    (hM : Tendsto (fun n => (M n : ℝ) / φ ^ n) atTop (𝓝 c))
    (hP : Tendsto (fun n => (P n : ℝ) / φ ^ n) atTop (𝓝 d))
    (heq : d = c) :
    Tendsto (fun n => (P n : ℝ) / M n) atTop (𝓝 1) := by
  have hφ : (0 : ℝ) < φ := Real.goldenRatio_pos
  have h := hP.div hM hc.ne'
  rw [heq, div_self hc.ne'] at h
  convert h using 1
  ext n
  simp only [Pi.div_apply]
  have hMpos : 0 < (M n : ℝ) := by exact_mod_cast M_pos n
  have hpow : 0 < φ ^ n := pow_pos hφ _
  field_simp

/-- If `d < c` forces the first missing prime of `C (n+2)` to appear, then `d = c`. -/
theorem d_eq_c_of_closing {c d : ℝ} (hdc0 : d ≤ c)
    (hclose : d < c → ∀ᶠ n : ℕ in atTop, P (n + 2) ∈ C (n + 2)) :
    d = c := by
  by_contra hne
  have hdc : d < c := lt_of_le_of_ne hdc0 hne
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hclose hdc)
  exact P_not_mem (N + 2) (hN N le_rfl)

theorem closing_count {n Y : ℕ} {U : Finset ℕ} {r : ℕ}
    (hr : r.Prime)
    (hUr : ∀ u ∈ U, 1 ≤ r - u ∧ r - u ≤ Y)
    (hcard : (U.filter (fun u => u ∉ C n)).card + holes n Y < U.card) :
    r ∈ C (n + 1) :=
  final_step hr hUr hcard

theorem extra_prime_of_binary {n t q p u : ℕ}
    (ht : t ∈ C n) (hq : q ∈ C n) (hp : p ∈ C (n + 1))
    (htodd : Odd t) (hqodd : Odd q) (ht3 : 3 ≤ t)
    (hu : u.Prime) (heq : 2 * u = t + q + 2 * p) :
    u ∈ C (n + 2) :=
  outlier_step ht hq hp htodd hqodd ht3 hu heq

end Conway
