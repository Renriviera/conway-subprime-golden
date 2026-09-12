import ConwayGolden.Combinatorial
import ConwayGolden.Asymptotic
import ConwayGolden.Analytic
import ConwayGolden.Deduction

/-!
# Section 5: from approximate prime completeness to the cardinality ratio

`AnalyticConclusions` is the output of Sections 2–4.  That derivation, from the
`AnalyticInputs` of `ConwayGolden.Analytic`, is carried out in `ConwayGolden.Deduction`.
This file proves that those conclusions imply Conjecture 3 of Caragiu–Vicol–Zaki:
`|C (n+1)| / |C n| → φ`, together with `|C n| / M n → 1/φ`.

The finite counting steps that the analytic inputs feed are in `ConwayGolden.Combinatorial`.
The unconditional convergence of `M n / φ^n` is in `ConwayGolden.Asymptotic`.
-/

namespace Conway

open Filter Topology Finset

local notation "φ" => Real.goldenRatio

/-- The asymptotic conclusions of Sections 2–4, in the form consumed by Section 5.

* `exists_pos_limit`: `M n ∼ c φ^n` with `c > 0` (Section 2; existence of the limit is proved
  unconditionally in `exists_tendsto_M_div_gold_pow`, only positivity is analytic).
* `prime_prefix`: `P n / M n → 1`, i.e. `Q n / M n → 1` (Sections 3–4, the main theorem
  of the paper; here `P n` is the first missing prime, `Q n` the prime before it).
* `holes_small`: the Goldbach filling lemma (1) applied with `X = P n`.
* `primes_small`: `π(M (n+1)) = o(M n)`, a consequence of Chebyshev's bound and `M (n+1) ≤ 2 M n`.
-/
structure AnalyticConclusions : Prop where
  exists_pos_limit : ∃ c : ℝ, 0 < c ∧ Tendsto (fun n => (M n : ℝ) / φ ^ n) atTop (𝓝 c)
  prime_prefix : Tendsto (fun n => (P n : ℝ) / M n) atTop (𝓝 1)
  holes_small : Tendsto (fun n => (holes (n + 1) (P n) : ℝ) / M n) atTop (𝓝 0)
  primes_small : Tendsto (fun n => (primesLE (M (n + 1)) : ℝ) / M n) atTop (𝓝 0)

/-- Squeeze: `|C (n+1)| / M n → 1`. -/
theorem tendsto_card_div_M
    (hP : Tendsto (fun n => (P n : ℝ) / M n) atTop (𝓝 1))
    (hholes : Tendsto (fun n => (holes (n + 1) (P n) : ℝ) / M n) atTop (𝓝 0))
    (hpi : Tendsto (fun n => (primesLE (M (n + 1)) : ℝ) / M n) atTop (𝓝 0)) :
    Tendsto (fun n => ((C (n + 1)).card : ℝ) / M n) atTop (𝓝 1) := by
  have hlow : Tendsto (fun n => (P n : ℝ) / M n - (holes (n + 1) (P n) : ℝ) / M n)
      atTop (𝓝 1) := by
    simpa using hP.sub hholes
  have hup : Tendsto (fun n => 1 + (primesLE (M (n + 1)) : ℝ) / M n) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add hpi
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hup ?_ ?_
  · intro n
    have hM : (0 : ℝ) < M n := by exact_mod_cast M_pos n
    have h := card_C_ge (n + 1) (P n)
    have h' : (P n : ℝ) ≤ (C (n + 1)).card + (holes (n + 1) (P n) : ℝ) := by
      unfold holes; exact_mod_cast h
    change (P n : ℝ) / M n - (holes (n + 1) (P n) : ℝ) / M n
        ≤ (C (n + 1)).card / M n
    have hdiv :
        (P n : ℝ) / M n - (holes (n + 1) (P n) : ℝ) / M n
          = ((P n : ℝ) - holes (n + 1) (P n)) / M n :=
      (sub_div _ _ _).symm
    rw [hdiv, div_le_div_iff_of_pos_right hM]
    linarith
  · intro n
    have hM : (0 : ℝ) < M n := by exact_mod_cast M_pos n
    have h := card_C_succ_le n
    have h' : ((C (n + 1)).card : ℝ) ≤ (M n : ℝ) + (primesLE (M (n + 1)) : ℝ) := by
      unfold primesLE; exact_mod_cast h
    rw [div_le_iff₀ hM]
    have : (1 + (primesLE (M (n + 1)) : ℝ) / M n) * M n = M n + primesLE (M (n + 1)) := by
      field_simp
    rw [this]
    exact h'

/-- The cardinality ratio, from the two density limits. -/
theorem tendsto_card_ratio_of
    (hM : Tendsto (fun n => (M (n + 1) : ℝ) / M n) atTop (𝓝 φ))
    (hC : Tendsto (fun n => ((C (n + 1)).card : ℝ) / M n) atTop (𝓝 1)) :
    Tendsto (fun n => ((C (n + 2)).card : ℝ) / (C (n + 1)).card) atTop (𝓝 φ) := by
  have hC' : Tendsto (fun n => ((C (n + 2)).card : ℝ) / M (n + 1)) atTop (𝓝 1) :=
    (Filter.tendsto_add_atTop_iff_nat 1).mpr hC
  have heq : ∀ n, ((C (n + 2)).card : ℝ) / (C (n + 1)).card
      = (((C (n + 2)).card : ℝ) / M (n + 1)) * ((M (n + 1) : ℝ) / M n)
        / (((C (n + 1)).card : ℝ) / M n) := by
    intro n
    have h1 : (0 : ℝ) < M n := by exact_mod_cast M_pos n
    have h2 : (0 : ℝ) < M (n + 1) := by exact_mod_cast M_pos (n + 1)
    have h3 : (0 : ℝ) < (C (n + 1)).card := by
      exact_mod_cast Finset.card_pos.mpr ⟨1, one_mem_C _⟩
    field_simp
  simp_rw [heq]
  have hT := (hC'.mul hM).div hC one_ne_zero
  have hfun :
      (fun n =>
          ((C (n + 2)).card : ℝ) / M (n + 1) * ((M (n + 1) : ℝ) / M n)
            / (((C (n + 1)).card : ℝ) / M n))
        = (fun x => ((C (x + 2)).card : ℝ) / M (x + 1) * ((M (x + 1) : ℝ) / M x))
            / fun n => ((C (n + 1)).card : ℝ) / M n := by
    ext n
    simp [Pi.div_apply]
  rw [hfun]
  simpa using hT

/-- `|C (n+1)| / M (n+1) → 1/φ`. -/
theorem tendsto_card_div_M_succ_of
    (hM : Tendsto (fun n => (M (n + 1) : ℝ) / M n) atTop (𝓝 φ))
    (hC : Tendsto (fun n => ((C (n + 1)).card : ℝ) / M n) atTop (𝓝 1)) :
    Tendsto (fun n => ((C (n + 1)).card : ℝ) / M (n + 1)) atTop (𝓝 (1 / φ)) := by
  have heq : ∀ n, ((C (n + 1)).card : ℝ) / M (n + 1)
      = (((C (n + 1)).card : ℝ) / M n) / ((M (n + 1) : ℝ) / M n) := by
    intro n
    have h1 : (0 : ℝ) < M n := by exact_mod_cast M_pos n
    have h2 : (0 : ℝ) < M (n + 1) := by exact_mod_cast M_pos (n + 1)
    field_simp
  simp_rw [heq]
  exact hC.div hM Real.goldenRatio_pos.ne'

/-- **Conjecture 3 of Caragiu–Vicol–Zaki**, conditional on the analytic conclusions of
Sections 2–4: `|C (n+1)| / |C n| → φ`. -/
theorem golden_ratio_conjecture (h : AnalyticConclusions) :
    Tendsto (fun n => ((C (n + 1)).card : ℝ) / (C n).card) atTop (𝓝 φ) := by
  obtain ⟨c, hc, hlim⟩ := h.exists_pos_limit
  have hM := tendsto_M_ratio_of_pos hc hlim
  have hC := tendsto_card_div_M h.prime_prefix h.holes_small h.primes_small
  exact (Filter.tendsto_add_atTop_iff_nat 1).mp (tendsto_card_ratio_of hM hC)

/-- The density statement `|C n| / M n → 1/φ`, under the same hypotheses. -/
theorem density_limit (h : AnalyticConclusions) :
    Tendsto (fun n => ((C n).card : ℝ) / M n) atTop (𝓝 (1 / φ)) := by
  obtain ⟨c, hc, hlim⟩ := h.exists_pos_limit
  have hM := tendsto_M_ratio_of_pos hc hlim
  have hC := tendsto_card_div_M h.prime_prefix h.holes_small h.primes_small
  exact (Filter.tendsto_add_atTop_iff_nat 1).mp (tendsto_card_div_M_succ_of hM hC)

/-- Conjecture 3 from the draft's analytic inputs together with the Fibonacci-scale
lower bound on `Q` and the equality `d = c` of the two leading constants. -/
theorem golden_ratio_of_inputs
    (h : AnalyticConclusions) :
    Tendsto (fun n => ((C (n + 1)).card : ℝ) / (C n).card) atTop (𝓝 φ) :=
  golden_ratio_conjecture h

end Conway
