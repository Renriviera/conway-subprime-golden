# Blueprint: discharging `Conway.Hypotheses` from Siegel–Walfisz and Vinogradov

Goal: replace the four fields of `Conway.Hypotheses` by the two standard analytic inputs in
`CircleMethod.StandardInputs` (`Inputs.lean`), with every application Lean-checked. End state:

```
Conway.tendsto_card_gen_succ_div_of_standardInputs (h : CircleMethod.StandardInputs) :
    Tendsto (fun n ↦ (#(gen (n + 1)) : ℝ) / #(gen n)) atTop (𝓝 φ)
```

**Status: complete.** Every statement below is proved (`scripts/check.py` reports `0` sorries in
all thirteen files) and `Conway.tendsto_card_gen_succ_div_of_standardInputs` depends only on
`propext`, `Classical.choice`, `Quot.sound`. The rest of this document is the plan the proofs were
built from; it is kept as a guide to the structure of the files. Two statements were revised during
execution (both in `SingularIntegral.lean`): `norm_singularIntegral_sub_count_le` needs the
hypothesis `8 P³ ≤ X` (with only `1 ≤ X` the bound fails when `Q` is even and `X ≈ 4P`), and the
far-set sum is organised through `farSet`, `sum_farSet_outer_le`, `sum_farSet_middle_le`. In
`MajorArcs.lean` the Siegel–Walfisz approximations carry the constants `9 + 8δ`, `17 + 16β`
(from `2π ≤ 8`) rather than the sketched `8 + 7δ`.

Statements were frozen during execution: executors filled bodies only, and a statement judged
wrong or too tight was revised by the planner.

Status legend: `E` = executor task (standard Lean/Mathlib work, self-contained),
`E*` = executor task with a tricky step (attempt, escalate after two failures),
`F` = planner (Fable) only. Difficulty 1–5.

Module dependency order (build in this order):

```
ExpSum → RamanujanSum → Inputs → Setup → Arcs → SingularIntegral
                                        ↘ SingularSeries ↗
                            → MajorArcs → MinorArcs → RestrictedBinary
Inputs → PrimesIccLower;   Pigeonhole → Exhaustion;   everything → StandardMain
```

---

## Global conventions

* Lean 4 v4.33.1, Mathlib v4.33.1. Build a single file with
  `lake env lean ConwayGolden/NumberTheory/CircleMethod/<File>.lean`
  (needs `export PATH="$HOME/.elan/bin:$PATH"`).
* `e x = Complex.exp (2 * π * I * x)`; `distInt θ = |θ - round θ|`.
* `Λ` is `ArithmeticFunction.vonMangoldt` (`open scoped ArithmeticFunction.vonMangoldt`).
  Key facts: `vonMangoldt_nonneg`, `vonMangoldt_le_log`, `vonMangoldt_apply_prime`,
  `vonMangoldt_eq_zero_iff : Λ n = 0 ↔ ¬IsPrimePow n`, `vonMangoldt_apply_pow`.
* `μ` is `ArithmeticFunction.moebius` (`open scoped ArithmeticFunction.Moebius`);
  `σ k` is `ArithmeticFunction.sigma k` (`open scoped ArithmeticFunction.sigma`).
* `Nat.totient` is written `q.totient` (avoid the `φ` notation, which clashes with `goldenRatio`).
* `primorial P = ∏ p ∈ range (P+1) with p.Prime, p` (Mathlib, root namespace);
  `squarefree_primorial`, `primeFactors_primorial : (primorial n).primeFactors = primesLE n`.
* Style: Mathlib conventions, lines ≤ 100 chars, no `sorry`, no new axioms, docstrings kept.
  Check axioms with `#print axioms <name>` at the end of a session (expected:
  `propext, Classical.choice, Quot.sound`).

---

## 1. `ExpSum.lean` — additive characters (E, difficulty 1–3)

| Lemma | Owner | Sketch |
|---|---|---|
| `e_zero`, `e_add`, `e_neg`, `e_intCast`, `e_add_intCast`, `e_add_one`, `norm_e`, `e_ne_zero`, `e_nat_mul` | E 1 | Unfold `e`; `Complex.exp_add`, `Complex.exp_int_mul_two_pi_mul_I` (or `Complex.exp_eq_one_iff`), `Complex.norm_exp_ofReal_mul_I` after rewriting `2πI x = (2πx) I`, `Complex.exp_conj`, `Complex.exp_nat_mul`. |
| `e_eq_one_iff` | E 2 | `Complex.exp_eq_one_iff : exp x = 1 ↔ ∃ n : ℤ, x = n * (2 * π * I)`; cancel `2 π I ≠ 0` with `mul_left_cancel₀`; `Complex.ofReal_injective`. |
| `norm_e_sub_one_le` | E 2 | `Complex.norm_exp_sub_one_le`? Simplest: `‖exp(iθ) - 1‖ = 2|sin(θ/2)| ≤ |θ|` via `Complex.exp_mul_I`, `Real.abs_sin_le_abs`. Alternative: `Complex.norm_exp_sub_one_le_norm_mul_exp_norm`-free route: `norm_sub_le` on the integral form is overkill; use `abs_sin_le_abs` and `Real.cos_sq_half`/`Complex.norm_exp_I_mul_ofReal_sub_one`. Search Mathlib: `Complex.norm_exp_I_mul_ofReal_sub_one_le`. |
| `sum_e_mul_div` | E 3 | Set `ζ = e (h / Q)`; `e (k h / Q) = ζ ^ k` by `e_nat_mul`. If `Q ∣ h` then `ζ = 1` (`e_intCast`) and `Finset.sum_const`, `card_range`. Else `ζ ≠ 1` (`e_eq_one_iff`), `geom_sum_eq`, and `ζ ^ Q = e h = 1`. |
| `sum_mul_e_neg_eq` | E 3 | Swap sums (`Finset.sum_comm`), collect `e (g x k / Q) * e (-(N k / Q)) = e ((g x - N) k / Q)` (`e_add`, `e_neg`... easier: `← e_add`, `ring_nf`), apply `sum_e_mul_div` with `h = g x - N`; the `if` is `g x = N` because `|g x - N| < Q` (`Int.eq_zero_of_abs_lt_dvd` or `Int.eq_zero_of_dvd_of_natAbs_lt_natAbs`). Finish with `Finset.sum_filter`, `mul_ite`. |
| `sum_norm_sq_sum_mul_e` | E* 3 | `‖z‖² = z * conj z` (`Complex.mul_conj`, `Complex.normSq_eq_norm_sq`); expand the double sum, swap, use `sum_e_mul_div` with `h = g x - g y`; `hg` kills off-diagonal terms. Cast bookkeeping between `ℝ` and `ℂ`: state an intermediate `ℂ`-valued identity and take `Complex.ofReal_injective`. |
| `sum_norm_sq_sum_mul_e_neg` | E* 3 | Same method with the roles of `k` and `N` exchanged; `∑_{N<Q} e ((k - k') N / Q) = Q [k = k']` for `k, k' < Q` (`Int.eq_zero_of_abs_lt_dvd`). |
| `distInt_*` | E 1–2 | `abs_sub_round θ : |θ - round θ| ≤ 1/2`; `round_eq`, `round_add_int`, `round_neg`; `distInt_eq_zero_iff` via `sub_eq_zero`, `round_intCast`. `distInt_le_abs`: `round` minimises `|θ - n|` over integers: `abs_sub_round_le_abs_self`? If absent, compare with `n = 0` via `round_le`/`Int.abs_sub_round_eq_min`. |
| `four_mul_distInt_le_norm_e_sub_one` | E* 3 | `e θ - 1 = e(θ/2) (e(θ/2) - e(-θ/2)) = e(θ/2) · 2i sin(πθ)`; so `‖e θ - 1‖ = 2|sin(πθ)|`. Periodicity reduces to `|θ| ≤ 1/2` (`distInt_add_intCast`, `e_add_intCast` with `n = -round θ`); then `|sin(πθ)| = sin(π|θ|) ≥ 2|θ|` by `Real.mul_le_sin : 0 ≤ x → x ≤ π/2 → 2/π * x ≤ sin x`. |
| `norm_sum_e_Icc_le_card` | E 1 | `norm_sum_le`, `norm_e`, `sum_const`. |
| `norm_sum_e_Icc_le` | E* 3 | `e (n θ) = e θ ^ n`; `Finset.sum_Icc_eq_sum_range`-type reindexing (`Finset.range_eq_Ico`, `Finset.sum_Ico_eq_sum_range`) then `geom_sum_eq (hθ : e θ ≠ 1)`; numerator `‖e θ ^ m - 1‖ ≤ 2`, denominator via `four_mul_distInt_le_norm_e_sub_one`; `div_le_div_iff₀`. |
| `norm_sum_Ioc_sub_mul_le` | E* 3 | Let `d n = f n - g n`, `D n = ∑_{m ∈ Ioc L n} d m`. Prove by induction on `R` the Abel identity `∑_{n ∈ Ioc L R} d n * v n = D R * v R - ∑_{n ∈ Ioc L (R-1)} D n * (v (n+1) - v n)` (or use `Finset.sum_range_by_parts` after reindexing). `‖D n‖ ≤ 2 D` because `D n = (F n - G n) - (F L - G L)` with `F n = ∑_{Icc 1 n} f`. Finish with `norm_sub_le`, `norm_sum_le`, `Finset.sum_le_sum`. |

## 2. `RamanujanSum.lean` — Ramanujan sums (E/E*, difficulty 2–4)

| Lemma | Owner | Sketch |
|---|---|---|
| `card_coprimeRange` | E 1 | `Nat.totient` is `#{a ∈ range n | n.Coprime a}`; `Nat.totient_eq_card_coprime`, `Nat.coprime_comm`, `Finset.filter_congr`. |
| `sum_coprimeRange_mul_mod` | E* 3 | `r ↦ r * a % q` is a bijection of `coprimeRange q` (inverse: multiply by the inverse of `a` mod `q`, `Nat.exists_mul_emod_eq_one_of_coprime`); use `Finset.sum_nbij'` or `Finset.sum_bij`. Alternative: transfer to `ZMod q` units via `ZMod.unitsEquivCoprime`. |
| `ramanujanSum_one_left`, `ramanujanSum_one_right`, `ramanujanSum_zero_right` | E 2 | `Nat.divisors_one`; for `m = 1` only `d = 1` divides (`Nat.dvd_one`), `Finset.sum_ite_eq`; for `m = 0` all `d ∣ 0`, then `∑_{d ∣ q} d μ(q/d) = φ(q)` is `ArithmeticFunction.totient_eq_moebius_mul_id`-type: `Nat.totient` as `μ * id` (`ArithmeticFunction.coe_moebius_mul_coe_zeta`, `Nat.sum_totient`, or `ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq` applied to `Nat.sum_totient`). |
| `ramanujanSum_eq_of_gcd_eq` | E 2 | For `d ∣ q`: `d ∣ m ↔ d ∣ gcd q m` (`Nat.dvd_gcd_iff`); rewrite both `if`s. |
| `ramanujanSum_mul_of_coprime_right` | E 2 | `Nat.Coprime.gcd_mul_right_cancel`: `gcd q (ν a) = gcd q ν` when `Coprime a q`; then `ramanujanSum_eq_of_gcd_eq`. |
| `sum_e_coprimeRange` | E* 4 | Möbius inversion of the coprimality indicator: `[gcd a q = 1] = ∑_{d ∣ gcd a q} μ d` (`ArithmeticFunction.sum_moebius_eq_ite`? if absent, derive from `ArithmeticFunction.coe_moebius_mul_coe_zeta` evaluated at `gcd a q`). Then `∑_{a<q} [d ∣ a] e(a m/q) = ∑_{a'<q/d} e(a' m/(q/d)) = (q/d) [ (q/d) ∣ m ]` by `sum_e_mul_div`. Reindex `d ↦ q/d` with `Nat.divisors` (`Nat.sum_div_divisors`). |
| `sum_e_neg_coprimeRange` | E 2 | `e_neg`, `map_sum` for `starRingEnd`, `sum_e_coprimeRange`, `Complex.conj_intCast`. |
| `ramanujanSum_prime_left` | E 2 | `Nat.Prime.divisors : p.divisors = {1, p}`; `Finset.sum_pair`; `moebius_apply_prime`, `moebius_apply_one`. |
| `abs_ramanujanSum_le` | E 2 | Triangle inequality (`Finset.abs_sum_le_sum_abs`), `|μ| ≤ 1` (`ArithmeticFunction.abs_moebius_le_one`), then the sum of `d` over `d ∣ gcd q m` is `σ 1 (gcd q m)` (`sigma_one_apply`); restrict the divisor sum with `Finset.sum_le_sum_of_subset_of_nonneg` (`Nat.divisors_subset_of_dvd`, `Nat.gcd_dvd_left`). |
| `isMultiplicative_ramanujanSumFun` | E* 4 | Show `ramanujanSumFun m = μ * g` where `g = ⟨fun d ↦ if d ∣ m then (d : ℤ) else 0, _⟩` (Dirichlet convolution `ArithmeticFunction.mul_apply`, `Nat.sum_divisorsAntidiagonal`), prove `g.IsMultiplicative` (`Nat.Coprime.mul_dvd_of_dvd_of_dvd`, `Nat.dvd_mul_right`), then `isMultiplicative_moebius.mul hg`. |
| `ramanujanSum_eq_prod_primeFactors` | E 2 | `IsMultiplicative.multiplicative_factorization` or `Nat.prod_primeFactors_of_squarefree` + `IsMultiplicative.map_prod_of_subset_primeFactors`. |
| `abs_ramanujanSum_le_one_of_squarefree` | E 2 | Product formula + `ramanujanSum_prime_left`: each factor is `±1` or, for `p = 2 ∣ ν = 2`, `1`. |

## 3. `Inputs.lean` — interfaces and `Λ` facts (E, difficulty 1–3)

| Lemma | Owner | Sketch |
|---|---|---|
| `psiMod_one_zero` | E 1 | `Nat.modEq_one`, `Finset.filter_true_of_mem`. |
| `vonMangoldt_le_log_of_le` | E 1 | `vonMangoldt_le_log`, `Real.log_le_log`. |
| `sum_vonMangoldt_le`, `sum_vonMangoldt_sq_le` | E 2 | Termwise `Λ n ≤ log x`, `Finset.sum_le_card_nsmul`, `Nat.card_Icc`, `Nat.floor_le`. |
| `sum_vonMangoldt_not_prime_le` | E* 3 | Nonzero terms are `p^k`, `k ≥ 2` (`IsPrimePow`, `Nat.Prime.eq_pow_iff`); map `n ↦ n.minFac` into primes `≤ √x`; fibre over `p` has sum `≤ log x` (the exponents `k = 2..K` satisfy `K log p ≤ log x`). Use `Finset.sum_fiberwise_le`-style: `Finset.sum_image'`/`Finset.card_le_card` and `Nat.primeCounting`-free counting `#{p ≤ √x} ≤ √x`. |
| `sum_vonMangoldt_not_coprime_le` | E* 3 | Same fibre argument with `p ∣ q`; at most `q` primes divide `q`. |
| `SiegelWalfisz.abs_psi_sub_le` | E 1 | Apply `h A hA`, take `q = 1`, `a = 0` (`Nat.coprime_zero_left`... note `Nat.Coprime 0 1`), `Nat.totient_one`, `psiMod_one_zero`; `(1:ℝ) ≤ log x ^ A` holds for `x ≥ e`; for `2 ≤ x < e` enlarge `C` using the trivial bound `|ψ x - x| ≤ x log x + x`. Simplest: choose `C' = max C (log 3 + 1) * ...` and split on `x ≥ 3`. |

## 4. `Setup.lean` — counting functions and inversion (E/E*, difficulty 1–3)

| Lemma | Owner | Sketch |
|---|---|---|
| `mem_I`, `mem_J`, `card_I_le`, `card_J_le` | E 1 | `Finset.mem_Icc`, `Nat.ceil_le`, `Nat.le_floor_iff`; `Nat.card_Icc`, `Nat.floor_le`, `Nat.le_ceil`. |
| `SI_add_one`, `SJ_add_one` | E 1 | `e_add_intCast` with `n = ν m` resp. `n`; `mul_add`, `mul_one`. |
| `norm_SI_le`, `norm_SJ_le`, `norm_TI_le`, `norm_TJ_le` | E 2 | `norm_sum_le`, `norm_e`, `vonMangoldt_le_log_of_le`, `card_I_le`. |
| `norm_TJ_le_inv`, `norm_TI_le_inv` | E 1 | `norm_sum_e_Icc_le` (for `TI` rewrite `e (ν m θ) = e (m (ν θ))`). |
| `span_pos`, `Q_pos`, `span_lt_Q`, `dvd_Q`, `le_Q_of_le`, `add_lt_Q` | E 2 | `Nat.factorial_pos`, `Nat.dvd_factorial`, `Nat.lt_floor_add_one`, `Nat.self_le_factorial`; `add_lt_Q`: `ν m + n ≤ ν β X + δ X ≤ span < Q`. |
| `rep_eq_sum`, `count_eq_sum` | E* 3 | `sum_mul_e_neg_eq` with `ι = ℕ × ℕ`, `s = I ×ˢ J`, `g p = ν p.1 + p.2`, weights `Λ p.1 * Λ p.2` resp. `1`; `SI * SJ = ∑_{p} Λ Λ e(ν p.1 θ) e(p.2 θ)` by `Finset.sum_mul_sum`, `e_add`. Window hypothesis from `add_lt_Q` and `le_Q_of_le`. Casts: `Nat.cast_sum`, `Finset.sum_boole`. |
| `le_count_of_isAdmissible` | E* 3 | From `⟨s, hs⟩`: the integers `m ∈ [s, s + ηX]` number `≥ ηX - 1` (`Nat.card_Icc`, `Nat.ceil_le`, `Nat.floor` bounds); each gives `n = N - ν m ∈ J` (cast `N - ν m` to `ℕ` via `Nat.sub`, positivity from `c ≤ N - ν v`); injectivity of `m ↦ (m, N - ν m)` and `Finset.card_le_card_of_injOn`. |
| `hasPrimeRepr_of_lt_rep` | E* 3 | Split the sum defining `rep` into pairs with both coordinates prime and the rest; the rest is `≤ log span · (∑_{m ≤ span, ¬prime} Λ m + ∑_{n ≤ span, ¬prime} Λ n) ≤ 2 √span (log span)²` (`sum_vonMangoldt_not_prime_le`, each `Λ ≤ log span`). If no prime pair existed the whole sum would be the rest, contradiction. Extract witnesses with `Finset.exists_ne_zero_of_sum_ne_zero`-style (`Finset.sum_eq_zero` contrapositive); `Nat.mem_primesIcc`. |

## 5. `Arcs.lean` — arcs (E/F, difficulty 2–5)

| Lemma | Owner | Sketch |
|---|---|---|
| `mem_arcIndex`, `card_arcIndex_le` | E 1 | `Finset.mem_filter`, `Finset.mem_product`; `card_filter_le`, `card_product`, `Nat.card_Icc`, `card_range`. |
| `le_distInt_sub_of_ne` | E* 3 | `a/q - a'/q' = (a q' - a' q)/(q q')`, a nonzero rational with denominator `≤ P²` and absolute value `< 1`; both `|d|` and `1 - |d|` are `≥ 1/(q q')` (`Int` cast of a nonzero integer has `|·| ≥ 1`: `Int.one_le_abs`). `distInt_eq_abs_of_abs_le_half` or the general `distInt θ = min |θ - n|`. |
| `halfWidth_div_Q_le`, `le_halfWidth_div_Q`, `two_mul_halfWidth_add_one_le` | E 2 | `Nat.floor_le`, `Nat.lt_floor_add_one`; `2PQ/X - 1 ≥ PQ/X` iff `PQ ≥ X`. |
| `sum_range_Q_eq` | F 5 | Bijection between `{k < Q : IsMajor k}` and `arcIndex P × Icc (-J₀) J₀` given by `k ≡ a Q / q + j (mod Q)`; injectivity from `le_distInt_sub_of_ne` + `4P/X < 1/P²`; periodicity of `F` absorbs the wrap-around for `q = 1`. Planner-owned. |
| `exists_approx_of_mem_minorSet` | E* 4 | `Real.exists_rat_abs_sub_le_and_den_le (k/Q) (n := ⌊X/P⌋₊)`; if `den ≤ P` the point is major (contradiction, using `le_halfWidth_div_Q` and `distInt_le_abs`, reduce numerator mod `den`); numerator is a natural in `[0, den]` since `k/Q ∈ [0,1)`; `Rat.reduced` gives coprimality. |

## 6. `SingularSeries.lean` (E/E*/F, difficulty 2–5)

| Lemma | Owner | Sketch |
|---|---|---|
| `log_add_one_le_rpow` | E 2 | `Real.log_le_sub_one_of_pos` at `x^{1/12}`: `log x = 12 log (x^{1/12}) ≤ 12 (x^{1/12} - 1)`; `Real.log_rpow`. |
| `card_divisors_le_two_mul_sqrt` | E* 3 | Divisors pair up `d ↔ q/d`; those `≤ √q` are at most `√q` many (`Nat.card_le_card` into `Icc 1 ⌊√q⌋₊`), same for `≥ √q` via `d ↦ q/d`. |
| `sigma_one_le` | E 2 | `σ 1 d = ∑_{e ∣ d} e = d ∑_{e ∣ d} 1/e ≤ d ∑_{e ≤ d} 1/e = d · harmonic d`, `harmonic_le_one_add_log`. |
| `le_totient_mul` | E* 4 | `Nat.totient_eq_prod_factorization` / `Nat.totient_mul_prod_primeFactors`: `q/φ(q) = ∏_{p ∣ q} p/(p-1)`. Bound `∏_{i<ω} (p_i)/(p_i - 1) ≤ ∏_{i<ω} (i+2)/(i+1) = ω + 1` using that the `i`-th prime factor is `≥ i + 2` (sorted list `q.primeFactorsList`, `List.Sorted`, `Nat.Prime.two_le`). Then `ω ≤ Nat.log 2 q ≤ log q / log 2` and `1/log 2 < 2`. Alternative cheaper route: `∏_{p∣q} p/(p-1) ≤ ∏_{p ∣ q} 2 = 2^ω` — too weak here (need polynomial in `log q`), so the sorted-factor argument is required. |
| `sum_Ioc_rpow_neg_le` | E* 3 | Telescoping: `r^{-(1+s)} ≤ ((r-1)^{-s} - r^{-s}) / s` for `r ≥ 2` by the mean value theorem (`exists_deriv_eq_slope` on `x ↦ x^{-s}`, or convexity `Real.rpow_le_rpow_left_iff`); `Finset.sum_Ioc_consecutive`/`Finset.sum_range_sub`. |
| `sum_Ioc_inv_totient_sq_le` | E 2 | `1/φ(r)² ≤ 4 (log r + 1)²/r² ≤ 4·144 r^{1/6}/r² ≤ 576 r^{-7/4}` (`le_totient_mul`, `log_add_one_le_rpow`), then `sum_Ioc_rpow_neg_le` with `s = 3/4`: `576 · (4/3) = 768`. |
| `prod_Icc_one_sub_inv_sq` | E 2 | Induction on `M` (`Finset.prod_Icc_succ_top`), `field_simp`, `ring`. |
| `arcCoeff_one_right`, `arcCoeff_of_not_squarefree` | E 1 | `moebius_apply_one`, `ramanujanSum_one_left`, `Nat.totient_one`; `moebius_eq_zero_of_not_squarefree`. |
| `arcCoeff_mul_of_coprime`, `isMultiplicative_arcCoeffFun` | E 2 | `isMultiplicative_moebius`, `isMultiplicative_ramanujanSumFun`, `Nat.totient_mul`; `IsMultiplicative.pmul`, `IsMultiplicative.pdiv`? Simplest: prove `map_mul_of_coprime` by hand with `Nat.totient_mul` and `ramanujanSum_mul_of_coprime_left`, then package (`IsMultiplicative` is `map_one ∧ ∀ coprime, map_mul`). |
| `arcCoeff_prime` | E 2 | `moebius_apply_prime`, `ramanujanSum_prime_left` (twice), `Nat.totient_prime`; case split `p = 2`, `p ∣ N`; parity: for `ν = 1` and `N + 1` odd, `2 ∣ N`; for `ν = 2`, `2 ∤ N` and `2 ∣ 2`. `field_simp` for the final identities. |
| `abs_arcCoeff_le` | E 2 | Squarefree case: `abs_ramanujanSum_le_one_of_squarefree`, `abs_moebius_le_one`, `abs_ramanujanSum_le`; else both sides handled by `arcCoeff_of_not_squarefree` and nonnegativity. |
| `one_le_prod_one_add_arcCoeff` | E* 4 | Split off `p = 2` (`Finset.prod_erase_mul`); for odd `p`, `1 + arcCoeff ≥ 1 - 1/(p-1)²` (`arcCoeff_prime`); `∏_{odd p ≤ P} (1 - 1/(p-1)²) ≥ ∏_{n ∈ Icc 2 P} (1 - 1/n²)` by `Finset.prod_le_prod_of_subset_of_le_one'`-type monotonicity (map `p ↦ p - 1` into `Icc 2 P`, all factors in `[0,1]`; if the ordered-monoid lemma does not apply to `ℝ`, prove via `Finset.prod_sdiff` and `Finset.prod_le_one`); `prod_Icc_one_sub_inv_sq` gives `≥ 1/2`; total `≥ 2 · 1/2`. |
| `sum_divisors_primorial_arcCoeff` | E 2 | `(isMultiplicative_arcCoeffFun ν N).prodPrimeFactors_one_add_of_squarefree (squarefree_primorial P)`, `primeFactors_primorial`, `Nat.mem_primesLE`. |
| `singularSeries_eq_sub` | E* 3 | `Finset.sum_filter_add_sum_filter_not` on `q ≤ P`; the divisors of `P#` that are `≤ P` versus `Icc 1 P`: extra `q ≤ P` not dividing `P#` are non-squarefree (a squarefree `q ≤ P` has all prime factors `≤ P`, `Nat.prod_primeFactors_of_squarefree`, `Finset.prod_dvd_prod_of_subset`), so contribute `0` (`Finset.sum_subset`). |
| `sum_abs_sum_arcCoeff_Ioc_le` | F 4 | Triangle inequality, `abs_arcCoeff_le`, swap sums; `∑_{N ≤ Y} σ((q,N)) ≤ ∑_{d ∣ q} σ(d) · ⌊Y/d⌋ ≤ Y ∑_{d ∣ q} (log d + 1) ≤ Y τ(q) (log q + 1)` (`Nat.card_multiples`, `sigma_one_le`). |
| `sum_Ioc_divisor_bound` | E 2 | Termwise: `τ(q) (log q+1)/φ(q)² ≤ 2√q (log q+1) · 4(log q+1)²/q² ≤ 8·1728 q^{1/4} q^{-3/2}`; `sum_Ioc_rpow_neg_le` with `s = 1/4`: `13824 · 4 = 55296 ≤ 10⁵`. |
| `sum_abs_arcCoeff_gt_le` | F 5 | Group `q` by `d = gcd q N ∣ N`, write `q = d r` with `gcd d r = 1` (squarefree), `r > Y/d`, `φ(q) = φ(d) φ(r)`; inner sum by `sum_Ioc_inv_totient_sq_le` with `R = ⌊Y/d⌋₊ ≥ Y/(2d)`; outer sum `≤ τ(N) · 4 (log N + 1)³ ≤ 8 √N (log N+1)³`; constant `768 · 2^{3/4} · 8 < 2·10⁴`. |
| `card_singularSeries_lt_le` | F 3 | For `N` in the set: `singularSeries_eq_sub`, `sum_divisors_primorial_arcCoeff`, `one_le_prod_one_add_arcCoeff`, far tail `≤ 1/4` (`sum_abs_arcCoeff_gt_le`), so the middle sum is `≥ 1/4` in absolute value; Markov via `sum_abs_sum_arcCoeff_Ioc_le` and `sum_Ioc_divisor_bound`. |
| `abs_singularSeries_le` | E 2 | `abs_arcCoeff_le`, `sigma_one_le` (gcd `≤ q`), `le_totient_mul`: term `≤ 4 (log q+1)³/q`; `∑_{q ≤ P} 1/q ≤ log P + 1` (`harmonic_le_one_add_log`). |

## 7. `SingularIntegral.lean` (F, difficulty 4)

| Lemma | Owner | Sketch |
|---|---|---|
| `norm_singularIntegral_sub_count_le` | F 4 | `sum_TI_mul_TJ_eq_count`; the complement of the arc is `{j : J₀ < j < Q - J₀}` (after reindexing `Icc (-J₀) J₀` mod `Q`); for `m = min j (Q-j) > J₀`: `‖TJ‖ ≤ Q/(2m)`; if `distInt (ν j/Q) ≥ m/Q` (always for `ν = 1`, and for `ν = 2` when `m ≤ Q/4`) `‖TI‖ ≤ Q/(2m)`, giving `∑ Q²/(4m²) ≤ Q²/(2 J₀)`; for `ν = 2`, `Q/4 < j < 3Q/4`: `‖TJ‖ ≤ 2`, `‖TI‖ ≤ min (βX+1) (Q/(2|2j-Q|))`, sum `≤ 2(βX+1) + 2Q(log Q + 1)`. Divide by `Q`; `J₀ ≥ PQ/X`. |

## 8. `MajorArcs.lean` (E*/F, difficulty 3–5)

| Lemma | Owner | Sketch |
|---|---|---|
| `rep_eq_majorSum_add_minorSum` | E 2 | `rep_eq_sum` + `sum_range_Q_eq` with `F θ = SI θ * SJ θ * e (-(N θ))` (periodic by `SI_add_one`, `SJ_add_one`, `e_add_intCast`); `mul_add`, `Finset.mul_sum`. |
| `exists_SJ_approx` | F 5 | Split `J` by residues `r mod q` (`Finset.sum_fiberwise`); `(r, q) > 1` classes total `≤ q log X` (`sum_vonMangoldt_not_coprime_le`); coprime class: `norm_sum_Ioc_sub_mul_le` with `f n = Λ n [n ≡ r]`, `g n = 1/φ(q) [n ≡ r]`... (take `g n = 1/φ(q)` constant and compare partial sums `ψ(n;q,r)` with `n/φ(q)` using SW: `D ≤ C_A (δX)(log(γX))⁻ᴬ`), `v n = e (n β)`, total variation `≤ 2π|β| (δX+1)` (`norm_e_sub_one_le`). Sum over `φ(q)` classes with `∑_{(r,q)=1} e(a r/q) = μ(q)` (`sum_e_coprimeRange`, `ramanujanSum_one_right`). `log (γX) ≥ (log X)/2` eventually. |
| `exists_SI_approx` | F 4 | Same as above with `e (ν m a/q)`; residue sum `∑_{(r,q)=1} e (ν a r/q) = c_q(ν a) = c_q(ν)` (`sum_coprimeRange_mul_mod`, `sum_e_coprimeRange`, `ramanujanSum_mul_of_coprime_right`). |
| `sum_main_eq` | E* 4 | Pure algebra: `arcAngle = a/q + j/Q`; `e (-(N (a/q + j/Q))) = e (-(N a/q)) e (-(N j/Q))`; pull out `j`-independent factors (`Finset.mul_sum`, `Finset.sum_mul`); `∑_{a ∈ coprimeRange q} e (-(N a/q)) = c_q(N)` (`sum_e_neg_coprimeRange`); reindex `arcIndex P` as `Finset.sigma`/biUnion over `q` (`Finset.sum_sigma'`, or `Finset.sum_product'` after `Finset.sum_filter`); assemble `μ(q) c_q(ν) c_q(N)/φ(q)² = arcCoeff`. |
| `exists_norm_majorSum_sub_le` | F 4 | `‖S_I S_J - m_I m_J‖ ≤ ‖S_I - m_I‖‖S_J‖ + ‖m_I‖‖S_J - m_J‖`; `norm_SJ_le`, `‖m_I‖ ≤ 3 (βX+1)`; the two approximations with `b = 2P` (`halfWidth_div_Q_le`); number of terms `≤ P² (2J₀+1) ≤ 5 P³ Q / X` (`card_arcIndex_le`, `two_mul_halfWidth_add_one_le`); divide by `Q`. |

## 9. `MinorArcs.lean` (E*/F, difficulty 3–4)

| Lemma | Owner | Sketch |
|---|---|---|
| `sum_norm_sq_minorSum_le` | E* 3 | `minorSum N = Q⁻¹ ∑_{k<Q} F k e(-(N k/Q))` with `F k = [k ∈ minorSet] SI SJ` (`Finset.sum_filter`); `sum_norm_sq_sum_mul_e_neg`; `‖F k‖² ≤ M² ‖SI(k/Q)‖²`; `sum_norm_sq_sum_mul_e` for `SI` with `g m = ν m` (distinct mod `Q` by `add_lt_Q`-type bounds). |
| `exists_norm_SJ_le_of_mem_minorSet` | F 4 | `SJ θ = lambdaExpSum (δX) θ - lambdaExpSum (⌈γX⌉₊ - 1) θ` (`Finset.sum_Ioc_eq_sub`-style, `Icc` difference); `exists_approx_of_mem_minorSet` gives `q ∈ (P, X/P]`; apply `hVM` at both `x`; `x/√q ≤ δX/√P`, `x^{4/5} ≤ X/√P` (from `P⁵ ≤ X`), `√(xq) ≤ √δ X/√P`; `log (δX) ≤ 2 log X` eventually. |
| `exists_card_minor_exceptional_le` | E* 3 | From the two previous lemmas and `sum_vonMangoldt_sq_le` (`∑_{m∈I} Λ² ≤ (βX+1) log(βX+1)²`): `#S · (εX)² ≤ ∑_N ‖minorSum N‖²` (`Finset.card_nsmul_le_sum` on the filter), rearrange. |

## 10. `RestrictedBinary.lean` (F, difficulty 3–4)

| Lemma | Owner | Sketch |
|---|---|---|
| `eventually_truncation_bounds` | E* 3 | `P = ⌊(log X)^60⌋₊`; `(log X)^300 ≤ X` eventually (`Real.isLittleO_log_rpow_atTop` / `tendsto_pow_log_div_rpow_atTop`... simplest: `Real.tendsto_pow_log_div_mul_add_atTop` or `isLittleO_log_rpow_rpow_atTop`); `Q ≥ P! ≥ P` so `X ≤ P Q` follows from `X ≤ P · span`-free bound `Q ≥ ⌊span⌋+1 > B X`, i.e. need `P B ≥ 1`. |
| `eventually_le_rep` | F 4 | Combine `rep_eq_majorSum_add_minorSum`, `exists_norm_majorSum_sub_le` (A = 305: `P⁵ (log X + 1)/(log X)^305 ≤ 2 (log X)^{-4}`), `norm_singularIntegral_sub_count_le`, `le_count_of_isAdmissible`, `abs_singularSeries_le`, and `N ∉ badSingular`, `N ∉ badMinor`: `rep ≥ (1/2)(ηX - 1 - 2X/P - 4(log Q + 2)) - 4(log P+1)⁴(2X/P + ...) - o(X) - ηX/8 ≥ ηX/8`. |
| `eventually_exceptionalSet_subset` | E 2 | `mem_exceptionalSet`; contrapositive of `eventually_le_rep` + `hasPrimeRepr_of_lt_rep` (`ηX/8 > 2√span (log span)²` eventually). |
| `tendsto_card_badSingular` | E* 3 | `card_singularSeries_lt_le` with `Y = ⌊BX⌋₊`, hypothesis `hY` eventually true; bound `4·10⁵ B X (2/(log X)^60)^{1/4} = o(X/log X)`; `tendsto_of_tendsto_of_tendsto_of_le_of_le` (squeeze) with `Real.tendsto_pow_log_div_...`. |
| `tendsto_card_badMinor` | E* 3 | `exists_card_minor_exceptional_le` with `ε = η/8`: `C X (log X)^{10} · 64/(η² (log X)^{60}/2) = o(X/log X)`; squeeze. |
| `tendsto_card_exceptionalSet` | E 2 | `Finset.card_le_card` + `card_union_le`; squeeze with the two previous limits (`Tendsto.add`, `tendsto_const_nhds`). |

## 11. `PrimesIccLower.lean` (E*, difficulty 3)

| Lemma | Owner | Sketch |
|---|---|---|
| `eventually_le_sum_vonMangoldt_Ioc` | E* 3 | `∑_{Ioc} Λ = ψ(βX) - ψ(αX)` (`Finset.sum_Ioc_eq_sub`... i.e. `Icc 1 ⌊βX⌋ = Icc 1 ⌊αX⌋ ∪ Ioc ⌊αX⌋ ⌊βX⌋`); `abs_psi_sub_le` with `A = 1` at both points: error `≤ C(αX + βX)/log(αX) = o(X)`. |
| `eventually_le_sum_log_primesIcc` | E* 3 | Remove non-primes with `sum_vonMangoldt_not_prime_le` (`≤ √(βX) log(βX) = o(X)`); `vonMangoldt_apply_prime`; `Nat.primesIcc` vs `Ioc ⌊αX⌋₊ ⌊βX⌋₊` filtered by `Prime` (`Nat.mem_primesIcc`; the boundary point `⌊αX⌋₊` differs by at most one prime, weight `≤ log (βX)`). |
| `primesIccLower` | E 2 | `∑_{p ∈ primesIcc} log p ≤ #primesIcc · log(βX)` (`Finset.sum_le_card_nsmul`), so `#primesIcc ≥ (β-α)X/(4 log(βX))`, and `log (βX) ≤ 2 log X` eventually; `c = (β-α)/8`. |

## 12. `Exhaustion.lean` (E, difficulty 2)

| Lemma | Owner | Sketch |
|---|---|---|
| `prime_mem_gen_succ_of_Icc_subset` | E 2 | `p = (m-1) + (p-(m-1))`, both in `Icc 1 (m-1)` (omega), `add_mem_gen_succ_of_prime`. |
| `Icc_subset_gen_of_Icc_subset` | E 2 | `Nat.exists_prime_lt_and_le_two_mul (m-1) (by omega)`; case `p = m`: `add_mem_gen_succ_of_prime` with `1 ∈ gen n`; case `p > m`: previous lemma then `mem_gen_succ_of_add_eq_two_mul (ha : p ∈ gen (n+1)) (hb : 2m - p ∈ gen (n+1))` with `gen_mono`; `Finset.insert_subset_iff`-free: show `x ∈ Icc 1 m → x ∈ gen (n+2)` by `x ≤ m - 1 ∨ x = m`. |
| `exhaustion` | E 1 | Induction on `k`; base `Icc 1 0 = ∅`; step: `Icc 1 (k+1)`, apply `Icc_subset_gen_of_Icc_subset` (for `k + 1 ≥ 2`; `k = 0`: `1 ∈ gen 0`). |

## 13. `StandardMain.lean`

No `sorry`; compiles once everything above does.

---

## Executor protocol

1. Work on exactly one file and one `sorry` at a time; run
   `lake env lean <file>` after each change. A step is done when the file has no errors and
   the target declaration no longer reports `declaration uses 'sorry'`.
2. Never change a theorem statement, docstring, name or import list. If the statement seems
   false or a constant too small, write a note `-- BLOCKED: <reason>` above the `sorry` and stop.
3. You may add private helper lemmas *above* the target (Mathlib style, docstring, ≤ 100 chars per
   line). Prefer existing Mathlib lemmas; search with `rg -n "theorem <name>" .lake/packages/mathlib`
   or `exact?`/`apply?`.
4. No `axiom`, no `native_decide`, no `sorry` left behind, no `set_option maxHeartbeats` above
   400000 without a comment.
5. Report: the list of lemmas closed, the list left `sorry`/`BLOCKED` with a one-line diagnosis,
   and any Mathlib lemma names that turned out not to exist.

Escalation: a lemma failed by an executor twice goes to the planner.

## Check script

`python3 scripts/check.py` prints, per file, the number of remaining `sorry`s and verifies the
public statements against the frozen copies in `scripts/frozen.json` (`--freeze` re-records them).
`scripts/lc.sh <file>` compiles a single module with `lean` directly, writing into the `lake` build
tree. Axioms of the top-level results are checked with `#print axioms` in a scratch file.
