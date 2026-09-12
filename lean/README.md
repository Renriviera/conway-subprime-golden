# Lean 4 formalization: Conway's subprime generations and the golden ratio

Lean 4 + Mathlib `v4.33.1`. Build from this directory:

```sh
export PATH="$HOME/.elan/bin:$PATH"
lake build
```

`lake build` completes without warnings. Every theorem depends only on the standard axioms
`propext`, `Classical.choice`, `Quot.sound` (checked with `#print axioms`).

The manuscript is `../conway-subprime-proof.tex`. The formalization follows a lean-friendly
arrangement of the same analytic ingredients (Siegel–Walfisz and a Vinogradov minor-arc bound)
rather than a line-by-line transcription of the paper. It follows Mathlib conventions:
one concept per file, `snake_case` theorem names built from the statement, module docstrings
with *Main definitions / Main statements*, and no `sorry`.

## Main theorem

```lean
theorem Conway.tendsto_card_gen_succ_div_of_standardInputs (h : CircleMethod.StandardInputs) :
    Tendsto (fun n : ℕ ↦ (#(gen (n + 1)) : ℝ) / #(gen n)) atTop (𝓝 φ)
```

(`Subprime/StandardMain.lean`). `CircleMethod.StandardInputs` consists of exactly two standard
analytic theorems, stated precisely in `NumberTheory/CircleMethod/Inputs.lean`:

* `SiegelWalfisz` — for every `A > 0` there is `C_A` with
  `|ψ(x; q, a) - x / φ(q)| ≤ C_A x / (log x)^A` for `x ≥ 2`, `q ≤ (log x)^A`, `(a, q) = 1`;
* `VinogradovMinorArc` — there is `C` with
  `‖∑_{n ≤ x} Λ(n) e(nα)‖ ≤ C (log x)^4 (x q^{-1/2} + x^{4/5} + (xq)^{1/2})`
  whenever `|α - a/q| ≤ q^{-2}`, `(a, q) = 1`.

Everything else — the discrete circle method, the major/minor-arc estimates, the singular
series and singular integral, the Chebyshev-type prime count, and the generation dynamics — is
Lean-checked. The intermediate result

```lean
theorem Conway.tendsto_card_gen_succ_div (h : Conway.Hypotheses) :
    Tendsto (fun n : ℕ ↦ (#(gen (n + 1)) : ℝ) / #(gen n)) atTop (𝓝 φ)
```

isolates the four problem-specific inputs actually used by the dynamics (`Conway.Hypotheses`,
see below), and `Conway.Hypotheses.of_standardInputs` derives them from `StandardInputs`.

Together with (all under `h : Conway.Hypotheses`)

| Statement | Content |
| --- | --- |
| `Conway.tendsto_genMax_succ_div` | `genMax (n + 1) / genMax n → φ` |
| `Conway.tendsto_card_gen_succ_div_genMax` | `#(gen (n + 1)) / genMax n → 1` |
| `Conway.tendsto_card_gen_div_genMax` | `#(gen n) / genMax n → φ⁻¹` |
| `Conway.eventually_primePrefix_genMax` | for `0 < ζ < 1`, every prime `≤ (1 - ζ) genMax n` lies in `gen n` for large `n` |

## The intermediate hypotheses

`Conway.Hypotheses` (`ConwayGolden/Subprime/Hypotheses.lean`) is a `Prop`-valued structure, not
an axiom. Its four fields are the only inputs used by the generation dynamics, and each is proved
from `StandardInputs` in `Subprime/StandardMain.lean`:

1. `exhaustion` — every initial segment `[1, k]` lies in some generation
   (Caragiu–Vicol–Zaki). Proved unconditionally in `Subprime/Exhaustion.lean` via Bertrand's
   postulate.
2. `primesIcc_lower` — for fixed `0 < α < β`, the interval `[α X, β X]` contains
   `≫ X / log X` primes for large `X`. Proved from Siegel–Walfisz with `q = 1` in
   `NumberTheory/CircleMethod/PrimesIccLower.lean`.
3. `restrictedBinary_one` — almost all admissible even `N` are sums `p + q` with `p`, `q` primes
   in prescribed proportional ranges (exceptional set `o(X / log X)`).
4. `restrictedBinary_two` — the same for `N = 2p + q`.

Items 3–4 are proved by a discrete circle method in `NumberTheory/CircleMethod/`
(`RestrictedBinary.lean` is the entry point); see the module map below. No prime-number-theorem
error term beyond Siegel–Walfisz and no almost-equal-primes Goldbach result is used.

## Module map

```
NumberTheory/PrimesIcc ─┐
NumberTheory/PrimeCountingLittleO ─┐
Analysis/SelfDivLog ──┐            │
Analysis/TendstoOfEventually ──┐   │
                               │   │
Subprime/Basic ──► Pigeonhole ──► PrimePrefix ──► Hypotheses
                                                     │
                       Filling ◄─────────────────────┤
                          │                          │
                       Extension ◄───────────────────┘
                          │
                        Boost ──► Weight ──► Comparison ──► Limit
```

| File | Content |
| --- | --- |
| `Analysis/SelfDivLog.lean` | `x / log x → ∞` and monotonicity on `[e, ∞)` |
| `Analysis/TendstoOfEventually.lean` | two-sided `ε` criterion for `Tendsto`; the contractive recursion `d (n+1) ≤ ρ d n + e n ⇒ d → 0` |
| `NumberTheory/PrimesIcc.lean` | `Nat.primesIcc a b`, primes in a real interval; counting bounds |
| `NumberTheory/PrimeCountingLittleO.lean` | `π ⌊x⌋₊ / x → 0` from Mathlib's Chebyshev bound |
| `Subprime/Basic.lean` | `subprime`, generations `gen n`, maxima `genMax n`, holes; Fibonacci inequality `genMax (n+2) ≤ genMax (n+1) + genMax n`, `genMax (n+1) ≤ 2 genMax n`, structural inclusions |
| `Subprime/Pigeonhole.lean` | the two generation mechanisms `(t + q)/2` and `2p + u`; pigeonhole against holes |
| `Subprime/PrimePrefix.lean` | `PrimePrefix n L`: all primes `≤ L` lie in `gen n` |
| `Subprime/Hypotheses.lean` | `PrimesIccLower`, `RestrictedBinary ν`, `Hypotheses` |
| `Subprime/Filling.lean` | buffered filling: holes below `(1 - θ) X` are `o(X / log X)` |
| `Subprime/Extension.lean` | proportional extension; `Profile λ j L`; normal propagation `(j, L) ↦ (j+1, λ L)` |
| `Subprime/Boost.lean` | increase of a profile by a factor `1 + κ` when the maximum runs ahead |
| `Subprime/Weight.lean` | golden weight `genWeight`, normalised `profileRatio`; growth/contraction laws |
| `Subprime/Comparison.lean` | bounded-step comparison; approximate prime completeness |
| `Subprime/Limit.lean` | Fibonacci saturation, the ratio recursion, and the four limits |

## The circle method (`NumberTheory/CircleMethod/`)

```
ExpSum → Inputs → RamanujanSum → Setup → Arcs → SingularIntegral ─┐
                              └──► SingularSeries ────────────────┤
                                                                  ▼
Inputs → PrimesIccLower              MajorArcs → MinorArcs → RestrictedBinary
Pigeonhole → Exhaustion                                              │
                                    StandardMain ◄───────────────────┘
```

| File | Content |
| --- | --- |
| `ExpSum.lean` | `e θ = exp(2πiθ)`, distance to the nearest integer, geometric-series bound `‖∑ e(nθ)‖ ≤ 1/(2‖θ‖)`, Abel summation, discrete orthogonality and Parseval on `ℤ/Q` |
| `Inputs.lean` | `SiegelWalfisz`, `VinogradovMinorArc`, `StandardInputs`; elementary bounds for `Λ` |
| `RamanujanSum.lean` | `c_q(n) = ∑_{(r,q)=1} e(rn/q)`, multiplicativity, `c_q(n) = μ(q)` for `(n,q) = 1`, `|c_q(n)| ≤ σ₁(gcd(q,n))` |
| `Setup.lean` | the parameter ranges `Ranges`, the intervals `I`, `J`, the sums `SI`, `SJ`, `TI`, `TJ`, the modulus `Q = P!·(⌊span⌋+1)`, the representation count `rep N` and its completed-sum identity |
| `Arcs.lean` | the grid `k/Q`, major arcs `a/q + j/Q` (`q ≤ P`, `|j| ≤ J₀`), disjointness, the major/minor decomposition of `∑_{k<Q}`, Dirichlet approximation on the minor arcs |
| `SingularSeries.lean` | `𝔖_P(N) = ∑_{q ≤ P} μ(q) c_q(ν) c_q(N)/φ(q)²`, finite Euler product, `𝔖 ≥ 1/2` off a small set, tail bounds via `σ₁(d)/φ(d)²` and `∑ 1/φ(r)²` |
| `SingularIntegral.lean` | `W(N) = Q⁻¹ ∑_{|j| ≤ J₀} TI TJ e(−Nj/Q)` versus the lattice count: `‖W − count‖ ≤ 2X/P + 4(log Q + 2)` |
| `MajorArcs.lean` | residue-class decomposition, Siegel–Walfisz on a major arc, `‖majorSum − 𝔖 W‖ ≤ C P⁵ X (log X + 1)/(log X)^A` |
| `MinorArcs.lean` | Vinogradov on the minor arcs (`‖SJ‖ ≤ C (log X)⁴ X/√P`), Parseval, the mean-square exceptional set |
| `PrimesIccLower.lean` | `primesIcc_lower` from Siegel–Walfisz at `q = 1` |
| `RestrictedBinary.lean` | assembly with `P = ⌊(log X)^60⌋`: `rep N ≥ ηX/8` off the bad sets, `#exceptionalSet = o(X/log X)` |

The design notes and lemma-by-lemma proof sketches are in `BLUEPRINT.md`; `scripts/check.py`
reports the `sorry` count per file (now `0`) and verifies that the public statements agree with the
frozen copies in `scripts/frozen.json`.

## Legacy

`legacy/` contains the first formalization (of the original, pre-revision argument). It is not
built and is kept only for reference; an identical copy is in `../proof-archive/`.
