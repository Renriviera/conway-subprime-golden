# Lean 4 formalization of the Conway cardinality-ratio argument

Lean 4 + Mathlib `v4.33.1`. Build from this directory:

```sh
export PATH="$HOME/.elan/bin:$PATH"
lake build
```

The source of the argument is `../prime-completeness.md` and `../conway-subprime-proof.tex`.
This is a formalization of that draft, not an independent proof of the cited analytic theorems.

## What is proved

| File | Content |
| --- | --- |
| `ConwayGolden/Basic.lean` | Conway function `s`, sets `C n`, maximum `M n`, first missing prime `P n`, complete prime prefix `Q n`, Fibonacci inequality, structural inclusion |
| `ConwayGolden/Combinatorial.lean` | Bootstrap pigeonhole, outlier generation `(t+q)/2` then `p+b`, closing step |
| `ConwayGolden/Asymptotic.lean` | `M n / φ^n` converges from the Fibonacci inequality; contraction lemma |
| `ConwayGolden/Deduction.lean` | Scale selection `d < c φ^{-k} ≤ φ d`; interval arithmetic for `I, J, U`; `q`- and `a`-margins; positivity of `lim M n / φ^n` from `Q n ≫ φ^n` |
| `ConwayGolden/Main.lean` | Section 5: `AnalyticConclusions` imply `\|C(n+1)\| / \|C n\| → φ` and `\|C n\| / M n → 1/φ` |

The main conditional theorem is `Conway.golden_ratio_conjecture`:

```lean
AnalyticConclusions → Tendsto (fun n => |C (n+1)| / |C n|) atTop (𝓝 φ)
```

`lake build` completes with Lean 4.33.1 / Mathlib `v4.33.1`.

## What is assumed

`ConwayGolden/Analytic.lean` packages the draft's external inputs as a structure `AnalyticInputs`. These are not kernel axioms; they are hypotheses.

1. **Exhaustion** — Caragiu–Vicol–Zaki, Theorem 1: every finite initial segment appears in some `C N`.
2. **Goldbach filling** — Coppola–Laporta almost-all Goldbach with almost-equal primes.
3. **Prime estimates** — PNT with error: short intervals, proportional intervals, previous/next prime.
4. **Binary lemma** — almost-all `N = 2p + q` with `p, q` in two fixed positive-length intervals (the appendix).

`RoughScales` packages the `L k` bootstrap (`Q n ≫ φ^n`). The draft derives it from (1)–(3).

The circle-method appendix is not formalized. Mathlib does not contain those exponential-sum estimates.

## Module map

```
Basic ──────► Combinatorial
  │                │
  ├────────► Asymptotic
  │                │
  └────────► Analytic ──► Deduction ──► Main
```
