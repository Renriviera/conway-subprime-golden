# Weaker analytic inputs for the Conway ratio proof

8 September 2026. Research variant by OpenAI Astra and Romain Popescu.

The baseline is preserved verbatim in [`../../proof-archive/2026-09-08T135006Z/`](../../proof-archive/2026-09-08T135006Z/). Its manifest records SHA-256 hashes for the manuscript, PDF, research notes, computation, and existing Lean sources/configuration. The original files have not been edited by this investigation.

## Result of the investigation

**The cardinality-ratio conclusion survives with `o(X / log X)` exceptional sets.** The proof needs a new argument; merely substituting that rate into the old proof is not valid.

The revised [LaTeX manuscript](conway-subprime-proof.tex) proves a conditional reduction from:

1. Exhaustion of the positive integers by the Conway sets.
2. A lower bound of order `X / log X` for primes in each fixed positive proportional interval, and `π(X) = o(X)`. Ordinary PNT implies these; no PNT error term is used.
3. Restricted representations `N = p + q` for even targets, with `o(X / log X)` exceptions when the real overlap has positive proportional length.
4. The analogous restricted representations `N = 2p + q` for odd targets, with the same error scale.

Its conclusions are `M(n+1)/M(n) → φ`, approximate completeness of primes below `M(n)`, `|C(n)|/M(n-1) → 1`, the original cardinality ratio, and density `1/φ`.

It does **not** assert `M(n) ~ c φ^n` for a positive constant under these weakened assumptions. The stronger amplitude theorem remains in the preserved proof.

## What changed

| Component | Preserved proof | Revised proof |
| --- | --- | --- |
| Filling | `O_A(X/log^A X)` holes all the way to `X` | `o(X/log X)` holes below `(1-θ)X`, for each fixed positive buffer `θ` |
| Source of filling | Almost-equal-primes theorem | Fixed proportional ranges for ordinary binary Goldbach, followed by a dyadic argument |
| Coefficient-two binary input | Arbitrary logarithmic savings | `o(X/log X)` only |
| Prime estimates | Shrinking intervals and PNT with error | Proportional intervals and sublinear prime counting |
| Growth mechanism | Summable losses and positive amplitudes `c,d` | A finite increase of a generated prime profile and a bounded-step comparison |
| Main bookkeeping | Complete prime prefix `Q`, first missing prime, and limiting constants | `PrimePrefix(j,L)` and the weighted maximum `M(j+1)+M(j)/φ` |
| Final limit | Quotient of positive amplitude limits | Asymptotic Fibonacci equality, then a contracting ratio recurrence |

The buffer matters. With only fixed proportional ranges, discarding a boundary strip of length `θX` does not give an `o(X/log X)` error all the way to `X`. The revised proof uses only buffered filling and postpones `θ → 0` until the final density squeeze. It never substitutes a moving `θ(X)` into a theorem whose parameters must stay fixed.

## Why the new comparison works

Choose an accuracy `δ > 0` and a fixed `λ < φ` close to `φ`. A profile consists of complete prime cutoffs `L, λL` in generations `j, j+1`. Ordinary propagation advances this profile at rate `λ`.

If `M(j) > (1+δ)L`, select an earlier maximum prime `t` with

`(1+δ)L < t ≤ 2(1+δ)L`.

Two restricted prime intervals yield almost every prime `u` in a further interval through `(t+q)/2` and then `p+(t+q)/2`. A second pigeonhole pairs such a `u` with a buffered filled integer. This gives every prime up to `(λ³+δ/8)L` in generation `j+3`. One more propagation supplies a balanced pair of cutoffs, yielding a profile at `j+3` larger by a fixed factor `1+κ`.

The weighted maximum grows by at most `φ` each generation. If the ratio of weighted maximum to weighted profile exceeds `1+δ`, either the earlier or the later maximum triggers the increase. In three or four steps this ratio contracts by at most

`(φ/λ)^4 / (1+κ) < 1`.

At ordinary steps its growth is at most `φ/λ`, which is close to one. This bounds the ratio at all sufficiently late generations. Letting `δ → 0` gives approximate prime completeness. **No infinite series of error bounds occurs.** The manuscript gives an explicit formula for `λ` and checks all interval margins and generation indices.

## What does not follow from plain density zero

`o(X)` and `o(X/log X)` are different hypotheses. A set with only about `X/log X` elements has density zero and can still contain all prime candidates in a proportional interval. Likewise a translated prime set can account for every missing complementary integer in a particular pigeonhole.

This is an obstruction to the proposed substitution, not a proof that no other density-zero argument could exist. To use only `o(X)`, an additional theorem would have to prevent concentration of exceptions on the relevant primes or their translates. Such a transversality or weighted estimate is not part of a bare `DensityZero` statement.

In the preserved proof the problem also appears earlier: the chosen interval of width `X/log²X` contains only about `X/log³X` primes. An `o(X/log X)` hole estimate can be larger than that. Replacing this by a fixed proportional interval repairs the pigeonhole, but gives nonsummable relative losses in general. The new profile argument is what repairs the growth proof.

## Lean status and checked artifacts

[`WeakInputs.lean`](WeakInputs.lean) provides precise proposed interfaces using real scale parameters and natural-number targets. It also proves:

- two errors that are little-o on the prime-candidate scale cannot exhaust a candidate family with a positive lower bound on that scale;
- the upper and lower complementary-integer margins in the new profile-increase lemma.

The file is checked against the existing project's cached Lean/Mathlib environment, without adding dependencies or changing that project. The full new reduction is **not** formalized. In particular, deriving buffered filling, proving the profile-increase lemma, and assembling the bounded-step iteration are still mathematical arguments in the manuscript. See [`lean-check.log`](lean-check.log) for the actual compiler output.

The current baseline Lean source also has an important boundary: `golden_ratio_conjecture` and `golden_ratio_of_inputs` in `Main.lean` both take **`AnalyticConclusions`**, not `AnalyticInputs`. The former structure already assumes positive maximum amplitude and approximate prime completeness. `Deduction.lean` proves useful component lemmas, but does not assemble `AnalyticInputs → AnalyticConclusions`; its closing lemma takes the eventual closing assertion as a hypothesis. The comment claiming that this full derivation is carried out there overstates what the file presently proves. This investigation records the gap without editing the preserved project.

## External Lean developments: checked scope

- The current [PNT+ `MediumPNT.lean`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/main/PrimeNumberTheoremAnd/MediumPNT.lean) states `MediumPNT` for **Chebyshev ψ** with error `O(x exp(-c(log x)^(1/10)))`. Passing to prime counts still needs bridging lemmas. The weaker interface here requires only proportional intervals and sublinear prime counting. No PNT+ dependency has been installed or built in this investigation.
- The [erdos1054 project README](https://github.com/antoshashakov/Principia-Math-Solutions/tree/main/erdos1054) advertises a density-zero binary Goldbach theorem and compiler logs. Its [verification ledger](https://github.com/antoshashakov/Principia-Math-Solutions/blob/main/erdos1054/VERIFICATION.md) says the recorded master builds were not independently rerun there and comparator certification on the real masters was not run. I checked these statements, not the 31k-line proof or its transitive dependencies.
- That project's documented pin uses Lean `v4.31.0`, whereas this workspace uses `v4.33.1`. Its advertised headline is neither a proof of the stronger error scale nor a restricted-range theorem. Its internals might provide the needed estimates, but that requires inspecting actual declarations and rebuilding them; the headline alone does not establish it.

The next bounded formalization work is to implement the buffered-filling deduction and profile-increase/counting lemmas against the explicit weak interfaces. This can proceed before choosing or auditing an external analytic dependency.

## Rebuilding

From this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=tmp/pdfs conway-subprime-proof.tex
```

To check the small Lean support file from the workspace's `lean/` directory:

```sh
lake env lean ../proof-variants/lean-friendly/WeakInputs.lean
```
