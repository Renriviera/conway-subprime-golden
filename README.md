# Lean formalization: golden-ratio growth of Conway's subprime closure

This repository is a **Lean 4 supplement** to the paper

> Romain Popescu, *Golden-ratio growth of Conway's subprime closure*,
> submitted to arXiv (`math.NT`) and the *Journal of Number Theory*.

It is not the manuscript. The paper is the citable source for the theorem; this tree is the machine-checked companion, also intended as arXiv ancillary material and as a journal code supplement.

The formalization proves the Caragiu–Vicol–Zaki cardinality-ratio limit

\[
\lim_{n\to\infty}\frac{|C_{n+1}|}{|C_n|}=\varphi=\frac{1+\sqrt{5}}{2},
\]

assuming two standard analytic inputs: the Siegel–Walfisz theorem and a Vinogradov-type minor-arc bound. Everything else is Lean-checked, with no `sorry`.

## Contents

| Path | Role |
| --- | --- |
| [`lean/`](lean/) | Lake project (Lean `v4.33.1`, Mathlib `v4.33.1`) |
| [`lean/README.md`](lean/README.md) | Module map and theorem list |
| [`lean/BLUEPRINT.md`](lean/BLUEPRINT.md) | Lemma-by-lemma plan for the circle-method files |
| [`lean/scripts/check.py`](lean/scripts/check.py) | Zero-`sorry` and frozen-statement check |

## Build

From `lean/`:

```sh
export PATH="$HOME/.elan/bin:$PATH"
lake build
python3 scripts/check.py
```

Or from the repository root: `make build` and `make check`. Mathlib is fetched on the first `lake build`; the `.lake/` checkout is not in git.

The public theorem is

```lean
theorem Conway.tendsto_card_gen_succ_div_of_standardInputs
    (h : CircleMethod.StandardInputs) :
    Tendsto (fun n : ℕ ↦ (#(gen (n + 1)) : ℝ) / #(gen n)) atTop (𝓝 φ)
```

in `lean/ConwayGolden/Subprime/StandardMain.lean`. See [`lean/README.md`](lean/README.md) for the remaining limits and the two analytic hypotheses.

## Relation to the paper

The manuscript proves the same limit, with an appendix that uses Siegel–Walfisz / Vinogradov-type exponential-sum estimates for a restricted binary representation lemma. This development uses those same two inputs, then checks a lean-friendly arrangement of the generation dynamics (buffered filling, Fibonacci-scale profiles). It is not a line-by-line transcription of the TeX.

Once the arXiv identifier is assigned, record it here and in `CITATION.cff`.

## License

The Lean sources are released under the [Apache License 2.0](LICENSE). The paper remains under the author's copyright and the arXiv/journal licenses chosen at submission.
