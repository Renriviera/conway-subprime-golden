# Golden-ratio growth of Conway's subprime closure

Lean 4 formalization and manuscript for the cardinality-ratio conjecture of Caragiu, Vicol, and Zaki: the generations \(C_n\) of Conway's subprime closure satisfy

\[
\lim_{n\to\infty}\frac{|C_{n+1}|}{|C_n|}=\varphi=\frac{1+\sqrt{5}}{2}.
\]

The paper also proves the sharper asymptotics \(M_n\sim Q_n\sim c\varphi^n\) and \(|C_n|\sim c\varphi^{n-1}\), where \(M_n=\max C_n\) and \(Q_n\) is the last prime in the complete prime prefix of \(C_n\).

| | |
| --- | --- |
| Paper | [`conway-subprime-proof.tex`](conway-subprime-proof.tex) |
| Lean 4 + Mathlib | [`lean/`](lean/) |
| arXiv / JNT files | [`submission/`](submission/) |
| Author | Romain Popescu (`rep2159@columbia.edu`) |

## Theorem

Let \(s\) be Conway's subprime function (\(s(1)=1\), \(s(p)=p\) for primes, and \(s(m)=m/\mathrm{lpf}(m)\) for composites). Set \(C_0=\{1\}\) and

\[
C_{n+1}=C_n\cup\{s(a+b):a,b\in C_n\}.
\]

Caragiu–Vicol–Zaki proved that \(\bigcup_n C_n=\mathbb N\) and conjectured the golden-ratio growth of \(|C_n|\). The main theorem of the paper is:

\[
M_n\sim Q_n\sim c\varphi^n,\qquad |C_n|\sim c\varphi^{n-1},
\]

for an absolute constant \(c>0\). The two displayed limits

\[
\frac{|C_{n+1}|}{|C_n|}\to\varphi,\qquad \frac{|C_n|}{M_n}\to\frac1\varphi
\]

are immediate consequences.

## Paper

The manuscript is `conway-subprime-proof.tex` (PDFLaTeX, letter paper, 11pt). Compile with

```sh
make pdf
```

or `latexmk -pdf conway-subprime-proof.tex`. The argument uses:

- exhaustion of \(\mathbb N\) by the sets \(C_n\) ([Caragiu–Vicol–Zaki, Fibonacci Quarterly 55 (2017)](https://www.fq.math.ca/Papers1/55-4/CaragiuVicolZaki03162017.pdf));
- an almost-all Goldbach theorem with nearly equal primes, to fill almost every integer below a complete prime prefix;
- a restricted binary representation lemma \(N=2p+q\) proved in the appendix by the Hardy–Littlewood circle method (Siegel–Walfisz / Vinogradov-type inputs).

2020 MSC: `11N05`, `11P32`, `11P55`, `11B39`.

## Lean formalization

The formalization lives in [`lean/`](lean/) (Lean `v4.33.1`, Mathlib `v4.33.1`). It proves the same golden-ratio limit, taking as analytic input exactly two standard theorems:

- **Siegel–Walfisz** for primes in arithmetic progressions;
- **Vinogradov's minor-arc bound** for \(\sum_{n\le x}\Lambda(n)\,e(n\alpha)\).

Everything else — the discrete circle method, the restricted binary lemmas, the generation dynamics, and the four limits — is Lean-checked with no `sorry`. The public theorem is

```lean
theorem Conway.tendsto_card_gen_succ_div_of_standardInputs
    (h : CircleMethod.StandardInputs) :
    Tendsto (fun n : ℕ ↦ (#(gen (n + 1)) : ℝ) / #(gen n)) atTop (𝓝 φ)
```

Build from `lean/`:

```sh
export PATH="$HOME/.elan/bin:$PATH"
lake build
python3 scripts/check.py    # sorry count and frozen-statement check
```

`lake build` does not use the 6.5G `.lake/` checkout in git; Mathlib is fetched on first build. See [`lean/README.md`](lean/README.md) for the module map and [`lean/BLUEPRINT.md`](lean/BLUEPRINT.md) for the lemma-by-lemma plan.

The Lean development follows a lean-friendly arrangement of the same ingredients (buffered filling from restricted Goldbach, then Fibonacci-scale profiles). It is not a line-by-line transcription of the manuscript, but it verifies the same limit from the same class of analytic estimates used in the appendix.

## Submitting to arXiv and the Journal of Number Theory

Prepared files are in [`submission/`](submission/). The intended order is **arXiv `math.NT` first**, then *Journal of Number Theory* (Elsevier), citing the arXiv identifier.

```sh
make arxiv    # writes submission/arxiv/arxiv-upload.tar.gz
```

That tarball contains only the TeX source, an `00README.XXX`, and the Lean sources as ancillary files under `anc/`. It does not include `.aux`/`.log`, Mathlib, or journal cover-letter files.

Before uploading to arXiv:

1. Make this GitHub repository **public**, or remove the GitHub URL. arXiv requires that links to code resolve to a publicly available repository. The Lean sources are also bundled as ancillary files, so the formalization remains available even if the GitHub link is omitted.
2. New submitters to arXiv Mathematics currently need [personal endorsement](https://info.arxiv.org/help/endorsement.html) unless they already own a paper in an arXiv math category.
3. Category: `math.NT`. Suggested secondary: `math.CO`. Copy the title, comments, MSC, and abstract from [`submission/arxiv/metadata.txt`](submission/arxiv/metadata.txt).
4. License: CC BY 4.0 is a standard choice compatible with later journal publication; Elsevier explicitly allows arXiv preprints.

Then submit to [Journal of Number Theory](https://www.sciencedirect.com/journal/journal-of-number-theory) via Editorial Manager. Upload:

| File | Path |
| --- | --- |
| Manuscript PDF | compile with `make pdf` |
| LaTeX source | `conway-subprime-proof.tex` |
| Cover letter | [`submission/journal/cover-letter.md`](submission/journal/cover-letter.md) |
| Highlights | [`submission/journal/Highlights.txt`](submission/journal/Highlights.txt) |
| Competing interests | already in the manuscript (`Declarations of interest: none`) |
| Generative-AI disclosure | already in the manuscript, before the bibliography |
| Lean code (optional supplement) | `lean/` or the arXiv ancillary tree |

A checklist is in [`submission/README.md`](submission/README.md).

## Repository layout

```
conway-subprime-proof.tex   manuscript
lean/                       Lean 4 formalization (not the Mathlib checkout)
submission/                 arXiv package + JNT cover letter / highlights
conway.cpp                  small C++ experiment for early generations
experiment.txt              recorded output of that experiment
```

Working notes (`research.md`, `prime-completeness.md`, `proof-archive/`, `proof-variants/`) record earlier drafts. They are not part of the submission.

## License

The Lean formalization is released under the [Apache License 2.0](LICENSE). The manuscript remains the author's copyright until a journal copyright transfer; the intended arXiv license is CC BY 4.0.
