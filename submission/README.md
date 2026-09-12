# Submission files

This directory holds everything needed to post the paper on arXiv (`math.NT`) and then submit it to the *Journal of Number Theory*.

Recommended order: **arXiv first**, then the journal, citing the arXiv identifier. Elsevier's sharing policy treats arXiv posting as a preprint, not as prior publication.

## 1. arXiv (`math.NT`)

Build the upload tarball from the repository root:

```sh
make arxiv
```

This writes `submission/arxiv/arxiv-upload.tar.gz`. The archive contains:

- `conway-subprime-proof.tex` — sole top-level TeX file (PDFLaTeX)
- `00README.XXX` — `conway-subprime-proof.tex toplevelfile`
- `anc/lean/` — Lean sources, `lakefile.toml`, `lean-toolchain`, `README.md` (no `.lake/`, no `.tex`)

Do **not** upload `.aux`, `.log`, `.out`, `.synctex.gz`, Mathlib, the journal cover letter, or a precompiled PDF. arXiv compiles from source.

### Form fields

Copy from [`arxiv/metadata.txt`](arxiv/metadata.txt):

- Title, authors, affiliation, corresponding email
- Comments line (page count is filled after `make pdf`)
- MSC 2020: `11N05, 11P32, 11P55, 11B39`
- Primary category `math.NT`; optional cross-list `math.CO`
- License: CC BY 4.0

### Policy notes

- arXiv requires 10–14pt type and ≥1 inch margins. The manuscript uses 11pt and 1 inch margins.
- Links to code must resolve to a **public** repository. Make `https://github.com/Renriviera/conway-subprime-golden` public before announcement, or drop the GitHub URL and rely on the ancillary Lean tree.
- New authors in arXiv Mathematics need [endorsement](https://info.arxiv.org/help/endorsement.html) unless they already own a math paper. An institutional address is not enough by itself (policy of 10 December 2025).
- Processor: PDFLaTeX (TeX Live 2025 default is fine).

After announcement, record the identifier (e.g. `arXiv:2609.xxxxx`) in the journal cover letter.

## 2. Journal of Number Theory (Elsevier)

Submit at the journal's Editorial Manager portal from the [JNT homepage](https://www.sciencedirect.com/journal/journal-of-number-theory). The editor-in-chief is Dorian Goldfeld (Columbia).

Upload:

| Item | File |
| --- | --- |
| Cover letter | [`journal/cover-letter.md`](journal/cover-letter.md) |
| Highlights (optional, encouraged) | [`journal/Highlights.txt`](journal/Highlights.txt) |
| Manuscript PDF | built by `make pdf` |
| LaTeX source | `../conway-subprime-proof.tex` |
| Author CRediT | [`journal/credit.md`](journal/credit.md) |
| Competing interests | in the manuscript; also [`journal/competing-interests.md`](journal/competing-interests.md) |
| Generative-AI disclosure | in the manuscript, before the bibliography |

JNT has no extra formatting requirement at first submission beyond a complete article with abstract, keywords, and references. After acceptance, Elsevier applies `elsarticle` copy-editing.

Suggested reviewers are **not** included in the cover letter (Elsevier's current cover-letter guidance). Supply them in the Editorial Manager form if asked.

## 3. Checklist

- [ ] `make pdf` succeeds with no undefined references
- [ ] `python3 lean/scripts/check.py` reports `0` sorries
- [ ] GitHub repository is public, or the GitHub `\cite{Github}` URL is removed
- [ ] arXiv endorsement is in place
- [ ] `make arxiv` tarball compiles locally with `pdflatex` (two passes)
- [ ] arXiv metadata pasted from `arxiv/metadata.txt`
- [ ] After the arXiv identifier is assigned, insert it into the JNT cover letter
- [ ] JNT upload: PDF, TeX, cover letter, Highlights, competing-interest form
