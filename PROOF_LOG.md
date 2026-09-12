# Conway proof log

## 2026-09-08 — preserved baseline

Saved the current manuscript, compiled PDF, research notes, computation, and Lean source/configuration in [proof-archive/2026-09-08T135006Z](proof-archive/2026-09-08T135006Z/README.md). [MANIFEST.json](proof-archive/2026-09-08T135006Z/MANIFEST.json) records SHA-256 hashes. This is a verbatim preservation of the current research draft, not an additional certification of its correctness.

## 2026-09-08 — separate weaker-input variant

New work is in [proof-variants/lean-friendly](proof-variants/lean-friendly/README.md). The original manuscript and original Lean sources remain unchanged.

The revised argument proves a conditional reduction of the golden-ratio limit to proportional prime estimates and restricted binary estimates with `o(X/log X)` exceptions. It derives buffered filling from a restricted ordinary Goldbach input. A finite increase of a generated prime profile replaces the summability/positive-amplitude argument. The principal proof uses neither limiting amplitudes nor a first missing prime.

Bare `o(X)` exceptional sets do not justify the prime-candidate pigeonholes. The notes distinguish this obstruction from any claim that every possible density-zero approach is impossible.

The separate Lean support file checks the proposed interfaces and three elementary lemmas; it is not a full formalization of the revised argument. The notes also record that the existing baseline Lean final theorem assumes `AnalyticConclusions`, and that the complete derivation from `AnalyticInputs` is not implemented there.
