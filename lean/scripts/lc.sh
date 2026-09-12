#!/usr/bin/env bash
# Compile one module of ConwayGolden directly with `lean`, writing .olean/.ilean into the
# lake build tree, bypassing `lake` (which stalls on `git` in the Mathlib package on slow
# machines). Usage: scripts/lc.sh ConwayGolden/NumberTheory/CircleMethod/ExpSum.lean
# Prints errors/warnings except `declaration uses sorry`.
set -u
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
LP=".lake/build/lib/lean"
for p in .lake/packages/*; do LP="$LP:$p/.lake/build/lib/lean"; done
src="$1"
mod="${src%.lean}"
out=".lake/build/lib/lean/$mod"
mkdir -p "$(dirname "$out")"
LEAN_PATH="$LP" lean "$src" -o "$out.olean" -i "$out.ilean" 2>&1 \
  | grep -v "declaration uses \`sorry\`"
echo "[lc] done: $src (exit ${PIPESTATUS[0]})"
