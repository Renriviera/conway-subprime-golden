#!/usr/bin/env bash
# Build a tidy arXiv upload tarball (TeX + Lean ancillary sources).
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
STAGE="$(mktemp -d "${TMPDIR:-/tmp}/arxiv-conway.XXXXXX")"
OUT_DIR="$ROOT/submission/arxiv"
OUT_TAR="$OUT_DIR/arxiv-upload.tar.gz"

cleanup() { rm -rf "$STAGE"; }
trap cleanup EXIT

mkdir -p "$STAGE/anc"
cp "$ROOT/conway-subprime-proof.tex" "$STAGE/"
cp "$ROOT/submission/arxiv/00README.XXX" "$STAGE/"
cp "$ROOT/submission/arxiv/00README.json" "$STAGE/"

rsync -a \
  --exclude '.lake' \
  --exclude 'legacy' \
  --exclude '.DS_Store' \
  "$ROOT/lean/" "$STAGE/anc/lean/"

# arXiv: do not put TeX sources in anc/.
find "$STAGE/anc" -name '*.tex' -delete

# Sanity: a single documentclass, and no lake checkout.
if [[ -e "$STAGE/anc/lean/.lake" ]]; then
  echo "error: .lake must not be packaged" >&2
  exit 1
fi

python3 - "$STAGE" <<'PY'
import pathlib, sys
stage = pathlib.Path(sys.argv[1])
tex = list(stage.glob("*.tex"))
assert tex, "missing top-level tex"
n = sum(1 for p in tex if "documentclass" in p.read_text(encoding="utf-8", errors="ignore"))
assert n == 1, f"expected one top-level tex, found {n}"
print(f"packaging {len(list((stage/'anc'/'lean').rglob('*')))} ancillary paths")
PY

mkdir -p "$OUT_DIR"
tar -czf "$OUT_TAR" -C "$STAGE" .
echo "wrote $OUT_TAR"
tar -tzf "$OUT_TAR" | head
echo "..."
tar -tzf "$OUT_TAR" | wc -l
