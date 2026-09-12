#!/usr/bin/env python3
"""Progress and integrity checks for the circle-method skeleton.

Usage:
    python3 scripts/check.py            # report sorries and verify frozen statements
    python3 scripts/check.py --freeze   # (planner only) record current statements as frozen
    python3 scripts/check.py --axioms   # additionally run #print axioms on the main results

Statements are the text of every `theorem`/`lemma`/`def`/`structure` declaration from its
keyword up to (excluding) the first `:= by` / `:=` / `where` that ends the header. Executors may
not change them; the planner re-freezes after deliberate revisions.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FROZEN = ROOT / "scripts" / "frozen.json"
FILES = sorted(
    [
        *(ROOT / "ConwayGolden" / "NumberTheory" / "CircleMethod").glob("*.lean"),
        ROOT / "ConwayGolden" / "Subprime" / "Exhaustion.lean",
        ROOT / "ConwayGolden" / "Subprime" / "StandardMain.lean",
    ]
)
MAIN_RESULTS = [
    "Conway.tendsto_card_gen_succ_div_of_standardInputs",
    "Conway.Hypotheses.of_standardInputs",
    "CircleMethod.StandardInputs.restrictedBinary",
]

DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:private\s+)?"
    r"(theorem|lemma|def|structure)\s+([\w.'₀-₉]+)",
    re.MULTILINE,
)
END_RE = re.compile(r"(:=\s*by\b|:=|\bwhere\b)")


def declarations(text: str) -> dict[str, str]:
    """Map declaration name -> normalised header text."""
    out: dict[str, str] = {}
    for m in DECL_RE.finditer(text):
        start = m.start()
        end_m = END_RE.search(text, m.end())
        end = end_m.start() if end_m else len(text)
        header = " ".join(text[start:end].split())
        out[m.group(2)] = header
    return out


def count_sorries(text: str) -> int:
    body = re.sub(r"/-.*?-/", "", text, flags=re.DOTALL)
    body = re.sub(r"--.*", "", body)
    return len(re.findall(r"\bsorry\b", body))


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--freeze", action="store_true")
    ap.add_argument("--axioms", action="store_true")
    args = ap.parse_args()

    current: dict[str, dict[str, str]] = {}
    total = 0
    print(f"{'file':60s} {'sorry':>5s}")
    for f in FILES:
        text = f.read_text(encoding="utf-8")
        rel = str(f.relative_to(ROOT))
        current[rel] = declarations(text)
        n = count_sorries(text)
        total += n
        print(f"{rel:60s} {n:5d}")
    print(f"{'total':60s} {total:5d}")

    if args.freeze:
        FROZEN.write_text(json.dumps(current, indent=1, ensure_ascii=False, sort_keys=True))
        print(f"froze {sum(len(v) for v in current.values())} declarations -> {FROZEN}")
        return 0

    status = 0
    if FROZEN.exists():
        frozen = json.loads(FROZEN.read_text(encoding="utf-8"))
        for rel, decls in frozen.items():
            cur = current.get(rel, {})
            for name, header in decls.items():
                if name not in cur:
                    print(f"MISSING  {rel}: {name}")
                    status = 1
                elif cur[name] != header:
                    print(f"CHANGED  {rel}: {name}")
                    print(f"  frozen : {header}")
                    print(f"  current: {cur[name]}")
                    status = 1
        if status == 0:
            print("all frozen statements intact")
    else:
        print("no frozen statements recorded (run with --freeze)")

    if args.axioms:
        src = "import ConwayGolden\n" + "".join(f"#print axioms {n}\n" for n in MAIN_RESULTS)
        tmp = ROOT / ".check_axioms.lean"
        tmp.write_text(src)
        try:
            res = subprocess.run(
                ["lake", "env", "lean", str(tmp)], cwd=ROOT, capture_output=True, text=True
            )
            print(res.stdout)
            if "sorryAx" in res.stdout:
                print("WARNING: sorryAx present")
                status = 1
        finally:
            tmp.unlink(missing_ok=True)
    return status


if __name__ == "__main__":
    sys.exit(main())
