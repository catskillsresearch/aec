#!/usr/bin/env python3
"""Fail if Lean sources would lose Unicode to ``?`` in PDF listings."""

from __future__ import annotations

import re
import sys
from pathlib import Path

AEC_ROOT = Path(__file__).resolve().parent.parent
LISTINGS = AEC_ROOT / "lean-listings"
SCRIPTS = Path(__file__).resolve().parent
PREAMBLE = SCRIPTS / "tex_preamble.tex"

sys.path.insert(0, str(SCRIPTS.parent.parent / "DomainTheory" / "scripts"))
from lean_listing_sanitize import leanbox_literate_chars, sanitize_lean_for_arxiv  # noqa: E402

# Lean goal holes / metavariables (keep ``?`` in PDF when present in source).
_HOLE = re.compile(
    r"(^|[\s(,])(\?)(\s*[:'.,)\]}]|$|\s+(lam|∀|∃|_|$))"
    r"|(\?\w)"
)


def spurious_question_marks(original: str, sanitized: str) -> list[str]:
    """``?`` bytes introduced by sanitization (not present as ``?`` in source)."""
    issues: list[str] = []
    o_lines = original.splitlines()
    s_lines = sanitized.splitlines()
    if len(o_lines) != len(s_lines):
        return ["line count changed after sanitize"]
    for n, (o, s) in enumerate(zip(o_lines, s_lines, strict=True), 1):
        if "?" not in s:
            continue
        oq = [i for i, c in enumerate(o) if c == "?"]
        sq = [i for i, c in enumerate(s) if c == "?"]
        if len(sq) <= len(oq):
            continue
        for i in sq[len(oq) :]:
            snippet = s[max(0, i - 20) : i + 25]
            issues.append(f"line {n} col {i + 1}: …{snippet}…")
    return issues


def main() -> int:
    allowed = leanbox_literate_chars(preamble_path=PREAMBLE)
    missing: dict[str, int] = {}
    for path in (AEC_ROOT / "AEC").rglob("*.lean"):
        for ch in path.read_text(encoding="utf-8"):
            if ord(ch) >= 128 and ch not in allowed:
                missing[ch] = missing.get(ch, 0) + 1
    if missing:
        print("AEC Lean uses Unicode not in leanbox literate:", file=sys.stderr)
        for ch, n in sorted(missing.items(), key=lambda x: -x[1])[:30]:
            print(f"  U+{ord(ch):04X} {ch!r} ({n} uses)", file=sys.stderr)
        return 1

    bad: list[str] = []
    for path in sorted((AEC_ROOT / "AEC").rglob("*.lean")):
        orig = path.read_text(encoding="utf-8")
        san = sanitize_lean_for_arxiv(orig, preamble_path=PREAMBLE)
        for msg in spurious_question_marks(orig, san):
            bad.append(f"{path.relative_to(AEC_ROOT)}: {msg}")

    if LISTINGS.is_dir():
        for path in sorted(LISTINGS.glob("*.lean")):
            text = path.read_text(encoding="utf-8")
            for n, line in enumerate(text.splitlines(), 1):
                if "?" not in line:
                    continue
                if _HOLE.search(line):
                    continue
                if re.search(r"\?\s*=>|\?\s*by\b", line):
                    continue
                if re.search(r"[⟨([]\?\s*[:,)]", line):
                    bad.append(f"{path.name}: line {n}: suspicious ? …{line.strip()[:90]}")

    if bad:
        print("lean listing Unicode / ? check failed:", file=sys.stderr)
        for line in bad[:40]:
            print(f"  {line}", file=sys.stderr)
        if len(bad) > 40:
            print(f"  ... and {len(bad) - 40} more", file=sys.stderr)
        return 1

    n_list = len(list(LISTINGS.glob("*.lean"))) if LISTINGS.is_dir() else 0
    print(f"ok: leanbox covers AEC Unicode; {n_list} listing files checked")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
