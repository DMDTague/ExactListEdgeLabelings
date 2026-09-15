#!/usr/bin/env python3
"""Check source hygiene, proof placeholders, imports, and declaration inventory.

This is a source check, not a substitute for the Lean compiler or axiom audit.
Nested block comments, line comments, and strings are blanked before checking
proof tokens. Line numbers are preserved for reproducible diagnostics.
"""

from __future__ import annotations

import argparse
import collections
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TOKEN = re.compile(r"\b(?:sorry|admit|axiom|unsafe|opaque|native_decide|sorryAx)\b")
DECL = re.compile(
    r"^(?:@\[[^\n]*\]\s*)?"
    r"(?:(?:private|protected|noncomputable)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|inductive|instance|example)\b"
    r"[ \t]*([^\s:{(\n]*)",
    re.MULTILINE,
)
BARE_PROP_TARGET = re.compile(
    r"^[ \t]*(?:@\[[^\n]*\][ \t]*)?"
    r"(?:(?:private|protected|noncomputable)[ \t]+)*"
    r"(?:def|abbrev)[ \t]+([\w']+)[ \t]*:[ \t]*Prop[ \t]*:=",
    re.MULTILINE,
)


def strip_comments_and_strings(text: str) -> str:
    chars = list(text)
    depth = 0
    i = 0
    while i < len(text):
        start = i
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif text.startswith("--", i):
            newline = text.find("\n", i)
            i = len(text) if newline < 0 else newline
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        else:
            i += 1
            continue
        for j in range(start, min(i, len(chars))):
            if chars[j] != "\n":
                chars[j] = " "
    if depth:
        raise ValueError("unclosed block comment")
    return "".join(chars)


def source_files() -> list[Path]:
    return sorted([*ROOT.glob("*.lean"), *(ROOT / "BachThesisLean").rglob("*.lean")])


def inventory() -> list[dict]:
    rows = []
    for path in source_files():
        text = path.read_text(encoding="utf-8")
        clean = strip_comments_and_strings(text)
        for match in DECL.finditer(clean):
            row = {
                "file": str(path.relative_to(ROOT)),
                "line": clean[: match.start()].count("\n") + 1,
                "kind": match[1],
                "name": match[2],
            }
            if row["kind"] in {"theorem", "lemma"}:
                end = clean.find(":=", match.end())
                row["statement"] = text[match.start() : end].strip()
            rows.append(row)
    return rows


def check() -> list[str]:
    errors = []
    gaps_path = ROOT / "KNOWN_GAPS.md"
    gaps_text = gaps_path.read_text(encoding="utf-8") if gaps_path.exists() else ""
    for path in source_files():
        text = path.read_text(encoding="utf-8")
        relative = path.relative_to(ROOT)
        if not text.endswith("\n"):
            errors.append(f"{relative}: missing final newline")
        for number, line in enumerate(text.splitlines(), 1):
            if line.rstrip() != line or "\t" in line:
                errors.append(f"{relative}:{number}: trailing whitespace or tab")
        clean = strip_comments_and_strings(text)
        for match in TOKEN.finditer(clean):
            number = clean[: match.start()].count("\n") + 1
            errors.append(f"{relative}:{number}: forbidden proof token {match[0]}")
        for match in BARE_PROP_TARGET.finditer(clean):
            number = clean[: match.start()].count("\n") + 1
            name = match[1]
            if f"`{name}`" not in gaps_text:
                errors.append(
                    f"{relative}:{number}: bare proposition target {name}; "
                    "record it in KNOWN_GAPS.md"
                )

    visited = set()

    def visit(module: str) -> None:
        if module in visited:
            return
        visited.add(module)
        path = ROOT / (module.replace(".", "/") + ".lean")
        if not path.exists():
            errors.append(f"missing local import: {module}")
            return
        text = strip_comments_and_strings(path.read_text(encoding="utf-8"))
        for imported in re.findall(r"^import\s+(BachThesisLean[\w.]*)", text, re.MULTILINE):
            visit(imported)

    visit("BachThesisLean")
    for path in (ROOT / "BachThesisLean").rglob("*.lean"):
        module = ".".join(path.relative_to(ROOT).with_suffix("").parts)
        if module not in visited:
            errors.append(f"library file not imported by default target: {path.relative_to(ROOT)}")
    return errors


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inventory", type=Path, help="write declaration inventory as JSON")
    args = parser.parse_args()
    rows = inventory()
    if args.inventory:
        args.inventory.parent.mkdir(parents=True, exist_ok=True)
        args.inventory.write_text(json.dumps(rows, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    for kind, count in sorted(collections.Counter(row["kind"] for row in rows).items()):
        print(f"{kind}: {count}")
    errors = check()
    if errors:
        print("\n".join(errors))
        raise SystemExit(1)
    print("Source hygiene, proof-token, proposition-target, and import-coverage checks passed.")


if __name__ == "__main__":
    main()
