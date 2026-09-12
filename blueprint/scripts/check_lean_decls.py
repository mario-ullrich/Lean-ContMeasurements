#!/usr/bin/env python3
r"""Verify that every ``\lean{...}`` tag of the blueprint names a real declaration.

``leanblueprint checkdecls`` does this with a Lake dependency on ``checkdecls``.  This
script needs none: it extracts the declaration names from the blueprint source and
writes a Lean file of ``#check`` lines, which the compiler then either accepts or
rejects.  Compiling the file is a stronger test than a name lookup, since an ``@``
application also forces the declaration's type to elaborate.

Usage::

    python blueprint/scripts/check_lean_decls.py --output check_decls.lean
    lake env lean check_decls.lean

The file is written directly rather than to standard output, so that no shell can
interpose a byte-order mark, which Lean rejects.

The Lean file imports the project's two libraries, so the project must be built first.
Exits non-zero if the blueprint source is missing or names no declaration at all, which
is how a change to the ``\lean`` syntax would show up.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

LEAN_TAG = re.compile(r"\\lean\{([^}]*)\}", re.S)


def declarations(source: Path) -> list[str]:
    """The declaration names of every ``\\lean{...}`` tag, in order of appearance."""
    text = source.read_text(encoding="utf-8")
    names: list[str] = []
    for tag in LEAN_TAG.finditer(text):
        for name in tag.group(1).split(","):
            name = name.strip().replace("\n", "")
            if name:
                names.append(name)
    return names


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=Path("blueprint/src/content.tex"))
    parser.add_argument("--imports", nargs="*", default=["BasicResults", "ContMeasurements"])
    parser.add_argument("--output", type=Path, default=Path("check_decls.lean"))
    args = parser.parse_args()

    if not args.source.is_file():
        print(f"blueprint source not found: {args.source}", file=sys.stderr)
        return 1

    names = declarations(args.source)
    if not names:
        print(f"no \\lean tag found in {args.source}", file=sys.stderr)
        return 1

    lines = [f"import {module}" for module in args.imports]
    lines.append("")
    lines.append(f"-- {len(names)} declarations named by the blueprint")
    lines += [f"#check @{name}" for name in names]
    args.output.write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")
    print(f"{len(names)} declarations written to {args.output}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
