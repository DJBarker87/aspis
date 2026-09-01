#!/usr/bin/env python3
"""Qualify `Aeneas.Std.lift` after a translated Rust `lift` function.

The production statement module defines a Rust helper also named `lift`.
Aeneas emits subsequent uses of its monadic primitive as the unqualified name
`lift`, so Lean resolves them to the translated field helper.  Generated calls
to Rust functions are fully qualified; consequently every unqualified
`lift (` after this exact declaration is the Aeneas primitive.  This frozen
transform validates the exact count before changing only that suffix.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path


if len(sys.argv) != 2:
    raise SystemExit(f"usage: {sys.argv[0]} CALLER_FUNS")

path = Path(sys.argv[1])
source = path.read_text()
marker = (
    "def aspis_statement.atomic_state_only_terminal.lift\n"
    "  (value : aspis_core.field.M31) : Result aspis_core.field.QM31 := do"
)
if source.count(marker) != 1:
    raise SystemExit(
        f"translated production lift: expected one marker, found "
        f"{source.count(marker)}"
    )

start = source.index(marker)
prefix = source[:start]
suffix = source[start:]
pattern = re.compile(r"(?<![A-Za-z0-9_.])lift \(")
matches = list(pattern.finditer(suffix))
if len(matches) != 80:
    raise SystemExit(
        f"post-shadow Aeneas.Std.lift calls: expected 80, found {len(matches)}"
    )
if "Aeneas.Std.lift (" in suffix:
    raise SystemExit("post-shadow suffix was already normalized")

rewritten_suffix = pattern.sub("Aeneas.Std.lift (", suffix)
if pattern.search(rewritten_suffix):
    raise SystemExit("unqualified post-shadow lift remains")
if rewritten_suffix.count("Aeneas.Std.lift (") != 80:
    raise SystemExit("qualified post-shadow lift count changed unexpectedly")

path.write_text(prefix + rewritten_suffix)
print("qualified exact 80 post-shadow Aeneas.Std.lift calls: PASS")
