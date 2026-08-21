#!/usr/bin/env python3
"""Check the exact, narrow normalization of the Aeneas tail output."""

from __future__ import annotations

import argparse
import difflib
from pathlib import Path


IMPORT = "import Aeneas\n"
IMPORTS_432 = (
    "import Aeneas.Std\n"
    "import Aeneas.Tactic.RustAttributes\n"
    "import Aeneas.Data.Discriminant\n"
)


def replace_once(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"{label}: expected exactly one occurrence, found {count}")
    return text.replace(old, new, 1)


def compare(expected: str, actual: str, label: str) -> None:
    if expected == actual:
        return
    diff = "".join(
        difflib.unified_diff(
            expected.splitlines(keepends=True),
            actual.splitlines(keepends=True),
            fromfile=f"expected-{label}",
            tofile=f"checked-{label}",
            n=4,
        )
    )
    raise SystemExit(f"unexpected {label} normalization:\n{diff[:12000]}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("bundle", type=Path)
    args = parser.parse_args()

    raw = args.bundle / "generated/raw/V5TranscriptTailUnchangedGenerated"
    checked = args.bundle / "generated/V5TranscriptTailUnchangedGenerated"

    raw_types = (raw / "Types.lean").read_text(encoding="utf-8")
    expected_types = replace_once(raw_types, IMPORT, IMPORTS_432, "Types imports")
    compare(
        expected_types,
        (checked / "Types.lean").read_text(encoding="utf-8"),
        "Types.lean",
    )

    raw_funs = (raw / "Funs.lean").read_text(encoding="utf-8")
    expected_funs = replace_once(raw_funs, IMPORT, IMPORTS_432, "Funs imports")
    expected_funs = replace_once(
        expected_funs,
        "  next := core.slice.iter.IteratorIterMut.next\n",
        "  next := core.slice.iter.IteratorIterMut.next_without_writeback\n",
        "mutable iterator trait adapter",
    )
    expected_funs = replace_once(
        expected_funs,
        """    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
      aspis_core.field.QM31) iter
""",
        "    core.iter.adapters.enumerate.IteratorEnumerateMut.next iter\n",
        "mutable enumerate next",
    )
    expected_funs = replace_once(
        expected_funs,
        """        core.iter.traits.iterator.Iterator.enumerate.trait_default
          (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
          aspis_core.field.QM31) im
""",
        "        core.iter.adapters.enumerate.IteratorEnumerateMut.enumerate im\n",
        "mutable enumerate construction",
    )
    compare(
        expected_funs,
        (checked / "Funs.lean").read_text(encoding="utf-8"),
        "Funs.lean",
    )

    external = (checked / "FunsExternal.lean").read_text(encoding="utf-8")
    required = (
        "def core.slice.iter.IteratorIterMut.next_without_writeback",
        "def core.iter.adapters.enumerate.IteratorEnumerateMut.next",
        "def core.iter.adapters.enumerate.IteratorEnumerateMut.enumerate",
    )
    for marker in required:
        count = external.count(marker)
        if count != 1:
            raise SystemExit(f"FunsExternal.lean: {marker!r} occurs {count} times")

    print("checked raw Aeneas tail output and the three exact iterator substitutions")


if __name__ == "__main__":
    main()
