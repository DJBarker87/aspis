#!/usr/bin/env python3
"""Rename the one Rust tuple-constructor function that clashes with type M31.

This is an Aeneas naming-only patch.  It changes `attr_info.rename` in Charon
metadata and does not alter a declaration body, type, operand, or control-flow
edge.
"""

import json
import pathlib
import sys


def rendered_name(item_meta: dict) -> list[str] | None:
    name = item_meta.get("name")
    if not isinstance(name, list):
        return None
    rendered: list[str] = []
    for component in name:
        if not isinstance(component, dict) or "Ident" not in component:
            return None
        ident = component["Ident"]
        if not isinstance(ident, list) or not ident:
            return None
        rendered.append(ident[0])
    return rendered


def visit(value, matches: list[dict]) -> None:
    if isinstance(value, dict):
        item_meta = value.get("item_meta")
        if (
            isinstance(item_meta, dict)
            and "signature" in value
            and "body" in value
            and rendered_name(item_meta)
            == ["aspis_core", "field", "M31"]
        ):
            matches.append(item_meta)
        for child in value.values():
            visit(child, matches)
    elif isinstance(value, list):
        for child in value:
            visit(child, matches)


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: rename_m31_constructor.py INPUT.llbc OUTPUT.llbc")
    source = pathlib.Path(sys.argv[1])
    target = pathlib.Path(sys.argv[2])
    document = json.loads(source.read_text())
    matches: list[dict] = []
    visit(document, matches)
    if len(matches) != 1:
        raise SystemExit(f"expected one aspis_core::field::M31 function; found {len(matches)}")
    attr_info = matches[0].get("attr_info")
    if not isinstance(attr_info, dict):
        raise SystemExit("matched M31 declaration has no attr_info")
    previous = attr_info.get("rename")
    if previous not in (None, "M31_ctor"):
        raise SystemExit(f"unexpected existing rename: {previous!r}")
    attr_info["rename"] = "M31_ctor"
    target.write_text(json.dumps(document, separators=(",", ":")) + "\n")


if __name__ == "__main__":
    main()
