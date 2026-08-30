#!/usr/bin/env python3
"""Create a diagnostic LLBC with only one function-index interval executable.

All declaration ids, types, globals, traits, dependency groups, source spans,
and already-opaque functions are preserved. Structured bodies outside
`[start, end)` are set to the same JSON `"Opaque"` representation Charon uses
for an opaque body.
This is a reducer for translator failures, never an accepted source artifact.
The input must have been emitted with Charon's
`--no-dedup-serialized-ast`; removing a body from the ordinary hash-consed
encoding can remove the defining occurrence of a value used by later
`Deduplicated` references.
"""

import hashlib
import json
import resource
import sys
from pathlib import Path


def identifiers(value: object) -> list[str]:
    found: list[str] = []
    if isinstance(value, dict):
        ident = value.get("Ident")
        if isinstance(ident, list) and ident and isinstance(ident[0], str):
            found.append(ident[0])
        for child in value.values():
            found.extend(identifiers(child))
    elif isinstance(value, list):
        for child in value:
            found.extend(identifiers(child))
    return found


if len(sys.argv) not in (5, 6):
    raise SystemExit(
        f"usage: {sys.argv[0]} INPUT OUTPUT START END [EXCLUDE_INDEX,...]"
    )

input_path = Path(sys.argv[1])
output_path = Path(sys.argv[2])
start = int(sys.argv[3])
end = int(sys.argv[4])
excluded = (
    {int(value) for value in sys.argv[5].split(",") if value}
    if len(sys.argv) == 6
    else set()
)
if start < 0 or end <= start:
    raise SystemExit("require 0 <= START < END")

sys.setrecursionlimit(1_000_000)
input_bytes = input_path.read_bytes()
root = json.loads(input_bytes)


def contains_deduplicated(value: object) -> bool:
    if isinstance(value, dict):
        if "Deduplicated" in value:
            return True
        return any(contains_deduplicated(child) for child in value.values())
    if isinstance(value, list):
        return any(contains_deduplicated(child) for child in value)
    return False


if contains_deduplicated(root):
    raise SystemExit(
        "input contains hash-consed Deduplicated references; rerun Charon "
        "with --no-dedup-serialized-ast before partitioning"
    )
functions = root["translated"]["fun_decls"]
if end > len(functions):
    raise SystemExit(f"END {end} exceeds function count {len(functions)}")

selected: list[str] = []
selected_bodies = 0
for index, declaration in enumerate(functions):
    if declaration is None:
        continue
    name = "::".join(identifiers(declaration["item_meta"]["name"]))
    if start <= index < end and index not in excluded:
        if isinstance(declaration.get("body"), dict):
            selected_bodies += 1
            selected.append(f"{index} {declaration['def_id']} {name}")
    else:
        if isinstance(declaration.get("body"), dict):
            declaration["body"] = "Opaque"

output_bytes = json.dumps(root, separators=(",", ":"), ensure_ascii=False).encode()
output_path.write_bytes(output_bytes)
print(f"input_sha256={hashlib.sha256(input_bytes).hexdigest()}")
print(f"output_sha256={hashlib.sha256(output_bytes).hexdigest()}")
print(f"interval={start}:{end}")
print("excluded=" + ",".join(str(index) for index in sorted(excluded)))
print(f"selected_bodies={selected_bodies}")
for line in selected:
    print(f"selected={line}")
print(f"maxrss_kib={resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}")
