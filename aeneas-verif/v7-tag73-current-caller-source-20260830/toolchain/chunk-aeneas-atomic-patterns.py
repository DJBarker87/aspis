#!/usr/bin/env python3
"""Factor the exact generated 15-entry atomic copy-pattern constant.

The Aeneas declaration is a nested array literal.  Elaborating all fifteen
records in one declaration retains several gigabytes of syntax and coercion
state.  This generator parses the exact emitted declaration, emits one record
per module, then reconnects them through a typed 15-entry array.  No token in
an individual record is synthesized or evaluated.
"""

from __future__ import annotations

import hashlib
import re
import sys
from pathlib import Path


if len(sys.argv) != 3:
    raise SystemExit(f"usage: {sys.argv[0]} CALLER_FUNS CALLER_MODULE")

caller_funs = Path(sys.argv[1])
caller = sys.argv[2]
caller_dir = caller_funs.parent
source = caller_funs.read_text()

marker = (
    "/-- [aspis_statement::atomic_state_only_terminal::constants::"
    "ATOMIC_COPY_PATTERNS]"
)
if source.count(marker) != 1:
    raise SystemExit(
        f"ATOMIC_COPY_PATTERNS: expected one declaration marker, found "
        f"{source.count(marker)}"
    )

declaration_start = source.index(marker)
body_separator = "  :=\n"
separator_at = source.index(body_separator, declaration_start)
body_start = separator_at + len(body_separator)
array_prefix = "  Array.make 15#usize [\n"
array_at = source.index(array_prefix, body_start)
open_bracket = array_at + array_prefix.rindex("[")


def matching_square(text: str, start: int) -> int:
    depth = 0
    for index in range(start, len(text)):
        char = text[index]
        if char == "[":
            depth += 1
        elif char == "]":
            depth -= 1
            if depth == 0:
                return index
    raise ValueError("unterminated generated array")


close_bracket = matching_square(source, open_bracket)
next_marker = source.find("\n/-- [", close_bracket)
if next_marker == -1:
    namespace_end = source.find(f"\n\nend {caller}", close_bracket)
    if namespace_end == -1:
        raise SystemExit("could not locate declaration end")
    declaration_end = namespace_end
else:
    declaration_end = next_marker + 1

alias_text = source[body_start:array_at]
alias_pattern = re.compile(
    r"^  let (a[0-9]*) := (Array\.repeat 16#usize [0-9]+#(?:u8|u32))\n",
    re.MULTILINE,
)
aliases = alias_pattern.findall(alias_text)
if len(aliases) != 22:
    raise SystemExit(f"expected 22 exact repeat aliases, found {len(aliases)}")
if alias_pattern.sub("", alias_text).strip():
    raise SystemExit("unparsed ATOMIC_COPY_PATTERNS alias prelude")

entries_text = source[open_bracket + 1 : close_bracket]


def split_entries(text: str) -> list[str]:
    entries: list[str] = []
    start = 0
    round_depth = square_depth = brace_depth = 0
    for index, char in enumerate(text):
        if char == "(":
            round_depth += 1
        elif char == ")":
            round_depth -= 1
        elif char == "[":
            square_depth += 1
        elif char == "]":
            square_depth -= 1
        elif char == "{":
            brace_depth += 1
        elif char == "}":
            brace_depth -= 1
        elif char == "," and round_depth == square_depth == brace_depth == 0:
            token = text[start:index].strip()
            if token:
                entries.append(token)
            start = index + 1
        if min(round_depth, square_depth, brace_depth) < 0:
            raise ValueError("unbalanced generated record")
    token = text[start:].strip()
    if token:
        entries.append(token)
    if round_depth or square_depth or brace_depth:
        raise ValueError("unbalanced generated record at end")
    return entries


source_entries = split_entries(entries_text)
if len(source_entries) != 15:
    raise SystemExit(
        f"expected 15 exact pattern records, found {len(source_entries)}"
    )
if any(
    not entry.startswith("{") or not entry.endswith("}")
    for entry in source_entries
):
    raise SystemExit("generated pattern record does not have exact structure syntax")

namespace = "staged_atomic_patterns"
entries = source_entries.copy()
for alias, _ in sorted(aliases, key=lambda pair: len(pair[0]), reverse=True):
    entries = [
        re.sub(rf"\b{re.escape(alias)}\b", f"{namespace}.{alias}", entry)
        for entry in entries
    ]


def write(path: Path, contents: str) -> None:
    path.write_text(contents)


prologue = (
    "\nopen Aeneas Aeneas.Std Result ControlFlow Error\n"
    "set_option linter.dupNamespace false\n"
    "set_option linter.hashCommand false\n"
    "set_option linter.unusedVariables false\n"
    "noncomputable section\n\n"
    f"namespace {caller}\n"
    f"namespace {namespace}\n\n"
)
epilogue = f"\nend {namespace}\nend {caller}\n"

support_module = "AtomicPatternSupport"
alias_definitions = "\n".join(
    f"def {name} := {expression}" for name, expression in aliases
)
write(
    caller_dir / f"{support_module}.lean",
    f"import {caller}.FunsExternal\n"
    + prologue
    + alias_definitions
    + "\n"
    + epilogue,
)

compile_order = [f"{caller}/{support_module}.lean"]
pattern_names: list[str] = []
previous_module = support_module
for index, entry in enumerate(entries):
    module = f"AtomicPatternChunk{index:02d}"
    name = f"pattern{index:02d}"
    pattern_names.append(name)
    body = "\n".join("  " + line for line in entry.splitlines())
    extra = ""
    if index == len(entries) - 1:
        joined = ",\n".join(f"    {value}" for value in pattern_names)
        extra = (
            "\n\ndef patterns :\n"
            "    Array "
            "aspis_statement.atomic_state_only_terminal.CompiledAtomicPattern "
            "15#usize :=\n"
            f"  ⟨[\n{joined}\n  ], by rfl⟩"
        )
    write(
        caller_dir / f"{module}.lean",
        f"import {caller}.{previous_module}\n"
        + prologue
        + f"def {name} :\n"
        + "    aspis_statement.atomic_state_only_terminal.CompiledAtomicPattern :=\n"
        + body
        + extra
        + "\n"
        + epilogue,
    )
    compile_order.append(f"{caller}/{module}.lean")
    previous_module = module

header = source[declaration_start:body_start]
replacement = header + f"  {namespace}.patterns\n"
rewritten = source[:declaration_start] + replacement + source[declaration_end:]
rewritten_declaration = rewritten[
    declaration_start : declaration_start + len(replacement)
]
if (
    rewritten.count(marker) != 1
    or rewritten_declaration != replacement
    or "Array.make 15#usize" in rewritten_declaration
):
    raise SystemExit("exact ATOMIC_COPY_PATTERNS replacement failed")
caller_funs.write_text(rewritten)

original_declaration = source[declaration_start:declaration_end]
manifest = [
    "format=aspis-aeneas-atomic-pattern-chunks-v1",
    f"caller={caller}",
    "entries=15",
    "aliases=22",
    "declaration_sha256="
    + hashlib.sha256(original_declaration.encode()).hexdigest(),
]
for index, (source_entry, expanded_entry) in enumerate(
    zip(source_entries, entries, strict=True)
):
    manifest.append(
        f"entry={index:02d} "
        f"source_sha256={hashlib.sha256(source_entry.encode()).hexdigest()} "
        f"expanded_sha256={hashlib.sha256(expanded_entry.encode()).hexdigest()}"
    )
write(caller_dir / "AtomicPatternCompileOrder.txt", "\n".join(compile_order) + "\n")
write(caller_dir / "AtomicPatternLastModule.txt", f"{caller}.{previous_module}\n")
write(caller_dir / "AtomicPatternChunkManifest.txt", "\n".join(manifest) + "\n")

print("chunked exact 15-entry atomic copy-pattern registry: PASS")
