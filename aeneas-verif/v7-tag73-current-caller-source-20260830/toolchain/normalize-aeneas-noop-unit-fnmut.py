#!/usr/bin/env python3
"""Repair two exact no-op unit-returning FnMut translations.

Aeneas emitted the closure state as the complete `call_mut` result for two
`FnMut<Phase, ()>` callbacks.  The FnMut interface requires `(Unit, state)`.
This extraction-only transformer locates the two frozen production functions,
retains their exact closure-state type, and pairs that state with `()`.
"""

from __future__ import annotations

import sys
from pathlib import Path


if len(sys.argv) != 2:
    raise SystemExit(f"usage: {sys.argv[0]} CALLER_FUNS")

path = Path(sys.argv[1])
source = path.read_text()
names = [
    (
        "aspis_statement.atomic_state_only_terminal.atomic_semantic_packed."
        "closure.Insts."
        "CoreOpsFunctionFnMutTupleStateOnlyTerminalDiagnosticPhaseTuple."
        "call_mut"
    ),
    (
        "aspis_statement.atomic_state_only_terminal."
        "atomic_state_only_composition_parts_compiled_v3.closure_4.Insts."
        "CoreOpsFunctionFnMutTupleStateOnlyTerminalDiagnosticPhaseTuple."
        "call_mut"
    ),
]

for name in names:
    marker = "def\n  " + name
    if source.count(marker) != 1:
        raise SystemExit(
            f"{name}: expected one generated declaration, found "
            f"{source.count(marker)}"
        )
    start = source.index(marker)
    end = source.find("\n/-- [", start)
    if end == -1:
        raise SystemExit(f"{name}: could not locate next declaration")
    block = source[start:end]
    body = "\n  := do\n  ok c\n"
    if block.count(body) != 1:
        raise SystemExit(
            f"{name}: expected one exact no-op body, found {block.count(body)}"
        )
    body_at = block.index(body)
    result_marker = "\n  Result\n"
    result_at = block.rfind(result_marker, 0, body_at)
    if result_at == -1:
        raise SystemExit(f"{name}: exact result annotation not found")
    result_type_start = result_at + len(result_marker)
    result_type = " ".join(block[result_type_start:body_at].split())
    if ".closure" not in result_type or "Unit" in result_type:
        raise SystemExit(f"{name}: unexpected closure-state result type")
    replacement = (
        "\n  Result (Unit ×\n"
        f"    {result_type})\n"
        "  := do\n"
        "  ok ((), c)\n"
    )
    rewritten_block = block[:result_at] + replacement + block[body_at + len(body):]
    source = source[:start] + rewritten_block + source[end:]

if source.count("\n  ok ((), c)\n") != 3:
    raise SystemExit("expected the prior transcript callback plus two repaired callbacks")

path.write_text(source)
print("normalized exact two no-op Unit FnMut callbacks: PASS")
