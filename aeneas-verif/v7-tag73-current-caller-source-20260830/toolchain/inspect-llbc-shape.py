#!/usr/bin/env python3
"""Print only the frozen LLBC container/declaration shape.

This diagnostic deliberately does not alter the input.  It exists because the
43 MiB one-line JSON exceeds jq's default nesting limit.
"""

import json
import resource
import sys


def describe(value: object) -> str:
    if isinstance(value, dict):
        return "dict:" + ",".join(value.keys())
    if isinstance(value, list):
        return f"list:{len(value)}"
    return type(value).__name__


if len(sys.argv) not in (2, 3):
    raise SystemExit(f"usage: {sys.argv[0]} LLBC [FUNCTION-SUBSTRING]")

sys.setrecursionlimit(1_000_000)
with open(sys.argv[1], "rb") as source:
    root = json.load(source)

print("root", describe(root))
translated = root["translated"]
print("translated", describe(translated))
for key, value in translated.items():
    print(key, describe(value))
if len(sys.argv) == 3:
    pattern = sys.argv[2]
    for index, declaration in enumerate(translated["fun_decls"]):
        if declaration is None:
            continue
        rendered_name = json.dumps(declaration["item_meta"]["name"], separators=(",", ":"))
        if pattern in rendered_name:
            print(
                "function",
                index,
                declaration["def_id"],
                "body=" + describe(declaration.get("body")),
                rendered_name,
            )
print("maxrss_kib", resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
