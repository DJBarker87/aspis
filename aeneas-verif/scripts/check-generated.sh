#!/usr/bin/env bash
set -euo pipefail

if [[ "$#" -eq 0 ]]; then
  readonly script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
  readonly verification_dir="$(cd "$script_dir/.." && pwd -P)"
  readonly llbc_file="$verification_dir/llbc/aspis_core_field_add.llbc"
  readonly lean_file="$verification_dir/proof/AspisCoreFieldAdd.lean"
elif [[ "$#" -eq 2 ]]; then
  readonly llbc_file="$1"
  readonly lean_file="$2"
else
  echo "usage: $0 [LLBC_FILE LEAN_FILE]" >&2
  exit 2
fi

if [[ ! -s "$llbc_file" || ! -s "$lean_file" ]]; then
  echo "missing or empty generated artifact" >&2
  exit 1
fi

if ! jq -e '.translated.ordered_decls | length > 0' "$llbc_file" >/dev/null; then
  echo "LLBC has no declaration order; Aeneas would emit an empty namespace" >&2
  exit 1
fi
if ! jq -e '
    (.translated.type_decls | length) == 3 and
    (.translated.fun_decls | length) == 4 and
    (.translated.global_decls | length) == 1 and
    (.translated.ordered_decls | length) == 8
  ' "$llbc_file" >/dev/null; then
  echo "the narrow field-add extraction contains an unexpected declaration set" >&2
  exit 1
fi
if ! jq -e '
    [.translated.fun_decls[].item_meta.source_text]
    | any(. == "pub fn add(self, rhs: M31) -> M31 {\n        let s = self.0 + rhs.0;\n        M31(if s >= P { s - P } else { s })\n    }")
  ' "$llbc_file" >/dev/null; then
  echo "LLBC does not contain the tracked M31::add body" >&2
  exit 1
fi

grep -Fq "Source: 'crates/aspis-core/src/field.rs', lines 56:4-59:5" "$lean_file"
grep -Fq "def field.M31.add (self : field.M31) (rhs : field.M31)" "$lean_file"
grep -Fq "def field.CM31.add" "$lean_file"
grep -Fq "def field.QM31.add" "$lean_file"
grep -Fq "Std.U32.wrapping_add self rhs" "$lean_file"
grep -Fq "Std.U32.wrapping_sub s field.P" "$lean_file"
