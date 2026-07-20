#!/usr/bin/env bash
set -euo pipefail

if [[ "$#" -eq 0 ]]; then
  readonly script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
  readonly verification_dir="$(cd "$script_dir/.." && pwd -P)"
  readonly llbc_file="$verification_dir/llbc/aspis_core_field_add_sub_neg.llbc"
  readonly lean_file="$verification_dir/proof/AspisCoreFieldAddSubNeg.lean"
elif [[ "$#" -eq 2 ]]; then
  readonly llbc_file="$1"
  readonly lean_file="$2"
else
  echo "usage: $0 [LLBC_FILE LEAN_FILE]" >&2
  exit 2
fi

if [[ ! -s "$llbc_file" || ! -s "$lean_file" ]]; then
  echo "missing or empty combined additive artifact" >&2
  exit 1
fi

jq -e '
  (.translated.type_decls | length) == 3 and
  (.translated.fun_decls | length) == 10 and
  (.translated.global_decls | length) == 1 and
  (.translated.ordered_decls | length) == 14
' "$llbc_file" >/dev/null

jq -e '
  [.translated.fun_decls[].item_meta.source_text] == [
    "pub fn add(self, rhs: M31) -> M31 {\n        let s = self.0 + rhs.0;\n        M31(if s >= P { s - P } else { s })\n    }",
    "pub fn add(self, rhs: CM31) -> CM31 {\n        CM31 {\n            a: self.a.add(rhs.a),\n            b: self.b.add(rhs.b),\n        }\n    }",
    "pub fn add(self, rhs: QM31) -> QM31 {\n        QM31 {\n            c0: self.c0.add(rhs.c0),\n            c1: self.c1.add(rhs.c1),\n        }\n    }",
    "pub fn sub(self, rhs: M31) -> M31 {\n        let s = self.0 + P - rhs.0;\n        M31(if s >= P { s - P } else { s })\n    }",
    "pub fn sub(self, rhs: CM31) -> CM31 {\n        CM31 {\n            a: self.a.sub(rhs.a),\n            b: self.b.sub(rhs.b),\n        }\n    }",
    "pub fn sub(self, rhs: QM31) -> QM31 {\n        QM31 {\n            c0: self.c0.sub(rhs.c0),\n            c1: self.c1.sub(rhs.c1),\n        }\n    }",
    "pub fn neg(self) -> M31 {\n        if self.0 == 0 {\n            M31(0)\n        } else {\n            M31(P - self.0)\n        }\n    }",
    "pub fn neg(self) -> CM31 {\n        CM31 {\n            a: self.a.neg(),\n            b: self.b.neg(),\n        }\n    }",
    "pub fn neg(self) -> QM31 {\n        QM31 {\n            c0: self.c0.neg(),\n            c1: self.c1.neg(),\n        }\n    }",
    "pub const P: u32 = 0x7fff_ffff;"
  ]
' "$llbc_file" >/dev/null

grep -Fq "Source: 'crates/aspis-core/src/field.rs', lines 56:4-59:5" "$lean_file"
grep -Fq "Source: 'crates/aspis-core/src/field.rs', lines 62:4-65:5" "$lean_file"
grep -Fq "Source: 'crates/aspis-core/src/field.rs', lines 68:4-74:5" "$lean_file"
grep -Fq "Source: 'crates/aspis-core/src/field.rs', lines 220:4-225:5" "$lean_file"
grep -Fq "Source: 'crates/aspis-core/src/field.rs', lines 228:4-233:5" "$lean_file"
grep -Fq "Source: 'crates/aspis-core/src/field.rs', lines 236:4-241:5" "$lean_file"
grep -Fq "Source: 'crates/aspis-core/src/field.rs', lines 700:4-705:5" "$lean_file"
grep -Fq "Source: 'crates/aspis-core/src/field.rs', lines 708:4-713:5" "$lean_file"
grep -Fq "Source: 'crates/aspis-core/src/field.rs', lines 716:4-721:5" "$lean_file"

grep -Fq "def field.M31.add" "$lean_file"
grep -Fq "def field.M31.sub" "$lean_file"
grep -Fq "def field.M31.neg" "$lean_file"
grep -Fq "def field.CM31.add" "$lean_file"
grep -Fq "def field.CM31.sub" "$lean_file"
grep -Fq "def field.CM31.neg" "$lean_file"
grep -Fq "def field.QM31.add" "$lean_file"
grep -Fq "def field.QM31.sub" "$lean_file"
grep -Fq "def field.QM31.neg" "$lean_file"
