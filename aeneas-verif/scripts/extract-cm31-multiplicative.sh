#!/usr/bin/env bash
set -euo pipefail

readonly AENEAS_COMMIT="b59d5188c082f704a418c7cb4e52ad69328002d1"
readonly CHARON_COMMIT="cb50ff16b9f1066b8a97dc06da704de2da2fa41c"
readonly FIELD_SOURCE_BLOB="96e8c04efee6a8231adb2723dac9acf975993e06"

if [[ -z "${ASPIS_AENEAS_REPO:-}" || -z "${ASPIS_CHARON_REPO:-}" ]]; then
  echo "set ASPIS_AENEAS_REPO and ASPIS_CHARON_REPO to pinned official clones" >&2
  exit 2
fi

readonly script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly verification_dir="$(cd "$script_dir/.." && pwd -P)"
readonly workspace_dir="$(cd "$verification_dir/.." && pwd -P)"
readonly core_crate_dir="$workspace_dir/crates/aspis-core"
readonly field_source="$core_crate_dir/src/field.rs"

if [[ "$(git -C "$ASPIS_AENEAS_REPO" rev-parse HEAD)" != "$AENEAS_COMMIT" ]]; then
  echo "Aeneas is not at $AENEAS_COMMIT" >&2
  exit 2
fi
if [[ "$(git -C "$ASPIS_CHARON_REPO" rev-parse HEAD)" != "$CHARON_COMMIT" ]]; then
  echo "Charon is not at $CHARON_COMMIT" >&2
  exit 2
fi
if ! grep -Fq "$CHARON_COMMIT" "$ASPIS_AENEAS_REPO/charon-pin"; then
  echo "the pinned Aeneas checkout does not name the pinned Charon companion" >&2
  exit 2
fi
if [[ "$(git hash-object "$field_source")" != "$FIELD_SOURCE_BLOB" ]]; then
  echo "field.rs is not the audited source blob $FIELD_SOURCE_BLOB" >&2
  exit 2
fi

readonly charon_bin="$ASPIS_CHARON_REPO/bin/charon"
readonly aeneas_bin="$ASPIS_AENEAS_REPO/bin/aeneas"
if [[ ! -x "$charon_bin" || ! -x "$aeneas_bin" ]]; then
  echo "build the pinned local Charon and Aeneas clones before extracting" >&2
  exit 2
fi

readonly work_dir="$(mktemp -d /private/tmp/aspis-cm31-multiplicative.XXXXXX)"
readonly cargo_target_dir="$work_dir/cargo-target"
readonly staged_llbc="$work_dir/aspis_core_cm31_multiplicative.llbc"
readonly staged_proof_dir="$work_dir/proof"
trap 'rm -rf "$work_dir"' EXIT
mkdir -p "$staged_proof_dir"

(
  cd "$core_crate_dir"
  CARGO_TARGET_DIR="$cargo_target_dir" "$charon_bin" cargo \
    --preset=aeneas \
    --start-from=aspis_core::field::_::mul \
    --start-from=aspis_core::field::_::square \
    --start-from=aspis_core::field::_::mul_m31 \
    --dest-file="$staged_llbc" \
    -- \
    --release \
    --locked \
    -p aspis-core
)

"$aeneas_bin" \
  -backend lean \
  "$staged_llbc" \
  -dest "$staged_proof_dir" \
  -namespace AspisCoreCM31Multiplicative \
  -max-heartbeats 200000 \
  -max-recdepth 1000 \
  -abort-on-error \
  -warnings-as-errors \
  -no-progress-bar

readonly staged_lean="$staged_proof_dir/AspisCoreCm31Multiplicative.lean"

jq -e '
    (.translated.type_decls | length) == 8 and
    (.translated.fun_decls | length) == 21 and
    (.translated.global_decls | length) == 1 and
    (.translated.ordered_decls | length) == 35
  ' "$staged_llbc" >/dev/null

jq -e '
  [.translated.fun_decls[].item_meta.source_text]
  | any(. == "pub fn mul(self, rhs: CM31) -> CM31 {\n        let m0 = self.a.mul(rhs.a);\n        let m1 = self.b.mul(rhs.b);\n        let m2 = self.a.add(self.b).mul(rhs.a.add(rhs.b));\n        CM31 {\n            a: m0.sub(m1),\n            b: m2.sub(m0).sub(m1),\n        }\n    }")
  ' "$staged_llbc" >/dev/null
jq -e '
  [.translated.fun_decls[].item_meta.source_text]
  | any(. == "pub fn square(self) -> CM31 {\n        CM31 {\n            a: self.a.add(self.b).mul(self.a.sub(self.b)),\n            b: self.a.mul(self.b).double(),\n        }\n    }")
  ' "$staged_llbc" >/dev/null
jq -e '
  [.translated.fun_decls[].item_meta.source_text]
  | any(. == "pub fn mul_m31(self, rhs: M31) -> CM31 {\n        CM31 {\n            a: self.a.mul(rhs),\n            b: self.b.mul(rhs),\n        }\n    }")
  ' "$staged_llbc" >/dev/null

grep -Fq "namespace AspisCoreCM31Multiplicative" "$staged_lean"
grep -Fq "Source: 'crates/aspis-core/src/field.rs', lines 245:4-253:5" "$staged_lean"
grep -Fq "Source: 'crates/aspis-core/src/field.rs', lines 258:4-263:5" "$staged_lean"
grep -Fq "Source: 'crates/aspis-core/src/field.rs', lines 266:4-271:5" "$staged_lean"
grep -Fq "def field.CM31.mul" "$staged_lean"
grep -Fq "def field.CM31.square" "$staged_lean"
grep -Fq "def field.CM31.mul_m31" "$staged_lean"

mkdir -p "$verification_dir/llbc" "$verification_dir/proof"
cp "$staged_llbc" \
  "$verification_dir/llbc/aspis_core_cm31_multiplicative.llbc"
cp "$staged_lean" \
  "$verification_dir/proof/AspisCoreCm31Multiplicative.lean"
