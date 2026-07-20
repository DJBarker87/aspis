#!/usr/bin/env bash
set -euo pipefail

readonly AENEAS_COMMIT="b59d5188c082f704a418c7cb4e52ad69328002d1"
readonly CHARON_COMMIT="cb50ff16b9f1066b8a97dc06da704de2da2fa41c"
readonly FIELD_SOURCE_BLOB="96e8c04efee6a8231adb2723dac9acf975993e06"

if [[ -z "${ASPIS_AENEAS_REPO:-}" || -z "${ASPIS_CHARON_REPO:-}" ]]; then
  echo "set ASPIS_AENEAS_REPO and ASPIS_CHARON_REPO to pinned official clones" >&2
  exit 2
fi

readonly script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
readonly verification_dir="$(cd "$script_dir/.." && pwd)"
readonly workspace_dir="$(cd "$verification_dir/.." && pwd)"
readonly core_crate_dir="$workspace_dir/crates/aspis-core"
readonly field_source="$workspace_dir/crates/aspis-core/src/field.rs"

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

readonly work_dir="$(mktemp -d /private/tmp/aspis-field-ops-extract.XXXXXX)"
readonly cargo_target_dir="$work_dir/cargo-target"
readonly staged_llbc_dir="$work_dir/llbc"
readonly staged_proof_dir="$work_dir/proof"
readonly staged_namespaced_dir="$work_dir/namespaced"
trap 'rm -rf "$work_dir"' EXIT
mkdir -p "$staged_llbc_dir" "$staged_proof_dir" "$staged_namespaced_dir"

extract_one() {
  local selector="$1"
  local llbc_stem="$2"
  local lean_name="$3"
  local staged_llbc="$staged_llbc_dir/$llbc_stem.llbc"

  (
    cd "$core_crate_dir"
    CARGO_TARGET_DIR="$cargo_target_dir" "$charon_bin" cargo \
      --preset=aeneas \
      --start-from="$selector" \
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
    -max-heartbeats 200000 \
    -max-recdepth 1000 \
    -abort-on-error \
    -warnings-as-errors \
    -no-progress-bar

  if ! jq -e '.translated.ordered_decls | length > 0' "$staged_llbc" >/dev/null; then
    echo "$selector produced no ordered declarations" >&2
    exit 1
  fi
  if [[ ! -s "$staged_proof_dir/$lean_name" ]]; then
    echo "$selector produced no Lean file $lean_name" >&2
    exit 1
  fi
}

extract_one \
  "aspis_core::field::_::sub" \
  "aspis_core_field_sub" \
  "AspisCoreFieldSub.lean"
extract_one \
  "aspis_core::field::_::neg" \
  "aspis_core_field_neg" \
  "AspisCoreFieldNeg.lean"
extract_one \
  "aspis_core::field::reduce_u64" \
  "aspis_core_field_reduce_u64" \
  "AspisCoreFieldReduceU64.lean"
extract_one \
  "aspis_core::field::_::mul" \
  "aspis_core_field_mul" \
  "AspisCoreFieldMul.lean"

readonly sub_llbc="$staged_llbc_dir/aspis_core_field_sub.llbc"
readonly neg_llbc="$staged_llbc_dir/aspis_core_field_neg.llbc"
readonly reduce_llbc="$staged_llbc_dir/aspis_core_field_reduce_u64.llbc"
readonly mul_llbc="$staged_llbc_dir/aspis_core_field_mul.llbc"

"$aeneas_bin" \
  -backend lean \
  "$mul_llbc" \
  -dest "$staged_namespaced_dir" \
  -namespace AspisCoreMul \
  -max-heartbeats 200000 \
  -max-recdepth 1000 \
  -abort-on-error \
  -warnings-as-errors \
  -no-progress-bar

jq -e '
  [.translated.fun_decls[].item_meta.source_text]
  | any(. == "pub fn sub(self, rhs: M31) -> M31 {\n        let s = self.0 + P - rhs.0;\n        M31(if s >= P { s - P } else { s })\n    }")
' "$sub_llbc" >/dev/null
jq -e '
  [.translated.fun_decls[].item_meta.source_text]
  | any(. == "pub fn neg(self) -> M31 {\n        if self.0 == 0 {\n            M31(0)\n        } else {\n            M31(P - self.0)\n        }\n    }")
' "$neg_llbc" >/dev/null
jq -e '
  [.translated.fun_decls[].item_meta.source_text]
  | any(startswith("fn reduce_u64(x: u64) -> u32 {"))
' "$reduce_llbc" >/dev/null
jq -e '
  [.translated.fun_decls[].item_meta.source_text]
  | any(. == "pub fn mul(self, rhs: M31) -> M31 {\n        M31(reduce_u64(self.0 as u64 * rhs.0 as u64))\n    }")
' "$mul_llbc" >/dev/null
jq -e '
  [.translated.fun_decls[].item_meta.source_text]
  | any(startswith("fn reduce_u64(x: u64) -> u32 {"))
' "$mul_llbc" >/dev/null

readonly sub_lean="$staged_proof_dir/AspisCoreFieldSub.lean"
readonly neg_lean="$staged_proof_dir/AspisCoreFieldNeg.lean"
readonly reduce_lean="$staged_proof_dir/AspisCoreFieldReduceU64.lean"
readonly mul_lean="$staged_proof_dir/AspisCoreFieldMul.lean"
readonly namespaced_mul_lean="$staged_namespaced_dir/AspisCoreFieldMul.lean"

grep -Fq "Source: 'crates/aspis-core/src/field.rs', lines 62:4-65:5" "$sub_lean"
grep -Fq "def field.M31.sub (self : field.M31) (rhs : field.M31)" "$sub_lean"
grep -Fq "Std.U32.wrapping_add self field.P" "$sub_lean"
grep -Fq "Std.U32.wrapping_sub i rhs" "$sub_lean"

grep -Fq "Source: 'crates/aspis-core/src/field.rs', lines 68:4-74:5" "$neg_lean"
grep -Fq "def field.M31.neg (self : field.M31)" "$neg_lean"
grep -Fq "Std.U32.wrapping_sub field.P self" "$neg_lean"

grep -Fq "Source: 'crates/aspis-core/src/field.rs', lines 28:0-41:1" "$reduce_lean"
grep -Fq "def field.reduce_u64 (x : Std.U64)" "$reduce_lean"
grep -Fq "Std.U64.wrapping_shr x 31#u32" "$reduce_lean"
grep -Fq "Std.U64.wrapping_shr x1 31#u32" "$reduce_lean"

grep -Fq "Source: 'crates/aspis-core/src/field.rs', lines 77:4-79:5" "$mul_lean"
grep -Fq "def field.M31.mul (self : field.M31) (rhs : field.M31)" "$mul_lean"
grep -Fq "Std.U64.wrapping_mul i i1" "$mul_lean"
grep -Fq "field.reduce_u64 i2" "$mul_lean"
grep -Fq "namespace AspisCoreMul" "$namespaced_mul_lean"
grep -Fq "def field.M31.mul (self : field.M31) (rhs : field.M31)" \
  "$namespaced_mul_lean"

mkdir -p "$verification_dir/llbc" "$verification_dir/proof"
cp "$sub_llbc" "$verification_dir/llbc/aspis_core_field_sub.llbc"
cp "$neg_llbc" "$verification_dir/llbc/aspis_core_field_neg.llbc"
cp "$reduce_llbc" "$verification_dir/llbc/aspis_core_field_reduce_u64.llbc"
cp "$mul_llbc" "$verification_dir/llbc/aspis_core_field_mul.llbc"
cp "$sub_lean" "$verification_dir/proof/AspisCoreFieldSub.lean"
cp "$neg_lean" "$verification_dir/proof/AspisCoreFieldNeg.lean"
cp "$reduce_lean" "$verification_dir/proof/AspisCoreFieldReduceU64.lean"
cp "$mul_lean" "$verification_dir/proof/AspisCoreFieldMul.lean"
cp "$namespaced_mul_lean" \
  "$verification_dir/proof/AspisCoreFieldMulNamespaced.lean"
