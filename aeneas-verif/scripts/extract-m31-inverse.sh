#!/usr/bin/env bash
set -euo pipefail

readonly AENEAS_COMMIT="b59d5188c082f704a418c7cb4e52ad69328002d1"
readonly CHARON_COMMIT="cb50ff16b9f1066b8a97dc06da704de2da2fa41c"
readonly FIELD_SOURCE_BLOB="96e8c04efee6a8231adb2723dac9acf975993e06"
readonly M31_INV_SOURCE_SHA256="fc98a14fee9d100c0e12e099affba54b71c4b38e1ea14a381b7bdb79cc9b9621"
readonly RUST_TOOLCHAIN="nightly-2026-06-01"
readonly RUSTC_VERSION="rustc 1.98.0-nightly (14210df0e 2026-05-31)"
readonly CARGO_VERSION="cargo 1.98.0-nightly (fbb61be30 2026-05-26)"

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
if [[ "$(RUSTUP_TOOLCHAIN="$RUST_TOOLCHAIN" rustc --version)" != "$RUSTC_VERSION" ]]; then
  echo "missing or mismatched Rust toolchain $RUST_TOOLCHAIN" >&2
  exit 2
fi
if [[ "$(RUSTUP_TOOLCHAIN="$RUST_TOOLCHAIN" cargo --version)" != "$CARGO_VERSION" ]]; then
  echo "missing or mismatched Cargo for $RUST_TOOLCHAIN" >&2
  exit 2
fi

readonly charon_bin="$ASPIS_CHARON_REPO/bin/charon"
readonly aeneas_bin="$ASPIS_AENEAS_REPO/bin/aeneas"
if [[ ! -x "$charon_bin" || ! -x "$aeneas_bin" ]]; then
  echo "build the pinned local Charon and Aeneas clones before extracting" >&2
  exit 2
fi

readonly work_dir="$(mktemp -d /private/tmp/aspis-m31-inverse.XXXXXX)"
readonly cargo_target_dir="$work_dir/cargo-target"
readonly raw_llbc="$work_dir/aspis_core_m31_inverse_wildcard.llbc"
readonly staged_llbc_dir="$work_dir/llbc"
readonly staged_proof_dir="$work_dir/proof"
readonly staged_llbc="$staged_llbc_dir/aspis_core_m31_inverse.llbc"
readonly staged_lean="$staged_proof_dir/AspisCoreM31Inverse.lean"
lean_check_dir=""
trap 'rm -rf "$work_dir"; if [[ -n "$lean_check_dir" ]]; then rm -rf "$lean_check_dir"; fi' EXIT
mkdir -p "$staged_llbc_dir" "$staged_proof_dir"

# Pinned Charon cannot distinguish inherent methods by receiver type.  The
# documented `_::inv` selector therefore reaches M31, CM31, and QM31.  The
# complete maps are retained byte-for-byte below; only the already-topological
# ordered declaration schedule is cut immediately after the exact M31::inv
# declaration.  This prevents unrelated later roots (notably the arrow-typed
# CM31::inv_with) from entering Aeneas.
(
  cd "$core_crate_dir"
  RUSTUP_TOOLCHAIN="$RUST_TOOLCHAIN" \
    CARGO_TARGET_DIR="$cargo_target_dir" "$charon_bin" cargo \
    --preset=aeneas \
    --start-from=aspis_core::field::_::inv \
    --dest-file="$raw_llbc" \
    -- \
    --release \
    --locked \
    -p aspis-core
)

readonly inv_id="$(jq -er '
  [.translated.fun_decls[]
    | select(.item_meta.span.data.file_id == 0)
    | select(.item_meta.span.data.beg.line == 154)
    | select(.item_meta.span.data.end.line == 170)
    | select(.item_meta.source_text
        | startswith("pub fn inv(self) -> M31 {"))
    | .def_id]
  | if length == 1 then .[0]
    else error("expected exactly one production M31::inv declaration")
    end
' "$raw_llbc")"

# Authenticate the complete source text recorded by Charon, rather than only
# its signature prefix and span. `jq -j` emits the string without adding a
# newline, so the digest is over Charon's exact `source_text` bytes.
readonly inv_source_sha256="$(
  jq -j --argjson inv_id "$inv_id" '
    .translated.fun_decls[]
    | select(.def_id == $inv_id)
    | .item_meta.source_text
  ' "$raw_llbc" | shasum -a 256 | awk '{print $1}'
)"
if [[ "$inv_source_sha256" != "$M31_INV_SOURCE_SHA256" ]]; then
  echo "M31::inv source text is not the audited addition-chain body" >&2
  exit 1
fi

# The audited wildcard translation has 49 topological groups.  M31::inv is
# exactly the 35th group (zero-based index 34), is non-recursive, and occupies
# that group alone.  This also prevents accidentally slicing through an SCC.
jq -e --argjson inv_id "$inv_id" '
  (.translated.ordered_decls | length) == 49 and
  (.translated.ordered_decls[34] == {"Fun": {"NonRec": $inv_id}}) and
  ([.translated.ordered_decls | to_entries[]
      | select(.value == {"Fun": {"NonRec": $inv_id}}) | .key] == [34])
' "$raw_llbc" >/dev/null

jq --argjson inv_id "$inv_id" '
  .translated.ordered_decls |=
    (reduce .[] as $decl
      ({done: false, kept: []};
       if .done then .
       else
         .kept += [$decl]
         | if ($decl.Fun.NonRec? == $inv_id)
           then .done = true
           else .
           end
       end)
     | if .done then .kept
       else error("M31::inv missing from ordered declarations")
       end)
' "$raw_llbc" > "$staged_llbc"

# Prove mechanically that schedule selection did not rewrite any serialized
# type, function, global, trait, body, span, or source-text map. Sorting object
# keys makes this comparison independent of JSON printer key order.
jq -cS 'del(.translated.ordered_decls)' "$raw_llbc" > "$work_dir/raw-maps.json"
jq -cS 'del(.translated.ordered_decls)' "$staged_llbc" > "$work_dir/staged-maps.json"
cmp "$work_dir/raw-maps.json" "$work_dir/staged-maps.json"

# Prove separately that the staged schedule is literally the first 35 groups
# of the raw topological schedule; no group was rewritten or reordered.
jq -cS '.translated.ordered_decls[0:35]' "$raw_llbc" > "$work_dir/raw-prefix.json"
jq -cS '.translated.ordered_decls' "$staged_llbc" > "$work_dir/staged-schedule.json"
cmp "$work_dir/raw-prefix.json" "$work_dir/staged-schedule.json"

jq -e --argjson inv_id "$inv_id" '
  (.translated.type_decls | length) == 47 and
  (.translated.fun_decls | length) == 160 and
  (.translated.global_decls | length) == 6 and
  (.translated.ordered_decls | length) == 35 and
  (.translated.ordered_decls[-1].Fun.NonRec == $inv_id)
' "$staged_llbc" >/dev/null

# No later CM31/QM31 inverse root or function-pointer helper may survive in the
# Aeneas declaration schedule.
readonly forbidden_ids="$(jq -c '
  [.translated.fun_decls[]
    | select(.item_meta.span.data.file_id == 0)
    | select(
        (.item_meta.span.data.beg.line == 318) or
        (.item_meta.span.data.beg.line == 324) or
        (.item_meta.span.data.beg.line == 794) or
        (.item_meta.span.data.beg.line == 806))
    | .def_id]
' "$staged_llbc")"
jq -e --argjson forbidden "$forbidden_ids" '
  [.translated.ordered_decls[] | .Fun.NonRec? // empty]
  | all(. as $id | ($forbidden | index($id) | not))
' "$staged_llbc" >/dev/null

"$aeneas_bin" \
  -backend lean \
  "$staged_llbc" \
  -dest "$staged_proof_dir" \
  -namespace AspisCoreM31Inverse \
  -loops-to-rec \
  -max-heartbeats 200000 \
  -max-recdepth 1000 \
  -abort-on-error \
  -warnings-as-errors \
  -no-progress-bar

grep -Fq "Source: 'crates/aspis-core/src/field.rs', lines 154:4-170:5" \
  "$staged_lean"
grep -Fq "def field.M31.inv (self : field.M31)" "$staged_lean"
grep -Fq "massert (self != 0#u32)" "$staged_lean"
grep -Fq "def field.square_n_loop" "$staged_lean"
grep -Fq "partial_fixpoint" "$staged_lean"
grep -Fq "let t29 ← field.M31.mul m6 self" "$staged_lean"
grep -Fq "field.M31.mul m7 self" "$staged_lean"
if grep -Fq "def field.CM31.inv" "$staged_lean" ||
    grep -Fq "def field.QM31.inv" "$staged_lean" ||
    grep -Fq "inv_with" "$staged_lean"; then
  echo "unrelated extension-field inverse entered the generated model" >&2
  exit 1
fi

# Gate the produced model itself under the pinned Lean 4.31 Aeneas project.
# Lake requires the input to live below the package root, so use a uniquely
# named disposable subdirectory there and remove it through the EXIT trap.
lean_check_dir="$(mktemp -d "$verification_dir/proof/.m31-inverse-check.XXXXXX")"
cp "$staged_lean" "$lean_check_dir/AspisCoreM31Inverse.lean"
(
  cd "$verification_dir/proof"
  lake env lean "$lean_check_dir/AspisCoreM31Inverse.lean" \
    -o "$lean_check_dir/AspisCoreM31Inverse.olean"
)

mkdir -p "$verification_dir/llbc" "$verification_dir/proof"
cp "$staged_llbc" "$verification_dir/llbc/aspis_core_m31_inverse.llbc"
cp "$staged_lean" "$verification_dir/proof/AspisCoreM31Inverse.lean"
