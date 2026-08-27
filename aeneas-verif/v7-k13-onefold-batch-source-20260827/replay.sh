#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(git -C "$script_dir" rev-parse --show-toplevel)
source_commit=b44fc616098b3018e098572885a688a5935e5b47
expected_llbc=4fb9f5fd19f8dcabc5aca5981f51ca2269f86a806e9a6e7814d1666cec28e625
expected_add_llbc=9c90509a20b5b6f601bf0143593dc020d9b9e82589f9cd3f1e46a8862bfd0fde

: "${CHARON_BIN:?set CHARON_BIN to Charon 0.1.223}"
: "${AENEAS_BIN:?set AENEAS_BIN to Aeneas b59d518}"

test -x "$CHARON_BIN"
test -x "$AENEAS_BIN"
test "$(shasum -a 256 "$CHARON_BIN" | awk '{print $1}')" = \
  d785c5f18053c4d310c7388dfdb0b59adfc9854c28b632a34a8f6301ba1c4b43
test "$(shasum -a 256 "$AENEAS_BIN" | awk '{print $1}')" = \
  fbb8dac1a9a57e635a762e04b95aeb46dbd2dab2be5ed54fa9e0b1321c1962cf

replay_base=${TMPDIR:-/tmp}
replay_base=${replay_base%/}
replay_tmp=$(mktemp -d "$replay_base/aspis-v7-k13-fold.XXXXXX")
cleanup() {
  if [ "${KEEP_REPLAY_TMP:-0}" = 1 ]; then
    echo "retained replay workspace: $replay_tmp" >&2
    return
  fi
  case "$replay_tmp" in
    "$replay_base"/aspis-v7-k13-fold.*) rm -rf -- "$replay_tmp" ;;
    *) echo "refusing unsafe cleanup target: $replay_tmp" >&2 ;;
  esac
}
trap cleanup EXIT

source_tree="$replay_tmp/source"
mkdir -p "$source_tree"
git -C "$repo_root" archive "$source_commit" | tar -x -C "$source_tree"

test "$(shasum -a 256 "$source_tree/crates/aspis-core/src/v6_onefold.rs" | awk '{print $1}')" = \
  61406f4631a01a0bb2c59847867acf878546808e79ca7b5671f2e6df6bbdbc76
test "$(shasum -a 256 "$source_tree/crates/aspis-core/src/v6_query_batch.rs" | awk '{print $1}')" = \
  3c1d1dcdb2dcc9df30bf8723d9ba10444cbcd79bcbbca6854e1443eb1921eb9d

export CARGO_BUILD_JOBS=1
export CARGO_TARGET_DIR="$replay_tmp/target"
llbc="$replay_tmp/V7K13FoldResidual.llbc"
(
  cd "$source_tree"
  "$CHARON_BIN" cargo --preset aeneas --mir built --sysroot default \
    --start-from aspis_core::v6_onefold::fold_v6_onefold_queries \
    --start-from aspis_core::v6_query_batch::v7_final256_query_batch_shifted_residual \
    --dest-file "$llbc" -- --package aspis-core --lib
)

actual_llbc=$(jq -cS '
  .translated.options.dest_file = null |
  .translated.options.dest_dir = null |
  .translated.item_names |= sort_by(.key | tojson) |
  .translated.short_names |= sort_by(.key | tojson) |
  .translated.assoc_item_names |= sort_by(.key | tojson)
' "$llbc" | shasum -a 256 | awk '{print $1}')
echo "normalized fold/residual LLBC SHA-256: $actual_llbc"
test "$actual_llbc" = "$expected_llbc"

generated="$replay_tmp/generated"
"$AENEAS_BIN" -sequential -no-progress-bar -abort-on-error -backend lean \
  -namespace V7K13FoldResidualGenerated -dest "$generated" \
  -subdir V7K13FoldResidual -split-files -emit-json "$llbc"

cmp "$generated/V7K13FoldResidual/Types.lean" \
  "$script_dir/generated/V7K13FoldResidual/Types.lean"
cmp "$generated/V7K13FoldResidual/Funs.lean" \
  "$script_dir/generated/V7K13FoldResidual/Funs.lean"

# Aeneas b59d518 cannot join the mutable scale-array loop in the literal
# function.  Apply the checked extraction-only normalization: the recurrence
# is expanded into the same fifteen prepared multiplications and one array
# literal.  No validation, weight, claim, or result-flow statement changes.
test "$(shasum -a 256 "$script_dir/source-transform/unroll-query-batch-scales.patch" | awk '{print $1}')" = \
  0f380b6be8ade9dfe78d20839a7c950b507a3d0a3ea3b95db8ab17b547235f6c
patch --silent -d "$source_tree" -p1 < \
  "$script_dir/source-transform/unroll-query-batch-scales.patch"
test "$(shasum -a 256 "$source_tree/crates/aspis-core/src/v6_query_batch.rs" | awk '{print $1}')" = \
  4d6b16b57c1151fecd08320e079c3276817d40f4e10e52edf1bfebb47e6f5d1e

add_llbc="$replay_tmp/V7K13AddBatchNormalized.llbc"
(
  cd "$source_tree"
  "$CHARON_BIN" cargo --preset aeneas --mir built --sysroot default \
    --start-from aspis_core::v6_query_batch::add_v7_final256_query_batch_shifted \
    --start-from aspis_core::v6_query_batch::v7_final256_query_batch_shifted_residual \
    --dest-file "$add_llbc" -- --package aspis-core --lib
)

actual_add_llbc=$(jq -cS '
  .translated.options.dest_file = null |
  .translated.options.dest_dir = null |
  .translated.item_names |= sort_by(.key | tojson) |
  .translated.short_names |= sort_by(.key | tojson) |
  .translated.assoc_item_names |= sort_by(.key | tojson)
' "$add_llbc" | shasum -a 256 | awk '{print $1}')
echo "normalized shifted batch LLBC SHA-256: $actual_add_llbc"
test "$actual_add_llbc" = "$expected_add_llbc"

add_generated="$replay_tmp/add-generated"
"$AENEAS_BIN" -sequential -no-progress-bar -abort-on-error -backend lean \
  -namespace V7K13AddBatchGenerated -dest "$add_generated" \
  -subdir V7K13AddBatch -split-files -emit-json "$add_llbc"

# Aeneas b59d518 emits the newer Rust `Iterator::any` default as a field in
# two iterator impl records, while its pinned Lean backend predates that trait
# field.  The direct call remains translated and is supplied transparently in
# FunsExternal; remove only the two impossible record fields.
test "$(shasum -a 256 "$script_dir/source-transform/remove-generated-iterator-any.patch" | awk '{print $1}')" = \
  b1d0b1043e5b87979d27dc0919721c7c65b3a0172a7b9d0ba3b6846c6463cd6c
patch --silent -d "$add_generated" -p0 < \
  "$script_dir/source-transform/remove-generated-iterator-any.patch"

cmp "$add_generated/V7K13AddBatch/Types.lean" \
  "$script_dir/generated/V7K13AddBatch/Types.lean"
cmp "$add_generated/V7K13AddBatch/Funs.lean" \
  "$script_dir/generated/V7K13AddBatch/Funs.lean"

if rg -n '\b(sorry|admit|native_decide)\b' \
    "$script_dir/generated" "$script_dir/proof" --glob '*.lean'; then
  echo 'forbidden Lean placeholder found' >&2
  exit 1
fi

echo 'V7 K1.3 literal fold/residual and normalized batch extraction replay: PASS'
