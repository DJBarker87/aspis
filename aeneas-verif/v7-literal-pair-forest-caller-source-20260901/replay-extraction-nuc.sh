#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo=$(git -C "$script_dir" rev-parse --show-toplevel)

: "${CHARON_BIN:?set CHARON_BIN to pinned Charon 0.1.223}"
: "${AENEAS_BIN:?set AENEAS_BIN to pinned Aeneas d860ac47-tag73-looparity-r1}"
: "${RUSTUP_BIN:?set RUSTUP_BIN to rustup used by Charon}"

source_revision=309b9c73353366a32671901be64cf8386404fd89
test "$(git -C "$repo" rev-parse "$source_revision^{commit}")" = "$source_revision"
test "$(sha256sum "$CHARON_BIN" | awk '{print $1}')" = \
  b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c
test "$(sha256sum "$AENEAS_BIN" | awk '{print $1}')" = \
  7a6633fbb01fad506336c1a1ef54382924d261fe0bf4ac1a8c8f119e90462a4a
test "$("$CHARON_BIN" version)" = 0.1.223
test "$("$AENEAS_BIN" -version)" = 'aeneas d860ac47-tag73-looparity-r1'
test -x "$RUSTUP_BIN"
export PATH="${RUSTUP_BIN%/*}:$PATH"

replay_base=${TMPDIR:-/tmp}
replay_base=${replay_base%/}
replay_tmp=$(mktemp -d "$replay_base/aspis-v7-literal-caller.XXXXXX")
cleanup() {
  if [ "${KEEP_REPLAY_TMP:-0}" = 1 ]; then
    echo "retained replay workspace: $replay_tmp" >&2
    return
  fi
  case "$replay_tmp" in
    "$replay_base"/aspis-v7-literal-caller.*) rm -rf -- "$replay_tmp" ;;
    *) echo "refusing unsafe cleanup target: $replay_tmp" >&2 ;;
  esac
}
trap cleanup EXIT

mkdir -p "$replay_tmp/source"
git -C "$repo" archive "$source_revision" | tar -x -C "$replay_tmp/source"
git -C "$replay_tmp/source" apply \
  "$script_dir/toolchain/literal-caller-current309b-to-accepted-source.patch"

export CARGO_BUILD_JOBS=1
export CARGO_TARGET_DIR="$replay_tmp/cargo-target"
raw="$replay_tmp/full-raw.llbc"
patched="$replay_tmp/full-m31ctor.llbc"
helper="$replay_tmp/metadata-helper.llbc"

(
  cd "$replay_tmp/source"
  "$CHARON_BIN" cargo --preset aeneas --mir built --sysroot default \
    --start-from crate::v7_pair_forest_dispatch::process_with_clear_return_data \
    --include aspis_core --include aspis_statement \
    --opaque solana_account_info::AccountInfo \
    --opaque crate::v7_pair_forest_dispatch::exact_six_account_refs_v1 \
    --opaque crate::v7_pair_forest_dispatch::readonly_account_metadata_v1 \
    --opaque crate::v7_pair_forest_dispatch::borrow_readonly_account_data \
    --opaque crate::v7_pair_forest_dispatch::pair_forest_master_pda_v1 \
    --opaque crate::v7_pair_forest_dispatch::pair_forest_checkpoint_pda_v1 \
    --opaque crate::v7_pair_forest_dispatch::pair_forest_lane_pda_v1 \
    --opaque crate::v7_pair_forest_dispatch::verifier_registry_pda_v1 \
    --opaque crate::v7_pair_forest_dispatch::verifier_entry_pda_v1 \
    --opaque aspis_statement::pool_v1::pair_forest_copy_terminal::pool_v1_pair_forest_copy_inactive_row_groups_compiled_v1 \
    --opaque aspis_statement::pool_v1::pair_forest_copy_terminal::pool_v1_pair_forest_copy_inactive_group_masks_compiled_v1 \
    --opaque aspis_core::v6_onefold::gamma_combine_v6_c1_slot_major \
    --opaque aspis_core::field::qm31_dot3 \
    --opaque crate::verify::sbf_hashv \
    --dest-file "$raw" -- \
    --package aspis-verifier --lib --no-default-features \
    --features v7-pair-forest-one-tx-candidate

  "$CHARON_BIN" cargo --preset aeneas --mir built --sysroot default \
    --start-from crate::v7_pair_forest_dispatch::readonly_account_metadata_v1 \
    --dest-file "$helper" -- \
    --package aspis-verifier --lib --no-default-features \
    --features v7-pair-forest-one-tx-candidate
)

python3 - "$raw" "$helper" <<'PY'
import json
import sys
for path in sys.argv[1:]:
    with open(path) as stream:
        value = json.load(stream)
    assert value["charon_version"] == "0.1.223"
    assert value["has_errors"] is False
PY

python3 "$script_dir/toolchain/rename_m31_constructor.py" "$raw" "$patched"

full_out="$replay_tmp/full-generated"
helper_out="$replay_tmp/helper-generated"
"$AENEAS_BIN" -sequential -no-progress-bar -abort-on-error -backend lean \
  -namespace V7LiteralCallerCurrent309bMetadataAccountOpaqueAcceptedToolR1 \
  -dest "$full_out" \
  -subdir V7LiteralCallerCurrent309bMetadataAccountOpaqueAcceptedToolR1 \
  -split-files -emit-json "$patched"
"$AENEAS_BIN" -sequential -no-progress-bar -abort-on-error -backend lean \
  -namespace V7LiteralCallerReadonlyMetadataHelperCurrent309bR1 \
  -dest "$helper_out" \
  -subdir V7LiteralCallerReadonlyMetadataHelperCurrent309bR1 \
  -split-files -emit-json "$helper"

for file in Types.lean Funs.lean TypesExternal_Template.lean FunsExternal_Template.lean; do
  cmp "$full_out/V7LiteralCallerCurrent309bMetadataAccountOpaqueAcceptedToolR1/$file" \
    "$script_dir/generated/current309b-metadata-accountopaque-m31ctor-acceptedtool-r1/V7LiteralCallerCurrent309bMetadataAccountOpaqueAcceptedToolR1/$file"
done
cmp "$full_out/translation.json" \
  "$script_dir/generated/current309b-metadata-accountopaque-m31ctor-acceptedtool-r1/translation.json"

for file in Types.lean Funs.lean TypesExternal_Template.lean; do
  cmp "$helper_out/V7LiteralCallerReadonlyMetadataHelperCurrent309bR1/$file" \
    "$script_dir/generated/current309b-readonly-metadata-helper-r1/V7LiteralCallerReadonlyMetadataHelperCurrent309bR1/$file"
done
cmp "$helper_out/translation.json" \
  "$script_dir/generated/current309b-readonly-metadata-helper-r1/translation.json"

echo 'V7 literal pair-forest caller Charon/Aeneas replay: PASS'
