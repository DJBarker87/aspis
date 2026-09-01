#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo=$(git -C "$script_dir" rev-parse --show-toplevel)
source_revision=309b9c73353366a32671901be64cf8386404fd89

test "$(git -C "$repo" rev-parse "$source_revision^{commit}")" = "$source_revision"
(cd "$script_dir" && sha256sum -c CHECKSUMS.sha256 >/dev/null)
test "$(sha256sum "$script_dir/toolchain/literal-caller-current309b-to-accepted-source.patch" | awk '{print $1}')" = \
  730cdb97de2373b07a6ded1001d25452adec481e0d474f79e6166c6519a170e5
test "$(sha256sum "$script_dir/toolchain/rename_m31_constructor.py" | awk '{print $1}')" = \
  1dfc4f7984e9c30f85a5a813cb6bfc4f70661003f88192c7b548af13eeec7197

replay_base=${TMPDIR:-/tmp}
replay_base=${replay_base%/}
replay_tmp=$(mktemp -d "$replay_base/aspis-v7-literal-source-audit.XXXXXX")
cleanup() {
  case "$replay_tmp" in
    "$replay_base"/aspis-v7-literal-source-audit.*) rm -rf -- "$replay_tmp" ;;
    *) echo "refusing unsafe cleanup target: $replay_tmp" >&2 ;;
  esac
}
trap cleanup EXIT

git -C "$repo" archive "$source_revision" | tar -x -C "$replay_tmp"
git -C "$replay_tmp" apply --check \
  "$script_dir/toolchain/literal-caller-current309b-to-accepted-source.patch"
git -C "$replay_tmp" apply \
  "$script_dir/toolchain/literal-caller-current309b-to-accepted-source.patch"

test "$(sha256sum "$replay_tmp/programs/aspis-verifier/src/v7_verifier.rs" | awk '{print $1}')" = \
  ede2541418bb566d9dada7598d49b3acb41a3b4636f47446a65f274761b1641c
test "$(sha256sum "$replay_tmp/programs/aspis-verifier/src/v7_pair_forest_dispatch.rs" | awk '{print $1}')" = \
  d5a380e7782b1cb9673794470ed3951421d1df6e19b4fff7695ea1d8522e8df3

git -C "$repo" diff --exit-code \
  6702cfcc987e29381085039d9da8715dafbbfce8 "$source_revision" -- \
  crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal_constants.rs

python3 - "$script_dir" <<'PY'
import json
import pathlib
import sys

root = pathlib.Path(sys.argv[1])
full = json.loads((root / "extraction/V7LiteralCallerCurrent309bMetadataAccountOpaqueM31CtorR1.llbc").read_text())
assert full["charon_version"] == "0.1.223"
assert full["has_errors"] is False
options = full["translated"]["options"]
assert options["start_from"] == ["crate::v7_pair_forest_dispatch::process_with_clear_return_data"]
assert options["include"] == ["aspis_core", "aspis_statement"]
assert options["opaque"] == [
    "solana_account_info::AccountInfo",
    "crate::v7_pair_forest_dispatch::exact_six_account_refs_v1",
    "crate::v7_pair_forest_dispatch::readonly_account_metadata_v1",
    "crate::v7_pair_forest_dispatch::borrow_readonly_account_data",
    "crate::v7_pair_forest_dispatch::pair_forest_master_pda_v1",
    "crate::v7_pair_forest_dispatch::pair_forest_checkpoint_pda_v1",
    "crate::v7_pair_forest_dispatch::pair_forest_lane_pda_v1",
    "crate::v7_pair_forest_dispatch::verifier_registry_pda_v1",
    "crate::v7_pair_forest_dispatch::verifier_entry_pda_v1",
    "aspis_statement::pool_v1::pair_forest_copy_terminal::pool_v1_pair_forest_copy_inactive_row_groups_compiled_v1",
    "aspis_statement::pool_v1::pair_forest_copy_terminal::pool_v1_pair_forest_copy_inactive_group_masks_compiled_v1",
    "aspis_core::v6_onefold::gamma_combine_v6_c1_slot_major",
    "aspis_core::field::qm31_dot3",
    "crate::verify::sbf_hashv",
]

helper = json.loads((root / "extraction/V7LiteralCallerReadonlyMetadataHelperCurrent309bR1.llbc").read_text())
assert helper["charon_version"] == "0.1.223"
assert helper["has_errors"] is False
assert helper["translated"]["options"]["start_from"] == [
    "crate::v7_pair_forest_dispatch::readonly_account_metadata_v1"
]
assert helper["translated"]["options"]["opaque"] == []

for relative in [
    "generated/current309b-metadata-accountopaque-m31ctor-acceptedtool-r1/translation.json",
    "generated/current309b-readonly-metadata-helper-r1/translation.json",
]:
    translated = json.loads((root / relative).read_text())
    assert translated["charon_version"] == "0.1.223"
    assert translated["aeneas_version"] == "d860ac47-tag73-looparity-r1"
    assert translated["crate"] == "aspis_verifier"
PY

grep -Fq 'def v7_pair_forest_dispatch.process_with_clear_return_data' \
  "$script_dir/generated/current309b-metadata-accountopaque-m31ctor-acceptedtool-r1/V7LiteralCallerCurrent309bMetadataAccountOpaqueAcceptedToolR1/Funs.lean"
grep -Fq 'def v7_pair_forest_dispatch.readonly_account_metadata_v1' \
  "$script_dir/generated/current309b-readonly-metadata-helper-r1/V7LiteralCallerReadonlyMetadataHelperCurrent309bR1/Funs.lean"

! grep -REn '(^|[[:space:]])(sorry|admit|native_decide)([[:space:]]|$)' \
  "$script_dir/proof" --include='*.lean'
! grep -REn '^[[:space:]]*(axiom|opaque)[[:space:]]' \
  "$script_dir/proof" \
  "$script_dir/generated/current309b-readonly-metadata-helper-r1/V7LiteralCallerReadonlyMetadataHelperCurrent309bR1/TypesExternal.lean" \
  "$script_dir/generated/current309b-metadata-accountopaque-m31ctor-acceptedtool-r1/V7LiteralCallerCurrent309bMetadataAccountOpaqueAcceptedToolR1/TypesExternal.lean"

echo 'V7 literal pair-forest caller source audit: PASS'
