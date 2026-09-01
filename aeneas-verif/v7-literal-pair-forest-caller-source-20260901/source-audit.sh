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
test "$(sha256sum "$script_dir/toolchain/literal-caller-exact-six-len-preflight-normalization.patch" | awk '{print $1}')" = \
  169f7309e092400f034366db40c987d25dbe8c0c0edd398b44431f5f94f302df
test "$(sha256sum "$script_dir/toolchain/aeneas-d860ac47-identity-shared-slice-reborrow.patch" | awk '{print $1}')" = \
  0e7a1de83e485a650f830c787f6dbb7beef8fa1e652b938e0907d5eb50b210fd
test "$(sha256sum "$script_dir/toolchain/aeneas-d860ac47-shared-slice-index-nested-borrow.patch" | awk '{print $1}')" = \
  543b5de2bbe9c04995364b8ac4497581582fb471416fd4c3de49d72fe42b3052
test "$(sha256sum "$script_dir/toolchain/borrow-readonly-owned-result-probe.patch" | awk '{print $1}')" = \
  861daaa9bc544bd51e783d526d978cde2afa1b06a96024f16475873d9bda6555

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
git -C "$replay_tmp" apply --check \
  "$script_dir/toolchain/literal-caller-exact-six-len-preflight-normalization.patch"
git -C "$replay_tmp" apply \
  "$script_dir/toolchain/literal-caller-exact-six-len-preflight-normalization.patch"
git -C "$replay_tmp" apply --check \
  "$script_dir/toolchain/borrow-readonly-owned-result-probe.patch"

test "$(sha256sum "$replay_tmp/programs/aspis-verifier/src/v7_verifier.rs" | awk '{print $1}')" = \
  ede2541418bb566d9dada7598d49b3acb41a3b4636f47446a65f274761b1641c
test "$(sha256sum "$replay_tmp/programs/aspis-verifier/src/v7_pair_forest_dispatch.rs" | awk '{print $1}')" = \
  39d280b72c19c8fa0e3f0b8e06bd3df26fe4b7ae0e87e94873b0a59f1737d5a5

git -C "$repo" diff --exit-code \
  6702cfcc987e29381085039d9da8715dafbbfce8 "$source_revision" -- \
  crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal_constants.rs

python3 - "$script_dir" <<'PY'
import json
import pathlib
import sys

root = pathlib.Path(sys.argv[1])
full = json.loads((root / "extraction/V7LiteralCallerCurrent309bExactSixTransparentSharedIndexR1.llbc").read_text())
assert full["charon_version"] == "0.1.223"
assert full["has_errors"] is False
options = full["translated"]["options"]
assert options["start_from"] == ["crate::v7_pair_forest_dispatch::process_with_clear_return_data"]
assert options["include"] == ["aspis_core", "aspis_statement"]
assert options["opaque"] == [
    "solana_account_info::AccountInfo",
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

six_helper = json.loads((root / "extraction/V7LiteralCallerExactSixAccountRefsLenPreflightCurrent309bR1.llbc").read_text())
assert six_helper["charon_version"] == "0.1.223"
assert six_helper["has_errors"] is False
assert six_helper["translated"]["options"]["start_from"] == [
    "crate::v7_pair_forest_dispatch::exact_six_account_refs_v1"
]
assert six_helper["translated"]["options"]["opaque"] == [
    "solana_account_info::AccountInfo"
]

borrow_probe = json.loads((root / "extraction/borrow-owned-probe-r3/V7LiteralCallerBorrowReadonlyOwnedResultProbeR3.llbc").read_text())
assert borrow_probe["charon_version"] == "0.1.223"
assert borrow_probe["has_errors"] is False
assert borrow_probe["translated"]["options"]["start_from"] == [
    "crate::v7_pair_forest_dispatch::borrow_readonly_account_data_len_probe"
]
assert borrow_probe["translated"]["options"]["opaque"] == []

for relative in [
    "generated/current309b-readonly-metadata-helper-r1/translation.json",
    "generated/full-six-transparent-shared-index-r1/translation.json",
    "generated/six-len-preflight-shared-index-r1/translation.json",
]:
    translated = json.loads((root / relative).read_text())
    assert translated["charon_version"] == "0.1.223"
    assert translated["aeneas_version"] == "d860ac47-tag73-looparity-shared-index-r1"
    assert translated["crate"] == "aspis_verifier"
PY

grep -Fq 'def v7_pair_forest_dispatch.process_with_clear_return_data' \
  "$script_dir/generated/current309b-metadata-accountopaque-m31ctor-acceptedtool-r1/V7LiteralCallerCurrent309bMetadataAccountOpaqueAcceptedToolR1/Funs.lean"
grep -Fq 'def v7_pair_forest_dispatch.readonly_account_metadata_v1' \
  "$script_dir/generated/current309b-readonly-metadata-helper-r1/V7LiteralCallerReadonlyMetadataHelperCurrent309bR1/Funs.lean"
grep -Fq 'def v7_pair_forest_dispatch.process_with_clear_return_data' \
  "$script_dir/generated/full-six-transparent-shared-index-r1/V7LiteralCallerCurrent309bExactSixTransparentSharedIndexR1/Funs.lean"
grep -Fq 'def v7_pair_forest_dispatch.exact_six_account_refs_v1' \
  "$script_dir/generated/full-six-transparent-shared-index-r1/V7LiteralCallerCurrent309bExactSixTransparentSharedIndexR1/Funs.lean"
! grep -Fq 'axiom v7_pair_forest_dispatch.exact_six_account_refs_v1' \
  "$script_dir/generated/full-six-transparent-shared-index-r1/V7LiteralCallerCurrent309bExactSixTransparentSharedIndexR1/FunsExternal_Template.lean"
grep -Fq 'def v7_pair_forest_dispatch.borrow_readonly_account_data' \
  "$script_dir/proof/V7LiteralCallerReadonlyDataExternal.lean"
grep -Fq 'def core.cell.Ref.Insts.CoreOpsDerefDeref.deref' \
  "$script_dir/proof/V7LiteralCallerReadonlyDataExternal.lean"
grep -Fq 'theorem borrow_readonly_account_data_success_is_exact_view' \
  "$script_dir/proof/V7LiteralCallerReadonlyDataBridge.lean"
grep -Fq 'def core.bool.Bool.then_some' \
  "$script_dir/proof/V7LiteralCallerCorePrimitivesExternal.lean"
grep -Fq 'def core.num.U16.count_ones' \
  "$script_dir/proof/V7LiteralCallerCorePrimitivesExternal.lean"
grep -Fq 'def core.num.U16.trailing_zeros' \
  "$script_dir/proof/V7LiteralCallerCorePrimitivesExternal.lean"
grep -Fq 'def core.num.U64.trailing_ones' \
  "$script_dir/proof/V7LiteralCallerCorePrimitivesExternal.lean"
grep -Fq 'def core.num.Usize.reverse_bits' \
  "$script_dir/proof/V7LiteralCallerCorePrimitivesExternal.lean"
grep -Fq 'def core.num.Usize.checked_shl' \
  "$script_dir/proof/V7LiteralCallerCorePrimitivesExternal.lean"
grep -Fq 'def core.num.U32.checked_shl' \
  "$script_dir/proof/V7LiteralCallerCorePrimitivesExternal.lean"
grep -Fq 'def core.num.U32.is_power_of_two' \
  "$script_dir/proof/V7LiteralCallerCorePrimitivesExternal.lean"
grep -Fq 'def core.option.Option.as_ref' \
  "$script_dir/proof/V7LiteralCallerCorePrimitivesExternal.lean"
grep -Fq 'def core.option.Option.ok_or' \
  "$script_dir/proof/V7LiteralCallerCorePrimitivesExternal.lean"
grep -Fq 'def core.slice.Slice.first' \
  "$script_dir/proof/V7LiteralCallerCorePrimitivesExternal.lean"
grep -Fq 'def core.slice.Slice.last' \
  "$script_dir/proof/V7LiteralCallerCorePrimitivesExternal.lean"
grep -Fq 'theorem u32_checked_shl_out_of_range' \
  "$script_dir/proof/V7LiteralCallerCorePrimitivesBridge.lean"

! grep -REn '(^|[[:space:]])(sorry|admit|native_decide)([[:space:]]|$)' \
  "$script_dir/proof" --include='*.lean'
! grep -REn '^[[:space:]]*(axiom|opaque)[[:space:]]' \
  "$script_dir/proof" \
  "$script_dir/generated/current309b-readonly-metadata-helper-r1/V7LiteralCallerReadonlyMetadataHelperCurrent309bR1/TypesExternal.lean" \
  "$script_dir/generated/six-len-preflight-shared-index-r1/V7LiteralCallerExactSixAccountRefsLenPreflightSharedIndexCurrent309bR1/TypesExternal.lean" \
  "$script_dir/generated/current309b-metadata-accountopaque-m31ctor-acceptedtool-r1/V7LiteralCallerCurrent309bMetadataAccountOpaqueAcceptedToolR1/TypesExternal.lean"

echo 'V7 literal pair-forest caller source audit: PASS'
