#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo=$(git -C "$script_dir" rev-parse --show-toplevel)

: "${CHARON_BIN:?set CHARON_BIN to pinned Charon 0.1.223}"
: "${AENEAS_BIN:?set AENEAS_BIN to pinned Aeneas d860ac47-tag73-variantfn-namespace-r1}"
: "${RUSTUP_BIN:?set RUSTUP_BIN to the rustup executable used by Charon}"

source_revision=68ac0c73a1f93cc42c81ea04df52cd26d80ec79c
charon_sha=b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c
aeneas_sha=017fc5685a79d4aa3aa19f9529d57fdf167c1387c9b1fee63a254994f5ff9d5a

test "$(git -C "$repo" rev-parse "$source_revision^{commit}")" = "$source_revision"
test "$(sha256sum "$CHARON_BIN" | awk '{print $1}')" = "$charon_sha"
test "$(sha256sum "$AENEAS_BIN" | awk '{print $1}')" = "$aeneas_sha"
test "$($AENEAS_BIN -version)" = 'aeneas d860ac47-tag73-variantfn-namespace-r1'
test -x "$RUSTUP_BIN"
export PATH="${RUSTUP_BIN%/*}:$PATH"

replay_base=${TMPDIR:-/tmp}
replay_base=${replay_base%/}
replay_tmp=$(mktemp -d "$replay_base/aspis-v7-selected-terminal.XXXXXX")
cleanup() {
  if [ "${KEEP_REPLAY_TMP:-0}" = 1 ]; then
    echo "retained replay workspace: $replay_tmp" >&2
    return
  fi
  case "$replay_tmp" in
    "$replay_base"/aspis-v7-selected-terminal.*) rm -rf -- "$replay_tmp" ;;
    *) echo "refusing unsafe cleanup target: $replay_tmp" >&2 ;;
  esac
}
trap cleanup EXIT

mkdir -p "$replay_tmp/source"
git -C "$repo" archive "$source_revision" | tar -x -C "$replay_tmp/source"
mkdir -p "$replay_tmp/source/aeneas-verif/v7-tag73-selected-pool-callers-current/extraction"

features='pool-v1-kernel,pool-v1-pair-forest-packed-digest-selector-tensor-audit,pool-v1-pair-forest-binary-copy-weights-audit,pool-v1-pair-forest-endpoint-selector-cache-audit,pool-v1-pair-forest-semantic-factor-audit,pool-v1-pair-forest-pattern-window-audit,pool-v1-pair-forest-copy-tag-dot-basis-audit,pool-v1-pair-forest-copy-finish-dot-basis-audit,pool-v1-pair-forest-packed-range-audit,pool-v1-pair-forest-active-mask-basis-audit'
raw_rel='aeneas-verif/v7-tag73-selected-pool-callers-current/extraction/V7Tag73SelectedSemanticDirectRootsLoopForm19.llbc'
raw="$replay_tmp/source/$raw_rel"

export CARGO_BUILD_JOBS=1
export CARGO_TARGET_DIR="$replay_tmp/cargo-target"
(
  cd "$replay_tmp/source"
  "$CHARON_BIN" cargo --preset aeneas --mir built --sysroot default \
    --start-from crate::pool_v1::pair_forest_semantic_terminal::evaluate_pool_v1_pair_forest_private_transfer_selected_masked_terminal_compiled_tag73_v1 \
    --start-from crate::pool_v1::pair_forest_semantic_terminal::evaluate_pool_v1_pair_forest_withdrawal_selected_masked_terminal_compiled_tag73_v1 \
    --include aspis_core \
    --opaque aspis_core::field::qm31_dot3 \
    --dest-file "$raw_rel" -- \
    --package aspis-statement --lib --features "$features"
)

jq -e '.has_errors == false' "$raw" >/dev/null
jq -e '.translated.options.start_from == [
  "crate::pool_v1::pair_forest_semantic_terminal::evaluate_pool_v1_pair_forest_private_transfer_selected_masked_terminal_compiled_tag73_v1",
  "crate::pool_v1::pair_forest_semantic_terminal::evaluate_pool_v1_pair_forest_withdrawal_selected_masked_terminal_compiled_tag73_v1"
] and .translated.options.include == ["aspis_core"] and
.translated.options.opaque == ["aspis_core::field::qm31_dot3"]' "$raw" >/dev/null
echo "replayed raw LLBC SHA-256: $(sha256sum "$raw" | awk '{print $1}')"

patched="$replay_tmp/V7Tag73SelectedSemanticDirectRootsCtorRename.llbc"
python3 "$script_dir/toolchain-patches/rename_m31_constructor.py" "$raw" "$patched"
fresh="$replay_tmp/generated"
"$AENEAS_BIN" -sequential -no-progress-bar -abort-on-error -backend lean \
  -namespace V7Tag73SelectedSemanticLoopFormGenerated -dest "$fresh" \
  -subdir V7Tag73SelectedSemanticLoopForm -split-files -emit-json "$patched"

for file in Types.lean Funs.lean TypesExternal_Template.lean FunsExternal_Template.lean; do
  cmp "$fresh/V7Tag73SelectedSemanticLoopForm/$file" \
    "$script_dir/generated/V7Tag73SelectedSemanticLoopForm/$file"
done
cmp "$fresh/translation.json" "$script_dir/generated/translation.json"

echo 'V7 selected semantic terminal Charon/Aeneas replay: PASS'
