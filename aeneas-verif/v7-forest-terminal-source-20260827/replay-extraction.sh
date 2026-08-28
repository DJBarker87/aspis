#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(CDPATH= cd -- "$script_dir/../.." && pwd)
: "${CHARON_BIN:?set CHARON_BIN to pinned Charon 0.1.223}"
: "${AENEAS_BIN:?set AENEAS_BIN to pinned patched Aeneas d860}"

expected_source_commit=2ff50df4b1dc58eb33ccb2f34c93e838cb72522c
git -C "$repo_root" cat-file -e "$expected_source_commit^{commit}"
if ! git -C "$repo_root" diff --quiet "$expected_source_commit" -- \
    crates/aspis-statement crates/aspis-core Cargo.toml Cargo.lock; then
  echo "extracted Rust differs from pinned source revision $expected_source_commit" >&2
  exit 1
fi

replay_tmp=$(mktemp -d "${TMPDIR:-/tmp}/aspis-v7-forest-extraction.XXXXXX")
cleanup() {
  case "$replay_tmp" in
    "${TMPDIR:-/tmp}"/aspis-v7-forest-extraction.*) rm -rf -- "$replay_tmp" ;;
    *) echo "refusing unsafe cleanup target: $replay_tmp" >&2 ;;
  esac
}
trap cleanup EXIT

export CARGO_BUILD_JOBS=1
export CARGO_TARGET_DIR="$replay_tmp/target"

cd "$repo_root"
"$CHARON_BIN" cargo --preset aeneas \
  --start-from 'aspis_statement::pool_v1::pair_forest_terminal::decode_pool_v1_pair_forest_terminal_statement_v1' \
  --start-from 'aspis_statement::pool_v1::pair_forest_terminal::decode_pool_v1_pair_forest_terminal_result_v1' \
  --start-from 'aspis_statement::pool_v1::pair_forest_terminal::host::verify_pool_v1_pair_forest_terminal_inactive_v1' \
  --opaque 'aspis_statement::atomic_statement::decode_digest_canonical' \
  --opaque 'aspis_statement::atomic_statement::encode_digest_canonical' \
  --opaque 'aspis_statement::pool_v1::pair_tree_profile::decode_pool_v1_pair_late_public_statement_v1' \
  --opaque 'aspis_statement::pool_v1::pair_tree_profile::encode_pool_v1_pair_late_public_statement_v1' \
  --opaque 'aspis_statement::pool_v1::pair_terminal::decode_pool_v1_pair_verified_afterstate_v1' \
  --opaque 'aspis_statement::pool_v1::pair_terminal::encode_pool_v1_pair_verified_afterstate_v1' \
  --opaque 'aspis_statement::pool_v1::payment_relation::decode_pool_v1_private_transfer_public_v1' \
  --opaque 'aspis_statement::pool_v1::payment_relation::decode_pool_v1_withdrawal_public_v1' \
  --opaque 'aspis_statement::pool_v1::payment_relation::encode_pool_v1_private_transfer_public_v1' \
  --opaque 'aspis_statement::pool_v1::payment_relation::encode_pool_v1_withdrawal_public_v1' \
  --opaque 'aspis_statement::pool_v1::pair_forest_accounts::encode_pool_v1_pair_forest_master_v1' \
  --opaque 'aspis_statement::pool_v1::pair_forest_accounts::encode_pool_v1_pair_forest_checkpoint_v1' \
  --opaque 'aspis_statement::pool_v1::pair_forest_accounts::encode_pool_v1_pair_forest_lane_state_v1' \
  --opaque 'aspis_statement::pool_v1::pair_forest_accounts::pool_v1_pair_forest_output_lane_v1' \
  --opaque 'aspis_statement::pool_v1::pair_forest_constraint_residuals::evaluate_pool_v1_pair_forest_private_transfer_constraint_residuals_v1' \
  --opaque 'aspis_statement::pool_v1::pair_forest_constraint_residuals::evaluate_pool_v1_pair_forest_withdrawal_constraint_residuals_v1' \
  --opaque 'aspis_statement::pool_v1::pair_forest_constraint_residuals::PoolV1PairForestConstraintResidualsV1::residual_count' \
  --opaque 'aspis_statement::pool_v1::pair_forest_constraint_residuals::PoolV1PairForestConstraintResidualsV1::all_zero' \
  --opaque 'aspis_statement::pool_v1::pair_forest_terminal::host::pair_empty_roots' \
  --dest-file "$replay_tmp/V7ForestTerminal.llbc" -- -p aspis-statement

test "$(jq -r '.has_errors' "$replay_tmp/V7ForestTerminal.llbc")" = false
normalized_hash=$(
  jq -cS '
    .translated.options.dest_file=null |
    .translated.options.dest_dir=null |
    .translated.item_names |= sort_by(.key|tojson) |
    .translated.short_names |= sort_by(.key|tojson) |
    .translated.assoc_item_names |= sort_by(.key|tojson)
  ' "$replay_tmp/V7ForestTerminal.llbc" | shasum -a 256 | awk '{print $1}'
)
test "$normalized_hash" = f03fd5dcd020851e2a31e6614070f0b92ab5e9b66845ee85dc211f7372f449b0

mkdir -p "$replay_tmp/generated"
"$AENEAS_BIN" -sequential -no-progress-bar -abort-on-error -backend lean \
  -namespace V7ForestTerminalGenerated -dest "$replay_tmp/generated" \
  -subdir V7ForestTerminal -split-files -emit-json \
  "$replay_tmp/V7ForestTerminal.llbc"

cmp "$replay_tmp/generated/V7ForestTerminal/Types.lean" \
  "$script_dir/generated/V7ForestTerminal/Types.lean"
cmp "$replay_tmp/generated/V7ForestTerminal/Funs.lean" \
  "$script_dir/generated/V7ForestTerminal/Funs.lean"
echo 'V7 forest terminal Charon/Aeneas extraction replay: PASS'
