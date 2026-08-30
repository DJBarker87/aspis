#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(CDPATH= cd -- "$script_dir/../.." && pwd)
replay_base=${TMPDIR:-/tmp}
replay_base=${replay_base%/}
target_dir=$(mktemp -d "$replay_base/aspis-v7-custody-rust.XXXXXX")
cleanup() {
  case "$target_dir" in
    "$replay_base"/aspis-v7-custody-rust.*) rm -rf -- "$target_dir" ;;
    *) echo "refusing unsafe cleanup target: $target_dir" >&2 ;;
  esac
}
trap cleanup EXIT

CARGO_BUILD_JOBS=1 CARGO_TARGET_DIR="$target_dir/target" \
  cargo test --manifest-path "$script_dir/harness/Cargo.toml" --locked

for test_name in \
  pair_forest::tests::vault_deposit_routes_one_occupied_empty_pair_and_creates_lane_history \
  pair_forest::tests::deposit_alias_or_bad_token_delta_fails_without_pool_writes \
  pair_forest::tests::one_terminal_withdrawal_authenticates_loader_and_checks_custody_delta_before_writes \
  deposit::tests::invalid_amount_payload_and_token2022_shape_fail_before_transfer
do
  NO_DNA=1 CARGO_BUILD_JOBS=1 cargo test --manifest-path \
    "$repo_root/programs/aspis-pool/Cargo.toml" \
    --features v7-pair-forest-one-tx-candidate "$test_name" -- --exact
done

echo 'V7 Pool vault-custody projected and focused production Rust replay: PASS'
