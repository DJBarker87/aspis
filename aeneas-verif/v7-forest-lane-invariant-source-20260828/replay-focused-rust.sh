#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(git -C "$script_dir" rev-parse --show-toplevel)

export CARGO_BUILD_JOBS=1
export RUSTFLAGS=${RUSTFLAGS:--Awarnings}

pool_source="$repo_root/programs/aspis-pool/src/pair_forest.rs"
statement_source="$repo_root/crates/aspis-statement/src/pool_v1"
for test_name in \
  program_invariant_lane_decoder_keeps_exact_boundary \
  authenticated_result_encoder_is_byte_exact_for_valid_lanes \
  deposit_invariant_append_is_byte_exact_at_measured_boundaries \
  deposit_invariant_source_root_still_requires_exact_retained_history \
  pair_forest_lane_persistence_surface_remains_closed \
  one_terminal_transfer_updates_only_selected_lane_history_and_marker; do
  rg -q "fn ${test_name}\\(" "$pool_source"
done
for test_name in \
  packed_public_digest_matches_all_transfer_and_withdrawal_bindings \
  every_generated_copy_weight_is_binary_and_skip_add_is_exact \
  endpoint_selector_cache_matches_every_generated_endpoint_exactly \
  compiled_copy_lane_matches_host_reference_off_domain; do
  rg -q "fn ${test_name}\\(" "$statement_source"
done

(
  cd "$repo_root"
  cargo test --release -p aspis-pool --no-default-features \
    --features pair-forest-source-invariant-audit \
    program_invariant_lane_decoder_keeps_exact_boundary
  cargo test --release -p aspis-pool --no-default-features \
    --features pair-forest-source-result-invariant-audit \
    authenticated_result_encoder_is_byte_exact_for_valid_lanes
  cargo test --release -p aspis-pool --no-default-features \
    --features pair-forest-deposit-invariant-audit \
    deposit_invariant_append_is_byte_exact_at_measured_boundaries
  cargo test --release -p aspis-pool --no-default-features \
    --features pair-forest-deposit-invariant-audit \
    deposit_invariant_source_root_still_requires_exact_retained_history
  cargo test --release -p aspis-pool --no-default-features \
    --features pair-forest-deposit-invariant-audit \
    pair_forest_lane_persistence_surface_remains_closed
  cargo test --release -p aspis-statement --no-default-features \
    --features pool-v1-pair-forest-packed-digest-audit \
    packed_public_digest_matches_all_transfer_and_withdrawal_bindings
  cargo test --release -p aspis-statement --no-default-features \
    --features pool-v1-pair-forest-binary-copy-weights-audit \
    every_generated_copy_weight_is_binary_and_skip_add_is_exact
  cargo test --release -p aspis-statement --no-default-features \
    --features pool-v1-pair-forest-endpoint-selector-cache-audit \
    endpoint_selector_cache_matches_every_generated_endpoint_exactly
  cargo test --release -p aspis-statement --no-default-features \
    --features pool-v1-pair-forest-binary-copy-weights-audit,pool-v1-pair-forest-endpoint-selector-cache-audit \
    compiled_copy_lane_matches_host_reference_off_domain
  cargo test --release -p aspis-pool --no-default-features \
    --features pair-forest-verifier-lane-invariant-audit,pair-forest-source-result-invariant-audit,pair-forest-direct-result-audit \
    one_terminal_transfer_updates_only_selected_lane_history_and_marker
  cargo check -p aspis-pool --no-default-features \
    --features pair-forest-verifier-lane-invariant-audit,pair-forest-source-result-invariant-audit,pair-forest-direct-result-audit
  cargo check -p aspis-verifier --no-default-features \
    --features v7-pair-forest-lane-invariant-audit,v7-pair-forest-fixed-canonical-audit,v7-pair-forest-packed-digest-audit,v7-pair-forest-binary-copy-weights-audit,v7-pair-forest-endpoint-selector-cache-audit
)

echo 'V7 forest lane invariant focused Rust replay: PASS'
