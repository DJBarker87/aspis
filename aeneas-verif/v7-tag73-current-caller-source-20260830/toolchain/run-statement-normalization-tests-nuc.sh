#!/usr/bin/env bash
set -euo pipefail

readonly task=/home/dombarker/project-offloads/aspis-v7-aeneas-source-unblock-20260830
readonly repo="$task/normalized-source-statement-r2"
readonly target="$task/target-normalized-r2"
readonly log="$task/logs/statement-normalization-release-tests-r2.log"
readonly time_log="$task/logs/statement-normalization-release-tests-r2.time"
readonly atomic="$repo/crates/aspis-statement/src/atomic_state_only_terminal.rs"

export PATH=/home/dombarker/.cargo/bin:$PATH
export CARGO_BUILD_JOBS=1
export CARGO_TARGET_DIR="$target"

test "$(sha256sum "$atomic" | cut -d' ' -f1)" = \
  bcd974a18999d507893e2b7d00b5aec89f1c66b374831af87807f1cbcc4d67d3

tests=(
  cross_partition_selectors_match_semantic_partition_off_domain
  sparse_atomic_initial_sums_match_dense_zero_weight_reference
  rank_74_routing_matches_the_183_link_walk_at_random_qm31_points
  diagnostic_terminal_is_the_same_polynomial_at_random_qm31_points
  tag73_adds_only_the_inactive_helper_aggregate_term
)

cd "$repo"
/usr/bin/time -v -o "$time_log" bash -c '
  set -euo pipefail
  for test_name in "$@"; do
    cargo test \
      --locked \
      --release \
      --package aspis-statement \
      --lib \
      --no-default-features \
      "$test_name" \
      -- \
      --nocapture
  done
' bash "${tests[@]}" > "$log" 2>&1

test "$(grep -c 'test result: ok. 1 passed; 0 failed' "$log")" -eq "${#tests[@]}"
printf 'statement source-normalization focused release tests: PASS\n'
