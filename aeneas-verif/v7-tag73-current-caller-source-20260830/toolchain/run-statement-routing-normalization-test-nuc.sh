#!/usr/bin/env bash
set -euo pipefail

readonly task=/home/dombarker/project-offloads/aspis-v7-aeneas-source-unblock-20260830
readonly repo="$task/normalized-source-statement-r5"
readonly target="$task/target-normalized-r2"
readonly log="$task/logs/statement-routing-normalization-release-test-r5.log"
readonly time_log="$task/logs/statement-routing-normalization-release-test-r5.time"
readonly atomic="$repo/crates/aspis-statement/src/atomic_state_only_terminal.rs"

export PATH=/home/dombarker/.cargo/bin:$PATH
export CARGO_BUILD_JOBS=1
export CARGO_TARGET_DIR="$target"

test "$(sha256sum "$atomic" | cut -d' ' -f1)" = \
  2ebfe2973d3d57829dbc19f616335ed551eedc940dc53d57ce4e61e098188203

cd "$repo"
/usr/bin/time -v -o "$time_log" \
  cargo test \
    --locked \
    --release \
    --package aspis-statement \
    --lib \
    --no-default-features \
    rank_74_routing_matches_the_183_link_walk_at_random_qm31_points \
    -- \
    --nocapture \
    > "$log" 2>&1

test "$(grep -c 'test result: ok. 1 passed; 0 failed' "$log")" -eq 1
printf 'statement routing source-normalization focused release test: PASS\n'
