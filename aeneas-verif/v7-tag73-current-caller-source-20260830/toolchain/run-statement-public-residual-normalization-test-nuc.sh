#!/usr/bin/env bash
set -euo pipefail

readonly task=/home/dombarker/project-offloads/aspis-v7-aeneas-source-unblock-20260830
readonly repo="$task/normalized-source-statement-r6"
readonly target="$task/target-normalized-r2"
readonly log="$task/logs/statement-public-residual-normalization-release-test-r6.log"
readonly time_log="$task/logs/statement-public-residual-normalization-release-test-r6.time"
readonly atomic="$repo/crates/aspis-statement/src/atomic_state_only_terminal.rs"

export PATH=/home/dombarker/.cargo/bin:$PATH
export CARGO_BUILD_JOBS=1
export CARGO_TARGET_DIR="$target"

test "$(sha256sum "$atomic" | cut -d' ' -f1)" = \
  35566dbf25ad4eb2e7abcf355aaba3320ec7cbb5c60de14908dcf48b79f3cac2

cd "$repo"
/usr/bin/time -v -o "$time_log" \
  cargo test \
    --locked \
    --release \
    --package aspis-statement \
    --lib \
    --no-default-features \
    diagnostic_terminal_is_the_same_polynomial_at_random_qm31_points \
    -- \
    --nocapture \
    > "$log" 2>&1

test "$(grep -c 'test result: ok. 1 passed; 0 failed' "$log")" -eq 1
printf 'statement public-residual source-normalization focused release test: PASS\n'
