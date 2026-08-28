#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(git -C "$script_dir" rev-parse --show-toplevel)

export CARGO_BUILD_JOBS=1
export RUSTFLAGS=${RUSTFLAGS:--Awarnings}

(
  cd "$repo_root"
  cargo test -p aspis-pool --no-default-features \
    --features pair-forest-source-invariant-audit \
    terminal_program_invariant_lane_decoder_keeps_exact_boundary
  cargo test -p aspis-pool --no-default-features \
    --features pair-forest-source-result-invariant-audit \
    authenticated_result_encoder_is_byte_exact_for_valid_lanes
)

echo 'V7 forest lane invariant focused Rust replay: PASS'
