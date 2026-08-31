#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(CDPATH= cd -- "$script_dir/../.." && pwd)

export CARGO_BUILD_JOBS=1
cargo test --manifest-path "$script_dir/harness/Cargo.toml"
cargo test --manifest-path "$repo_root/programs/aspis-registry/Cargo.toml" \
  --lib v2_ -- --nocapture

echo 'V7 Registry V2 deployment certificate Rust replay: PASS'

