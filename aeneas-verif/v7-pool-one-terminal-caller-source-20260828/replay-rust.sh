#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
replay_base=${TMPDIR:-/tmp}
replay_base=${replay_base%/}
target_dir=$(mktemp -d "$replay_base/aspis-v7-pool-caller-rust.XXXXXX")
cleanup() {
  case "$target_dir" in
    "$replay_base"/aspis-v7-pool-caller-rust.*) rm -rf -- "$target_dir" ;;
    *) echo "refusing unsafe cleanup target: $target_dir" >&2 ;;
  esac
}
trap cleanup EXIT

CARGO_BUILD_JOBS=1 CARGO_TARGET_DIR="$target_dir/target" \
  cargo test --manifest-path "$script_dir/harness/Cargo.toml" --locked

echo 'V7 Pool one-terminal projected Rust replay: PASS'
