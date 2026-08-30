#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(CDPATH= cd -- "$script_dir/../.." && pwd)

cd "$repo_root"
cargo test -p aspis-registry --lib
cargo test -p aspis-pool --features pair-forest-account-evidence \
  pair_forest_dispatch::tests
cargo test --manifest-path \
  "$script_dir/harness/Cargo.toml"
"$script_dir/source-audit.sh"

echo 'V7 registry/operator focused Rust replay: PASS'
