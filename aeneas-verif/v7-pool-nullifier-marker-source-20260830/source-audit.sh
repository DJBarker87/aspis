#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(CDPATH= cd -- "$script_dir/../.." && pwd)

git -C "$repo_root" merge-base --is-ancestor \
  da77d5f5a22681200cceec8e90fc69ac2cc81ad8 HEAD

"$repo_root/aeneas-verif/v7-pool-one-terminal-caller-source-20260828/source-audit.sh"

test "$(shasum -a 256 "$script_dir/harness/src/lib.rs" | awk '{print $1}')" = \
  96fa52fb2bda38346d59fac8a68206182ec52a6a94e60e9e0b3d44da4b843eb4
test "$(shasum -a 256 "$script_dir/extraction/V7PoolNullifierMarker.llbc" | awk '{print $1}')" = \
  36a7404e9bd5785dce1bc74ec1b4b419d3206e9e73a17920a0cd895b05781f42

echo 'V7 Pool nullifier-marker source/control-flow audit: PASS'
