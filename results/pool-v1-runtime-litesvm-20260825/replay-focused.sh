#!/bin/sh
set -eu

evidence_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(CDPATH= cd -- "$evidence_dir/../.." && pwd)
replay_output=${1:-"$evidence_dir/evidence.replay.json"}

if [ -f "$evidence_dir/MANIFEST.sha256" ]; then
    (cd "$evidence_dir" && shasum -a 256 -c MANIFEST.sha256)
fi

cd "$repo_root"
NO_DNA=1 CARGO_BUILD_JOBS=1 cargo run \
    --locked \
    --release \
    --manifest-path "$evidence_dir/harness/Cargo.toml" \
    -- \
    "$evidence_dir/artifacts/aspis_pool.so" \
    "$evidence_dir/artifacts/aspis_pool_runtime_mock_verifier.so" \
    "$replay_output"
