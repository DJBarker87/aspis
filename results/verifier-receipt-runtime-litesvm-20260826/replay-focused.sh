#!/bin/sh
set -eu

evidence_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(CDPATH= cd -- "$evidence_dir/../.." && pwd)
source_commit=b484a8772680e90681cb099b57929b9700c1d4a1
expected_artifact_sha=PENDING
expected_artifact_bytes=0
artifact="$evidence_dir/artifacts/aspis_verifier.so"
proof="$repo_root/results/spend/v7-devnet-20260825-fullc2/v7-proof.bin"
statement="$repo_root/results/spend/v7-devnet-20260825-fullc2/v7-statement.json"
metadata="$repo_root/results/spend/v7-devnet-20260825-fullc2/v7-honest-proof.json"
output=${1:-"$evidence_dir/evidence.replay.json"}

test "$expected_artifact_sha" != PENDING
test "$expected_artifact_bytes" -gt 0
test -f "$artifact"
test -f "$proof"
test -f "$statement"
test -f "$metadata"
git -C "$repo_root" cat-file -e "$source_commit^{commit}"

if [ -f "$evidence_dir/MANIFEST.sha256" ]; then
    (cd "$evidence_dir" && shasum -a 256 -c MANIFEST.sha256)
fi

tmp=$(mktemp -d "${TMPDIR:-/tmp}/aspis-receipt-replay.XXXXXX")
trap 'rm -rf "$tmp"' EXIT HUP INT TERM
mkdir -p "$tmp/source"
git -C "$repo_root" archive "$source_commit" | tar -x -C "$tmp/source"
mkdir -p "$tmp/source/results/verifier-receipt-runtime-litesvm-20260826"
cp -R "$evidence_dir/harness" \
    "$tmp/source/results/verifier-receipt-runtime-litesvm-20260826/harness"

NO_DNA=1 CARGO_BUILD_JOBS=2 cargo run \
    --locked \
    --release \
    --manifest-path \
    "$tmp/source/results/verifier-receipt-runtime-litesvm-20260826/harness/Cargo.toml" \
    -- \
    "$artifact" \
    "$proof" \
    "$statement" \
    "$metadata" \
    "$expected_artifact_sha" \
    "$expected_artifact_bytes" \
    "$output"
