#!/usr/bin/env bash
set -euo pipefail

bundle_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
artifact="$bundle_dir/artifacts/aspis_registry.so"
expected_sha="1066ffc4bf8a12a0ea56b64474b70e172162fc7852b66293c0c8c5f1380f0ff6"
actual_sha="$(shasum -a 256 "$artifact" | awk '{print $1}')"
test "$actual_sha" = "$expected_sha"

cd "$bundle_dir/harness"
NO_DNA=1 CARGO_BUILD_JOBS=1 cargo run --locked --release -- \
  ../artifacts/aspis_registry.so ../evidence.json | tee ../run.log
