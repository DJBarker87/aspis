#!/usr/bin/env bash
set -euo pipefail

readonly bundle="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly root="$(cd "$bundle/../.." && pwd -P)"
readonly harness="$bundle/harness"
readonly expected_source_blob="27fea89d4095718a0df5d22532d6cd4d24a5a6b3"

[[ "$(cargo kani --version)" == "cargo-kani 0.67.0" ]]
[[ "$(git -C "$root" hash-object crates/aspis-core/src/circle_pcs_shape.rs)" == \
  "$expected_source_blob" ]]

(
  cd "$harness"
  cargo kani --exact \
    --harness proofs::production_validation_success_returns_input
)

echo "Production V5 shape validation preserves its input on success: PASS"
