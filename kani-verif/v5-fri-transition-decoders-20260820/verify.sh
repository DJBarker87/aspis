#!/usr/bin/env bash
set -euo pipefail

readonly bundle="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly root="$(cd "$bundle/../.." && pwd -P)"

[[ "$(git -C "$root" hash-object crates/aspis-core/src/circle_query.rs)" == \
  "085f0d082d9d2fe61d46ceb69f4a2b06bc6a0727" ]]
[[ "$(cargo kani --version)" == "cargo-kani 0.67.0" ]]
[[ "$(bitwuzla --version)" == "0.9.1" ]]

cd "$bundle"

cargo kani --exact --harness proofs::unchanged_full_decoder_equals_reference \
  --no-assertion-reach-checks --solver bitwuzla \
  --output-format old -Z unstable-options \
  --cbmc-args --unwinding-assertions

cargo kani --exact --harness proofs::unchanged_selected_decoder_equals_reference \
  --no-assertion-reach-checks --solver bitwuzla \
  --output-format old -Z unstable-options \
  --cbmc-args --unwinding-assertions
