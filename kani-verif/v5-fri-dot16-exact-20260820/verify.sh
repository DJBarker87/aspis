#!/usr/bin/env bash
set -euo pipefail

bundle_dir="$(cd "$(dirname "$0")" && pwd)"
repo_dir="$(cd "$bundle_dir/../.." && pwd)"

test "$(git -C "$repo_dir" hash-object crates/aspis-core/src/field.rs)" = \
  "a28ff94de05265102ca819849805a7f73c675800"
test "$(cargo kani --version)" = "cargo-kani 0.67.0"
bitwuzla --version | grep -Fx "0.9.1" >/dev/null
kissat --version | grep -Fx "4.0.4" >/dev/null

cd "$bundle_dir"

cargo kani --exact --harness proofs::production_dot16_equals_indexed_dot16 \
  --no-assertion-reach-checks --no-default-checks \
  --solver bitwuzla --output-format old -Z unstable-options \
  --cbmc-args --property proofs::production_dot16_equals_indexed_dot16.assertion.9

cargo kani --exact --harness proofs::production_dot16_acceptance_safety_and_unwind \
  --no-assertion-reach-checks --solver kissat \
  --output-format old -Z unstable-options \
  --cbmc-args --unwinding-assertions

cargo kani --exact --harness proofs::indexed_dot16_acceptance_safety_and_unwind \
  --no-assertion-reach-checks --solver kissat \
  --output-format old -Z unstable-options \
  --cbmc-args --unwinding-assertions
