#!/usr/bin/env bash
set -euo pipefail

readonly bundle_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly repo_dir="$(cd "$bundle_dir/../.." && pwd -P)"

check_source() {
  local relative_file="$1"
  local expected_blob="$2"
  local expected_sha256="$3"

  [[ "$(git -C "$repo_dir" hash-object "$relative_file")" == "$expected_blob" ]]
  [[ "$(shasum -a 256 "$repo_dir/$relative_file" | awk '{print $1}')" == "$expected_sha256" ]]
}

check_source \
  "crates/aspis-core/src/circle_fri.rs" \
  "d9382a35ec7a660b696171e7609f443995a009bf" \
  "7df47ac39aeda39b15c536927310cd7612a23984907b7eb05d32613f8e156f9b"
check_source \
  "crates/aspis-core/src/circle_line_merkle.rs" \
  "088917245f072b44e1b6bb0fa02d707ba5062274" \
  "8c3fe1a4a60d037e7c6bd251ac451fd314991528f3831f7f892c5fb376da821a"
check_source \
  "crates/aspis-core/src/field.rs" \
  "a28ff94de05265102ca819849805a7f73c675800" \
  "dadd6bac7c6c44fcb13e1a1ca26e9d2b6f767370bb6e802640948f15fc795836"
check_source \
  "crates/aspis-core/build.rs" \
  "62e5f3ff65bcb35bc61db8636648ab3addfeee47" \
  "ed57b3d0beb1dc8de4ed55945faae5a7be7d97b6d4ee686b24b01744e7ce54b5"

[[ "$(cargo kani --version)" == "cargo-kani 0.67.0" ]]
[[ "$(bitwuzla --version)" == "0.9.1" ]]

cd "$bundle_dir"
cargo fmt --check

run_kani_checked() {
  local log
  log="$(mktemp -t aspis-coordinate-kani)"
  if "$@" 2>&1 | tee "$log"; then
    if ! grep -Fq 'VERIFICATION:- SUCCESSFUL' "$log"; then
      printf 'Kani exited zero without its successful-verification marker\n' >&2
      rm -f -- "$log"
      return 1
    fi
  else
    local command_status=$?
    rm -f -- "$log"
    return "$command_status"
  fi
  rm -f -- "$log"
}

run_value() {
  local harness="$1"
  local property="$2"
  printf 'Verifying %s\n' "$harness"
  run_kani_checked cargo kani --exact --harness "$harness" \
    --no-assertion-reach-checks --no-default-checks --solver bitwuzla \
    -Z unstable-options --cbmc-args --property "$property"
  printf 'Verified %s\n' "$harness"
}

run_value \
  proofs::released_single_circle_point_is_valid_and_equal \
  proofs::released_single_circle_point_is_valid_and_equal.assertion.1
run_value \
  proofs::released_selected_circle_point_shapes_are_exact \
  proofs::released_selected_circle_point_shapes_are_exact.assertion.1
for ordinal in {1..18}; do
  run_value \
    proofs::released_selected_circle_points_equal_at_each_ordinal \
    "proofs::released_selected_circle_points_equal_at_each_ordinal.assertion.$ordinal"
done
