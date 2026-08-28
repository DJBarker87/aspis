#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(git -C "$script_dir" rev-parse --show-toplevel)
pair_source="$repo_root/programs/aspis-pool/src/pair_forest.rs"
dispatch_source="$repo_root/programs/aspis-pool/src/processor.rs"
manifest="$repo_root/programs/aspis-pool/Cargo.toml"

# Production source is the committed default-off fast-path port.  The bundle
# commit is a descendant and changes no Pool Rust.
git -C "$repo_root" merge-base --is-ancestor \
  86d072be958bed4b6817b6cdc1fb5eb4f0c65ac7 HEAD

test "$(shasum -a 256 "$pair_source" | awk '{print $1}')" = \
  94cc57ee00d5a134141b994ed2a27c962d5a132f49fd6b97cc503377e6922e91
test "$(shasum -a 256 "$dispatch_source" | awk '{print $1}')" = \
  84b6dbfa9ec12d56184bb0c1e250ed731af83fa44c91fbd05505c38ae356c995
test "$(shasum -a 256 "$manifest" | awk '{print $1}')" = \
  c3c634e11e9cac3159eba3048b5d3659f94d4eb275e70cdd54cc10776a627461

# Exact lane-account mutation inventory: deposit, authenticated terminal, and
# the eight-lane initialization loop.  Any fourth byte write fails this audit.
lane_writes=$(rg -n \
  'lane_data(?:\[lane\])?\.copy_from_slice\((next_lane_image|lane_images\[lane\])\.as_ref\(\)\)' \
  "$pair_source")
test "$(printf '%s\n' "$lane_writes" | wc -l | tr -d ' ')" = 3
printf '%s\n' "$lane_writes" | rg -q '^861:'
printf '%s\n' "$lane_writes" | rg -q '^1362:'
printf '%s\n' "$lane_writes" | rg -q '^1646:'

# Pin the functions that construct each image and the terminal feature routes.
rg -q '^fn prepare_deposit_append_v1\(' "$pair_source"
rg -q '^fn next_lane_image_box_v1\(' "$pair_source"
rg -q '^fn genesis_lane_image_box_v1\(' "$pair_source"
rg -q '^fn decode_lane_account_from_program_invariant_v1\(' "$pair_source"
rg -q '^fn encode_lane_from_authenticated_result_v1\(' "$pair_source"

for dispatch in \
  process_pair_forest_initialize_with_runtime_v1 \
  process_pair_forest_checkpoint_with_runtime_v1 \
  process_pair_forest_deposit_with_runtime_v1 \
  process_pair_forest_terminal_v1 \
  process_pair_forest_terminal_full_asf8_v1
do
  test "$(rg -c "^[[:space:]]*$dispatch\\(" "$dispatch_source")" = 1
done

# No production migration route exists at this revision.  A future migration
# must be implemented, made one-shot, and added to this exhaustive audit.
if rg -n 'pair_forest.*migration|migration.*pair_forest' \
    "$pair_source" "$dispatch_source"; then
  echo 'unexpected production forest migration route' >&2
  exit 1
fi

echo 'V7 forest lane production source/write inventory audit: PASS'
