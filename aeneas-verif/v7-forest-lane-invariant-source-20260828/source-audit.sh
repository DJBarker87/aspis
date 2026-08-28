#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(git -C "$script_dir" rev-parse --show-toplevel)
pair_source="$repo_root/programs/aspis-pool/src/pair_forest.rs"
dispatch_source="$repo_root/programs/aspis-pool/src/processor.rs"
manifest="$repo_root/programs/aspis-pool/Cargo.toml"
pool_verifier_dispatch="$repo_root/programs/aspis-pool/src/pair_forest_dispatch.rs"
verifier_manifest="$repo_root/programs/aspis-verifier/Cargo.toml"
verifier_reader="$repo_root/programs/aspis-verifier/src/v7_pair_forest_dispatch.rs"

# Production source contains the committed default-off fast-path port and the
# six-account immutable-release authentication gate.  The bundle commit is a
# descendant; exact hashes below fail closed on any later source drift.
git -C "$repo_root" merge-base --is-ancestor \
  a789a9c6ff1f0a879e4f7396377e9c39df445974 HEAD

test "$(shasum -a 256 "$pair_source" | awk '{print $1}')" = \
  3016a0cabe44dd7d3994aaac1d949195d480a4ac609e914cc4adbd3ea15ae71a
test "$(shasum -a 256 "$dispatch_source" | awk '{print $1}')" = \
  84b6dbfa9ec12d56184bb0c1e250ed731af83fa44c91fbd05505c38ae356c995
test "$(shasum -a 256 "$manifest" | awk '{print $1}')" = \
  448bdca453f0ceb0769b8e87bde7f8866ef648d161cb04e1031c58e8cc12f87c
test "$(shasum -a 256 "$pool_verifier_dispatch" | awk '{print $1}')" = \
  cdf8a64ddbc700606b4396be9ce46a21c854c18e085a7cf802f306c36fac93eb
test "$(shasum -a 256 "$verifier_manifest" | awk '{print $1}')" = \
  446dae08bef0cbb3ccba8220134defcfe933e3ab359a91c2cf41a171b50ba89e
test "$(shasum -a 256 "$verifier_reader" | awk '{print $1}')" = \
  276c3eb0d157408e2f132e69001e77c32f306baa86450f1e8fab9cdcb8fbadbb

# Exact lane-account mutation inventory: deposit, authenticated terminal, and
# the eight-lane initialization loop.  Any fourth byte write fails this audit.
lane_writes=$(rg -n \
  'lane_data(?:\[lane\])?\.copy_from_slice\((next_lane_image|lane_images\[lane\])\.as_ref\(\)\)' \
  "$pair_source")
test "$(printf '%s\n' "$lane_writes" | wc -l | tr -d ' ')" = 3
printf '%s\n' "$lane_writes" | rg -q '^861:'
printf '%s\n' "$lane_writes" | rg -q '^1362:'
printf '%s\n' "$lane_writes" | rg -q '^1671:'

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

# The verifier-side shortcut is not activated by owner/PDA alone.  Pin the
# immutable audit release root, exact registry authentication, six-account CPI
# forwarding and the fresh-only decoder boundary in the hash-pinned source.
rg -q '^fn authenticate_invariant_release_registry_v1\(' "$verifier_reader"
rg -q '^fn decode_lane_from_pool_release_invariant_box_v1\(' "$verifier_reader"
rg -q '^const PAIR_FOREST_INVARIANT_POOL_PROGRAM_AUDIT_V1: \[u8; 32\] = \[0x41; 32\];' \
  "$verifier_reader"
rg -q '^const PAIR_FOREST_INVARIANT_REGISTRY_PROGRAM_AUDIT_V1: \[u8; 32\] = \[0x44; 32\];' \
  "$verifier_reader"
rg -q '^const PAIR_FOREST_INVARIANT_POLICY_BINDING_AUDIT_V1: \[u8; 32\] = \[7; 32\];' \
  "$verifier_reader"
rg -q 'master\.verifier_policy\.registry_authority != \[0u8; 32\]' "$verifier_reader"
rg -q 'POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_REGISTRY' "$verifier_reader"
rg -q 'registry\.is_immutable\(\)' "$verifier_reader"
rg -q 'registry\.is_paused\(\)' "$verifier_reader"
rg -q 'entry\.verifier_program != verifier_program\.to_bytes\(\)' "$verifier_reader"
rg -q 'entry\.profile_binding != V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING' "$verifier_reader"
rg -q 'entry\.release_binding != V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING' "$verifier_reader"
rg -q 'entry\.statement_version != POOL_V1_PAIR_FOREST_TERMINAL_VERSION' "$verifier_reader"
rg -q 'let \[proof_account, master_account, checkpoint_account, lane_account, registry_account, entry_account\] =' \
  "$verifier_reader"
rg -q 'freshly initialized by that release' "$verifier_reader"
rg -q 'let \[registry, entry\] = registry_accounts' "$pool_verifier_dispatch"
rg -q 'AccountMeta::new_readonly\(\*registry\.key, false\)' "$pool_verifier_dispatch"
rg -q 'AccountMeta::new_readonly\(\*entry\.key, false\)' "$pool_verifier_dispatch"

# No production migration route exists at this revision.  A future migration
# must be implemented, made one-shot, and added to this exhaustive audit.
if rg -n 'pair_forest.*migration|migration.*pair_forest' \
    "$pair_source" "$dispatch_source"; then
  echo 'unexpected production forest migration route' >&2
  exit 1
fi

echo 'V7 forest lane production source/write inventory audit: PASS'
