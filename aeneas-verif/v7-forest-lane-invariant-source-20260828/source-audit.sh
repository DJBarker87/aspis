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
statement_manifest="$repo_root/crates/aspis-statement/Cargo.toml"
semantic_terminal="$repo_root/crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs"
copy_terminal="$repo_root/crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs"
copy_constants="$repo_root/crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal_constants.rs"

# Production source contains the committed default-off fast-path port and the
# six-account immutable-release authentication gate.  The bundle commit is a
# descendant; exact hashes below fail closed on any later source drift.
git -C "$repo_root" merge-base --is-ancestor \
  a789a9c6ff1f0a879e4f7396377e9c39df445974 HEAD
git -C "$repo_root" merge-base --is-ancestor 2dae6bea HEAD
git -C "$repo_root" merge-base --is-ancestor d49af9e3 HEAD
git -C "$repo_root" merge-base --is-ancestor 37c6ea1f HEAD
git -C "$repo_root" merge-base --is-ancestor eb3fbcde HEAD
git -C "$repo_root" merge-base --is-ancestor \
  74cc65d4f0da48ea8a49e833c0f35398195b3ec4 HEAD
git -C "$repo_root" merge-base --is-ancestor \
  5bd2e3e433a13f5b3243cf3762b47b34d73abad9 HEAD

test "$(shasum -a 256 "$pair_source" | awk '{print $1}')" = \
  8cdf153df70c593380fed33c9d8054ee49c9f9d876238126eae3849a3cbc4620
test "$(shasum -a 256 "$dispatch_source" | awk '{print $1}')" = \
  3c989ba201b622c01e67edec7cba8b17ba30663b386a4f316e757ff06dad7354
test "$(shasum -a 256 "$manifest" | awk '{print $1}')" = \
  4c9c42e6b46b07dec31a013f6fbee0aa5f399af3c7f74071461d116b7d06dc61
test "$(shasum -a 256 "$pool_verifier_dispatch" | awk '{print $1}')" = \
  7e45910a3d64e328dc234ede290119770e898bcb48f277d978219740ec891514
test "$(shasum -a 256 "$verifier_manifest" | awk '{print $1}')" = \
  7f8d8fe0633a86e26d7693b71abb2ca16f7ed58cbe9b0896ee49b7454318557d
test "$(shasum -a 256 "$verifier_reader" | awk '{print $1}')" = \
  4577c435a5c41a147331ca7d42b65053e181d58dca1b4322ef96b48c85babf77
test "$(shasum -a 256 "$statement_manifest" | awk '{print $1}')" = \
  cf8babeac16a1987ed1dbd05454f77cb0f217779c33d6384a986eccf9e5b5231
test "$(shasum -a 256 "$semantic_terminal" | awk '{print $1}')" = \
  efbc5be87e271419d7b09e1bb6e3a83984d42795bc20067ea039814fb89ffa58
test "$(shasum -a 256 "$copy_terminal" | awk '{print $1}')" = \
  50062fff8b6afbffad3ddbb8eda09992353a9171c4955151cece26a654c6a6d5
test "$(shasum -a 256 "$copy_constants" | awk '{print $1}')" = \
  cfce7ec499d3cfd54cf91eb88675e45d89ada5ce073fe00c78be5211204fbc50

# Exact lane-account mutation inventory: deposit, authenticated terminal, and
# the eight-lane initialization loop.  Any fourth byte write fails this audit.
lane_writes=$(rg -n \
  'lane_data(?:\[lane\])?\.copy_from_slice\((next_lane_image|lane_images\[lane\])\.as_ref\(\)\)' \
  "$pair_source")
test "$(printf '%s\n' "$lane_writes" | wc -l | tr -d ' ')" = 3
printf '%s\n' "$lane_writes" | rg -q '^980:'
printf '%s\n' "$lane_writes" | rg -q '^1545:'
printf '%s\n' "$lane_writes" | rg -q '^1858:'

# Pin the functions that construct each image and the terminal feature routes.
rg -q '^fn prepare_deposit_append_v1\(' "$pair_source"
rg -q '^fn next_lane_image_box_v1\(' "$pair_source"
rg -q '^fn genesis_lane_image_box_v1\(' "$pair_source"
rg -q '^fn decode_lane_account_from_program_invariant_v1\(' "$pair_source"
rg -q '^fn encode_lane_from_authenticated_result_v1\(' "$pair_source"
rg -q '^fn append_pair_leaf_from_program_invariant_v1\(' "$pair_source"
rg -q '^fn decode_deposit_lane_box_v1\(' "$pair_source"
rg -q '^fn validate_lane_current_page\(' "$pair_source"
rg -q '^pair-forest-deposit-invariant-audit = \["pair-forest-account-evidence"\]' \
  "$manifest"
candidate_features=$(sed -n \
  '/^v7-pair-forest-one-tx-candidate = \[/,/^\]/p' "$manifest")
if printf '%s\n' "$candidate_features" | rg -q \
    'pair-forest-deposit-invariant-audit'; then
  echo 'deposit invariant audit unexpectedly enabled in candidate aggregate' >&2
  exit 1
fi

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

# The three selected terminal arithmetic/result cuts retain their exact input
# schedules and fail-closed authentication boundaries.  These are feature
# gated experiments, not alternate proof relations.
rg -q '^fn add_digest_binding_packed\(' "$semantic_terminal"
rg -q '^fn public_digest_packed\(' "$semantic_terminal"
rg -q 'selector\.mul\(qm31_pack_base4\(&residuals\)\)' "$semantic_terminal"
rg -q '^fn add_binary_weight\(' "$copy_terminal"
rg -q '0 => sum,' "$copy_terminal"
rg -q '1 => sum\.add\(selector\),' "$copy_terminal"
rg -q 'unreachable!\("generated Pool V1 pair-forest Copy weight is not binary"\)' \
  "$copy_terminal"
rg -q '^fn validate_pair_forest_terminal_result_direct_v1\(' "$pair_source"
rg -q 'let result = decode_pool_v1_pair_forest_terminal_result_v1\(&returned_data\)' \
  "$pool_verifier_dispatch"
rg -q 'exact_bytes: returned_data\.into_boxed_slice\(\)' "$pool_verifier_dispatch"
rg -q 'let result_bytes = authenticated\.exact_bytes\(\);' "$pair_source"
rg -q '^pool-v1-pair-forest-packed-digest-audit = \[\]' "$statement_manifest"
rg -q '^pool-v1-pair-forest-binary-copy-weights-audit = \[\]' "$statement_manifest"
rg -q '^pair-forest-direct-result-audit = ' "$manifest"

# The endpoint-selector memo is keyed by the complete generated row tag. A
# direct-map collision cannot return a cached value: it takes the unchanged
# literal selector computation, stores the exact requested row/value, and
# keeps producer-then-consumer visitation in the hash-pinned source.
rg -q '^struct EndpointSelectorCache \{' "$copy_terminal"
rg -q 'if self\.rows\[slot\] == row \{' "$copy_terminal"
rg -q 'let value = selectors\.row\(usize::from\(row\)\);' "$copy_terminal"
rg -q 'self\.rows\[slot\] = row;' "$copy_terminal"
rg -q 'self\.values\[slot\] = value;' "$copy_terminal"
rg -q '^pool-v1-pair-forest-endpoint-selector-cache-audit = \[\]' \
  "$statement_manifest"
rg -q '^v7-pair-forest-endpoint-selector-cache-audit = \[' "$verifier_manifest"

# No production migration route exists at this revision.  A future migration
# must be implemented, made one-shot, and added to this exhaustive audit.
if rg -n 'pair_forest.*migration|migration.*pair_forest' \
    "$pair_source" "$dispatch_source"; then
  echo 'unexpected production forest migration route' >&2
  exit 1
fi

echo 'V7 forest lane production source/write inventory audit: PASS'
