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

test "$(shasum -a 256 "$pair_source" | awk '{print $1}')" = \
  4702885ad27659b99ea72dbbb3b96945411616d63392f7d4f9a93cae986085e1
test "$(shasum -a 256 "$dispatch_source" | awk '{print $1}')" = \
  84b6dbfa9ec12d56184bb0c1e250ed731af83fa44c91fbd05505c38ae356c995
test "$(shasum -a 256 "$manifest" | awk '{print $1}')" = \
  f5b42a59c788694ce6a0eba02b193e50f9c58028e1ba55bd8827118656f9aa2e
test "$(shasum -a 256 "$pool_verifier_dispatch" | awk '{print $1}')" = \
  95281016c34355c7f5bbb5e8ac31cacfa9c743699ecfeb1c8ddbae2cc1a3afc8
test "$(shasum -a 256 "$verifier_manifest" | awk '{print $1}')" = \
  e563f04f7871c25b0d3d43094ce61a7f39143508c5193d53e14991013ea4a428
test "$(shasum -a 256 "$verifier_reader" | awk '{print $1}')" = \
  276c3eb0d157408e2f132e69001e77c32f306baa86450f1e8fab9cdcb8fbadbb
test "$(shasum -a 256 "$statement_manifest" | awk '{print $1}')" = \
  f268aa7a85b32969f57b3a21fcefffd5310c98b522bf467b151232e91e2d537a
test "$(shasum -a 256 "$semantic_terminal" | awk '{print $1}')" = \
  0f3cbc9aead222e49ffaaa678e5f952a52c5f93aa28f5de802a3390993157edd
test "$(shasum -a 256 "$copy_terminal" | awk '{print $1}')" = \
  f6f8018ed3e3ae2a29ec21d12c9ac1b7ffb93024d73d188c66ea514e05c05d86
test "$(shasum -a 256 "$copy_constants" | awk '{print $1}')" = \
  bc4d72deed0c4b17cefa5092aa05bbc5587c76123df69bd4b4e1187f46280cf6

# Exact lane-account mutation inventory: deposit, authenticated terminal, and
# the eight-lane initialization loop.  Any fourth byte write fails this audit.
lane_writes=$(rg -n \
  'lane_data(?:\[lane\])?\.copy_from_slice\((next_lane_image|lane_images\[lane\])\.as_ref\(\)\)' \
  "$pair_source")
test "$(printf '%s\n' "$lane_writes" | wc -l | tr -d ' ')" = 3
printf '%s\n' "$lane_writes" | rg -q '^861:'
printf '%s\n' "$lane_writes" | rg -q '^1403:'
printf '%s\n' "$lane_writes" | rg -q '^1712:'

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
