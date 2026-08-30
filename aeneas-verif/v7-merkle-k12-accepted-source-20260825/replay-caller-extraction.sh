#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(git -C "$script_dir" rev-parse --show-toplevel)
production_commit=01f5f4f722cfdf6bc29c157fc3db6ff5ab5e413a
production_tree=f634f5d7d8ff6606f1a9db40771111e49f5f7e53
expected_charon_sha=b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c
expected_aeneas_sha=87f65bd36e0dad06d322f833fcb4cb6c3e7d84acf149b31d0c4e61656d23ea4a
expected_aeneas_version='aeneas d860ac47-patched-result-aware'
expected_normalized_llbc_sha=8d964e12a81635c597c65074f92e27608aa886e8095fd42c71ba94b01e9d5513

: "${CHARON_BIN:?set CHARON_BIN to the pinned Linux Charon binary}"
: "${AENEAS_BIN:?set AENEAS_BIN to the fully patched result-aware Linux Aeneas binary}"
: "${AENEAS_LEAN_BACKEND:?set AENEAS_LEAN_BACKEND to the pinned Aeneas backends/lean directory}"

test -x "$CHARON_BIN"
test -x "$AENEAS_BIN"
test -f "$AENEAS_LEAN_BACKEND/lakefile.lean"
command -v cmp >/dev/null
command -v git >/dev/null
command -v jq >/dev/null
command -v lake >/dev/null
command -v mktemp >/dev/null
command -v patch >/dev/null
command -v rg >/dev/null
command -v sha256sum >/dev/null
command -v tar >/dev/null

mem_available_kb=$(awk '/^MemAvailable:/ { print $2 }' /proc/meminfo)
test "$mem_available_kb" -ge 25165824
cgroup_path=$(awk -F: '$1 == "0" { print $3 }' /proc/self/cgroup)
test -n "$cgroup_path"
test "$(tr -d '\n' < "/sys/fs/cgroup$cgroup_path/memory.high")" = 23622320128
test "$(tr -d '\n' < "/sys/fs/cgroup$cgroup_path/memory.max")" = 30064771072
test "$(tr -d '\n' < "/sys/fs/cgroup$cgroup_path/memory.swap.max")" = 0

test "$(sha256sum "$CHARON_BIN" | awk '{print $1}')" = "$expected_charon_sha"
test "$(sha256sum "$AENEAS_BIN" | awk '{print $1}')" = "$expected_aeneas_sha"
test "$("$AENEAS_BIN" -version)" = "$expected_aeneas_version"
test "$(git -C "$repo_root" rev-parse "$production_commit^{commit}")" = "$production_commit"
test "$(git -C "$repo_root" rev-parse "$production_commit^{tree}")" = "$production_tree"
(
  cd "$repo_root"
  sha256sum -c "$script_dir/CALLER-GENERATED.sha256"
)

replay_base=${TMPDIR:-/tmp}
replay_base=${replay_base%/}
replay_tmp=$(mktemp -d "$replay_base/v7-merkle-caller-extraction.XXXXXX")
cleanup() {
  case "$replay_tmp" in
    "$replay_base"/v7-merkle-caller-extraction.*) rm -rf -- "$replay_tmp" ;;
    *) echo "refusing unsafe cleanup target: $replay_tmp" >&2 ;;
  esac
}
trap cleanup EXIT

source_tree="$replay_tmp/source"
mkdir -p "$source_tree"
git -C "$repo_root" archive "$production_commit" | tar -x -C "$source_tree"
(
  cd "$source_tree"
  sha256sum -c "$script_dir/DEPLOYED-SOURCE.sha256"
)

export CARGO_BUILD_JOBS=1
export CARGO_TARGET_DIR="$replay_tmp/cargo-target"
fresh_llbc="$replay_tmp/V7MerkleCaller.llbc"
(
  cd "$source_tree"
  "$CHARON_BIN" cargo \
    --preset aeneas \
    --mir built \
    --sysroot default \
    --start-from crate::v7_onefold::verify_and_gamma_combine_v7_openings \
    --include aspis_core::v7_onefold \
    --include aspis_core::v7_merkle208 \
    --include aspis_core::state_only_private_merkle \
    --include aspis_core::v6_onefold::gamma_combine_v6_packed_layer0 \
    --include aspis_core::field \
    --dest-file "$fresh_llbc" \
    -- --package aspis-core --lib
)

normalize_llbc() {
  jq -cS '
    .translated.options.dest_file = null |
    .translated.options.dest_dir = null |
    .translated.item_names |= sort_by(.key | tojson) |
    .translated.short_names |= sort_by(.key | tojson) |
    .translated.assoc_item_names |= sort_by(.key | tojson)
  ' "$1"
}

fresh_normalized="$replay_tmp/fresh-normalized.llbc.json"
archived_normalized="$replay_tmp/archived-normalized.llbc.json"
normalize_llbc "$fresh_llbc" > "$fresh_normalized"
normalize_llbc "$script_dir/caller/extraction/V7MerkleCaller.llbc" > \
  "$archived_normalized"
test "$(sha256sum "$fresh_normalized" | awk '{print $1}')" = \
  "$expected_normalized_llbc_sha"
cmp "$fresh_normalized" "$archived_normalized"

fresh_generated="$replay_tmp/generated"
mkdir -p "$fresh_generated"
"$AENEAS_BIN" \
  -sequential -no-progress-bar -abort-on-error -backend lean \
  -namespace V7MerkleCallerGenerated \
  -dest "$fresh_generated" -subdir V7MerkleCaller \
  -split-files -emit-json "$fresh_llbc"

for generated_module in \
    Types.lean \
    TypesExternal_Template.lean \
    FunsExternal_Template.lean \
    Funs.lean; do
  cmp "$fresh_generated/V7MerkleCaller/$generated_module" \
    "$script_dir/caller/generated/V7MerkleCaller/$generated_module"
done
cmp "$fresh_generated/translation.json" \
  "$script_dir/caller/extraction/translation.json"

cp "$script_dir/caller/generated/V7MerkleCaller/TypesExternal.lean" \
  "$fresh_generated/V7MerkleCaller/"
cp "$script_dir/caller/generated/V7MerkleCaller/FunsExternal.lean" \
  "$fresh_generated/V7MerkleCaller/"

# The caller and the standalone four-function extraction intentionally share
# one executable interpretation of their identical Rust-library externals.
# Stage that checked dependency before applying the deterministic compatibility
# overlay to Aeneas's still-byte-compared raw caller output.
cp -R "$script_dir/generated/V7MerkleK12" "$fresh_generated/"
patch --fuzz=0 -p1 -d "$fresh_generated" < \
  "$script_dir/toolchain/v7-merkle-caller-generated-compat.patch"

# Stage the independent exact deferred-parser extraction.  Its original
# external module is checksum-covered; the deterministic overlay removes only
# the duplicate Slice.last definition and reuses the identical Merkle one.
deferred_parser_source="$repo_root/aeneas-verif/v7-onefold-accepted-source-20260825/parser/generated-exact/V7DeferredParser"
cp -R "$deferred_parser_source" "$fresh_generated/"
patch --fuzz=0 -p1 -d "$fresh_generated" < \
  "$script_dir/toolchain/v7-deferred-parser-combined-external.patch"
patch --fuzz=0 -p1 -d "$fresh_generated" < \
  "$script_dir/toolchain/v7-deferred-parser-caller-combined.patch"

export LEAN_NUM_THREADS=1
export LEAN_PATH="$AENEAS_LEAN_BACKEND:$fresh_generated"
(
  cd "$AENEAS_LEAN_BACKEND"
  for module_name in TypesExternal Types FunsExternal Funs; do
    lake env lean -j1 -R "$fresh_generated" \
      -o "$fresh_generated/V7MerkleK12/$module_name.olean" \
      "$fresh_generated/V7MerkleK12/$module_name.lean"
  done
  for module_name in TypesExternal Types FunsExternal Funs; do
    lake env lean -j1 -R "$fresh_generated" \
      -o "$fresh_generated/V7MerkleCaller/$module_name.olean" \
      "$fresh_generated/V7MerkleCaller/$module_name.lean"
  done
  for module_name in Types FunsExternal Funs; do
    lake env lean -j1 -R "$fresh_generated" \
      -o "$fresh_generated/V7DeferredParser/$module_name.olean" \
      "$fresh_generated/V7DeferredParser/$module_name.lean"
  done
  cp "$script_dir/caller/proof/V7MerkleCallerNamespaceBridge.lean" \
    "$fresh_generated/"
  lake env lean -j1 -R "$fresh_generated" \
    -o "$fresh_generated/V7MerkleCallerNamespaceBridge.olean" \
    "$fresh_generated/V7MerkleCallerNamespaceBridge.lean"
)

if rg -n '\b(axiom|sorry|admit|sorryAx)\b' \
    "$script_dir/caller/generated/V7MerkleCaller/TypesExternal.lean" \
    "$script_dir/caller/generated/V7MerkleCaller/FunsExternal.lean" \
    "$script_dir/caller/generated/V7MerkleCaller/Types.lean" \
    "$script_dir/caller/generated/V7MerkleCaller/Funs.lean" \
    "$script_dir/caller/proof/V7MerkleCallerNamespaceBridge.lean"; then
  echo 'forbidden axiom or Lean placeholder found in executable caller model' >&2
  exit 1
fi

echo 'V7 exact-base caller extraction, combined Lean import, and namespace bridge: PASS'
