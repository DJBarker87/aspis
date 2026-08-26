#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(git -C "$script_dir" rev-parse --show-toplevel)
production_commit=01f5f4f722cfdf6bc29c157fc3db6ff5ab5e413a
production_tree=f634f5d7d8ff6606f1a9db40771111e49f5f7e53
expected_charon_sha=b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c
expected_aeneas_sha=87f65bd36e0dad06d322f833fcb4cb6c3e7d84acf149b31d0c4e61656d23ea4a
expected_aeneas_version='aeneas d860ac47-patched-result-aware'
expected_normalized_llbc_sha=f43c3b6596bb4a527d46d9c4163e6ce21eef3db0ef6a55ecb6261b7fa5368d91

: "${CHARON_BIN:?set CHARON_BIN to the pinned Linux NUC Charon binary}"
: "${AENEAS_BIN:?set AENEAS_BIN to the result-aware Linux NUC Aeneas binary}"

test -x "$CHARON_BIN"
test -x "$AENEAS_BIN"
command -v cmp >/dev/null
command -v git >/dev/null
command -v jq >/dev/null
command -v mktemp >/dev/null
command -v patch >/dev/null
command -v rg >/dev/null
command -v sha256sum >/dev/null
command -v tar >/dev/null

test "$(hostname -s)" = nuc
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

replay_base=${TMPDIR:-/tmp}
replay_base=${replay_base%/}
replay_tmp=$(mktemp -d "$replay_base/v7-merkle-k12-extraction.XXXXXX")
cleanup() {
  case "$replay_tmp" in
    "$replay_base"/v7-merkle-k12-extraction.*) rm -rf -- "$replay_tmp" ;;
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
fresh_llbc="$replay_tmp/V7MerkleK12.llbc"
(
  cd "$source_tree"
  "$CHARON_BIN" cargo \
    --preset aeneas \
    --mir built \
    --sysroot default \
    --start-from crate::v7_merkle208::truncate_sha256_v7 \
    --start-from crate::v7_merkle208::private_leaf_hash_v7 \
    --start-from crate::v7_merkle208::node_hash_v7 \
    --start-from crate::v7_merkle208::verify_two_minimal_subtrees_v7_bytes \
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
normalize_llbc "$script_dir/extraction/V7MerkleK12.llbc" > "$archived_normalized"
test "$(sha256sum "$fresh_normalized" | awk '{print $1}')" = \
  "$expected_normalized_llbc_sha"
cmp "$fresh_normalized" "$archived_normalized"

fresh_generated="$replay_tmp/generated"
mkdir -p "$fresh_generated"
"$AENEAS_BIN" \
  -sequential -no-progress-bar -abort-on-error -backend lean \
  -namespace V7MerkleK12Generated \
  -dest "$fresh_generated" -subdir V7MerkleK12 \
  -split-files -emit-json "$fresh_llbc"

patch --silent -d "$fresh_generated" -p1 < \
  "$script_dir/extraction/aeneas-failure-diagnostic-normalization.patch"
cmp "$fresh_generated/V7MerkleK12/Types.lean" \
  "$script_dir/generated/V7MerkleK12/Types.lean"
cmp "$fresh_generated/V7MerkleK12/TypesExternal_Template.lean" \
  "$script_dir/generated/V7MerkleK12/TypesExternal_Template.lean"
cmp "$fresh_generated/V7MerkleK12/FunsExternal_Template.lean" \
  "$script_dir/generated/V7MerkleK12/FunsExternal_Template.lean"
cmp "$fresh_generated/V7MerkleK12/Funs.lean" \
  "$script_dir/generated/V7MerkleK12/Funs.lean"
cmp "$fresh_generated/translation.json" \
  "$script_dir/extraction/translation.json"

if rg -n '\b(axiom|sorry|admit|sorryAx)\b' \
    "$script_dir/generated/V7MerkleK12/TypesExternal.lean" \
    "$script_dir/generated/V7MerkleK12/Types.lean" \
    "$script_dir/generated/V7MerkleK12/FunsExternal.lean" \
    "$script_dir/generated/V7MerkleK12/Funs.lean" \
    "$script_dir/proof" --glob '*.lean'; then
  echo 'forbidden axiom or Lean placeholder found in checked bundle source' >&2
  exit 1
fi

echo 'V7 K1.2 exact-base four-root extraction equality: PASS'
