#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(git -C "$script_dir" rev-parse --show-toplevel)

: "${AENEAS_LEAN_BACKEND:?set AENEAS_LEAN_BACKEND to the pinned Aeneas backends/lean directory}"
test -f "$AENEAS_LEAN_BACKEND/lakefile.lean"
command -v lake >/dev/null
command -v mktemp >/dev/null
command -v patch >/dev/null

mem_available_kb=$(awk '/^MemAvailable:/ { print $2 }' /proc/meminfo)
test "$mem_available_kb" -ge 25165824
cgroup_path=$(awk -F: '$1 == "0" { print $3 }' /proc/self/cgroup)
test -n "$cgroup_path"
test "$(tr -d '\n' < "/sys/fs/cgroup$cgroup_path/memory.high")" = 23622320128
test "$(tr -d '\n' < "/sys/fs/cgroup$cgroup_path/memory.max")" = 30064771072
test "$(tr -d '\n' < "/sys/fs/cgroup$cgroup_path/memory.swap.max")" = 0

replay_base=${TMPDIR:-/tmp}
replay_base=${replay_base%/}
replay_workspace=$(mktemp -d "$replay_base/v7-merkle-caller-namespace.XXXXXX")
cleanup() {
  case "$replay_workspace" in
    "$replay_base"/v7-merkle-caller-namespace.*)
      rm -rf -- "$replay_workspace" ;;
    *) echo "refusing unsafe cleanup target: $replay_workspace" >&2 ;;
  esac
}
trap cleanup EXIT

cp -R "$script_dir/generated/V7MerkleK12" "$replay_workspace/"
cp -R "$script_dir/caller/generated/V7MerkleCaller" "$replay_workspace/"
patch --fuzz=0 -p1 -d "$replay_workspace" < \
  "$script_dir/toolchain/v7-merkle-caller-generated-compat.patch"

deferred_parser_source="$repo_root/aeneas-verif/v7-onefold-accepted-source-20260825/parser/generated-exact/V7DeferredParser"
cp -R "$deferred_parser_source" "$replay_workspace/"
patch --fuzz=0 -p1 -d "$replay_workspace" < \
  "$script_dir/toolchain/v7-deferred-parser-combined-external.patch"
patch --fuzz=0 -p1 -d "$replay_workspace" < \
  "$script_dir/toolchain/v7-deferred-parser-caller-combined.patch"

cp "$script_dir/caller/proof/V7MerkleCallerNamespaceBridge.lean" \
  "$replay_workspace/"

export LEAN_NUM_THREADS=1
export LEAN_PATH="$AENEAS_LEAN_BACKEND:$replay_workspace"
(
  cd "$AENEAS_LEAN_BACKEND"
  for module_name in TypesExternal Types FunsExternal Funs; do
    lake env lean -j1 -R "$replay_workspace" \
      -o "$replay_workspace/V7MerkleK12/$module_name.olean" \
      "$replay_workspace/V7MerkleK12/$module_name.lean"
  done
  for module_name in TypesExternal Types FunsExternal; do
    lake env lean -j1 -R "$replay_workspace" \
      -o "$replay_workspace/V7MerkleCaller/$module_name.olean" \
      "$replay_workspace/V7MerkleCaller/$module_name.lean"
  done
  for module_name in Types FunsExternal Funs; do
    lake env lean -j1 -R "$replay_workspace" \
      -o "$replay_workspace/V7DeferredParser/$module_name.olean" \
      "$replay_workspace/V7DeferredParser/$module_name.lean"
  done
  lake env lean -j1 -R "$replay_workspace" \
    -o "$replay_workspace/V7MerkleCaller/Funs.olean" \
    "$replay_workspace/V7MerkleCaller/Funs.lean"
  lake env lean -j1 -R "$replay_workspace" \
    -o "$replay_workspace/V7MerkleCallerNamespaceBridge.olean" \
    "$replay_workspace/V7MerkleCallerNamespaceBridge.lean"
)

echo 'V7 caller/Merkle/deferred-parser namespace bridge: PASS'
