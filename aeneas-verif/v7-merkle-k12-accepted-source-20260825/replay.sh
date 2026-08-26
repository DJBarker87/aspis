#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(git -C "$script_dir" rev-parse --show-toplevel)
production_commit=01f5f4f722cfdf6bc29c157fc3db6ff5ab5e413a
production_tree=f634f5d7d8ff6606f1a9db40771111e49f5f7e53

: "${AENEAS_LEAN_BACKEND:?set AENEAS_LEAN_BACKEND to the pinned Aeneas backends/lean directory}"

test -d "$AENEAS_LEAN_BACKEND"
test -f "$AENEAS_LEAN_BACKEND/lakefile.lean"
command -v git >/dev/null
command -v lake >/dev/null
command -v mktemp >/dev/null
command -v patch >/dev/null
command -v rg >/dev/null
command -v shasum >/dev/null
command -v tar >/dev/null

cd "$repo_root"
test "$(git rev-parse "$production_commit^{commit}")" = "$production_commit"
test "$(git rev-parse "$production_commit^{tree}")" = "$production_tree"
shasum -a 256 -c "$script_dir/GENERATED-PROOF.sha256"
shasum -a 256 -c "$script_dir/CALLER-GENERATED.sha256"
shasum -a 256 -c "$script_dir/TOOLCHAIN.sha256"
shasum -a 256 -c "$script_dir/MANIFEST.sha256"

checked_lean_sources=(
  "$script_dir/generated/V7MerkleK12/TypesExternal.lean"
  "$script_dir/generated/V7MerkleK12/Types.lean"
  "$script_dir/generated/V7MerkleK12/FunsExternal.lean"
  "$script_dir/generated/V7MerkleK12/Funs.lean"
  "$script_dir/caller/generated/V7MerkleCaller/TypesExternal.lean"
  "$script_dir/caller/generated/V7MerkleCaller/Types.lean"
  "$script_dir/caller/generated/V7MerkleCaller/FunsExternal.lean"
  "$script_dir/caller/generated/V7MerkleCaller/Funs.lean"
  "$script_dir/caller/proof"
  "$script_dir/proof"
)
if rg -n '\b(sorry|admit|sorryAx|axiom)\b' "${checked_lean_sources[@]}" \
    --glob '*.lean'; then
  echo 'forbidden Lean placeholder or project-specific axiom found in checked bundle source' >&2
  exit 1
fi

case "$(hostname -s)" in
  nuc*) ;;
  *) echo 'full source-to-accepted replay is permitted only on nuc.local' >&2; exit 1 ;;
esac

mem_available_kb=$(awk '/^MemAvailable:/ { print $2 }' /proc/meminfo)
test "$mem_available_kb" -ge 25165824
cgroup_path=$(awk -F: '$1 == "0" { print $3 }' /proc/self/cgroup)
test -n "$cgroup_path"
test "$(tr -d '\n' < "/sys/fs/cgroup$cgroup_path/memory.high")" = 23622320128
test "$(tr -d '\n' < "/sys/fs/cgroup$cgroup_path/memory.max")" = 30064771072
test "$(tr -d '\n' < "/sys/fs/cgroup$cgroup_path/memory.swap.max")" = 0

replay_workspace=$(mktemp -d "$AENEAS_LEAN_BACKEND/v7-merkle-k12-replay.XXXXXX")
source_base=${TMPDIR:-/tmp}
source_base=${source_base%/}
source_workspace=$(mktemp -d "$source_base/v7-merkle-k12-source.XXXXXX")
cleanup() {
  case "$replay_workspace" in
    "$AENEAS_LEAN_BACKEND"/v7-merkle-k12-replay.*)
      rm -rf -- "$replay_workspace"
      ;;
    *)
      echo "refusing unsafe cleanup target: $replay_workspace" >&2
      ;;
  esac
  case "$source_workspace" in
    "$source_base"/v7-merkle-k12-source.*)
      rm -rf -- "$source_workspace"
      ;;
    *)
      echo "refusing unsafe cleanup target: $source_workspace" >&2
      ;;
  esac
}
trap cleanup EXIT

git archive "$production_commit" | tar -x -C "$source_workspace"
(
  cd "$source_workspace"
  shasum -a 256 -c "$script_dir/DEPLOYED-SOURCE.sha256"
)
if rg -n '\b(sorry|admit|sorryAx)\b|^[[:space:]]*axiom\b' \
    "$source_workspace/aeneas-verif/v7-onefold-accepted-source-20260825/parser/generated-exact/V7DeferredParser" \
    "$source_workspace/aeneas-verif/v7-onefold-accepted-source-20260825/parser/proof/V7DeferredParserSourceBridge.lean" \
    --glob '*.lean' --glob '!**/*_Template.lean'; then
  echo 'forbidden Lean placeholder found in source-pinned parser bridge' >&2
  exit 1
fi

cp -R "$script_dir/generated/V7MerkleK12" "$replay_workspace/"
cp -R "$script_dir/caller/generated/V7MerkleCaller" "$replay_workspace/"
patch --fuzz=0 --silent -d "$replay_workspace" -p1 < \
  "$script_dir/toolchain/v7-merkle-caller-generated-compat.patch"
cp "$script_dir/proof/V7MerkleK12SourceBridge.lean" "$replay_workspace/"
cp "$script_dir/proof/V7MerkleK12LayoutBridge.lean" "$replay_workspace/"
cp "$script_dir/proof/V7MerkleK12AcceptedBridge.lean" "$replay_workspace/"
cp "$script_dir/proof/V7MerkleK12TraversalBridge.lean" "$replay_workspace/"
cp "$script_dir/proof/V7MerkleK12InnerTraceBridge.lean" "$replay_workspace/"
cp "$script_dir/proof/V7MerkleK12OuterTraceBridge.lean" "$replay_workspace/"
cp "$script_dir/caller/proof/V7MerkleCallerNamespaceBridge.lean" \
  "$replay_workspace/"
cp "$script_dir/proof/V7MerkleK12CallerBridge.lean" "$replay_workspace/"
cp -R \
  "$source_workspace/aeneas-verif/v7-onefold-accepted-source-20260825/parser/generated-exact/V7DeferredParser" \
  "$replay_workspace/"
cp \
  "$source_workspace/aeneas-verif/v7-onefold-accepted-source-20260825/parser/proof/V7DeferredParserSourceBridge.lean" \
  "$replay_workspace/"
patch --silent -d "$replay_workspace" -p1 < \
  "$script_dir/toolchain/v7-deferred-parser-combined-external.patch"
patch --fuzz=0 --silent -d "$replay_workspace" -p1 < \
  "$script_dir/toolchain/v7-deferred-parser-caller-combined.patch"
mkdir -p "$replay_workspace/AspisFormal/Pool"
for frozen_module in \
    V7MerkleQueryGrammar \
    V7MerkleQueryExtractor \
    V7MerkleParserRoundtrip; do
  cp "$source_workspace/AspisFormal/AspisFormal/Pool/$frozen_module.lean" \
    "$replay_workspace/AspisFormal/Pool/"
done

export LEAN_NUM_THREADS=1
export LEAN_PATH="$AENEAS_LEAN_BACKEND:$replay_workspace"

cd "$AENEAS_LEAN_BACKEND"
for module_name in TypesExternal Types FunsExternal Funs; do
  lake env lean -j1 \
    -o "$replay_workspace/V7MerkleK12/$module_name.olean" \
    "$replay_workspace/V7MerkleK12/$module_name.lean"
done
for caller_module in TypesExternal Types FunsExternal; do
  lake env lean -j1 -R "$replay_workspace" \
    -o "$replay_workspace/V7MerkleCaller/$caller_module.olean" \
    "$replay_workspace/V7MerkleCaller/$caller_module.lean"
done
for parser_module in Types FunsExternal Funs; do
  lake env lean -j1 -R "$replay_workspace" \
    -o "$replay_workspace/V7DeferredParser/$parser_module.olean" \
    "$replay_workspace/V7DeferredParser/$parser_module.lean"
done
lake env lean -j1 -R "$replay_workspace" \
  -o "$replay_workspace/V7MerkleCaller/Funs.olean" \
  "$replay_workspace/V7MerkleCaller/Funs.lean"
lake env lean -j1 -R "$replay_workspace" \
  -o "$replay_workspace/V7DeferredParserSourceBridge.olean" \
  "$replay_workspace/V7DeferredParserSourceBridge.lean"
lake env lean -j1 -R "$replay_workspace" \
  -o "$replay_workspace/V7MerkleCallerNamespaceBridge.olean" \
  "$replay_workspace/V7MerkleCallerNamespaceBridge.lean"
for frozen_module in \
    V7MerkleQueryGrammar \
    V7MerkleQueryExtractor \
    V7MerkleParserRoundtrip; do
  lake env lean -j1 -R "$replay_workspace" \
    -o "$replay_workspace/AspisFormal/Pool/$frozen_module.olean" \
    "$replay_workspace/AspisFormal/Pool/$frozen_module.lean"
done
lake env lean -j1 -R "$replay_workspace" \
  -o "$replay_workspace/V7MerkleK12SourceBridge.olean" \
  "$replay_workspace/V7MerkleK12SourceBridge.lean"
lake env lean -j1 -R "$replay_workspace" \
  -o "$replay_workspace/V7MerkleK12LayoutBridge.olean" \
  "$replay_workspace/V7MerkleK12LayoutBridge.lean"
lake env lean -j1 -R "$replay_workspace" \
  -o "$replay_workspace/V7MerkleK12AcceptedBridge.olean" \
  "$replay_workspace/V7MerkleK12AcceptedBridge.lean"
lake env lean -j1 -R "$replay_workspace" \
  -o "$replay_workspace/V7MerkleK12TraversalBridge.olean" \
  "$replay_workspace/V7MerkleK12TraversalBridge.lean"
lake env lean -j1 -R "$replay_workspace" \
  -o "$replay_workspace/V7MerkleK12InnerTraceBridge.olean" \
  "$replay_workspace/V7MerkleK12InnerTraceBridge.lean"
lake env lean -j1 -R "$replay_workspace" \
  -o "$replay_workspace/V7MerkleK12OuterTraceBridge.olean" \
  "$replay_workspace/V7MerkleK12OuterTraceBridge.lean"
lake env lean -j1 -R "$replay_workspace" \
  "$replay_workspace/V7MerkleK12CallerBridge.lean"

echo 'V7 K1.2 exact translated caller/source layout, traversal, and accepted-predicate replay: PASS'
