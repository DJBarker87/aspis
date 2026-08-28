#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(CDPATH= cd -- "$script_dir/../.." && pwd)

: "${AENEAS_LEAN_BACKEND:?set AENEAS_LEAN_BACKEND to the pinned Aeneas backends/lean directory}"
: "${ASPIS_EXACT_K12_OLEAN_ROOT:?set ASPIS_EXACT_K12_OLEAN_ROOT to the focused AspisFormal build lib/lean directory}"

test -d "$AENEAS_LEAN_BACKEND"
test -f "$AENEAS_LEAN_BACKEND/lakefile.lean"
test -f "$ASPIS_EXACT_K12_OLEAN_ROOT/AspisFormal/K1/V7Tag73ExactConcreteK12Bound.olean"
command -v lake >/dev/null
command -v mktemp >/dev/null
command -v patch >/dev/null
command -v rg >/dev/null
command -v shasum >/dev/null

cd "$repo_root"
shasum -a 256 -c "$script_dir/GENERATED-PROOF.sha256"
shasum -a 256 -c "$script_dir/CALLER-GENERATED.sha256"
shasum -a 256 -c "$script_dir/TOOLCHAIN.sha256"

checked_sources=(
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
if rg -n '\b(sorry|admit|sorryAx|native_decide)\b|^[[:space:]]*axiom\b' \
    "${checked_sources[@]}" --glob '*.lean'; then
  echo 'forbidden Lean placeholder, native_decide, or project axiom found' >&2
  exit 1
fi

case "$(hostname -s)" in
  nuc*) ;;
  *) echo 'exact K1.2 integration replay is permitted only on nuc.local' >&2; exit 1 ;;
esac

cgroup_path=$(awk -F: '$1 == "0" { print $3 }' /proc/self/cgroup)
test -n "$cgroup_path"
test "$(tr -d '\n' < "/sys/fs/cgroup$cgroup_path/memory.high")" = 23622320128
test "$(tr -d '\n' < "/sys/fs/cgroup$cgroup_path/memory.max")" = 30064771072
test "$(tr -d '\n' < "/sys/fs/cgroup$cgroup_path/memory.swap.max")" = 0

replay_workspace=$(mktemp -d "$AENEAS_LEAN_BACKEND/v7-merkle-k12-exact-integration.XXXXXX")
cleanup() {
  if test "${ASPIS_KEEP_REPLAY:-0}" = 1; then
    echo "retained replay workspace: $replay_workspace"
    return
  fi
  case "$replay_workspace" in
    "$AENEAS_LEAN_BACKEND"/v7-merkle-k12-exact-integration.*)
      rm -rf -- "$replay_workspace"
      ;;
    *)
      echo "refusing unsafe cleanup target: $replay_workspace" >&2
      ;;
  esac
}
trap cleanup EXIT

cp -R "$script_dir/generated/V7MerkleK12" "$replay_workspace/"
cp -R "$script_dir/caller/generated/V7MerkleCaller" "$replay_workspace/"
patch --fuzz=0 --silent -d "$replay_workspace" -p1 < \
  "$script_dir/toolchain/v7-merkle-caller-generated-compat.patch"
cp -R \
  "$repo_root/aeneas-verif/v7-onefold-accepted-source-20260825/parser/generated-exact/V7DeferredParser" \
  "$replay_workspace/"
cp \
  "$repo_root/aeneas-verif/v7-onefold-accepted-source-20260825/parser/proof/V7DeferredParserSourceBridge.lean" \
  "$replay_workspace/"
patch --silent -d "$replay_workspace" -p1 < \
  "$script_dir/toolchain/v7-deferred-parser-combined-external.patch"
patch --fuzz=0 --silent -d "$replay_workspace" -p1 < \
  "$script_dir/toolchain/v7-deferred-parser-caller-combined.patch"
cp "$script_dir/proof/V7MerkleK12SourceBridge.lean" "$replay_workspace/"
cp "$script_dir/proof/V7MerkleK12LayoutBridge.lean" "$replay_workspace/"
cp "$script_dir/proof/V7MerkleK12AcceptedBridge.lean" "$replay_workspace/"
cp "$script_dir/proof/V7MerkleK12TraversalBridge.lean" "$replay_workspace/"
cp "$script_dir/proof/V7MerkleK12InnerTraceBridge.lean" "$replay_workspace/"
cp "$script_dir/proof/V7MerkleK12OuterTraceBridge.lean" "$replay_workspace/"
cp "$script_dir/caller/proof/V7MerkleCallerNamespaceBridge.lean" "$replay_workspace/"
cp "$script_dir/proof/V7MerkleK12CallerBridge.lean" "$replay_workspace/"
cp "$script_dir/proof/V7MerkleK12ExactK12Integration.lean" "$replay_workspace/"

mkdir -p "$replay_workspace/AspisFormal/Pool"
for frozen_module in \
    V7MerkleQueryGrammar \
    V7MerkleQueryExtractor \
    V7MerkleParserRoundtrip; do
  cp "$repo_root/AspisFormal/AspisFormal/Pool/$frozen_module.lean" \
    "$replay_workspace/AspisFormal/Pool/"
done

export LEAN_NUM_THREADS=1
export LEAN_PATH="$AENEAS_LEAN_BACKEND:$ASPIS_EXACT_K12_OLEAN_ROOT:$replay_workspace"

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
for proof_module in \
    V7MerkleK12SourceBridge \
    V7MerkleK12LayoutBridge \
    V7MerkleK12AcceptedBridge \
    V7MerkleK12TraversalBridge \
    V7MerkleK12InnerTraceBridge \
    V7MerkleK12OuterTraceBridge \
    V7MerkleK12CallerBridge; do
  lake env lean -j1 -R "$replay_workspace" \
    -o "$replay_workspace/$proof_module.olean" \
    "$replay_workspace/$proof_module.lean"
done
lake env lean -j1 \
  -o "$replay_workspace/V7MerkleK12ExactK12Integration.olean" \
  "$replay_workspace/V7MerkleK12ExactK12Integration.lean"

echo 'V7 literal Merkle caller to maintained exact K1.2 obligations replay: PASS'
