#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
: "${AENEAS_LEAN_BACKEND:?set AENEAS_LEAN_BACKEND to the pinned Aeneas backends/lean directory}"
: "${LAKE_BIN:?set LAKE_BIN to the Lean 4.31 lake binary}"

replay_base=${TMPDIR:-/tmp}
replay_base=${replay_base%/}
replay_tmp=$(mktemp -d "$replay_base/aspis-v7-selected-terminal-lean.XXXXXX")
cleanup() {
  case "$replay_tmp" in
    "$replay_base"/aspis-v7-selected-terminal-lean.*) rm -rf -- "$replay_tmp" ;;
    *) echo "refusing unsafe cleanup target: $replay_tmp" >&2 ;;
  esac
}
trap cleanup EXIT

cp -R "$script_dir/generated/V7Tag73SelectedSemanticLoopForm" "$replay_tmp/"
cp "$script_dir/proof/V7SelectedSemanticRootBridge.lean" "$replay_tmp/"

! grep -REn '(^|[[:space:]])(sorry|admit|native_decide)([[:space:]]|$)' \
  "$replay_tmp" --include='*.lean'
! grep -REn '^[[:space:]]*(axiom|opaque)[[:space:]]' \
  "$replay_tmp/V7Tag73SelectedSemanticLoopForm/TypesExternal.lean" \
  "$replay_tmp/V7Tag73SelectedSemanticLoopForm/FunsExternal.lean" \
  "$replay_tmp/V7SelectedSemanticRootBridge.lean"

(
  cd "$AENEAS_LEAN_BACKEND"
  export LEAN_PATH="$replay_tmp"
  "$LAKE_BIN" env lean \
    -R "$replay_tmp" \
    -o "$replay_tmp/V7Tag73SelectedSemanticLoopForm/TypesExternal.olean" \
    "$replay_tmp/V7Tag73SelectedSemanticLoopForm/TypesExternal.lean"
  "$LAKE_BIN" env lean \
    -R "$replay_tmp" \
    -o "$replay_tmp/V7Tag73SelectedSemanticLoopForm/Types.olean" \
    "$replay_tmp/V7Tag73SelectedSemanticLoopForm/Types.lean"
  "$LAKE_BIN" env lean \
    -R "$replay_tmp" \
    -o "$replay_tmp/V7Tag73SelectedSemanticLoopForm/FunsExternal.olean" \
    "$replay_tmp/V7Tag73SelectedSemanticLoopForm/FunsExternal.lean"
  "$LAKE_BIN" env lean \
    -R "$replay_tmp" \
    -o "$replay_tmp/V7Tag73SelectedSemanticLoopForm/Funs.olean" \
    "$replay_tmp/V7Tag73SelectedSemanticLoopForm/Funs.lean"
  "$LAKE_BIN" env lean -R "$replay_tmp" \
    -o "$replay_tmp/V7SelectedSemanticRootBridge.olean" \
    "$replay_tmp/V7SelectedSemanticRootBridge.lean"
)

echo 'V7 selected semantic terminal Lean replay: PASS'
