#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
: "${AENEAS_LEAN_BACKEND:?set AENEAS_LEAN_BACKEND to the Aeneas Lean backend}"
: "${LEAN_BIN:?set LEAN_BIN to the pinned Lean 4.31 binary}"

test -x "$LEAN_BIN"
test "$($LEAN_BIN --version | sed -E 's/^Lean \(version ([^,]+),.*$/\1/')" = '4.31.0'
backend_path=$(cd "$AENEAS_LEAN_BACKEND" && lake env printenv LEAN_PATH 2>/dev/null)
replay_base=${TMPDIR:-/tmp}
replay_base=${replay_base%/}
work_tmp=$(mktemp -d "$replay_base/aspis-v7-pool-caller-lean.XXXXXX")
cleanup() {
  case "$work_tmp" in
    "$replay_base"/aspis-v7-pool-caller-lean.*) rm -rf -- "$work_tmp" ;;
    *) echo "refusing unsafe cleanup target: $work_tmp" >&2 ;;
  esac
}
trap cleanup EXIT

cp -R "$script_dir/generated/V7PoolOneTerminalCaller" "$work_tmp/"
cp "$script_dir/proof/V7PoolOneTerminalCallerSourceBridge.lean" "$work_tmp/"
find "$work_tmp" -type f -name '*.olean' -delete

export LEAN_NUM_THREADS=1
export LEAN_PATH="$backend_path:$work_tmp"

"$LEAN_BIN" -DmaxHeartbeats=8000000 -DmaxRecDepth=16000 \
  --root="$work_tmp" \
  -o "$work_tmp/V7PoolOneTerminalCaller/Types.olean" \
  "$work_tmp/V7PoolOneTerminalCaller/Types.lean"
"$LEAN_BIN" -DmaxHeartbeats=8000000 -DmaxRecDepth=16000 \
  --root="$work_tmp" \
  -o "$work_tmp/V7PoolOneTerminalCaller/FunsExternal.olean" \
  "$work_tmp/V7PoolOneTerminalCaller/FunsExternal.lean"
"$LEAN_BIN" -DmaxHeartbeats=8000000 -DmaxRecDepth=16000 \
  --root="$work_tmp" \
  -o "$work_tmp/V7PoolOneTerminalCaller/Funs.olean" \
  "$work_tmp/V7PoolOneTerminalCaller/Funs.lean"
"$LEAN_BIN" -DmaxHeartbeats=8000000 -DmaxRecDepth=16000 \
  --root="$work_tmp" \
  "$work_tmp/V7PoolOneTerminalCallerSourceBridge.lean"

if rg -n '\b(sorry|admit|native_decide)\b|^[[:space:]]*axiom[[:space:]]' \
    "$work_tmp/V7PoolOneTerminalCaller/Types.lean" \
    "$work_tmp/V7PoolOneTerminalCaller/Funs.lean" \
    "$work_tmp/V7PoolOneTerminalCaller/FunsExternal.lean" \
    "$work_tmp/V7PoolOneTerminalCallerSourceBridge.lean"; then
  echo 'forbidden compiled Lean construct found' >&2
  exit 1
fi

echo 'V7 Pool one-terminal Lean source replay: PASS'
