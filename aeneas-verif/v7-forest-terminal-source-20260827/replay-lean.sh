#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
: "${AENEAS_LEAN_BACKEND:?set AENEAS_LEAN_BACKEND to the pinned Aeneas Lean backend}"

test -f "$AENEAS_LEAN_BACKEND/lakefile.lean" -o \
  -f "$AENEAS_LEAN_BACKEND/lakefile.toml"
replay_tmp=$(mktemp -d "$AENEAS_LEAN_BACKEND/aspis-v7-forest-terminal.XXXXXX")
cleanup() {
  case "$replay_tmp" in
    "$AENEAS_LEAN_BACKEND"/aspis-v7-forest-terminal.*) rm -rf -- "$replay_tmp" ;;
    *) echo "refusing unsafe cleanup target: $replay_tmp" >&2 ;;
  esac
}
trap cleanup EXIT

cp -R "$script_dir/generated/V7ForestTerminal" "$replay_tmp/"
cp "$script_dir/proof/V7ForestTerminalLayoutBridge.lean" "$replay_tmp/"
cp "$script_dir/proof/V7ForestTerminalParserBridge.lean" "$replay_tmp/"
cp "$script_dir/proof/V7ForestTerminalCallerBridge.lean" "$replay_tmp/"

export LEAN_NUM_THREADS=1
export LEAN_PATH="$replay_tmp:$AENEAS_LEAN_BACKEND/.lake/build/lib/lean"

compile() {
  source_file=$1
  output_file=${source_file%.lean}.olean
  (cd "$AENEAS_LEAN_BACKEND" &&
    lake env lean -j1 -o "$output_file" "$source_file")
}

compile "$replay_tmp/V7ForestTerminal/TypesExternal.lean"
compile "$replay_tmp/V7ForestTerminal/Types.lean"
compile "$replay_tmp/V7ForestTerminal/FunsExternal.lean"
compile "$replay_tmp/V7ForestTerminal/Funs.lean"
compile "$replay_tmp/V7ForestTerminalLayoutBridge.lean"
compile "$replay_tmp/V7ForestTerminalParserBridge.lean"
compile "$replay_tmp/V7ForestTerminalCallerBridge.lean"

echo 'V7 forest terminal Rust-to-Lean source replay: PASS'
