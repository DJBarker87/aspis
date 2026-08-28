#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
: "${AENEAS_LEAN_BACKEND:?set AENEAS_LEAN_BACKEND to the Aeneas Lean backend}"

test -f "$AENEAS_LEAN_BACKEND/lakefile.lean" -o \
  -f "$AENEAS_LEAN_BACKEND/lakefile.toml"
work_tmp=$(mktemp -d "$AENEAS_LEAN_BACKEND/aspis-v7-lane-invariant.XXXXXX")
cleanup() {
  case "$work_tmp" in
    "$AENEAS_LEAN_BACKEND"/aspis-v7-lane-invariant.*) rm -rf -- "$work_tmp" ;;
    *) echo "refusing unsafe cleanup target: $work_tmp" >&2 ;;
  esac
}
trap cleanup EXIT

cp -R "$script_dir/generated/V7ForestLaneInvariant" "$work_tmp/"
cp "$script_dir"/proof/*.lean "$work_tmp/"

export LEAN_NUM_THREADS=1
export LEAN_PATH="$work_tmp:$AENEAS_LEAN_BACKEND/.lake/build/lib/lean"

compile() {
  source_file=$1
  output_file=${source_file%.lean}.olean
  (cd "$AENEAS_LEAN_BACKEND" &&
    lake env lean -j1 --root="$work_tmp" -o "$output_file" "$source_file")
}

compile "$work_tmp/V7ForestLaneInvariant/Types.lean"
compile "$work_tmp/V7ForestLaneInvariant/FunsExternal.lean"
compile "$work_tmp/V7ForestLaneInvariant/Funs.lean"
compile "$work_tmp/V7ForestLaneEncoderBridge.lean"
compile "$work_tmp/V7ForestLaneHotDecodeBridge.lean"
compile "$work_tmp/V7ForestLaneWriterInvariant.lean"
compile "$work_tmp/V7ForestLaneCallerBridge.lean"
compile "$work_tmp/V7ForestVerifierAsq8ReaderBridge.lean"
compile "$work_tmp/V7SelectedTerminalCutsBridge.lean"
compile "$work_tmp/V7EndpointSelectorCacheBridge.lean"

if rg -n '\b(sorry|admit|native_decide)\b|^[[:space:]]*axiom[[:space:]]' \
    "$work_tmp/V7ForestLaneInvariant/Types.lean" \
    "$work_tmp/V7ForestLaneInvariant/Funs.lean" \
    "$work_tmp/V7ForestLaneInvariant/FunsExternal.lean" \
    "$work_tmp"/V7ForestLane*Bridge.lean \
    "$work_tmp/V7ForestVerifierAsq8ReaderBridge.lean" \
    "$work_tmp/V7SelectedTerminalCutsBridge.lean" \
    "$work_tmp/V7EndpointSelectorCacheBridge.lean" \
    "$work_tmp/V7ForestLaneWriterInvariant.lean"; then
  echo 'forbidden compiled Lean construct found' >&2
  exit 1
fi

echo 'V7 forest lane invariant Lean source replay: PASS'
