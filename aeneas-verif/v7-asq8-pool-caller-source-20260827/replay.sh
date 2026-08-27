#!/usr/bin/env bash
set -euo pipefail

bundle_root="$(cd "$(dirname "$0")" && pwd)"
backend="${AENEAS_LEAN_BACKEND:?set AENEAS_LEAN_BACKEND to the pinned Aeneas backends/lean directory}"
lean="${LEAN_BIN:-$HOME/.elan/bin/lake}"
stage="$(mktemp -d "$backend/aspis-asq8-caller-replay.XXXXXX")"
trap 'rm -rf "$stage"' EXIT

(cd "$bundle_root" && shasum -a 256 -c evidence/SHA256SUMS)

if rg -n '\b(sorry|admit|native_decide)\b|sorryAx' "$bundle_root" \
    --glob '*.lean'; then
  echo "forbidden proof construct found" >&2
  exit 1
fi

mkdir -p "$stage/ASQ8Dispatch" "$stage/ASQ8NextLane"
cp "$bundle_root/generated/ASQ8Dispatch/"*.lean "$stage/ASQ8Dispatch/"
cp "$bundle_root/generated/ASQ8NextLane/"*.lean "$stage/ASQ8NextLane/"
cp "$bundle_root/proof/"*.lean "$stage/"

run_lean() {
  local source="$1"
  local output="$2"
  (cd "$backend" && env LEAN_PATH="$stage:." "$lean" env lean \
    -o "$output" "$source")
}

run_lean "$stage/ASQ8Dispatch/TypesExternal.lean" \
  "$stage/ASQ8Dispatch/TypesExternal.olean"
run_lean "$stage/ASQ8Dispatch/Types.lean" \
  "$stage/ASQ8Dispatch/Types.olean"
run_lean "$stage/ASQ8Dispatch/FunsExternal.lean" \
  "$stage/ASQ8Dispatch/FunsExternal.olean"
run_lean "$stage/ASQ8Dispatch/Funs.lean" \
  "$stage/ASQ8Dispatch/Funs.olean"

run_lean "$stage/ASQ8NextLane/Types.lean" \
  "$stage/ASQ8NextLane/Types.olean"
run_lean "$stage/ASQ8NextLane/FunsExternal.lean" \
  "$stage/ASQ8NextLane/FunsExternal.olean"
run_lean "$stage/ASQ8NextLane/Funs.lean" \
  "$stage/ASQ8NextLane/Funs.olean"

run_lean "$stage/ASQ8DispatchSourceBridge.lean" \
  "$stage/ASQ8DispatchSourceBridge.olean"
run_lean "$stage/ASQ8NextLaneSourceBridge.lean" \
  "$stage/ASQ8NextLaneSourceBridge.olean"
run_lean "$stage/ASQ8CallerWriteOrderBridge.lean" \
  "$stage/ASQ8CallerWriteOrderBridge.olean"
(cd "$backend" && env LEAN_PATH="$stage:." "$lean" env lean \
  "$stage/ASQ8Axioms.lean")

echo "V7 ASQ8 Pool caller source replay: PASS"
