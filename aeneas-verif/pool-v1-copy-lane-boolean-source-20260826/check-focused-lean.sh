#!/usr/bin/env bash
set -euo pipefail

readonly bundle=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
readonly repo=$(cd "$bundle/../.." && pwd -P)
readonly generated="$bundle/generated"
readonly proof="$bundle/proof"
readonly arithmetic="$repo/aeneas-verif/component-b-weight-at/arithmetic-lean432"

readonly lean_bin="${LEAN_BIN:?set LEAN_BIN to Lean 4.32.0}"
readonly aeneas_lean_root="${AENEAS_LEAN_ROOT:?set AENEAS_LEAN_ROOT}"
readonly out="${COPY_LANE_LEAN_OUT:?set COPY_LANE_LEAN_OUT to a new output directory}"
readonly target="${COPY_LANE_LEAN_TARGET:-root}"

case "$($lean_bin --version)" in
  "Lean (version 4.32.0,"*) ;;
  *) echo "expected Lean 4.32.0" >&2; exit 1 ;;
esac

[[ -f "$aeneas_lean_root/.lake/build/lib/lean/Aeneas/Std.olean" ]]
[[ "$target" == generated || "$target" == root || "$target" == field ||
   "$target" == source ]]
if [[ -e "$out" ]]; then
  [[ -d "$out" ]]
  [[ -z "$(find "$out" -mindepth 1 -maxdepth 1 -print -quit)" ]]
else
  mkdir -p "$out"
fi
mkdir -p "$out/PoolV1CopyLaneBooleanGenerated"

readonly formal_lean_path=${FORMAL_LEAN_PATH:-$(
  cd "$repo/AspisFormal" && lake env printenv LEAN_PATH
)}
export LEAN_NUM_THREADS=1
export LEAN_PATH="$out:$generated:$proof:$arithmetic:$aeneas_lean_root/.lake/build/lib/lean:$formal_lean_path"

compile() {
  local source=$1 output=$2
  "$lean_bin" -o "$output" "$source"
}

compile \
  "$generated/PoolV1CopyLaneBooleanGenerated/Types.lean" \
  "$out/PoolV1CopyLaneBooleanGenerated/Types.olean"
while IFS= read -r source; do
  module=$(basename "$source" .lean)
  compile "$source" \
    "$out/PoolV1CopyLaneBooleanGenerated/$module.olean"
done < <(printf '%s\n' \
  "$generated"/PoolV1CopyLaneBooleanGenerated/FunsPart*.lean | sort -V)
compile "$generated/PoolV1CopyLaneBooleanGenerated/Funs.lean" \
  "$out/PoolV1CopyLaneBooleanGenerated/Funs.olean"
if [[ "$target" != generated ]]; then
  compile "$proof/PoolV1CopyLaneBooleanRoot.lean" \
    "$out/PoolV1CopyLaneBooleanRoot.olean"
fi

if [[ "$target" == field || "$target" == source ]]; then
  compile "$proof/PoolV1CopyLaneBooleanFieldSemantics.lean" \
    "$out/PoolV1CopyLaneBooleanFieldSemantics.olean"
fi
if [[ "$target" == source ]]; then
  compile "$proof/PoolV1CopyLaneBooleanSourceBridge.lean" \
    "$out/PoolV1CopyLaneBooleanSourceBridge.olean"
fi

if rg -n '\b(sorry|admit|axiom|native_decide)\b' "$proof"; then
  echo "forbidden proof escape found" >&2
  exit 1
fi

echo "native Pool V1 Boolean Copy-lane focused Lean target '$target': PASS"
