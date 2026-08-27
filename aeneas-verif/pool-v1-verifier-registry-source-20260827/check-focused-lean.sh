#!/usr/bin/env bash
set -euo pipefail

readonly bundle=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
readonly repo=$(cd "$bundle/../.." && pwd -P)
readonly generated="$bundle/generated"
readonly proof="$bundle/proof"

readonly lean_bin="${LEAN_BIN:?set LEAN_BIN to Lean 4.32.0}"
readonly aeneas_lean_root="${AENEAS_LEAN_ROOT:?set AENEAS_LEAN_ROOT}"
readonly lean_out="${REGISTRY_LEAN_OUT:?set REGISTRY_LEAN_OUT to a new output directory}"

case "$($lean_bin --version)" in
  "Lean (version 4.32.0,"*) ;;
  *) echo "expected Lean 4.32.0" >&2; exit 1 ;;
esac

[[ -f "$aeneas_lean_root/.lake/build/lib/lean/Aeneas/Std.olean" ]]
if [[ -e "$lean_out" ]]; then
  [[ -d "$lean_out" ]]
  [[ -z "$(find "$lean_out" -mindepth 1 -maxdepth 1 -print -quit)" ]]
else
  mkdir -p "$lean_out"
fi
mkdir -p "$lean_out/VerifierRegistryDecoders"
mkdir -p "$lean_out/VerifierRegistryReadonly"

readonly formal_lean_path=${FORMAL_LEAN_PATH:-$(
  cd "$repo/AspisFormal" && lake env printenv LEAN_PATH
)}
export LEAN_NUM_THREADS=1
export LEAN_PATH="$lean_out:$generated:$proof:$aeneas_lean_root/.lake/build/lib/lean:$formal_lean_path"

compile() {
  local source=$1 output=$2
  "$lean_bin" -o "$output" "$source"
}

compile "$generated/VerifierRegistryDecoders/Types.lean" \
  "$lean_out/VerifierRegistryDecoders/Types.olean"
compile "$generated/VerifierRegistryDecoders/FunsExternal.lean" \
  "$lean_out/VerifierRegistryDecoders/FunsExternal.olean"
compile "$generated/VerifierRegistryDecoders/Funs.lean" \
  "$lean_out/VerifierRegistryDecoders/Funs.olean"
compile "$generated/VerifierRegistryReadonly/Funs.lean" \
  "$lean_out/VerifierRegistryReadonly/Funs.olean"
compile "$proof/PoolV1VerifierRegistrySourceBridge.lean" \
  "$lean_out/PoolV1VerifierRegistrySourceBridge.olean"

if rg -n \
    '(^|[[:space:]])(sorry|admit|native_decide)([[:space:]]|$)|^[[:space:]]*axiom([[:space:]]|$)' \
    "$generated" "$proof"; then
  echo "forbidden proof escape found" >&2
  exit 1
fi

echo "Pool V1 verifier-registry focused Lean replay: PASS"
