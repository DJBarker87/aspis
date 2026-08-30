#!/usr/bin/env bash
set -euo pipefail

readonly lean_root="${1:?pass the generated Lean module root}"
readonly aeneas_backend="${2:?pass the pinned Aeneas Lean backend}"
readonly aspis_formal_project="${3:-}"
readonly lake_bin="${LAKE_BIN:-$(command -v lake)}"

cd "$aeneas_backend"
readonly backend_path="$($lake_bin env printenv LEAN_PATH)"
if [[ -n "$aspis_formal_project" ]]; then
  test -f "$aspis_formal_project/lakefile.toml"
  cd "$aspis_formal_project"
  readonly aspis_path="$($lake_bin env printenv LEAN_PATH)"
  export LEAN_PATH="$lean_root:$aspis_path:$backend_path"
else
  export LEAN_PATH="$lean_root:$backend_path"
fi
readonly lean_bin="${LEAN_BIN:-$(command -v lean)}"
cd "$lean_root"

"$lean_bin" -o V7BinaryFrontier/TypesExternal.olean \
  V7BinaryFrontier/TypesExternal.lean
"$lean_bin" -o V7BinaryFrontier/Types.olean \
  V7BinaryFrontier/Types.lean
"$lean_bin" -o V7BinaryFrontier/FunsExternal.olean \
  V7BinaryFrontier/FunsExternal.lean
"$lean_bin" -o V7BinaryFrontier/Funs.olean \
  V7BinaryFrontier/Funs.lean
if [[ -f V7BinaryFrontierBodyBridge.lean ]]; then
  "$lean_bin" -o V7BinaryFrontierBodyBridge.olean \
    V7BinaryFrontierBodyBridge.lean
fi
if [[ -f V7BinaryFrontierLoopBridge.lean ]]; then
  "$lean_bin" -o V7BinaryFrontierLoopBridge.olean \
    V7BinaryFrontierLoopBridge.lean
fi
if [[ -f V7BinaryFrontierSortModel.lean ]]; then
  "$lean_bin" -o V7BinaryFrontierSortModel.olean \
    V7BinaryFrontierSortModel.lean
fi
if [[ -f V7BinaryFrontierSortSourceBridge.lean ]]; then
  "$lean_bin" -o V7BinaryFrontierSortSourceBridge.olean \
    V7BinaryFrontierSortSourceBridge.lean
fi
if [[ -f V7BinaryFrontierK13Integration.lean ]]; then
  test -n "$aspis_formal_project"
  "$lean_bin" -o V7BinaryFrontierK13Integration.olean \
    V7BinaryFrontierK13Integration.lean
fi

if [[ -d V7FirstCompact ]]; then
  "$lean_bin" -o V7FirstCompact/TypesExternal.olean \
    V7FirstCompact/TypesExternal.lean
  "$lean_bin" -o V7FirstCompact/Types.olean \
    V7FirstCompact/Types.lean
  "$lean_bin" -o V7FirstCompact/FunsExternal.olean \
    V7FirstCompact/FunsExternal.lean
  "$lean_bin" -o V7FirstCompact/Funs.olean \
    V7FirstCompact/Funs.lean
fi

for caller_bridge in \
  V7FirstCompactFrontierBodyBridge \
  V7FirstCompactFrontierLoopBridge \
  V7FirstCompactFrontierSortSourceBridge \
  V7FirstCompactFrontierK13Integration \
  V7FirstCompactCallerBridge \
  V7FirstCompactK13RawScheduleBridge
do
  if [[ -f "$caller_bridge.lean" ]]; then
    test -n "$aspis_formal_project"
    "$lean_bin" -o "$caller_bridge.olean" "$caller_bridge.lean"
  fi
done
