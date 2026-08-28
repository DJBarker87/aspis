#!/usr/bin/env bash
set -euo pipefail

readonly lean_root="${1:?pass the generated Lean module root}"
readonly aeneas_backend="${2:?pass the pinned Aeneas Lean backend}"
readonly lake_bin="${LAKE_BIN:-/home/dombarker/.elan/bin/lake}"

cd "$aeneas_backend"
readonly backend_path="$($lake_bin env printenv LEAN_PATH)"
export LEAN_PATH="$lean_root:$backend_path"
readonly lean_bin="$HOME/.elan/toolchains/leanprover--lean4---v4.31.0/bin/lean"
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
