#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
: "${AENEAS_LEAN_BACKEND:?set AENEAS_LEAN_BACKEND to the pinned Aeneas backends/lean directory}"
: "${LEAN_BIN:?set LEAN_BIN to the pinned Lean 4.31 binary}"
: "${LAKE_BIN:?set LAKE_BIN to the lake executable}"

test "$("$LEAN_BIN" --version | sed -E 's/^Lean \(version ([^,]+),.*$/\1/')" = 4.31.0
backend_path=$(cd "$AENEAS_LEAN_BACKEND" && "$LAKE_BIN" env printenv LEAN_PATH 2>/dev/null)

replay_base=${TMPDIR:-/tmp}
replay_base=${replay_base%/}
replay_tmp=$(mktemp -d "$replay_base/aspis-v7-literal-metadata-lean.XXXXXX")
cleanup() {
  case "$replay_tmp" in
    "$replay_base"/aspis-v7-literal-metadata-lean.*) rm -rf -- "$replay_tmp" ;;
    *) echo "refusing unsafe cleanup target: $replay_tmp" >&2 ;;
  esac
}
trap cleanup EXIT

cp -R \
  "$script_dir/generated/current309b-readonly-metadata-helper-r1/V7LiteralCallerReadonlyMetadataHelperCurrent309bR1" \
  "$replay_tmp/"
cp -R \
  "$script_dir/generated/current309b-metadata-accountopaque-m31ctor-acceptedtool-r1/V7LiteralCallerCurrent309bMetadataAccountOpaqueAcceptedToolR1" \
  "$replay_tmp/"
cp -R \
  "$script_dir/generated/six-len-preflight-shared-index-r1/V7LiteralCallerExactSixAccountRefsLenPreflightSharedIndexCurrent309bR1" \
  "$replay_tmp/"
cp "$script_dir/proof/V7LiteralCallerReadonlyMetadataExternal.lean" "$replay_tmp/"
cp "$script_dir/proof/V7LiteralCallerReadonlyMetadataBridge.lean" "$replay_tmp/"
cp "$script_dir/proof/V7LiteralCallerReadonlyDataExternal.lean" "$replay_tmp/"
cp "$script_dir/proof/V7LiteralCallerReadonlyDataBridge.lean" "$replay_tmp/"
cp "$script_dir/proof/V7LiteralCallerCorePrimitivesExternal.lean" "$replay_tmp/"
cp "$script_dir/proof/V7LiteralCallerCorePrimitivesBridge.lean" "$replay_tmp/"
cp "$script_dir/proof/V7LiteralCallerExactSixAccountRefsBridge.lean" "$replay_tmp/"

export LEAN_PATH="$replay_tmp:$backend_path"
targets=(
  V7LiteralCallerReadonlyMetadataHelperCurrent309bR1/TypesExternal
  V7LiteralCallerReadonlyMetadataHelperCurrent309bR1/Types
  V7LiteralCallerReadonlyMetadataHelperCurrent309bR1/Funs
  V7LiteralCallerCurrent309bMetadataAccountOpaqueAcceptedToolR1/TypesExternal
  V7LiteralCallerCurrent309bMetadataAccountOpaqueAcceptedToolR1/Types
  V7LiteralCallerReadonlyMetadataExternal
  V7LiteralCallerReadonlyMetadataBridge
  V7LiteralCallerReadonlyDataExternal
  V7LiteralCallerReadonlyDataBridge
  V7LiteralCallerCorePrimitivesExternal
  V7LiteralCallerCorePrimitivesBridge
  V7LiteralCallerExactSixAccountRefsLenPreflightSharedIndexCurrent309bR1/TypesExternal
  V7LiteralCallerExactSixAccountRefsLenPreflightSharedIndexCurrent309bR1/Types
  V7LiteralCallerExactSixAccountRefsLenPreflightSharedIndexCurrent309bR1/Funs
  V7LiteralCallerExactSixAccountRefsBridge
)
for target in "${targets[@]}"; do
  echo "LEAN_TARGET=$target"
  "$LEAN_BIN" -R "$replay_tmp" -o "$replay_tmp/$target.olean" "$replay_tmp/$target.lean"
done

echo 'V7 literal readonly-metadata, core-primitives, and exact-six Lean replay: PASS'
