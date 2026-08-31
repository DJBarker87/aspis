#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
: "${AENEAS_LEAN_BACKEND:?set AENEAS_LEAN_BACKEND to the Aeneas Lean backend}"
: "${LEAN_BIN:?set LEAN_BIN to the pinned Lean 4.31 binary}"

test -x "$LEAN_BIN"
test "$("$LEAN_BIN" --version | sed -E 's/^Lean \(version ([^,]+),.*$/\1/')" = 4.31.0
backend_path=$(cd "$AENEAS_LEAN_BACKEND" && lake env printenv LEAN_PATH 2>/dev/null)
fixed_module_dir="$script_dir/../v7-registry-v2-one-terminal-caller-source-20260831/generated/V7RegistryV2OneTerminalCaller"
test -f "$fixed_module_dir/Types.lean"

replay_base=${TMPDIR:-/tmp}
replay_base=${replay_base%/}
work_tmp=$(mktemp -d "$replay_base/aspis-v7-registry-v2-accountinfo-lean.XXXXXX")
cleanup() {
  case "$work_tmp" in
    "$replay_base"/aspis-v7-registry-v2-accountinfo-lean.*) rm -rf -- "$work_tmp" ;;
    *) echo "refusing unsafe cleanup target: $work_tmp" >&2 ;;
  esac
}
trap cleanup EXIT

cp -R "$script_dir/generated/V7RegistryV2ProductionCodecs" "$work_tmp/"
cp -R "$script_dir/generated/V7RegistryV2ProductionReadonly" "$work_tmp/"
cp -R "$fixed_module_dir" "$work_tmp/"
cp "$script_dir/proof/V7RegistryV2AccountInfoProjectionBridge.lean" "$work_tmp/"
find "$work_tmp" -type f -name '*.olean' -delete

export LEAN_NUM_THREADS=1
export LEAN_PATH="$backend_path:$work_tmp"

run_module() {
  local source=$1 output=${1%.lean}.olean
  "$LEAN_BIN" -DmaxHeartbeats=8000000 -DmaxRecDepth=16000 \
    --root="$work_tmp" -o "$output" "$source"
}

run_module "$work_tmp/V7RegistryV2OneTerminalCaller/Types.lean"
run_module "$work_tmp/V7RegistryV2ProductionCodecs/Types.lean"
run_module "$work_tmp/V7RegistryV2ProductionCodecs/FunsExternal.lean"
run_module "$work_tmp/V7RegistryV2ProductionCodecs/Funs.lean"
run_module "$work_tmp/V7RegistryV2ProductionReadonly/TypesExternal.lean"
run_module "$work_tmp/V7RegistryV2ProductionReadonly/Types.lean"
run_module "$work_tmp/V7RegistryV2ProductionReadonly/FunsExternal.lean"
run_module "$work_tmp/V7RegistryV2ProductionReadonly/Funs.lean"
"$LEAN_BIN" -DmaxHeartbeats=8000000 -DmaxRecDepth=16000 \
  --root="$work_tmp" \
  "$work_tmp/V7RegistryV2AccountInfoProjectionBridge.lean"

if rg -n '\b(sorry|admit|native_decide)\b|^[[:space:]]*axiom[[:space:]]' \
    "$work_tmp/V7RegistryV2OneTerminalCaller/Types.lean" \
    "$work_tmp/V7RegistryV2ProductionCodecs/Types.lean" \
    "$work_tmp/V7RegistryV2ProductionCodecs/FunsExternal.lean" \
    "$work_tmp/V7RegistryV2ProductionCodecs/Funs.lean" \
    "$work_tmp/V7RegistryV2ProductionReadonly/TypesExternal.lean" \
    "$work_tmp/V7RegistryV2ProductionReadonly/Types.lean" \
    "$work_tmp/V7RegistryV2ProductionReadonly/FunsExternal.lean" \
    "$work_tmp/V7RegistryV2ProductionReadonly/Funs.lean" \
    "$work_tmp/V7RegistryV2AccountInfoProjectionBridge.lean"; then
  echo 'forbidden compiled Lean construct found' >&2
  exit 1
fi

echo 'V7 Registry V2 AccountInfo projection Lean replay: PASS'
