#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
: "${AENEAS_LEAN_BACKEND:?set AENEAS_LEAN_BACKEND to the Aeneas Lean backend}"
: "${LEAN_BIN:?set LEAN_BIN to the pinned Lean 4.31 binary}"

test -x "$LEAN_BIN"
test "$("$LEAN_BIN" --version | sed -E 's/^Lean \(version ([^,]+),.*$/\1/')" = 4.31.0
backend_path=$(cd "$AENEAS_LEAN_BACKEND" && lake env printenv LEAN_PATH 2>/dev/null)
accountinfo_bundle="$script_dir/../v7-registry-v2-accountinfo-correspondence-20260831"
caller_bundle="$script_dir/../v7-registry-v2-one-terminal-caller-source-20260831"

replay_base=${TMPDIR:-/tmp}
replay_base=${replay_base%/}
work_tmp=$(mktemp -d "$replay_base/aspis-v7-registry-v2-deployment-lean.XXXXXX")
cleanup() {
  if [ "${KEEP_REPLAY_TMP:-0}" = 1 ]; then
    echo "retained replay workspace: $work_tmp" >&2
    return
  fi
  case "$work_tmp" in
    "$replay_base"/aspis-v7-registry-v2-deployment-lean.*) rm -rf -- "$work_tmp" ;;
    *) echo "refusing unsafe cleanup target: $work_tmp" >&2 ;;
  esac
}
trap cleanup EXIT

cp -R "$caller_bundle/generated/V7RegistryV2OneTerminalCaller" "$work_tmp/"
cp -R "$accountinfo_bundle/generated/V7RegistryV2ProductionCodecs" "$work_tmp/"
cp -R "$accountinfo_bundle/generated/V7RegistryV2ProductionReadonly" "$work_tmp/"
cp -R "$script_dir/generated/V7RegistryV2DeploymentCertificate" "$work_tmp/"
cp "$caller_bundle/proof/V7RegistryV2OneTerminalCallerSourceBridge.lean" "$work_tmp/"
cp "$accountinfo_bundle/proof/V7RegistryV2AccountInfoProjectionBridge.lean" "$work_tmp/"
cp "$script_dir/proof/V7RegistryV2DeploymentCertificateSourceBridge.lean" "$work_tmp/"
find "$work_tmp" -type f -name '*.olean' -delete

export LEAN_NUM_THREADS=1
export LEAN_PATH="$backend_path:$work_tmp"

run_module() {
  local source=$1 output=${1%.lean}.olean
  "$LEAN_BIN" -DmaxHeartbeats=8000000 -DmaxRecDepth=16000 \
    --root="$work_tmp" -o "$output" "$source"
}

run_module "$work_tmp/V7RegistryV2OneTerminalCaller/Types.lean"
run_module "$work_tmp/V7RegistryV2OneTerminalCaller/FunsExternal.lean"
run_module "$work_tmp/V7RegistryV2OneTerminalCaller/Funs.lean"
run_module "$work_tmp/V7RegistryV2ProductionCodecs/Types.lean"
run_module "$work_tmp/V7RegistryV2ProductionCodecs/FunsExternal.lean"
run_module "$work_tmp/V7RegistryV2ProductionCodecs/Funs.lean"
run_module "$work_tmp/V7RegistryV2ProductionReadonly/TypesExternal.lean"
run_module "$work_tmp/V7RegistryV2ProductionReadonly/Types.lean"
run_module "$work_tmp/V7RegistryV2ProductionReadonly/FunsExternal.lean"
run_module "$work_tmp/V7RegistryV2ProductionReadonly/Funs.lean"
run_module "$work_tmp/V7RegistryV2AccountInfoProjectionBridge.lean"
run_module "$work_tmp/V7RegistryV2OneTerminalCallerSourceBridge.lean"
run_module "$work_tmp/V7RegistryV2DeploymentCertificate/Types.lean"
run_module "$work_tmp/V7RegistryV2DeploymentCertificate/Funs.lean"
"$LEAN_BIN" -DmaxHeartbeats=8000000 -DmaxRecDepth=16000 \
  --root="$work_tmp" "$work_tmp/V7RegistryV2DeploymentCertificateSourceBridge.lean"

mapfile -t compiled_sources < <(
  find "$work_tmp" -type f -name '*.lean' ! -name '*_Template.lean' -print | sort
)
if rg -n '\b(sorry|admit|native_decide)\b|^[[:space:]]*axiom[[:space:]]' \
    "${compiled_sources[@]}"; then
  echo 'forbidden compiled Lean construct found' >&2
  exit 1
fi

echo 'V7 Registry V2 deployment certificate Lean replay: PASS'
