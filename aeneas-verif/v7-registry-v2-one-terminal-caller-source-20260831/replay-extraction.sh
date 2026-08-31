#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
: "${CHARON_BIN:?set CHARON_BIN to the pinned Charon binary}"
: "${AENEAS_BIN:?set AENEAS_BIN to Aeneas b59d5188-lean432-extended}"

test -x "$CHARON_BIN"
test -x "$AENEAS_BIN"
test "$(shasum -a 256 "$CHARON_BIN" | awk '{print $1}')" = \
  b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c
test "$(shasum -a 256 "$AENEAS_BIN" | awk '{print $1}')" = \
  4632746db1bf6c3953f2971078965a2a5a8ad6cf5f75636b46b397bc50c550b5
test "$($AENEAS_BIN -version)" = 'aeneas b59d5188-lean432-extended'

replay_base=${TMPDIR:-/tmp}
replay_base=${replay_base%/}
replay_tmp=$(mktemp -d "$replay_base/aspis-v7-registry-v2-one-terminal-extraction.XXXXXX")
cleanup() {
  if [ "${KEEP_REPLAY_TMP:-0}" = 1 ]; then
    echo "retained replay workspace: $replay_tmp" >&2
    return
  fi
  case "$replay_tmp" in
    "$replay_base"/aspis-v7-registry-v2-one-terminal-extraction.*) rm -rf -- "$replay_tmp" ;;
    *) echo "refusing unsafe cleanup target: $replay_tmp" >&2 ;;
  esac
}
trap cleanup EXIT

cp -R "$script_dir/harness" "$replay_tmp/harness"
rm -rf -- "$replay_tmp/harness/target"
test "$(shasum -a 256 "$replay_tmp/harness/src/lib.rs" | awk '{print $1}')" = \
  d40539bea731d315404a29501c7db391f8a8b8ec8e26bd5d99a7c75a729985e7

export CARGO_BUILD_JOBS=1
export CARGO_TARGET_DIR="$replay_tmp/target"
llbc="$replay_tmp/V7RegistryV2OneTerminalCaller.llbc"
(
  cd "$replay_tmp/harness"
  "$CHARON_BIN" cargo --preset aeneas \
    --start-from v7_registry_v2_one_terminal_caller_source::execute_atomic_transaction \
    --dest-file "$llbc" -- --lib
)

generated="$replay_tmp/generated"
"$AENEAS_BIN" -sequential -no-progress-bar -abort-on-error -backend lean \
  -namespace V7RegistryV2OneTerminalCallerGenerated -dest "$generated" \
  -subdir V7RegistryV2OneTerminalCaller -split-files -emit-json "$llbc"

for generated_file in Types.lean Funs.lean FunsExternal_Template.lean; do
  cmp "$generated/V7RegistryV2OneTerminalCaller/$generated_file" \
    "$script_dir/generated/V7RegistryV2OneTerminalCaller/$generated_file"
done
cmp "$generated/translation.json" "$script_dir/generated/translation.json"

echo "replayed raw LLBC SHA-256: $(shasum -a 256 "$llbc" | awk '{print $1}')"
echo 'V7 Registry V2 one-terminal Charon/Aeneas extraction replay: PASS'
