#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
: "${CHARON_BIN:?set CHARON_BIN to Charon 0.1.223}"
: "${AENEAS_BIN:?set AENEAS_BIN to Aeneas b59d518}"

test -x "$CHARON_BIN"
test -x "$AENEAS_BIN"
test "$(shasum -a 256 "$CHARON_BIN" | awk '{print $1}')" = \
  d785c5f18053c4d310c7388dfdb0b59adfc9854c28b632a34a8f6301ba1c4b43
test "$(shasum -a 256 "$AENEAS_BIN" | awk '{print $1}')" = \
  fbb8dac1a9a57e635a762e04b95aeb46dbd2dab2be5ed54fa9e0b1321c1962cf
test "$("$AENEAS_BIN" -version)" = 'aeneas b59d518'

replay_base=${TMPDIR:-/tmp}
replay_base=${replay_base%/}
replay_tmp=$(mktemp -d "$replay_base/aspis-v7-custody-extraction.XXXXXX")
cleanup() {
  if [ "${KEEP_REPLAY_TMP:-0}" = 1 ]; then
    echo "retained replay workspace: $replay_tmp" >&2
    return
  fi
  case "$replay_tmp" in
    "$replay_base"/aspis-v7-custody-extraction.*) rm -rf -- "$replay_tmp" ;;
    *) echo "refusing unsafe cleanup target: $replay_tmp" >&2 ;;
  esac
}
trap cleanup EXIT

cp -R "$script_dir/harness" "$replay_tmp/harness"
rm -rf -- "$replay_tmp/harness/target"
test "$(shasum -a 256 "$replay_tmp/harness/src/lib.rs" | awk '{print $1}')" = \
  95334962c7285a96aa51aa3380732b6b23963032a9cec0e3bd30ca74c10dec4b

export CARGO_BUILD_JOBS=1
export CARGO_TARGET_DIR="$replay_tmp/target"
llbc="$replay_tmp/V7PoolVaultCustody.llbc"
(
  cd "$replay_tmp/harness"
  "$CHARON_BIN" cargo --preset aeneas \
    --start-from v7_pool_vault_custody_source::execute_atomic_custody \
    --dest-file "$llbc" -- --lib
)

generated="$replay_tmp/generated"
"$AENEAS_BIN" -sequential -no-progress-bar -abort-on-error -backend lean \
  -namespace V7PoolVaultCustodyGenerated -dest "$generated" \
  -subdir V7PoolVaultCustody -split-files -emit-json "$llbc"

for generated_file in Types.lean Funs.lean; do
  cmp "$generated/V7PoolVaultCustody/$generated_file" \
    "$script_dir/generated/V7PoolVaultCustody/$generated_file"
done
cmp "$generated/translation.json" "$script_dir/generated/translation.json"
test "$(shasum -a 256 \
  "$script_dir/generated/V7PoolVaultCustody/FunsExternal.lean" | awk '{print $1}')" = \
  48eb1e1fcba609a052eb2eaa1ae407d104d490061320ccb6f8d2f757f73a8c37

echo "replayed raw LLBC SHA-256: $(shasum -a 256 "$llbc" | awk '{print $1}')"
echo 'V7 Pool vault-custody Charon/Aeneas extraction replay: PASS'
