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
test "$($AENEAS_BIN -version)" = 'aeneas b59d518'

replay_base=${TMPDIR:-/tmp}
replay_base=${replay_base%/}
replay_tmp=$(mktemp -d "$replay_base/aspis-v7-lane-invariant.XXXXXX")
cleanup() {
  if [ "${KEEP_REPLAY_TMP:-0}" = 1 ]; then
    echo "retained replay workspace: $replay_tmp" >&2
    return
  fi
  case "$replay_tmp" in
    "$replay_base"/aspis-v7-lane-invariant.*) rm -rf -- "$replay_tmp" ;;
    *) echo "refusing unsafe cleanup target: $replay_tmp" >&2 ;;
  esac
}
trap cleanup EXIT

cp -R "$script_dir/harness" "$replay_tmp/harness"
rm -rf -- "$replay_tmp/harness/target"
test "$(shasum -a 256 "$replay_tmp/harness/src/lib.rs" | awk '{print $1}')" = \
  7f3a70095742cfe00eb84f47ed5890557b6ab7b60fda03c5b235cc3d00fbc0a9

export CARGO_BUILD_JOBS=1
export CARGO_TARGET_DIR="$replay_tmp/target"
llbc="$replay_tmp/V7ForestLaneInvariant.llbc"
(
  cd "$replay_tmp/harness"
  "$CHARON_BIN" cargo --preset aeneas \
    --start-from v7_forest_lane_invariant_source::hot_decode_projected \
    --start-from v7_forest_lane_invariant_source::fast_encode_projected \
    --start-from v7_forest_lane_invariant_source::strict_encode_projected \
    --start-from v7_forest_lane_invariant_source::direct_asq8_lane_read_projected \
    --start-from v7_forest_lane_invariant_source::apply_production_lane_write \
    --dest-file "$llbc" -- --lib
)

echo "replayed raw LLBC SHA-256: $(shasum -a 256 "$llbc" | awk '{print $1}')"

generated="$replay_tmp/generated"
"$AENEAS_BIN" -sequential -no-progress-bar -abort-on-error -backend lean \
  -namespace V7ForestLaneInvariantGenerated -dest "$generated" \
  -subdir V7ForestLaneInvariant -split-files -emit-json "$llbc"

for generated_file in Types.lean Funs.lean FunsExternal_Template.lean; do
  cmp "$generated/V7ForestLaneInvariant/$generated_file" \
    "$script_dir/generated/V7ForestLaneInvariant/$generated_file"
done
cmp "$generated/translation.json" "$script_dir/generated/translation.json"

echo 'V7 forest lane Charon/Aeneas extraction replay: PASS'
