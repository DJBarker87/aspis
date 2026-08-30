#!/usr/bin/env bash
set -euo pipefail

readonly repo=${ASPIS_SOURCE_ROOT:-/home/dombarker/project-offloads/ZK-v7-one-tx-formal-consolidation-20260828}
readonly task=${ASPIS_AENEAS_TASK_ROOT:-/home/dombarker/project-offloads/aspis-v7-aeneas-source-unblock-20260830}
readonly charon=${CHARON_BIN:-/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/bin/charon}

export PATH=/home/dombarker/.cargo/bin:$PATH
export CARGO_BUILD_JOBS=1
export CARGO_TARGET_DIR=$task/target

mkdir -p "$task/extraction" "$task/logs"
cd "$repo"
exec "$charon" cargo \
  --preset aeneas \
  --mir built \
  --sysroot default \
  --start-from crate::v6_onefold::gamma_combine_v6_c1_slot_major \
  --dest-file "$task/extraction/V7GammaSlotMajor.llbc" \
  -- \
  --locked \
  --package aspis-core \
  --lib \
  --no-default-features
