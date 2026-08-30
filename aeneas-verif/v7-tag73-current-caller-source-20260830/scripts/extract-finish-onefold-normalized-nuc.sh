#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
bundle_dir=$(CDPATH= cd -- "$script_dir/.." && pwd)
readonly repo=${ASPIS_SOURCE_ROOT:-/home/dombarker/project-offloads/aspis-v7-aeneas-source-unblock-20260830/normalized-source-r3}
readonly task=${ASPIS_AENEAS_TASK_ROOT:-/home/dombarker/project-offloads/aspis-v7-aeneas-source-unblock-20260830}
readonly charon=${CHARON_BIN:-/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/bin/charon}
readonly source_revision=bcd03b12293f2737dfa1da1436092a0a24a6ae24

export PATH=/home/dombarker/.cargo/bin:$PATH
export CARGO_BUILD_JOBS=1
export CARGO_TARGET_DIR=$task/target-normalized-r3

mkdir -p "$task/extraction" "$task/logs"
test "$(tr -d '\n' < "$bundle_dir/source/REVISION")" = "$source_revision"
(cd "$repo" && sha256sum -c "$bundle_dir/source/NORMALIZED-KEY-SOURCE.sha256")
cd "$repo"
exec "$charon" cargo \
  --preset aeneas \
  --mir built \
  --sysroot default \
  --start-from aspis_core::v6_transcript::finish_onefold_relation \
  --include aspis_core \
  --opaque 'aspis_core::sumcheck::_::weight_at' \
  --opaque aspis_core::v6_onefold::gamma_combine_v6_c1_slot_major \
  --opaque aspis_core::field::qm31_dot3 \
  --dest-file "$task/extraction/V7Tag73FinishOnefoldNormalized.llbc" \
  -- \
  --locked \
  --package aspis-verifier \
  --lib \
  --no-default-features \
  --features v7-production-tag73
