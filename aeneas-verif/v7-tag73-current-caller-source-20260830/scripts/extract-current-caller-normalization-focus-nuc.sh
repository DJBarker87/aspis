#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
bundle_dir=$(CDPATH= cd -- "$script_dir/.." && pwd)
readonly repo=${ASPIS_SOURCE_ROOT:-/home/dombarker/project-offloads/aspis-v7-aeneas-source-unblock-20260830/normalized-source-r2}
readonly task=${ASPIS_AENEAS_TASK_ROOT:-/home/dombarker/project-offloads/aspis-v7-aeneas-source-unblock-20260830}
readonly charon=${CHARON_BIN:-/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/bin/charon}
readonly source_revision=bcd03b12293f2737dfa1da1436092a0a24a6ae24

export PATH=/home/dombarker/.cargo/bin:$PATH
export CARGO_BUILD_JOBS=1
export CARGO_TARGET_DIR=$task/target-normalized-r2

mkdir -p "$task/extraction" "$task/logs"
test "$(tr -d '\n' < "$bundle_dir/source/REVISION")" = "$source_revision"
(cd "$repo" && sha256sum -c "$bundle_dir/source/NORMALIZED-KEY-SOURCE.sha256")
cd "$repo"
exec "$charon" cargo \
  --preset aeneas \
  --mir built \
  --sysroot default \
  --start-from aspis_core::sumcheck::fold_grouped_rows_twice \
  --start-from aspis_core::state_only_hiding::state_only_hiding_layout_factor_fingerprint_for_registry \
  --start-from 'aspis_core::sumcheck::_::dot' \
  --include aspis_core \
  --dest-file "$task/extraction/V7Tag73CurrentNormalizationFocus.llbc" \
  -- \
  --locked \
  --package aspis-verifier \
  --lib \
  --no-default-features \
  --features v7-production-tag73
