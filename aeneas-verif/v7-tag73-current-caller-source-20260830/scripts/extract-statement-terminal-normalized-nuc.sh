#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
bundle_dir=$(CDPATH= cd -- "$script_dir/.." && pwd)
readonly repo=${ASPIS_SOURCE_ROOT:-/home/dombarker/project-offloads/aspis-v7-aeneas-source-unblock-20260830/normalized-source-statement-r6}
readonly task=${ASPIS_AENEAS_TASK_ROOT:-/home/dombarker/project-offloads/aspis-v7-aeneas-source-unblock-20260830}
readonly charon=${CHARON_BIN:-/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/bin/charon}
readonly source_revision=bcd03b12293f2737dfa1da1436092a0a24a6ae24

export PATH=/home/dombarker/.cargo/bin:$PATH
export CARGO_BUILD_JOBS=1
export CARGO_TARGET_DIR=$task/target-normalized-r2

mkdir -p "$task/extraction" "$task/logs"
test "$(tr -d '\n' < "$bundle_dir/source/REVISION")" = "$source_revision"
(cd "$repo" && sha256sum -c "$bundle_dir/source/NORMALIZED-KEY-SOURCE.sha256")
test "$(sha256sum "$repo/crates/aspis-statement/src/atomic_state_only_terminal.rs" | cut -d' ' -f1)" = \
  35566dbf25ad4eb2e7abcf355aaba3320ec7cbb5c60de14908dcf48b79f3cac2
cd "$repo"
exec "$charon" cargo \
  --preset aeneas \
  --mir built \
  --sysroot default \
  --start-from aspis_statement::atomic_state_only_terminal::atomic_state_only_selected_masked_terminal_value_compiled_tag73 \
  --include aspis_statement \
  --include aspis_core \
  --dest-file "$task/extraction/V7Tag73StatementTerminalNormalizedPublicResidualFocus.llbc" \
  -- \
  --locked \
  --package aspis-verifier \
  --lib \
  --no-default-features \
  --features v7-production-tag73
