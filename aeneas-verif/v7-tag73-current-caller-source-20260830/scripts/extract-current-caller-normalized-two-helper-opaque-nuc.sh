#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
bundle_dir=$(CDPATH= cd -- "$script_dir/.." && pwd)
readonly repo=${ASPIS_SOURCE_ROOT:-/home/dombarker/project-offloads/aspis-v7-aeneas-source-unblock-20260830/normalized-source-statement-r9}
readonly task=${ASPIS_AENEAS_TASK_ROOT:-/home/dombarker/project-offloads/aspis-v7-aeneas-source-unblock-20260830}
readonly charon=${CHARON_BIN:-/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/bin/charon}
readonly source_revision=bcd03b12293f2737dfa1da1436092a0a24a6ae24

export PATH=/home/dombarker/.cargo/bin:$PATH
export CARGO_BUILD_JOBS=1
export CARGO_TARGET_DIR=$task/target-normalized-r2

mkdir -p "$task/extraction" "$task/logs"
test "$(tr -d '\n' < "$bundle_dir/source/REVISION")" = "$source_revision"
(cd "$repo" && sha256sum -c "$bundle_dir/source/NORMALIZED-STATEMENT-OWNED-KEY-SOURCE.sha256")
test "$(sha256sum "$repo/crates/aspis-statement/src/atomic_state_only_terminal.rs" | cut -d' ' -f1)" = \
  eb23c8acf92b915b156d91a704bd1a3eed33af240dbbc73c8aeeceb15791f404
test "$(sha256sum "$repo/programs/aspis-verifier/src/v7_verifier.rs" | cut -d' ' -f1)" = \
  9ea0dfbc183bc96a2ff9dceee8c5d5161ea1ac0fab200d7635145cd4f24294b1
cd "$repo"
exec "$charon" cargo \
  --preset aeneas \
  --mir built \
  --sysroot default \
  --start-from crate::v7_verifier::verify_v7_read_only_with_statement_digest \
  --include aspis_core \
  --include aspis_statement \
  --opaque aspis_core::v6_onefold::gamma_combine_v6_c1_slot_major \
  --opaque aspis_core::field::qm31_dot3 \
  --dest-file "$task/extraction/V7Tag73CurrentNormalizedStatementOwnedTwoHelpersOpaque.llbc" \
  -- \
  --locked \
  --package aspis-verifier \
  --lib \
  --no-default-features \
  --features v7-production-tag73
