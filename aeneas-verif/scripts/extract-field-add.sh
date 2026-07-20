#!/usr/bin/env bash
set -euo pipefail

readonly AENEAS_COMMIT="b59d5188c082f704a418c7cb4e52ad69328002d1"
readonly CHARON_COMMIT="cb50ff16b9f1066b8a97dc06da704de2da2fa41c"

if [[ -z "${ASPIS_AENEAS_REPO:-}" || -z "${ASPIS_CHARON_REPO:-}" ]]; then
  echo "set ASPIS_AENEAS_REPO and ASPIS_CHARON_REPO to pinned official clones" >&2
  exit 2
fi

readonly script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly verification_dir="$(cd "$script_dir/.." && pwd -P)"
readonly workspace_dir="$(cd "$verification_dir/.." && pwd -P)"
readonly core_crate_dir="$workspace_dir/crates/aspis-core"

if [[ "$(git -C "$ASPIS_AENEAS_REPO" rev-parse HEAD)" != "$AENEAS_COMMIT" ]]; then
  echo "Aeneas is not at $AENEAS_COMMIT" >&2
  exit 2
fi
if [[ "$(git -C "$ASPIS_CHARON_REPO" rev-parse HEAD)" != "$CHARON_COMMIT" ]]; then
  echo "Charon is not at $CHARON_COMMIT" >&2
  exit 2
fi
if ! grep -Fq "$CHARON_COMMIT" "$ASPIS_AENEAS_REPO/charon-pin"; then
  echo "the pinned Aeneas checkout does not name the pinned Charon companion" >&2
  exit 2
fi

readonly charon_bin="$ASPIS_CHARON_REPO/bin/charon"
readonly aeneas_bin="$ASPIS_AENEAS_REPO/bin/aeneas"
if [[ ! -x "$charon_bin" || ! -x "$aeneas_bin" ]]; then
  echo "build the pinned local Charon and Aeneas clones before extracting" >&2
  exit 2
fi

readonly work_dir="$(mktemp -d /private/tmp/aspis-field-add-extract.XXXXXX)"
readonly cargo_target_dir="$work_dir/cargo-target"
readonly generated_llbc="$verification_dir/llbc/aspis_core_field_add.llbc"
readonly generated_lean="$verification_dir/proof/AspisCoreFieldAdd.lean"
trap 'rm -rf "$work_dir"' EXIT
mkdir -p "$verification_dir/llbc" "$verification_dir/proof"

(
  cd "$core_crate_dir"
  CARGO_TARGET_DIR="$cargo_target_dir" "$charon_bin" cargo \
    --preset=aeneas \
    --start-from=aspis_core::field::_::add \
    --dest-file="$generated_llbc" \
    -- \
    --release \
    --locked \
    -p aspis-core
)

"$aeneas_bin" \
  -backend lean \
  "$generated_llbc" \
  -dest "$verification_dir/proof" \
  -max-heartbeats 200000 \
  -max-recdepth 1000 \
  -abort-on-error \
  -warnings-as-errors \
  -no-progress-bar

"$script_dir/check-generated.sh" \
  "$generated_llbc" \
  "$generated_lean"
