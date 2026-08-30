#!/usr/bin/env bash
set -euo pipefail

package_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
: "${ASPIS_CHARON_BIN:?set ASPIS_CHARON_BIN to the pinned Charon binary}"
: "${ASPIS_AENEAS_BIN:?set ASPIS_AENEAS_BIN to the pinned Aeneas binary}"
charon_bin="$ASPIS_CHARON_BIN"
aeneas_bin="$ASPIS_AENEAS_BIN"
temp_root=${TMPDIR:-/tmp}
target_dir="$(mktemp -d "$temp_root/v5-atomic-terminal-complete-target.XXXXXX")"
output_dir="$(mktemp -d "$temp_root/v5-atomic-terminal-complete-lean.XXXXXX")"
llbc_file="$(mktemp "$temp_root/V5AtomicTerminalCompleteSource.XXXXXX.llbc")"

cd "$package_dir/harness"
CARGO_TARGET_DIR="$target_dir" "$charon_bin" cargo \
  --preset aeneas \
  --mir built \
  --start-from 'v5_atomic_terminal_source_harness::v5_atomic_terminal::verify_v5_atomic_terminal_from_bytes' \
  --opaque 'aspis_statement::atomic_state_only_terminal::atomic_state_only_selected_unmasked_terminal_value_compiled_v3' \
  --dest-file "$llbc_file" \
  -- \
  --offline

"$aeneas_bin" \
  -backend lean \
  -namespace V5AtomicTerminalCompleteSourceGenerated \
  -dest "$output_dir" \
  -split-files \
  -print-error-emitters \
  -abort-on-error \
  -no-progress-bar \
  "$llbc_file"

cmp "$llbc_file" "$package_dir/extraction/V5AtomicTerminalCompleteSource.llbc"
cmp "$output_dir/Types.lean" "$package_dir/generated/V5AtomicTerminalCompleteSource/Types.lean"
cmp \
  <(perl -0777 -pe 's/\n+\z/\n/' "$output_dir/FunsExternal_Template.lean") \
  "$package_dir/generated/V5AtomicTerminalCompleteSource/FunsExternal_Template.lean"
cmp "$output_dir/Funs.lean" "$package_dir/generated/V5AtomicTerminalCompleteSource/Funs.lean"

echo "V5 atomic-terminal complete source extraction matches the checked-in snapshot."
