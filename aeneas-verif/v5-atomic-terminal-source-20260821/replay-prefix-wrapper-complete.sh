#!/usr/bin/env bash
set -euo pipefail

package_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_dir="$(cd "$package_dir/../.." && pwd)"
charon_bin="${ASPIS_CHARON_BIN:-/Users/dominic/charon-cb50-metadata/bin/charon}"
aeneas_bin="${ASPIS_AENEAS_BIN:-/Users/dominic/aeneas-aspis-v5-final/src/_build/default/main.exe}"
target_dir="$(mktemp -d /private/tmp/v5-atomic-prefix-wrapper-target.XXXXXX)"
output_dir="$(mktemp -d /private/tmp/v5-atomic-prefix-wrapper-lean.XXXXXX)"
llbc_file="$(mktemp /private/tmp/V5AtomicTerminalPrefixWrapperComplete.XXXXXX.llbc)"

cd "$repo_dir/programs/aspis-verifier"
CARGO_TARGET_DIR="$target_dir" "$charon_bin" cargo \
  --preset aeneas \
  --sysroot default \
  --mir built \
  --start-from 'aspis_verifier::v5_cu_probe::verify_mode9_atomic_terminal_with_prefix' \
  --opaque 'aspis_statement::atomic_state_only_terminal::atomic_state_only_selected_unmasked_terminal_value_compiled_v3' \
  --dest-file "$llbc_file" \
  -- \
  --offline \
  --lib

"$aeneas_bin" \
  -backend lean \
  -namespace V5AtomicTerminalPrefixWrapperCompleteGenerated \
  -dest "$output_dir" \
  -split-files \
  -print-error-emitters \
  -abort-on-error \
  -no-progress-bar \
  "$llbc_file"

cmp "$llbc_file" "$package_dir/extraction/V5AtomicTerminalPrefixWrapperComplete.llbc"
cmp "$output_dir/Types.lean" "$package_dir/generated/V5AtomicTerminalPrefixWrapperComplete/Types.lean"
cmp \
  <(perl -0777 -pe 's/\n+\z/\n/' "$output_dir/FunsExternal_Template.lean") \
  "$package_dir/generated/V5AtomicTerminalPrefixWrapperComplete/FunsExternal_Template.lean"
cmp "$output_dir/Funs.lean" "$package_dir/generated/V5AtomicTerminalPrefixWrapperComplete/Funs.lean"

echo "Direct production V5 terminal-wrapper extraction matches the checked-in snapshot."
