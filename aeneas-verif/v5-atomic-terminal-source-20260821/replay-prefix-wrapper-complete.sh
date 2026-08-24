#!/usr/bin/env bash
set -euo pipefail

package_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_dir="$(cd "$package_dir/../.." && pwd)"
charon_bin="${ASPIS_CHARON_BIN:-/Users/dominic/charon-cb50-metadata/bin/charon}"
aeneas_bin="${ASPIS_AENEAS_BIN:-/Users/dominic/aeneas-aspis-v5-final/src/_build/default/main.exe}"
target_dir="$(mktemp -d /private/tmp/v5-atomic-prefix-wrapper-target.XXXXXX)"
output_dir="$(mktemp -d /private/tmp/v5-atomic-prefix-wrapper-lean.XXXXXX)"
normalized_dir="$(mktemp -d /private/tmp/v5-atomic-prefix-wrapper-normalized.XXXXXX)"
llbc_dir="$(mktemp -d /private/tmp/v5-atomic-prefix-wrapper-llbc.XXXXXX)"
llbc_file="$llbc_dir/V5AtomicTerminalPrefixWrapperComplete.llbc"
raw_dir="$package_dir/raw/V5AtomicTerminalPrefixWrapperComplete"
checked_dir="$package_dir/generated/V5AtomicTerminalPrefixWrapperComplete"
normalization_patch="$package_dir/extraction/prefix-wrapper-lean432-normalization.patch"

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

# Charon serializes four internal lookup maps in hash-table iteration order and
# records the chosen destination path.  Those bytes vary between otherwise
# identical runs.  Sort exactly those maps and erase only that path before
# comparing the complete LLBC JSON; all declarations and bodies remain in the
# comparison.
canonical_llbc() {
  jq -S '
    .translated.options.dest_file = "<normalized>" |
    .translated.item_names |= sort_by(.key | tojson) |
    .translated.short_names |= sort_by(.key | tojson) |
    .translated.assoc_item_names |= sort_by(.key | tojson) |
    .translated.files |= sort_by(.key | tojson)
  ' "$1"
}
cmp \
  <(canonical_llbc "$llbc_file") \
  <(canonical_llbc \
    "$package_dir/extraction/V5AtomicTerminalPrefixWrapperComplete.llbc")
cmp "$output_dir/Types.lean" "$raw_dir/Types.lean"
cmp \
  <(perl -0777 -pe 's/\n+\z/\n/' "$output_dir/FunsExternal_Template.lean") \
  "$raw_dir/FunsExternal_Template.lean"
cmp "$output_dir/Funs.lean" "$raw_dir/Funs.lean"

# Preserve the translator output above byte-for-byte.  The proof imports a
# separately checked Lean 4.32 normalization: imports are narrowed, obsolete
# duplicate discriminant registrations are removed, mutable-iterator adapters
# are made type-correct, and the opaque terminal evaluator is replaced by an
# explicit equality-carrying boundary.  The tracked patch is the entire delta.
cp "$raw_dir/Types.lean" "$normalized_dir/Types.lean"
cp "$raw_dir/FunsExternal_Template.lean" \
  "$normalized_dir/FunsExternal_Template.lean"
cp "$raw_dir/Funs.lean" "$normalized_dir/Funs.lean"
patch -d "$normalized_dir" -p1 < "$normalization_patch"

cmp "$normalized_dir/Types.lean" "$checked_dir/Types.lean"
cmp "$normalized_dir/FunsExternal_Template.lean" \
  "$checked_dir/FunsExternal_Template.lean"
cmp "$normalized_dir/Funs.lean" "$checked_dir/Funs.lean"

echo "Direct production V5 terminal-wrapper extraction and deterministic Lean 4.32 normalization match the checked-in snapshots."
