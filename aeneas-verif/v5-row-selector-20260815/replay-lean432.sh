#!/usr/bin/env bash
set -euo pipefail

readonly bundle="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly root="$(cd "$bundle/../.." && pwd -P)"
readonly harness="$bundle/harness"
readonly checked_expand="$bundle/generated/V5RowExpand"
readonly checked_row="$bundle/generated/V5RowAccess"
readonly checked_row_external="$checked_row/FunsExternal.lean"

readonly charon_repo="${ASPIS_CHARON_REPO:?set ASPIS_CHARON_REPO to pinned Charon cb50ff16}"
readonly aeneas_repo="${ASPIS_AENEAS_REPO:?set ASPIS_AENEAS_REPO to pinned Aeneas b59d5188}"
readonly aeneas_lean_lib="${AENEAS_LEAN_LIB:?set AENEAS_LEAN_LIB to the Lean-4.32 Aeneas library directory}"
readonly charon_bin="${CHARON_BIN:-$charon_repo/bin/charon}"
readonly aeneas_bin="${AENEAS_BIN:-$aeneas_repo/bin/aeneas}"

readonly expected_charon_commit="cb50ff16b9f1066b8a97dc06da704de2da2fa41c"
readonly expected_aeneas_commit="b59d5188c082f704a418c7cb4e52ad69328002d1"
readonly expected_terminal_blob="8d607ab0ed63ffaf24372ad58bdfb3750edc0765"
readonly expected_field_blob="a28ff94de05265102ca819849805a7f73c675800"
readonly expected_harness_toml_blob="3a4cea97ee149500c71486a9f5b0c1cbebc899d3"
readonly expected_harness_lock_blob="10e8c1acf9e1c8edbcc0cbab59bc74f93bd4f51a"
readonly expected_expand_types_sha256="7bb0960cae0f8d1c83a5cb2bdd6edb89e4152db1533d2f3b77a2bccb3427ab3b"
readonly expected_expand_funs_sha256="2c2f397acd32ed5d6afad2a8c6d8b9e67a96bd3db48c0ce32e7ea27745e0b2a6"
readonly expected_row_types_sha256="ac6c41fdc0e82284b4e56eaa3b01fb66abbbc3dd14c1670d231142a81ef6a173"
readonly expected_row_funs_sha256="1ce81fcbf9ae894823bf1187ed02ebe4a177a489492af79e74d1f9129ba19a05"

if [[ -n "${LEAN432_BIN:-}" ]]; then
  lean_cmd=("$LEAN432_BIN")
elif command -v elan >/dev/null 2>&1; then
  lean_cmd=(elan run leanprover/lean4:v4.32.0 lean)
else
  lean_cmd=("$(command -v lean)")
fi
readonly -a lean_cmd

case "$("${lean_cmd[@]}" --version)" in
  "Lean (version 4.32.0,"*) ;;
  *) echo "expected Lean 4.32.0" >&2; exit 1 ;;
esac

[[ -x "$charon_bin" ]]
[[ -x "$aeneas_bin" ]]
[[ -f "$aeneas_lean_lib/Aeneas/Std.olean" ]]
[[ "$(git -C "$charon_repo" rev-parse HEAD)" == "$expected_charon_commit" ]]
[[ "$(git -C "$aeneas_repo" rev-parse HEAD)" == "$expected_aeneas_commit" ]]
[[ "$(git -C "$root" hash-object crates/aspis-statement/src/atomic_state_only_terminal.rs)" == "$expected_terminal_blob" ]]
[[ "$(git -C "$root" hash-object crates/aspis-core/src/field.rs)" == "$expected_field_blob" ]]
[[ "$(git -C "$root" hash-object "$harness/Cargo.toml")" == "$expected_harness_toml_blob" ]]
[[ "$(git -C "$root" hash-object "$harness/Cargo.lock")" == "$expected_harness_lock_blob" ]]

if [[ -n "${V5_ROW_SELECTOR_REPLAY_OUT:-}" ]]; then
  out=$V5_ROW_SELECTOR_REPLAY_OUT
  mkdir -p "$out"
  [[ -z "$(find "$out" -mindepth 1 -maxdepth 1 -print -quit)" ]]
else
  out=$(mktemp -d /private/tmp/v5-row-selector.XXXXXX)
fi
readonly out
readonly raw_expand="$out/raw-expand"
readonly raw_row="$out/raw-row"
readonly checked_src="$out/checked-src"
readonly olean_root="$out/olean"
readonly log="$out/replay.log"
mkdir -p "$raw_expand" "$raw_row" \
  "$checked_src/V5RowExpand" "$checked_src/V5RowAccess" \
  "$olean_root/V5RowExpand" "$olean_root/V5RowAccess"
: > "$log"

extract() {
  local stem=$1 start=$2 namespace=$3 destination=$4
  shift 4
  local llbc="$out/$stem.llbc"
  (
    cd "$harness"
    CARGO_TARGET_DIR="$out/cargo-$stem" "$charon_bin" cargo \
      --preset aeneas \
      --start-from "$start" \
      "$@" \
      --include aspis_core::field \
      --dest-file "$llbc" -- --release --locked
  ) >> "$log" 2>&1
  local aeneas_stage_log="$out/$stem-aeneas.log"
  set +e
  "$aeneas_bin" -backend lean -namespace "$namespace" \
    -split-files -no-progress-bar -dest "$destination" "$llbc" \
    > "$aeneas_stage_log" 2>&1
  local aeneas_status=$?
  set -e
  cat "$aeneas_stage_log" >> "$log"
  if [[ $aeneas_status -ne 0 ]]; then
    if [[ "$stem" != V5RowAccess ]] || \
        ! rg -F "Ignoring the body of 'aspis_statement_row_selector_extraction::atomic_state_only_terminal::{aspis_statement_row_selector_extraction::atomic_state_only_terminal::AtomicSelectors}::row'" \
          "$aeneas_stage_log" >/dev/null; then
      echo "unexpected Aeneas translation failure in $stem" >&2
      exit "$aeneas_status"
    fi
  fi
}

extract V5RowExpand \
  'aspis_statement_row_selector_extraction::atomic_state_only_terminal::_::expand' \
  V5RowExpandGenerated "$raw_expand"
extract V5RowAccess \
  'aspis_statement_row_selector_extraction::atomic_state_only_terminal::_::row' \
  V5RowAccessGenerated "$raw_row" \
  --exclude 'aspis_statement_row_selector_extraction::atomic_state_only_terminal::AtomicSelectors::_' \
  --exclude 'aspis_statement_row_selector_extraction::atomic_state_only_terminal::projected_row_index'

# Pinned Aeneas emits the unsuffixed Rust shift literal as `I32`, while its
# Lean model for `usize::wrapping_shr` correctly requires `U32`. Rust's trait
# call also uses `u32`; normalize that one generated argument on both replay
# and checked sides before comparison and compilation.
perl -pi -e 's/4#i32/4#u32/' "$raw_row/Funs.lean"
rg -F 'def atomic_state_only_terminal.AtomicSemanticSelectors.row' \
  "$raw_row/Funs.lean" >/dev/null
if rg -F 'def atomic_state_only_terminal.AtomicSelectors.row' \
    "$raw_row/Funs.lean"; then
  echo "unwanted copy-selector row method reached checked output" >&2
  exit 1
fi

normalize() {
  perl -0777 -pe \
    's/import Aeneas(?:\.Std)?\n//g; s/import Aeneas\.Tactic\.RustAttributes\n//g; s/import (?:V5RowExpand|V5RowAccess)\.(?:Types|FunsExternal)\n//g; s{/-.*?-/}{}gs; s{--[^\n]*}{}g; s/\s+//g' \
    "$1"
}

compare_one() {
  local raw=$1 checked=$2 expected=$3 name=$4
  normalize "$raw" > "$out/raw-$name.semantic"
  normalize "$checked" > "$out/checked-$name.semantic"
  cmp "$out/raw-$name.semantic" "$out/checked-$name.semantic"
  [[ "$(shasum -a 256 "$out/raw-$name.semantic" | awk '{print $1}')" == "$expected" ]]
}

compare_one "$raw_expand/Types.lean" "$checked_expand/Types.lean" \
  "$expected_expand_types_sha256" expand-types
compare_one "$raw_expand/Funs.lean" "$checked_expand/Funs.lean" \
  "$expected_expand_funs_sha256" expand-funs
compare_one "$raw_row/Types.lean" "$checked_row/Types.lean" \
  "$expected_row_types_sha256" row-types
compare_one "$raw_row/Funs.lean" "$checked_row/Funs.lean" \
  "$expected_row_funs_sha256" row-funs

cp "$checked_expand/Types.lean" "$checked_src/V5RowExpand/Types.lean"
cp "$checked_expand/Funs.lean" "$checked_src/V5RowExpand/Funs.lean"
cp "$checked_row/Types.lean" "$checked_src/V5RowAccess/Types.lean"
cp "$checked_row_external" "$checked_src/V5RowAccess/FunsExternal.lean"
cp "$checked_row/Funs.lean" "$checked_src/V5RowAccess/Funs.lean"

aspis_path=$(
  cd "$root/AspisFormal"
  NO_DNA=1 lake env printenv LEAN_PATH
)
export LEAN_PATH="$olean_root:$checked_src:$aeneas_lean_lib:$aspis_path"
(
  cd "$checked_src"
  "${lean_cmd[@]}" -j 1 -o "$olean_root/V5RowExpand/Types.olean" \
    V5RowExpand/Types.lean
  "${lean_cmd[@]}" -j 1 -o "$olean_root/V5RowExpand/Funs.olean" \
    V5RowExpand/Funs.lean
  "${lean_cmd[@]}" -j 1 -o "$olean_root/V5RowAccess/Types.olean" \
    V5RowAccess/Types.lean
  "${lean_cmd[@]}" -j 1 -o "$olean_root/V5RowAccess/FunsExternal.olean" \
    V5RowAccess/FunsExternal.lean
  "${lean_cmd[@]}" -j 1 -o "$olean_root/V5RowAccess/Funs.olean" \
    V5RowAccess/Funs.lean
) >> "$log" 2>&1

if rg -n '\b(sorry|admit|native_decide|axiom|unsafe|ofReduceBool)\b' \
    "$checked_expand" "$checked_row" \
    "$root/AspisFormal/AspisFormal/V5ProductionRowSelector.lean"; then
  echo "forbidden proof token" >&2
  exit 1
fi

(
  cd "$root/AspisFormal"
  NO_DNA=1 lake env lean AspisFormal/V5ProductionRowSelector.lean
) >> "$log" 2>&1

if rg -n 'sorryAx|ofReduceBool' "$log"; then
  echo "forbidden axiom in row-selector proof" >&2
  exit 1
fi
if ! awk '
  / depends on axioms: \[/ { active = 1; sub(/^.*\[/, "") }
  active {
    line = $0
    gsub(/propext|Classical\.choice|Quot\.sound/, "", line)
    gsub(/[\[\],[:space:]]/, "", line)
    if (line != "") { print "unexpected axiom: " line; bad = 1 }
    if ($0 ~ /\]/) active = 0
  }
  END { exit bad }
' "$log"; then
  exit 1
fi

echo "Lean 4.32 V5 row-selector replay: PASS"
echo "V5_ROW_SELECTOR_REPLAY_OUT=$out"
echo "log: $log"
