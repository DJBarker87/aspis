#!/usr/bin/env bash
set -euo pipefail

readonly bundle="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly root="$(cd "$bundle/../.." && pwd -P)"
readonly checked="$bundle/generated/ParentCore"
readonly charon_bin="${CHARON_BIN:?set CHARON_BIN to Charon 0.1.223}"
readonly aeneas_bin="${AENEAS_BIN:?set AENEAS_BIN to Aeneas d860ac47}"

test "$($charon_bin version)" = "0.1.223"
test "$($aeneas_bin -version)" = "aeneas d860ac47"
test "$(git -C "$root" hash-object crates/aspis-core/src/circle_fri.rs)" = \
  "d9382a35ec7a660b696171e7609f443995a009bf"

readonly out="$(mktemp -d /private/tmp/v5-fri-parent-reextract.XXXXXX)"
"$charon_bin" cargo --preset aeneas \
  --start-from \
  aspis_core_parent_helper_extraction::circle_fri::derive_parent_line_points \
  --dest-file "$out/ParentCore.llbc" -- \
  --manifest-path "$bundle/parent-helper-harness/Cargo.toml"

"$aeneas_bin" -backend lean -split-files \
  -namespace V5FriCoordinateProduction \
  -dest "$out/generated" -subdir ParentCore "$out/ParentCore.llbc"

normalize_types() {
  perl -pe \
    's{^import Aeneas$}{import Aeneas.Std\nimport Aeneas.Data.Discriminant}; s{\.\./\.\./\.\./crates/}{<repo>/crates/}g' \
    "$1"
}

normalize_funs() {
  perl -pe \
    's{^import Aeneas$}{import Aeneas.Std\nimport Aeneas.Tactic.RustAttributes}; s{\.\./\.\./\.\./crates/}{<repo>/crates/}g' \
    "$1"
}

diff -u <(normalize_types "$out/generated/ParentCore/Types.lean") \
  "$checked/Types.lean"
diff -u <(normalize_funs "$out/generated/ParentCore/Funs.lean") \
  "$checked/Funs.lean"

test "$(rg -c '^axiom ' \
  "$out/generated/ParentCore/FunsExternal_Template.lean")" = "1"
rg -q '^axiom core\.option\.Option\.ok_or' \
  "$out/generated/ParentCore/FunsExternal_Template.lean"

AENEAS_LEAN_PATH="${AENEAS_LEAN_PATH:?set the full matching Aeneas lake LEAN_PATH}" \
LEAN432_BIN="${LEAN432_BIN:-$(command -v lean)}" \
  "$bundle/replay-parent-helper-lean432.sh"

echo "Unchanged parent-coordinate helper re-extraction: PASS"
