#!/usr/bin/env bash
set -euo pipefail

readonly bundle="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly root="$(cd "$bundle/../.." && pwd -P)"
readonly generated="$bundle/generated/V5Dot16Reference"
readonly proof="$bundle/proof/V5FriDot16ReferenceSemantics.lean"
readonly reducer_source="$root/aeneas-verif/proof/AspisCoreFieldReduceU64.lean"
readonly reducer_proof="$root/aeneas-verif/proof/M31ReduceU64Proof.lean"
readonly lean_bin="${LEAN432_BIN:-$(command -v lean)}"
readonly aeneas_lib="${AENEAS_LEAN_LIB:?set AENEAS_LEAN_LIB to the matching Lean 4.32 Aeneas library}"

readonly expected_field_blob="a28ff94de05265102ca819849805a7f73c675800"
readonly expected_reference_sha256="04b782484afb5fda8be112a7a8e563bcac7f7f60b7de780ed84bf3d60c6fc09e"

case "$($lean_bin --version)" in
  "Lean (version 4.32.0,"*) ;;
  *) echo "expected Lean 4.32.0" >&2; exit 1 ;;
esac

[[ -f "$aeneas_lib/Aeneas/Std.olean" ]]
[[ "$(git -C "$root" hash-object crates/aspis-core/src/field.rs)" == \
  "$expected_field_blob" ]]
[[ "$(shasum -a 256 "$root/kani-verif/v5-fri-dot16-exact-20260820/src/lib.rs" | awk '{print $1}')" == \
  "$expected_reference_sha256" ]]

if [[ -n "${V5_FRI_DOT16_LEAN_OUT:-}" ]]; then
  out=$V5_FRI_DOT16_LEAN_OUT
  mkdir -p "$out"
  [[ -z "$(find "$out" -mindepth 1 -maxdepth 1 -print -quit)" ]]
else
  out=$(mktemp -d /private/tmp/v5-fri-dot16-lean432.XXXXXX)
fi
readonly out
readonly log="$out/lean432.log"
mkdir -p "$out/V5Dot16Reference"
: >"$log"

# The old reducer snapshot imports the full historical Aeneas umbrella.  Its
# definitions need only these two modules under the pinned Lean 4.32 library.
sed -e '/^import Aeneas$/c\
import Aeneas.Std\
import Aeneas.Tactic.RustAttributes' \
  "$reducer_source" >"$out/AspisCoreFieldReduceU64.lean"

aspis_path=${ASPIS_FORMAL_LEAN_PATH:-$(
  cd "$root/AspisFormal" && NO_DNA=1 lake env printenv LEAN_PATH
)}
export LEAN_PATH="$out:$aspis_path:$aeneas_lib"

compile() {
  local target=$1 source=$2
  echo "COMPILE $target" >>"$log"
  (
    cd "$(dirname "$source")"
    "$lean_bin" -j 1 -o "$out/$target.olean" "$(basename "$source")"
  ) >>"$log" 2>&1
}

compile AspisCoreFieldReduceU64 "$out/AspisCoreFieldReduceU64.lean"
compile M31ReduceU64Proof "$reducer_proof"
compile V5Dot16Reference/Types "$generated/Types.lean"
compile V5Dot16Reference/Funs "$generated/Funs.lean"
compile V5FriDot16ReferenceSemantics "$proof"

if rg -n '\b(sorry|admit|native_decide|axiom|unsafe|ofReduceBool)\b' \
    "$proof" "$reducer_proof" "$out/AspisCoreFieldReduceU64.lean" \
    "$generated/Types.lean" "$generated/Funs.lean"; then
  echo "forbidden proof shortcut or declaration" >&2
  exit 1
fi
if rg -n 'sorryAx|ofReduceBool' "$log"; then
  echo "forbidden proof dependency" >&2
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

echo "Lean 4.32 exact fixed-index V5 FRI dot semantics: PASS"
echo "V5_FRI_DOT16_LEAN_OUT=$out"
echo "log: $log"
