#!/usr/bin/env bash
set -euo pipefail

readonly bundle="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly root="$(cd "$bundle/../.." && pwd -P)"
readonly generated="$bundle/generated/V5FriDecoderReference"
readonly proof="$bundle/proof/V5FriDecoderReferenceSemantics.lean"
readonly lean_bin="${LEAN432_BIN:-$(command -v lean)}"
readonly aeneas_lib="${AENEAS_LEAN_LIB:?set AENEAS_LEAN_LIB to the matching Lean 4.32 Aeneas library}"

case "$($lean_bin --version)" in
  "Lean (version 4.32.0,"*) ;;
  *) echo "expected Lean 4.32.0" >&2; exit 1 ;;
esac

[[ -f "$aeneas_lib/Aeneas/Std.olean" ]]

if [[ -n "${V5_FRI_DECODER_LEAN_OUT:-}" ]]; then
  out=$V5_FRI_DECODER_LEAN_OUT
  mkdir -p "$out"
  [[ -z "$(find "$out" -mindepth 1 -maxdepth 1 -print -quit)" ]]
else
  out=$(mktemp -d /private/tmp/v5-fri-decoder-lean432.XXXXXX)
fi
readonly out
readonly log="$out/lean432.log"
mkdir -p "$out/V5FriDecoderReference"
: >"$log"

aspis_path=${ASPIS_FORMAL_LEAN_PATH:-$(
  cd "$root/AspisFormal" && NO_DNA=1 lake env printenv LEAN_PATH
)}
readonly transition_out="${V5_FRI_COMBINED_LEAN_OUT:?set V5_FRI_COMBINED_LEAN_OUT to the checked transition-semantics olean directory}"
readonly component_b_out="${V5_FRI_COMPONENTB_LEAN_OUT:?set V5_FRI_COMPONENTB_LEAN_OUT to the checked Component-B correspondence olean directory}"
export LEAN_PATH="$out:$transition_out:$component_b_out:$aspis_path:$aeneas_lib"

compile() {
  local target=$1 source=$2
  echo "COMPILE $target" >>"$log"
  (
    cd "$(dirname "$source")"
    "$lean_bin" -j 1 -o "$out/$target.olean" "$(basename "$source")"
  ) >>"$log" 2>&1
}

compile V5FriDecoderReference/Types "$generated/Types.lean"
compile V5FriDecoderReference/FunsExternal "$generated/FunsExternal.lean"
compile V5FriDecoderReference/Funs "$generated/Funs.lean"
compile V5FriDecoderReferenceSemantics "$proof"

if rg -n '\b(sorry|admit|native_decide|axiom|unsafe|ofReduceBool)\b' \
    "$proof" "$generated/Types.lean" "$generated/FunsExternal.lean" \
    "$generated/Funs.lean"; then
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

echo "Lean 4.32 exact V5 FRI decoder semantics: PASS"
echo "V5_FRI_DECODER_LEAN_OUT=$out"
echo "log: $log"
