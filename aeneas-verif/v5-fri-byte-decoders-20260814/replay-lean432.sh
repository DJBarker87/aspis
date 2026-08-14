#!/usr/bin/env bash
set -euo pipefail

readonly bundle="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly root="$(cd "$bundle/../.." && pwd -P)"
readonly generated="$bundle/generated/V5FriDecoderGenerated"
readonly proof="$bundle/proof/V5FriDecoderProof.lean"
readonly lean_bin="${LEAN432_BIN:-$(command -v lean)}"
readonly aeneas_lib="${AENEAS_LEAN_LIB:?set AENEAS_LEAN_LIB to the patched Aeneas Lean library}"
readonly expected_field_blob="a28ff94de05265102ca819849805a7f73c675800"

case "$($lean_bin --version)" in
  "Lean (version 4.32.0,"*) ;;
  *) echo "expected Lean 4.32.0" >&2; exit 1 ;;
esac

[[ -f "$aeneas_lib/Aeneas/Std.olean" ]]
[[ "$(git -C "$root" hash-object crates/aspis-core/src/field.rs)" == \
  "$expected_field_blob" ]]

if [[ -n "${V5_FRI_DECODER_REPLAY_OUT:-}" ]]; then
  out=$V5_FRI_DECODER_REPLAY_OUT
  mkdir -p "$out"
  [[ -z "$(find "$out" -mindepth 1 -maxdepth 1 -print -quit)" ]]
else
  out=$(mktemp -d /private/tmp/v5-fri-byte-decoders.XXXXXX)
fi
readonly out
readonly log="$out/lean432.log"
mkdir -p "$out/V5FriDecoderGenerated"
: > "$log"

aspis_path=$(cd "$root/AspisFormal" && NO_DNA=1 lake env printenv LEAN_PATH)
export LEAN_PATH="$out:$aspis_path:$aeneas_lib"

compile() {
  local target=$1 source=$2
  echo "COMPILE $target" >> "$log"
  "$lean_bin" -j 1 -o "$out/$target.olean" "$source" >> "$log" 2>&1
}

compile V5FriDecoderGenerated/Types "$generated/Types.lean"
compile V5FriDecoderGenerated/FunsExternal "$generated/FunsExternal.lean"
compile V5FriDecoderGenerated/Funs "$generated/Funs.lean"
compile V5FriDecoderProof "$proof"

if rg -n '\b(sorry|admit|native_decide|axiom|unsafe|ofReduceBool)\b' \
    "$proof" "$generated/FunsExternal.lean"; then
  echo "forbidden proof token or handwritten external declaration" >&2
  exit 1
fi
if rg -n 'sorryAx|ofReduceBool' "$log"; then
  echo "forbidden axiom in decoder equality proof" >&2
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

echo "Lean 4.32 extracted V5 FRI byte-decoder equality: PASS"
echo "V5_FRI_DECODER_REPLAY_OUT=$out"
echo "log: $log"
