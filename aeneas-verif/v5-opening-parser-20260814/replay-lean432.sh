#!/usr/bin/env bash
set -euo pipefail

readonly bundle="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly root="$(cd "$bundle/../.." && pwd -P)"
readonly generated="$bundle/generated/V5OpeningParserGenerated"
readonly proof="$bundle/proof/V5OpeningParserProof.lean"
readonly lean_bin="${LEAN432_BIN:-$(command -v lean)}"
readonly aeneas_lib="${AENEAS_LEAN_LIB:?set AENEAS_LEAN_LIB to the patched Aeneas Lean library}"
readonly expected_source_prefix_sha256="d4a50847fd2bf42d07e1c811d53779447fc91ccd3c4f803022c8bf639aa8fd1c"

case "$($lean_bin --version)" in
  "Lean (version 4.32.0,"*) ;;
  *) echo "expected Lean 4.32.0" >&2; exit 1 ;;
esac
[[ -f "$aeneas_lib/Aeneas/Std.olean" ]]

actual_source_prefix_sha256=$(
  sed -n '1,205p' "$root/crates/aspis-core/src/state_only_private_openings.rs" |
    shasum -a 256 | awk '{print $1}'
)
[[ "$actual_source_prefix_sha256" == "$expected_source_prefix_sha256" ]]

if [[ -n "${V5_OPENING_PARSER_REPLAY_OUT:-}" ]]; then
  out=$V5_OPENING_PARSER_REPLAY_OUT
  mkdir -p "$out"
  [[ -z "$(find "$out" -mindepth 1 -maxdepth 1 -print -quit)" ]]
else
  out=$(mktemp -d /private/tmp/v5-opening-parser.XXXXXX)
fi
readonly out
readonly log="$out/lean432.log"
mkdir -p "$out/V5OpeningParserGenerated"
: > "$log"

aspis_path=${ASPIS_FORMAL_LEAN_PATH:-$(
  cd "$root/AspisFormal" && NO_DNA=1 lake env printenv LEAN_PATH
)}
export LEAN_PATH="$out:$aspis_path:$aeneas_lib"

compile() {
  local target=$1 source=$2
  echo "COMPILE $target" >> "$log"
  "$lean_bin" -j 1 -o "$out/$target.olean" "$source" >> "$log" 2>&1
}

compile V5OpeningParserGenerated/Types "$generated/Types.lean"
compile V5OpeningParserGenerated/FunsExternal "$generated/FunsExternal.lean"
compile V5OpeningParserGenerated/Funs "$generated/Funs.lean"
compile V5OpeningParserProof "$proof"

if rg -n '\b(sorry|admit|native_decide|axiom|unsafe|ofReduceBool)\b' \
    "$proof" "$generated/FunsExternal.lean"; then
  echo "forbidden proof token or handwritten external declaration" >&2
  exit 1
fi
if rg -n 'sorryAx|ofReduceBool' "$log"; then
  echo "forbidden axiom in opening parser proof" >&2
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

echo "Lean 4.32 extracted V5 raw opening parser equality: PASS"
echo "V5_OPENING_PARSER_REPLAY_OUT=$out"
echo "log: $log"
