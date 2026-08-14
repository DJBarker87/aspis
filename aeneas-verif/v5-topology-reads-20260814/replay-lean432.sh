#!/usr/bin/env bash
set -euo pipefail

readonly bundle="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly root="$(cd "$bundle/../.." && pwd -P)"
readonly generated="$bundle/generated/V5TopologyReadsGenerated"
readonly proof="$bundle/proof/V5TopologyReadsProof.lean"
readonly lean_bin="${LEAN432_BIN:-$(command -v lean)}"
readonly aeneas_lib="${AENEAS_LEAN_LIB:?set AENEAS_LEAN_LIB to the patched Aeneas Lean library}"
readonly expected_source_excerpt_sha256="2f3b3a99434b8dbab2c243fc5750c4c2039e77fff0f8a7b68a5d875a98b210ee"

case "$($lean_bin --version)" in
  "Lean (version 4.32.0,"*) ;;
  *) echo "expected Lean 4.32.0" >&2; exit 1 ;;
esac
[[ -f "$aeneas_lib/Aeneas/Std.olean" ]]

actual_source_excerpt_sha256=$(
  sed -n '334,448p' "$root/crates/aspis-core/src/merkle.rs" |
    shasum -a 256 | awk '{print $1}'
)
[[ "$actual_source_excerpt_sha256" == "$expected_source_excerpt_sha256" ]]

if [[ -n "${V5_TOPOLOGY_READS_REPLAY_OUT:-}" ]]; then
  out=$V5_TOPOLOGY_READS_REPLAY_OUT
  mkdir -p "$out"
  [[ -z "$(find "$out" -mindepth 1 -maxdepth 1 -print -quit)" ]]
else
  out=$(mktemp -d /private/tmp/v5-topology-reads.XXXXXX)
fi
readonly out
readonly log="$out/lean432.log"
mkdir -p "$out/V5TopologyReadsGenerated"
: > "$log"

aspis_path=$(cd "$root/AspisFormal" && NO_DNA=1 lake env printenv LEAN_PATH)
export LEAN_PATH="$out:$aspis_path:$aeneas_lib"

compile() {
  local target=$1 source=$2
  echo "COMPILE $target" >> "$log"
  "$lean_bin" -j 1 -o "$out/$target.olean" "$source" >> "$log" 2>&1
}

compile V5TopologyReadsGenerated/Types "$generated/Types.lean"
compile V5TopologyReadsGenerated/FunsExternal "$generated/FunsExternal.lean"
compile V5TopologyReadsGenerated/Funs "$generated/Funs.lean"
compile V5TopologyReadsProof "$proof"

if rg -n '\b(sorry|admit|native_decide|axiom|unsafe|ofReduceBool)\b' \
    "$proof" "$generated/FunsExternal.lean"; then
  echo "forbidden proof token or handwritten external declaration" >&2
  exit 1
fi
if rg -n 'sorryAx|ofReduceBool' "$log"; then
  echo "forbidden axiom in topology-read proof" >&2
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

echo "Lean 4.32 extracted V5 topology read bindings: PASS"
echo "V5_TOPOLOGY_READS_REPLAY_OUT=$out"
echo "log: $log"
