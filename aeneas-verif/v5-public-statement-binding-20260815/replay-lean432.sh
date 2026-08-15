#!/usr/bin/env bash
set -euo pipefail

readonly bundle="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly root="$(cd "$bundle/../.." && pwd -P)"
readonly generated="$bundle/generated/AspisV5TerminalExtract"
readonly proof="$bundle/proof/V5PublicStatementBindingProof.lean"
readonly lean_bin="${LEAN432_BIN:-$(command -v lean)}"
readonly aeneas_lib="${AENEAS_LEAN_LIB:?set AENEAS_LEAN_LIB to the Lean-4.32 Aeneas library}"

case "$($lean_bin --version)" in
  "Lean (version 4.32.0,"*) ;;
  *) echo "expected Lean 4.32.0" >&2; exit 1 ;;
esac
[[ -f "$aeneas_lib/Aeneas/Std.olean" ]]

check_hash() {
  local expected=$1 file=$2
  local actual
  actual=$(shasum -a 256 "$root/$file" | awk '{print $1}')
  [[ "$actual" == "$expected" ]] || {
    echo "source hash mismatch: $file" >&2
    exit 1
  }
}

check_hash 84c14aab5656afaf36998f7bb085c35120578a9d3eb3f4c3fe8bbf6ebbf949b7 \
  programs/aspis-verifier/src/v5_atomic_terminal.rs
check_hash 6f40c88c7a6b9f1ce657dd07eaa3e323c4bd3578839d874ba0a16c0117ce8224 \
  programs/aspis-verifier/src/v5_cu_probe.rs
check_hash 32c75a198064af1bf7700a3cf92198e6bd01d8655405a55736b37d8302c4dc09 \
  crates/aspis-statement/src/atomic_statement.rs
check_hash dadd6bac7c6c44fcb13e1a1ca26e9d2b6f767370bb6e802640948f15fc795836 \
  crates/aspis-core/src/field.rs

if [[ -n "${V5_PUBLIC_STATEMENT_REPLAY_OUT:-}" ]]; then
  out=$V5_PUBLIC_STATEMENT_REPLAY_OUT
  mkdir -p "$out"
  [[ -z "$(find "$out" -mindepth 1 -maxdepth 1 -print -quit)" ]]
else
  out=$(mktemp -d /private/tmp/v5-public-statement.XXXXXX)
fi
readonly out
readonly log="$out/lean432.log"
mkdir -p "$out/AspisV5TerminalExtract"
: > "$log"

aspis_path=$(cd "$root/AspisFormal" && NO_DNA=1 lake env printenv LEAN_PATH)
if [[ ! -f "$root/AspisFormal/.lake/build/lib/lean/AspisFormal/V5AcceptedSpendRelation.olean" ]]; then
  echo "run 'cd AspisFormal && NO_DNA=1 lake build AspisFormal.V5AcceptedSpendRelation' first" >&2
  exit 1
fi
export LEAN_PATH="$out:$aspis_path:$aeneas_lib"

compile() {
  local target=$1 source=$2
  echo "COMPILE $target" >> "$log"
  "$lean_bin" -j 1 -o "$out/$target.olean" "$source" >> "$log" 2>&1
}

compile AspisV5TerminalExtract/Types "$generated/Types.lean"
compile AspisV5TerminalExtract/FunsExternal "$generated/FunsExternal.lean"
compile AspisV5TerminalExtract/Funs "$generated/Funs.lean"
compile V5PublicStatementBindingProof "$proof"

if rg -n '^[[:space:]]*(axiom|opaque|unsafe)[[:space:]]|\b(sorry|admit|native_decide|ofReduceBool)\b' \
    "$proof" "$generated/FunsExternal.lean"; then
  echo "forbidden proof escape or handwritten axiom" >&2
  exit 1
fi

if rg -n 'sorryAx|ofReduceBool|core\.fmt\.Formatter' "$log"; then
  echo "forbidden axiom in public-statement theorem closure" >&2
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

echo "Lean 4.32 V5 public-statement binding: PASS"
echo "V5_PUBLIC_STATEMENT_REPLAY_OUT=$out"
echo "log: $log"
