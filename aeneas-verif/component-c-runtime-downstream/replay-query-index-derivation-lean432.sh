#!/bin/sh
set -eu

bundle=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
root=$(CDPATH= cd -- "$bundle/../.." && pwd)
generated="$bundle/replay/runtime_schedule/RuntimeSchedule.lean"
proof="$bundle/proof/RuntimeQueryIndexDerivation.lean"
lean_bin=${LEAN432_BIN:-/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean}
aeneas_lib=${AENEAS_LEAN_LIB:-$root/aeneas-verif/component-a-encoder-eval-residual/capstone/.lake/build/lib/lean}

if [ ! -x "$lean_bin" ]; then
  echo "missing Lean 4.32 binary: $lean_bin" >&2
  exit 1
fi

formal_path=${ASPIS_FORMAL_LEAN_PATH:-$(
  cd "$root/AspisFormal" && NO_DNA=1 lake env printenv LEAN_PATH
)}
out=$(mktemp -d "${TMPDIR:-/tmp}/v5-query-index-derivation.XXXXXX")
log="$out/lean432.log"

LEAN_PATH="$formal_path:$aeneas_lib" \
  "$lean_bin" -j 1 -o "$out/RuntimeSchedule.olean" "$generated"

LEAN_PATH="$out:$formal_path:$aeneas_lib" \
  "$lean_bin" -j 1 "$proof" >"$log" 2>&1

if rg -n '\b(sorry|admit|native_decide)\b' "$proof"; then
  echo "forbidden proof shortcut found" >&2
  exit 1
fi

if rg -n 'sorryAx' "$log"; then
  echo "unexpected sorryAx dependency" >&2
  exit 1
fi

echo "Lean 4.32 extracted V5 later-index derivation: PASS"
echo "V5_QUERY_INDEX_REPLAY_OUT=$out"
echo "log: $log"
