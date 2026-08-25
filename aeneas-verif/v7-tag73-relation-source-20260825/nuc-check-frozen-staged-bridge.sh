#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
backend=${AENEAS_LEAN_BACKEND:-$(cd "$script_dir/.." && pwd)}
lake_bin=${LAKE_BIN:-$HOME/.elan/bin/lake}
support=V7Tag73ExtractionTransformEquivalence
proof=V7Tag73FrozenStagedAcceptedPathBridge
log=${FOCUSED_LOG:-$script_dir/frozen-staged-bridge-focused-lean.log}

export LEAN_PATH="$backend:$script_dir"
export LEAN_NUM_THREADS=1

exec > >(tee "$log") 2>&1
cd "$backend"

# A fresh focused stage does not contain this small, package-local import.
# Compile it once; retries of the bridge leaf reuse the exact newer `.olean`.
if [[ ! -f "$script_dir/$support.olean" ||
      "$script_dir/$support.lean" -nt "$script_dir/$support.olean" ]]; then
  /usr/bin/time -v "$lake_bin" env lean -j1 \
    -o "$script_dir/$support.olean" "$script_dir/$support.lean"
fi

/usr/bin/time -v "$lake_bin" env lean -j1 \
  -o "$script_dir/$proof.olean" "$script_dir/$proof.lean"
sha256sum \
  "$script_dir/$support.lean" \
  "$script_dir/$support.olean" \
  "$script_dir/$proof.lean" \
  "$script_dir/$proof.olean"
printf '%s\n' 'V7 Tag-73 frozen-original to staged accepted-control bridge: PASS'
