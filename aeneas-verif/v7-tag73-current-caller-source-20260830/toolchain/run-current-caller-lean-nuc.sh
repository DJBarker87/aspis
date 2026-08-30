#!/usr/bin/env bash
set -euo pipefail

export PATH=/home/dombarker/.elan/bin:/usr/local/bin:/usr/bin:/bin

task=/home/dombarker/project-offloads/aspis-v7-aeneas-source-unblock-20260830
stage=${CURRENT_CALLER_STAGE:-$task/staged-current-helpersopaque-final-r3}
runtime=/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/aeneas-full/backends/lean
package_cache=/home/dombarker/project-offloads/ZK-v7-one-tx-formal-consolidation-20260828/AspisFormal
lean=/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean
evidence=${CURRENT_CALLER_EVIDENCE:-$task/logs/current-caller-lean-final-r5}
stop_after=${STOP_AFTER:-}

test -f "$stage/CurrentCallerCompileOrder.txt"
test -x "$lean"
test "$(git -C "$package_cache/.lake/packages/mathlib" rev-parse HEAD)" = \
  81a5d257c8e410db227a6665ed08f64fea08e997
mkdir -p "$evidence"
cd "$runtime"

# Do not invoke Lake here. The pinned Aeneas runtime's package URL changed
# spelling after its accepted cache was built, and Lake would delete and
# refetch that otherwise-valid cache. Reuse the byte-compatible Lean 4.32
# package graph explicitly; the complete dependency revisions match the
# current Aeneas manifest.
base="$runtime/.lake/build/lib/lean"
package_count=0
for package_path in "$package_cache"/.lake/packages/*/.lake/build/lib/lean; do
  test -d "$package_path"
  base="$package_path:$base"
  package_count=$((package_count + 1))
done
test "$package_count" = 8
export LEAN_PATH="$stage:$base"

while IFS= read -r target; do
  test -n "$target"
  slug=${target//\//-}
  slug=${slug%.lean}
  output="$stage/${target%.lean}.olean"
  time_file="$evidence/$slug.time"
  if test -f "$output" && test -s "$time_file"; then
    printf 'REUSE %s\n' "$target"
    if test "$target" = "$stop_after"; then
      exit 0
    fi
    continue
  fi
  printf 'TARGET %s\n' "$target"
  /usr/bin/time -v -o "$time_file" \
    "$lean" -j 1 -R "$stage" \
      -o "$output" "$stage/$target"
  if test "$target" = "$stop_after"; then
    exit 0
  fi
done < "$stage/CurrentCallerCompileOrder.txt"

# Raw generated templates are archival and intentionally excluded.  Every
# compiled source must remain free of proof holes, native-decide shortcuts,
# and project-defined axioms.
if find "$stage" -type f -name '*.lean' ! -name '*_Template.lean' -print0 |
    xargs -0 rg -n \
      '\bsorry\b|\badmit\b|sorryAx|native_decide|^[[:space:]]*axiom[[:space:]]'; then
  echo 'forbidden construct in compiled staged source' >&2
  exit 1
fi

find "$stage" -type f -print0 | sort -z | xargs -0 sha256sum \
  > "$evidence/staged-output.sha256"
printf 'current production caller helper-split Lean replay: PASS\n'
