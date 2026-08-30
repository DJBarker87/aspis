#!/usr/bin/env bash
set -euo pipefail
export PATH=/home/dombarker/.elan/bin:/usr/local/bin:/usr/bin:/bin

task=/home/dombarker/project-offloads/aspis-v7-aeneas-source-unblock-20260830
stage="$task/staged-qm31-dot3-literal-r1"
runtime=/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/aeneas-full/backends/lean
evidence="$task/logs/qm31-dot3-literal-lean-r1"

mkdir -p "$evidence"
cd "$runtime"
base=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$stage:$base"

while IFS= read -r target; do
  slug=${target//\//-}
  slug=${slug%.lean}
  printf 'TARGET %s\n' "$target"
  /usr/bin/time -v -o "$evidence/$slug.time" \
    lake env lean -j 1 -R "$stage" \
      -o "$stage/${target%.lean}.olean" "$stage/$target"
done < "$stage/Qm31Dot3CompileOrder.txt"

printf 'qm31_dot3 literal Lean replay: PASS\n'
