#!/usr/bin/env bash
set -euo pipefail
export PATH=/home/dombarker/.elan/bin:/usr/local/bin:/usr/bin:/bin

task=/home/dombarker/project-offloads/aspis-v7-aeneas-source-unblock-20260830
stage="$task/staged-focused-split-r5"
runtime=/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/aeneas-full/backends/lean
evidence="$task/logs/focused-circle-preflight-r2"

mkdir -p "$evidence"
cd "$runtime"
base=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$stage:$base"

compile() {
  local target=$1
  local slug=${target//\//-}
  slug=${slug%.lean}
  printf 'TARGET %s\n' "$target"
  /usr/bin/time -v -o "$evidence/$slug.time" \
    lake env lean -j 1 -R "$stage" \
      -o "$stage/${target%.lean}.olean" "$stage/$target"
}

compile V7AuthenticateFoldGammaOpaque/CircleTableSupport.lean
compile V7AuthenticateFoldGammaOpaque/CircleTable_RATE512_CIRCLE_LOW8_WINDOW_Chunk00.lean

printf 'focused circle-table preflight: PASS\n'
