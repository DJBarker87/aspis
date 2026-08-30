#!/usr/bin/env bash
set -euo pipefail

readonly task=/home/dombarker/project-offloads/aspis-v7-aeneas-source-unblock-20260830
readonly caller_source="$task/generated-current-normalized-statement-owned-twohelpers-final-r9/V7Tag73CurrentHelpersOpaque"
readonly gamma_source="$task/raw-focused-split-r2/V7GammaSlotMajorLiteral"
readonly dot_source="$task/raw-focused-split-r2/V7Qm31Dot3Reduced"
readonly output="$task/raw-current-normalized-statement-owned-twohelpers-final-r9"

for source in "$caller_source" "$gamma_source" "$dot_source"; do
  test -f "$source/Types.lean"
  test -f "$source/Funs.lean"
done
test ! -e "$output"

mkdir "$output"
ln -s "$caller_source" "$output/V7Tag73CurrentHelpersOpaque"
ln -s "$gamma_source" "$output/V7GammaSlotMajorLiteral"
ln -s "$dot_source" "$output/V7Qm31Dot3Reduced"

find -L "$output" -maxdepth 2 -type f -print0 | sort -z | xargs -0 sha256sum \
  > "$task/logs/current-normalized-statement-owned-twohelpers-raw-r9.sha256"
