#!/usr/bin/env bash
set -euo pipefail

readonly task=/home/dombarker/project-offloads/aspis-v7-aeneas-source-unblock-20260830
readonly aeneas="$task/aeneas-looparity-r1"
readonly input="$task/extraction/V7Tag73CurrentNormalizedHelpersOpaque.llbc"
readonly output="$task/generated-current-normalized-looparity-r1"
readonly log="$task/logs/current-normalized-looparity-aeneas-r1.log"
readonly time_log="$task/logs/current-normalized-looparity-aeneas-r1.time"

test "$(sha256sum "$aeneas" | cut -d' ' -f1)" = \
  1228a8e2f301740b46e916750811574edbbf7a948f4ba26802653f290210a918
test "$(sha256sum "$input" | cut -d' ' -f1)" = \
  a7648b39817917caba5e013f732ce72f24a9f973eb4ec6330df90ca51bda1971
test ! -e "$output"

/usr/bin/time -v -o "$time_log" \
  "$aeneas" \
    -sequential \
    -no-progress-bar \
    -abort-on-error \
    -backend lean \
    -namespace V7Tag73CurrentHelpersOpaque \
    -dest "$output" \
    -subdir V7Tag73CurrentHelpersOpaque \
    -split-files \
    -emit-json \
    "$input" \
    > "$log" 2>&1

find "$output" -type f -print0 | sort -z | xargs -0 sha256sum \
  > "$task/logs/current-normalized-looparity-aeneas-r1-output.sha256"
