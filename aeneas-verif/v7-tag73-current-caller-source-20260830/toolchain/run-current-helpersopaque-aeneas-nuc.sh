#!/usr/bin/env bash
set -euo pipefail

task=/home/dombarker/project-offloads/aspis-v7-aeneas-source-unblock-20260830
aeneas="$task/aeneas-repro-r1"
input="$task/extraction/V7Tag73CurrentHelpersOpaque.llbc"
output="$task/generated-current-helpersopaque-r1"
log="$task/logs/current-helpersopaque-aeneas-r1.log"
time_log="$task/logs/current-helpersopaque-aeneas-r1.time"

test "$(sha256sum "$aeneas" | cut -d' ' -f1)" = \
  e3e6e658ad26168421eb37627561930c1e13afa978f77b214a1201d9c4faa813
test "$(sha256sum "$input" | cut -d' ' -f1)" = \
  bc8ddfd91648c033bbd9f9f1a1c8875d425f2f6370bc4be1296e435a7df2754b
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
  > "$task/logs/current-helpersopaque-aeneas-r1-output.sha256"
