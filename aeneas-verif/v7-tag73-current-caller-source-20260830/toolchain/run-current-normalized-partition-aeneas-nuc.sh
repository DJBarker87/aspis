#!/usr/bin/env bash
set -euo pipefail

if [ "$#" -ne 3 ]; then
  echo "usage: $0 START END LABEL" >&2
  exit 64
fi

readonly start=$1
readonly end=$2
readonly label=$3
readonly task=/home/dombarker/project-offloads/aspis-v7-aeneas-source-unblock-20260830
readonly aeneas="$task/aeneas-repro-r1"
readonly source="$task/extraction/V7Tag73CurrentNormalizedHelpersOpaqueNoDedup.llbc"
readonly input="$task/extraction/V7Tag73CurrentNormalizedPart-${label}.llbc"
readonly output="$task/generated-current-normalized-part-${label}"
readonly log="$task/logs/current-normalized-part-${label}-aeneas.log"
readonly time_log="$task/logs/current-normalized-part-${label}-aeneas.time"

test "$(sha256sum "$aeneas" | cut -d' ' -f1)" = \
  e3e6e658ad26168421eb37627561930c1e13afa978f77b214a1201d9c4faa813
test "$(sha256sum "$source" | cut -d' ' -f1)" = \
  98d6903eebe9d891afea646133b94b05d7f28d72410f873dd46cdcaad6dc01bd
test ! -e "$input"
test ! -e "$output"

"$task/toolchain/partition-llbc-functions.py" \
  "$source" "$input" "$start" "$end" \
  > "$task/logs/current-normalized-part-${label}-partition.log"

/usr/bin/time -v -o "$time_log" \
  "$aeneas" \
    -sequential \
    -no-progress-bar \
    -abort-on-error \
    -backend lean \
    -namespace "V7Tag73CurrentNormalizedPart${label}" \
    -dest "$output" \
    -subdir "V7Tag73CurrentNormalizedPart${label}" \
    -split-files \
    -emit-json \
    "$input" \
    > "$log" 2>&1
