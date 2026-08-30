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
readonly source="$task/extraction/V7Tag73FinishOnefoldNormalizedNoDedup.llbc"
readonly input="$task/extraction/V7Tag73FinishOnefoldPart-${label}.llbc"
readonly output="$task/generated-finish-onefold-part-${label}"
readonly log="$task/logs/finish-onefold-part-${label}-aeneas.log"
readonly time_log="$task/logs/finish-onefold-part-${label}-aeneas.time"

test "$(sha256sum "$aeneas" | cut -d' ' -f1)" = \
  e3e6e658ad26168421eb37627561930c1e13afa978f77b214a1201d9c4faa813
test "$(sha256sum "$source" | cut -d' ' -f1)" = \
  0244da00d59dac0f19fae556a50ee7781a9948fa791e526ebeb0cc8db67cdfbc
test ! -e "$input"
test ! -e "$output"

"$task/toolchain/partition-llbc-functions.py" \
  "$source" "$input" "$start" "$end" \
  > "$task/logs/finish-onefold-part-${label}-partition.log"

/usr/bin/time -v -o "$time_log" \
  "$aeneas" \
    -sequential \
    -no-progress-bar \
    -abort-on-error \
    -backend lean \
    -namespace "V7Tag73FinishOnefoldPart${label}" \
    -dest "$output" \
    -subdir "V7Tag73FinishOnefoldPart${label}" \
    -split-files \
    -emit-json \
    "$input" \
    > "$log" 2>&1
