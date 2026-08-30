#!/usr/bin/env bash
set -euo pipefail

readonly task=/home/dombarker/project-offloads/aspis-v7-aeneas-source-unblock-20260830
readonly aeneas="$task/repro-toolchain/aeneas-d860ac47-tag73-looparity-r1"
readonly input="$task/extraction/V7Tag73CurrentNormalizedStatementOwnedTwoHelpersOpaque.llbc"
readonly output="$task/generated-current-normalized-statement-owned-twohelpers-final-r9"
readonly log="$task/logs/current-normalized-statement-owned-twohelpers-aeneas-r9.log"
readonly time_log="$task/logs/current-normalized-statement-owned-twohelpers-aeneas-r9.time"

test "$(sha256sum "$aeneas" | cut -d' ' -f1)" = \
  7a6633fbb01fad506336c1a1ef54382924d261fe0bf4ac1a8c8f119e90462a4a
test "$(sha256sum "$input" | cut -d' ' -f1)" = \
  b4d931347481d70935e1aa6445173f68a38e678cc3b67eba6a467ca502c1be69
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
  > "$task/logs/current-normalized-statement-owned-twohelpers-aeneas-r9-output.sha256"
