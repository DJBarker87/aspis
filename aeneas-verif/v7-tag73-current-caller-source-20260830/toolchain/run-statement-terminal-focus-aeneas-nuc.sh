#!/usr/bin/env bash
set -euo pipefail

readonly task=/home/dombarker/project-offloads/aspis-v7-aeneas-source-unblock-20260830
readonly aeneas="$task/repro-toolchain/aeneas-d860ac47-tag73-looparity-r1"
readonly input="$task/extraction/V7Tag73StatementTerminalNormalizedPublicResidualFocus.llbc"
readonly output="$task/generated-statement-terminal-normalized-public-residual-focus-r6"
readonly log="$task/logs/statement-terminal-normalized-public-residual-focus-aeneas-r6.log"
readonly time_log="$task/logs/statement-terminal-normalized-public-residual-focus-aeneas-r6.time"

test "$(sha256sum "$aeneas" | cut -d' ' -f1)" = \
  7a6633fbb01fad506336c1a1ef54382924d261fe0bf4ac1a8c8f119e90462a4a
test "$(sha256sum "$input" | cut -d' ' -f1)" = \
  c0f2a509a0982fb9d4d02c0b69076026d8c257f330392a3feae3278c727e1367
test ! -e "$output"

/usr/bin/time -v -o "$time_log" \
  "$aeneas" \
    -sequential \
    -no-progress-bar \
    -abort-on-error \
    -backend lean \
    -namespace V7Tag73StatementTerminalFocus \
    -dest "$output" \
    -subdir V7Tag73StatementTerminalFocus \
    -split-files \
    -emit-json \
    "$input" \
    > "$log" 2>&1

find "$output" -type f -print0 | sort -z | xargs -0 sha256sum \
  > "$task/logs/statement-terminal-normalized-public-residual-focus-aeneas-r6-output.sha256"
