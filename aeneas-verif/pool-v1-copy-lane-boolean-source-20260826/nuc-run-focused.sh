#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 3 ]]; then
  echo "usage: $0 UNIT EVIDENCE_DIR COMMAND [ARG ...]" >&2
  exit 2
fi

readonly unit=$1
readonly evidence_dir=$2
readonly bundle=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
shift 2

[[ "$(hostname -s)" == nuc ]]
[[ "$unit" == aspis-copy-lane-* ]]
[[ "$evidence_dir" == "$bundle"/evidence/* ]]
mkdir -p "$evidence_dir"

awk '/^MemAvailable:|^SwapTotal:|^SwapFree:/ { print }' /proc/meminfo \
  > "$evidence_dir/host-before.txt"
readonly available_kib=$(awk '/^MemAvailable:/ { print $2 }' /proc/meminfo)
(( available_kib >= 24 * 1024 * 1024 ))

systemd-run --user --scope --unit="$unit" \
  -p MemoryHigh=18G -p MemoryMax=20G -p MemorySwapMax=0 -p TasksMax=64 \
  "$bundle/record-in-cgroup.sh" "$evidence_dir" "$@"

awk '/^MemAvailable:|^SwapTotal:|^SwapFree:/ { print }' /proc/meminfo \
  > "$evidence_dir/host-after.txt"
