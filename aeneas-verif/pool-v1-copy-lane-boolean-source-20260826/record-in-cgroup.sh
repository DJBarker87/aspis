#!/usr/bin/env bash
set -euo pipefail

readonly evidence_dir=$1
shift
readonly cgroup_path=$(awk -F: '$1 == "0" { print $3 }' /proc/self/cgroup)
readonly cgroup_root="/sys/fs/cgroup$cgroup_path"

[[ "$(hostname -s)" == nuc ]]
[[ "$(<"$cgroup_root/memory.high")" == 19327352832 ]]
[[ "$(<"$cgroup_root/memory.max")" == 21474836480 ]]
[[ "$(<"$cgroup_root/memory.swap.max")" == 0 ]]

{
  printf 'cwd='; pwd
  printf 'command='; printf ' %q' "$@"; printf '\n'
} > "$evidence_dir/command.txt"

set +e
/usr/bin/time -v -o "$evidence_dir/time.txt" "$@" \
  > "$evidence_dir/stdout.txt" 2> "$evidence_dir/stderr.txt"
status=$?
set -e
printf '%s\n' "$status" > "$evidence_dir/exit-status.txt"

{
  printf 'memory.high='; tr -d '\n' < "$cgroup_root/memory.high"; printf '\n'
  printf 'memory.max='; tr -d '\n' < "$cgroup_root/memory.max"; printf '\n'
  printf 'memory.swap.max='; tr -d '\n' < "$cgroup_root/memory.swap.max"; printf '\n'
  printf 'memory.peak='; tr -d '\n' < "$cgroup_root/memory.peak"; printf '\n'
  printf 'memory.swap.current='; tr -d '\n' < "$cgroup_root/memory.swap.current"; printf '\n'
  cat "$cgroup_root/memory.events"
} > "$evidence_dir/cgroup.txt"

exit "$status"
