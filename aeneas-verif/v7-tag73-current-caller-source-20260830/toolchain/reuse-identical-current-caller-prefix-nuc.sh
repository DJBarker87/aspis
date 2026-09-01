#!/usr/bin/env bash
set -euo pipefail

if test "$#" -ne 4; then
  echo "usage: $0 OLD_STAGE NEW_STAGE OLD_EVIDENCE NEW_EVIDENCE" >&2
  exit 2
fi

old_stage=$1
new_stage=$2
old_evidence=$3
new_evidence=$4

test -f "$old_stage/CurrentCallerCompileOrder.txt"
test -f "$new_stage/CurrentCallerCompileOrder.txt"
mkdir -p "$new_evidence"

# The memory-safe staging generator may extend the compile order by splitting
# the first changed suffix module.  Reuse is therefore defined by the maximal
# byte-identical target prefix, not by equality of the complete order files.
# Every reused target must still exist, have identical source, and have its
# prior `.olean` plus timing evidence.

reused=0
while IFS= read -r target; do
  test -n "$target"
  old_source="$old_stage/$target"
  new_source="$new_stage/$target"
  test -f "$new_source"
  if ! test -f "$old_source"; then
    printf 'FIRST_NEW %s\n' "$target"
    break
  fi
  if ! cmp -s "$old_source" "$new_source"; then
    printf 'FIRST_CHANGED %s\n' "$target"
    break
  fi

  old_olean="$old_stage/${target%.lean}.olean"
  new_olean="$new_stage/${target%.lean}.olean"
  slug=${target//\//-}
  slug=${slug%.lean}
  old_time="$old_evidence/$slug.time"
  new_time="$new_evidence/$slug.time"
  test -s "$old_olean"
  test -s "$old_time"
  mkdir -p "$(dirname -- "$new_olean")"
  cp --reflink=auto "$old_olean" "$new_olean"
  cp --reflink=auto "$old_time" "$new_time"
  reused=$((reused + 1))
done < "$new_stage/CurrentCallerCompileOrder.txt"

test "$reused" -gt 0
printf 'REUSED_IDENTICAL_PREFIX %s\n' "$reused"
