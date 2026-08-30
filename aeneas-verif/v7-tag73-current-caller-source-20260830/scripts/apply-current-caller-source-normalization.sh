#!/usr/bin/env bash
set -euo pipefail

if test "$#" -ne 1; then
  echo "usage: $0 SOURCE_COPY" >&2
  exit 2
fi

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
bundle_dir=$(CDPATH= cd -- "$script_dir/.." && pwd)
repo=$1
readonly source_revision=bcd03b12293f2737dfa1da1436092a0a24a6ae24
readonly patch="$bundle_dir/toolchain/current-caller-aeneas-source-normalization.patch"

test -d "$repo"
test "$(sha256sum "$patch" | cut -d' ' -f1)" = \
  bd3e715a32bb0dff3cf1bab56c65df09dd596ad772be63b92d76ebd5d6d8f3a9

if git -C "$repo" rev-parse HEAD >/dev/null 2>&1; then
  test "$(git -C "$repo" rev-parse HEAD)" = "$source_revision"
  git -C "$repo" diff --quiet
  git -C "$repo" diff --cached --quiet
fi

(cd "$repo" && sha256sum -c "$bundle_dir/source/NORMALIZATION-INPUT.sha256")
(cd "$repo" && git apply --recount --check "$patch")
(cd "$repo" && git apply --recount "$patch")
(cd "$repo" && sha256sum -c "$bundle_dir/source/NORMALIZED-KEY-SOURCE.sha256")

if git -C "$repo" rev-parse HEAD >/dev/null 2>&1; then
  test "$(git -C "$repo" diff --name-only | sort)" = \
    "$(printf '%s\n' \
      crates/aspis-core/src/state_only_hiding.rs \
      crates/aspis-core/src/sumcheck.rs | sort)"
fi

printf 'current caller source normalization: PASS\n'
