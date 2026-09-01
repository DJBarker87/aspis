#!/usr/bin/env bash
set -euo pipefail

if test "$#" -ne 1; then
  echo "usage: $0 BASE_NORMALIZED_SOURCE_COPY" >&2
  exit 2
fi

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
bundle_dir=$(CDPATH= cd -- "$script_dir/.." && pwd)
repo=$1
readonly source_revision=bcd03b12293f2737dfa1da1436092a0a24a6ae24
readonly patch="$bundle_dir/toolchain/current-statement-terminal-aeneas-source-normalization.patch"

test -d "$repo"
test "$(sha256sum "$patch" | cut -d' ' -f1)" = \
  22efcf75526f48466c6879dfe1f12cebc1e0ab398f9e3efaccb89ef69cb8906c

if git -C "$repo" rev-parse HEAD >/dev/null 2>&1; then
  test "$(git -C "$repo" rev-parse HEAD)" = "$source_revision"
fi

(cd "$repo" && sha256sum -c "$bundle_dir/source/NORMALIZED-KEY-SOURCE.sha256")
test "$(sha256sum "$repo/crates/aspis-statement/src/atomic_state_only_terminal.rs" | cut -d' ' -f1)" = \
  33d518ddc432866ae822917fb18a4ad5463d3fb6994fa448d097e303d937d7a9
(cd "$repo" && git apply --recount --check "$patch")
(cd "$repo" && git apply --recount "$patch")
(cd "$repo" && sha256sum -c \
  "$bundle_dir/source/NORMALIZED-STATEMENT-OWNED-KEY-SOURCE.sha256")

if git -C "$repo" rev-parse HEAD >/dev/null 2>&1; then
  test "$(git -C "$repo" diff --name-only | sort)" = \
    "$(printf '%s\n' \
      crates/aspis-core/src/state_only_hiding.rs \
      crates/aspis-core/src/sumcheck.rs \
      crates/aspis-statement/src/atomic_state_only_terminal.rs \
      programs/aspis-verifier/src/v7_verifier.rs | sort)"
fi

printf 'current statement/caller source normalization: PASS\n'
