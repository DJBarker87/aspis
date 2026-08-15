#!/usr/bin/env bash
set -euo pipefail

replay_bundle_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$replay_bundle_dir"

shasum -a 256 -c PATCHES.sha256

if [[ $# -eq 0 ]]; then
  echo "Patch bundle verified. Pass PATCHED_AENEAS_DIR and TAIL_LLBC to replay translation."
  exit 0
fi

if [[ $# -ne 2 ]]; then
  echo "usage: $0 [PATCHED_AENEAS_DIR TAIL_LLBC]" >&2
  exit 2
fi

patched_aeneas_dir=$1
tail_llbc=$2
expected_aeneas_tree=743286e4d49cbd53a7ae9dae393a166a64886728
expected_llbc_sha=53cddb3f8c70cd264dac85f56692b0f37811d2dd39e52e2e020a8ce94afc6388
expected_lean_sha=e7aa47feaa189c67a8853212ac40596fc5da54f2736c9b1a1fcd1fca1de772bc

actual_aeneas_tree=$(git -C "$patched_aeneas_dir" rev-parse HEAD^{tree})
test "$actual_aeneas_tree" = "$expected_aeneas_tree"

actual_llbc_sha=$(shasum -a 256 "$tail_llbc" | awk '{print $1}')
test "$actual_llbc_sha" = "$expected_llbc_sha"

(cd "$patched_aeneas_dir/src" && opam exec -- dune build main.exe)

replay_output_dir=$(mktemp -d /private/tmp/aspis-aeneas-replay.XXXXXX)
trap 'rm -r "$replay_output_dir"' EXIT
"$patched_aeneas_dir/src/_build/default/main.exe" \
  -backend lean -dest "$replay_output_dir" -checks "$tail_llbc"

actual_lean_sha=$(shasum -a 256 "$replay_output_dir/Tail.lean" | awk '{print $1}')
test "$actual_lean_sha" = "$expected_lean_sha"
echo "Focused selected-candidate translation reproduced: $actual_lean_sha"
