#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
bundle_dir=$(CDPATH= cd -- "$script_dir/.." && pwd)

readonly aeneas_commit=d860ac47ed548d3da6d799afc013779ce470516c
readonly charon_commit=cb50ff16b9f1066b8a97dc06da704de2da2fa41c
readonly patched_tree=de8340302a8a14448e47e2a878ac726ed29228b2
readonly aeneas_archive_sha=472d499c25a7e944f6754126df51de758cd8a5733f5a6ec2ce653c652cb65722

: "${AENEAS_SOURCE_ROOT:?set AENEAS_SOURCE_ROOT to the pinned Aeneas checkout}"
: "${CHARON_SOURCE_ROOT:?set CHARON_SOURCE_ROOT to the pinned Charon checkout}"
aeneas_source=$AENEAS_SOURCE_ROOT
aeneas_archive=${AENEAS_SOURCE_ARCHIVE:-}
charon_source=$CHARON_SOURCE_ROOT
output_dir=${OUTPUT_DIR:-$bundle_dir/evidence/toolchain-build-terminalcapture-local-output}
output_bin="$output_dir/aeneas-d860ac47-tag73-fixed-field"

test "$(uname -s)" = Darwin
if test -n "$aeneas_archive"; then
  test "$(shasum -a 256 "$aeneas_archive" | awk '{print $1}')" = \
    "$aeneas_archive_sha"
else
  test "$(git -C "$aeneas_source" rev-parse "$aeneas_commit^{commit}")" = "$aeneas_commit"
fi
test "$(git -C "$charon_source" rev-parse "$charon_commit^{commit}")" = "$charon_commit"
(cd "$bundle_dir" && sha256sum -c toolchain/PATCHES.sha256)

build_root=$(mktemp -d /tmp/v7-tag73-aeneas-local.XXXXXX)
cleanup() {
  case "$build_root" in
    /tmp/v7-tag73-aeneas-local.*) /bin/rm -rf -- "$build_root" ;;
    *) echo "refusing unexpected temporary path: $build_root" >&2 ;;
  esac
}
trap cleanup EXIT

mkdir -p "$build_root/aeneas" "$build_root/charon" "$build_root/prefix" "$output_dir"
if test -n "$aeneas_archive"; then
  tar -x -f "$aeneas_archive" -C "$build_root/aeneas"
else
  git -C "$aeneas_source" archive "$aeneas_commit" | tar -x -C "$build_root/aeneas"
fi
git -C "$charon_source" archive "$charon_commit" | tar -x -C "$build_root/charon"
git -C "$build_root/aeneas" init -q
git -C "$build_root/aeneas" add -A
git -C "$build_root/aeneas" -c user.name='Aeneas replay' -c user.email=replay@localhost \
  commit -qm baseline
for patch_file in \
  "$script_dir/aeneas-d860ac47-ocaml52-exhaustive-match.patch" \
  "$script_dir/aeneas-d860ac47-v6-result-flow.patch" \
  "$script_dir/aeneas-d860ac47-static-return-loan.patch" \
  "$script_dir/aeneas-d860ac47-loop-input-identity.patch" \
  "$script_dir/aeneas-d860ac47-shared-box-deref-copy.patch" \
  "$script_dir/aeneas-d860ac47-loop-return-drop-flag.patch" \
  "$script_dir/aeneas-d860ac47-loop-break-lifetime-cleanup.patch" \
  "$script_dir/aeneas-d860ac47-zero-write-shared-cont.patch" \
  "$script_dir/aeneas-d860ac47-loop-return-drop-switch.patch" \
  "$script_dir/aeneas-d860ac47-terminal-return-capture.patch"
do
  git -C "$build_root/aeneas" apply --check "$patch_file"
  git -C "$build_root/aeneas" apply "$patch_file"
done
git -C "$build_root/aeneas" diff --check
git -C "$build_root/aeneas" add -A
test "$(git -C "$build_root/aeneas" write-tree)" = "$patched_tree"

opam exec -- dune build --root "$build_root/charon" @install --profile release -j 2
opam exec -- dune install --root "$build_root/charon" \
  --prefix "$build_root/prefix"
export OCAMLPATH="$build_root/prefix/lib${OCAMLPATH:+:$OCAMLPATH}"
AENEAS_VERSION=d860ac47-tag73-fixed-field \
  opam exec -- dune build --root "$build_root/aeneas" src/main.exe \
    --profile release -j 2
cp "$build_root/aeneas/_build/default/src/main.exe" "$output_bin"
chmod 0755 "$output_bin"
test "$("$output_bin" -version)" = 'aeneas d860ac47-tag73-fixed-field'
shasum -a 256 "$output_bin" > "$output_dir/binary.sha256"
printf 'local patched Aeneas build: PASS\n'
