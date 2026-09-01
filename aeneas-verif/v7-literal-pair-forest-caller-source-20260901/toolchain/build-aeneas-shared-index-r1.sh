#!/usr/bin/env bash
set -euo pipefail

readonly aeneas_commit=d860ac47ed548d3da6d799afc013779ce470516c
readonly dependency_image=sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7
readonly version_tag=d860ac47-tag73-looparity-shared-index-r1
readonly expected_tree=f20adbb48524bea486594d0a404dc0a40805a86b
readonly expected_binary_sha=7c8d3b918ba45ad7bb0008efe95733e72953007349d531a46e13215cc6c098bf

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo=$(git -C "$script_dir" rev-parse --show-toplevel)
: "${AENEAS_SOURCE:?set AENEAS_SOURCE to a pinned d860ac47 checkout}"
: "${OUTPUT_BIN:?set OUTPUT_BIN to the requested output binary path}"
: "${DOCKER_BIN:=docker}"
readonly base_patch_dir="$repo/aeneas-verif/v7-tag73-fixed-field-source-20260826/toolchain"
readonly base_patch_manifest="$script_dir/BASE-PATCHES.sha256"
readonly array_patch="$script_dir/aeneas-d860ac47-array-default-excluded-trait.patch"
readonly loop_patch="$script_dir/aeneas-d860ac47-loop-break-arity-preflight.patch"
readonly identity_patch="$script_dir/aeneas-d860ac47-identity-shared-slice-reborrow.patch"
readonly shared_index_patch="$script_dir/aeneas-d860ac47-shared-slice-index-nested-borrow.patch"

test "$(hostname -s)" = nuc
test "$(git -C "$AENEAS_SOURCE" rev-parse "$aeneas_commit^{commit}")" = "$aeneas_commit"
test "$("$DOCKER_BIN" image inspect "$dependency_image" --format '{{.Id}}')" = "$dependency_image"
test "$(sha256sum "$array_patch" | awk '{print $1}')" = \
  55ebde98b523517b145012227f16cbd464d37eca71a3007deba09cae296d8bca
test "$(sha256sum "$loop_patch" | awk '{print $1}')" = \
  d2edccd176882fb908ccaefd3bb3ab77a64707b33c64ff8c03709ccf6225d434
test "$(sha256sum "$identity_patch" | awk '{print $1}')" = \
  0e7a1de83e485a650f830c787f6dbb7beef8fa1e652b938e0907d5eb50b210fd
test "$(sha256sum "$shared_index_patch" | awk '{print $1}')" = \
  543b5de2bbe9c04995364b8ac4497581582fb471416fd4c3de49d72fe42b3052

cgroup_path=$(awk -F: '$1 == "0" { print $3 }' /proc/self/cgroup)
test "$(cat "/sys/fs/cgroup$cgroup_path/memory.high")" = 6442450944
test "$(cat "/sys/fs/cgroup$cgroup_path/memory.max")" = 8589934592
test "$(cat "/sys/fs/cgroup$cgroup_path/memory.swap.max")" = 0

build_parent=${BUILD_PARENT:-/home/dombarker/project-offloads}
build_parent=${build_parent%/}
build_root=$(mktemp -d "$build_parent/v7-shared-index-aeneas-build.XXXXXX")
container_name="aspis-v7-shared-index-aeneas-build-$$"
cleanup() {
  "$DOCKER_BIN" rm -f "$container_name" >/dev/null 2>&1 || true
  case "$build_root" in
    "$build_parent"/v7-shared-index-aeneas-build.*)
      rm -rf -- "$build_root" ;;
    *)
      echo "refusing unexpected cleanup target: $build_root" >&2 ;;
  esac
}
trap cleanup EXIT

mkdir -p "$build_root/aeneas" "$build_root/output"
git -C "$AENEAS_SOURCE" archive "$aeneas_commit" | tar -x -C "$build_root/aeneas"
git -C "$build_root/aeneas" init -q
git -C "$build_root/aeneas" add -A
git -C "$build_root/aeneas" -c user.name=Codex -c user.email=codex@local commit -qm baseline

while read -r expected relative; do
  patch_file="$base_patch_dir/${relative#toolchain/}"
  test "$(sha256sum "$patch_file" | awk '{print $1}')" = "$expected"
  git -C "$build_root/aeneas" apply --check "$patch_file"
  git -C "$build_root/aeneas" apply "$patch_file"
done < "$base_patch_manifest"

git -C "$build_root/aeneas" apply --check "$array_patch"
git -C "$build_root/aeneas" apply "$array_patch"

git -C "$build_root/aeneas" apply --check "$loop_patch"
git -C "$build_root/aeneas" apply "$loop_patch"

git -C "$build_root/aeneas" apply --check "$identity_patch"
git -C "$build_root/aeneas" apply "$identity_patch"
git -C "$build_root/aeneas" apply --check "$shared_index_patch"
git -C "$build_root/aeneas" apply "$shared_index_patch"
git -C "$build_root/aeneas" diff --check
git -C "$build_root/aeneas" add -A
patched_tree=$(git -C "$build_root/aeneas" write-tree)
test "$patched_tree" = "$expected_tree"
printf 'patched tree: %s\n' "$patched_tree"

"$DOCKER_BIN" run --rm --name "$container_name" \
  --memory-reservation=6g --memory=8g --memory-swap=8g \
  -e AENEAS_BUILD_VERSION="$version_tag" \
  -v "$build_root/aeneas:/work/aeneas" \
  -v "$build_root/output:/work/output" \
  "$dependency_image" bash -lc '
    set -euo pipefail
    export OPAMJOBS=2 DUNEJOBS=2
    cd /work/aeneas/src
    AENEAS_VERSION="$AENEAS_BUILD_VERSION" OCAMLPARAM=_,ccopt=-static \
      opam exec -- dune build main.exe --profile release -j 2
    cp _build/default/main.exe /work/output/aeneas
  '

binary="$build_root/output/aeneas"
test "$("$binary" -version)" = "aeneas $version_tag"
binary_sha=$(sha256sum "$binary" | awk '{print $1}')
test "$binary_sha" = "$expected_binary_sha"
mkdir -p "$(dirname -- "$OUTPUT_BIN")"
install -m 0755 "$binary" "$OUTPUT_BIN"
printf 'binary SHA-256: %s\n' "$binary_sha"
