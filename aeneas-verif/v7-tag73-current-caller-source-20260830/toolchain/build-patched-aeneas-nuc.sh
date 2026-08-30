#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
bundle_dir=$(CDPATH= cd -- "$script_dir/.." && pwd)

readonly aeneas_commit=d860ac47ed548d3da6d799afc013779ce470516c
readonly patched_tree=031a61b263bffddabfd04e3476fb53a3754fdb64
readonly dependency_image=sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7
readonly version_tag=d860ac47-tag73-looparity-r1
readonly expected_binary_sha=7a6633fbb01fad506336c1a1ef54382924d261fe0bf4ac1a8c8f119e90462a4a

aeneas_source=${AENEAS_SOURCE_ROOT:-/home/dombarker/project-offloads/aeneas-d860-v6-src}
output_dir=${OUTPUT_DIR:-/home/dombarker/project-offloads/v7-tag73-current-caller-toolchain}

test "$(hostname -s)" = nuc
test "$(git -C "$aeneas_source" rev-parse "$aeneas_commit^{commit}")" = "$aeneas_commit"
(cd "$bundle_dir" && sha256sum -c toolchain/BASE-PATCHES.sha256)
test "$(docker image inspect "$dependency_image" --format '{{.Id}}')" = "$dependency_image"

cgroup_path=$(awk -F: '$1 == "0" { print $3 }' /proc/self/cgroup)
memory_high=$(tr -d '\n' < "/sys/fs/cgroup$cgroup_path/memory.high")
memory_max=$(tr -d '\n' < "/sys/fs/cgroup$cgroup_path/memory.max")
memory_swap_max=$(tr -d '\n' < "/sys/fs/cgroup$cgroup_path/memory.swap.max")
test "$memory_high" = 6442450944
test "$memory_max" = 8589934592
test "$memory_swap_max" = 0

build_root=$(mktemp -d /home/dombarker/project-offloads/v7-current-caller-aeneas-build.XXXXXX)
container_name="aspis-v7-current-caller-aeneas-build-$$"
cleanup() {
  docker rm -f "$container_name" >/dev/null 2>&1 || true
  case "$build_root" in
    /home/dombarker/project-offloads/v7-current-caller-aeneas-build.*)
      rm -rf -- "$build_root" ;;
    *)
      echo "refusing unexpected cleanup target: $build_root" >&2 ;;
  esac
}
trap cleanup EXIT

mkdir -p "$build_root/aeneas" "$build_root/output" "$output_dir"
git -C "$aeneas_source" archive "$aeneas_commit" | tar -x -C "$build_root/aeneas"
git -C "$build_root/aeneas" init -q
git -C "$build_root/aeneas" add -A
git -C "$build_root/aeneas" -c user.name=Codex -c user.email=codex@local \
  commit -qm baseline

while read -r expected relative; do
  patch_file="$bundle_dir/$relative"
  test "$(sha256sum "$patch_file" | awk '{print $1}')" = "$expected"
  git -C "$build_root/aeneas" apply --check "$patch_file"
  git -C "$build_root/aeneas" apply "$patch_file"
done < "$script_dir/BASE-PATCHES.sha256"

array_patch="$script_dir/aeneas-d860ac47-array-default-excluded-trait.patch"
test "$(sha256sum "$array_patch" | awk '{print $1}')" = \
  55ebde98b523517b145012227f16cbd464d37eca71a3007deba09cae296d8bca
git -C "$build_root/aeneas" apply --check "$array_patch"
git -C "$build_root/aeneas" apply "$array_patch"
loop_arity_patch="$script_dir/aeneas-d860ac47-loop-break-arity-preflight.patch"
test "$(sha256sum "$loop_arity_patch" | awk '{print $1}')" = \
  d2edccd176882fb908ccaefd3bb3ab77a64707b33c64ff8c03709ccf6225d434
git -C "$build_root/aeneas" apply --check "$loop_arity_patch"
git -C "$build_root/aeneas" apply "$loop_arity_patch"
git -C "$build_root/aeneas" diff --check
git -C "$build_root/aeneas" add -A
test "$(git -C "$build_root/aeneas" write-tree)" = "$patched_tree"

docker run --rm --name "$container_name" \
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

test "$("$build_root/output/aeneas" -version)" = "aeneas $version_tag"
actual_binary_sha=$(sha256sum "$build_root/output/aeneas" | awk '{print $1}')
printf 'candidate binary SHA-256: %s\n' "$actual_binary_sha"
test "$actual_binary_sha" = "$expected_binary_sha"
install -m 0755 "$build_root/output/aeneas" "$output_dir/aeneas-$version_tag"
printf 'patched tree: %s\nbinary SHA-256: %s\n' "$patched_tree" "$actual_binary_sha"
