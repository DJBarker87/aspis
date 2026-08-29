#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
bundle_dir=$(CDPATH= cd -- "$script_dir/.." && pwd)

readonly aeneas_commit=d860ac47ed548d3da6d799afc013779ce470516c
readonly charon_commit=cb50ff16b9f1066b8a97dc06da704de2da2fa41c
readonly patched_tree=${AENEAS_PATCHED_TREE:-de8340302a8a14448e47e2a878ac726ed29228b2}
readonly image=ocaml/opam@sha256:42f6e13e9aceedc701eefdb89fca9fd1868c8cadd1144b334ca799474eadb702
readonly version_tag=${AENEAS_VERSION_TAG:-d860ac47-tag73-fixed-field}
readonly extra_patch=${AENEAS_EXTRA_PATCH:-}
readonly extra_patch_two=${AENEAS_EXTRA_PATCH_TWO:-}
readonly extra_patch_three=${AENEAS_EXTRA_PATCH_THREE:-}
readonly extra_patch_four=${AENEAS_EXTRA_PATCH_FOUR:-}
readonly extra_patch_five=${AENEAS_EXTRA_PATCH_FIVE:-}
readonly extra_patch_six=${AENEAS_EXTRA_PATCH_SIX:-}
readonly extra_patch_seven=${AENEAS_EXTRA_PATCH_SEVEN:-}
readonly extra_patch_eight=${AENEAS_EXTRA_PATCH_EIGHT:-}
readonly extra_patch_nine=${AENEAS_EXTRA_PATCH_NINE:-}
readonly extra_patch_ten=${AENEAS_EXTRA_PATCH_TEN:-}

aeneas_source=${AENEAS_SOURCE_ROOT:-/home/dombarker/project-offloads/aeneas-d860-v6-src}
charon_source=${CHARON_SOURCE_ROOT:-/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon}
output_dir=${OUTPUT_DIR:-/home/dombarker/project-offloads/v7-tag73-fixed-field-source-20260826-toolchain}
output_bin="$output_dir/aeneas-d860ac47-tag73-fixed-field"

test "$(hostname -s)" = nuc
available_kib=$(awk '/^MemAvailable:/ { print $2 }' /proc/meminfo)
test "$available_kib" -ge $((24 * 1024 * 1024))
cgroup_path=$(awk -F: '$1 == "0" { print $3 }' /proc/self/cgroup)
test "$(tr -d '\n' < "/sys/fs/cgroup$cgroup_path/memory.high")" = 19327352832
test "$(tr -d '\n' < "/sys/fs/cgroup$cgroup_path/memory.max")" = 21474836480
test "$(tr -d '\n' < "/sys/fs/cgroup$cgroup_path/memory.swap.max")" = 0
test "$(git -C "$aeneas_source" rev-parse "$aeneas_commit^{commit}")" = "$aeneas_commit"
test "$(git -C "$charon_source" rev-parse "$charon_commit^{commit}")" = "$charon_commit"
(cd "$bundle_dir" && sha256sum -c toolchain/PATCHES.sha256)
if test -n "$extra_patch"; then
  case "$extra_patch" in
    "$script_dir"/*.patch) ;;
    *) echo "refusing extra patch outside the frozen toolchain directory" >&2; exit 2 ;;
  esac
  test -f "$extra_patch"
fi
if test -n "$extra_patch_two"; then
  case "$extra_patch_two" in
    "$script_dir"/*.patch) ;;
    *) echo "refusing second extra patch outside the frozen toolchain directory" >&2; exit 2 ;;
  esac
  test -f "$extra_patch_two"
fi
if test -n "$extra_patch_three"; then
  case "$extra_patch_three" in
    "$script_dir"/*.patch) ;;
    *) echo "refusing third extra patch outside the frozen toolchain directory" >&2; exit 2 ;;
  esac
  test -f "$extra_patch_three"
fi
if test -n "$extra_patch_four"; then
  case "$extra_patch_four" in
    "$script_dir"/*.patch) ;;
    *) echo "refusing fourth extra patch outside the frozen toolchain directory" >&2; exit 2 ;;
  esac
  test -f "$extra_patch_four"
fi
if test -n "$extra_patch_five"; then
  case "$extra_patch_five" in
    "$script_dir"/*.patch) ;;
    *) echo "refusing fifth extra patch outside the frozen toolchain directory" >&2; exit 2 ;;
  esac
  test -f "$extra_patch_five"
fi
if test -n "$extra_patch_six"; then
  case "$extra_patch_six" in
    "$script_dir"/*.patch) ;;
    *) echo "refusing sixth extra patch outside the frozen toolchain directory" >&2; exit 2 ;;
  esac
  test -f "$extra_patch_six"
fi
if test -n "$extra_patch_seven"; then
  case "$extra_patch_seven" in
    "$script_dir"/*.patch) ;;
    *) echo "refusing seventh extra patch outside the frozen toolchain directory" >&2; exit 2 ;;
  esac
  test -f "$extra_patch_seven"
fi
if test -n "$extra_patch_eight"; then
  case "$extra_patch_eight" in
    "$script_dir"/*.patch) ;;
    *) echo "refusing eighth extra patch outside the frozen toolchain directory" >&2; exit 2 ;;
  esac
  test -f "$extra_patch_eight"
fi
if test -n "$extra_patch_nine"; then
  case "$extra_patch_nine" in
    "$script_dir"/*.patch) ;;
    *) echo "refusing ninth extra patch outside the frozen toolchain directory" >&2; exit 2 ;;
  esac
  test -f "$extra_patch_nine"
fi
if test -n "$extra_patch_ten"; then
  case "$extra_patch_ten" in
    "$script_dir"/*.patch) ;;
    *) echo "refusing tenth extra patch outside the frozen toolchain directory" >&2; exit 2 ;;
  esac
  test -f "$extra_patch_ten"
fi

build_root=$(mktemp -d /home/dombarker/project-offloads/v7-tag73-aeneas-build.XXXXXX)
container_id=
cleanup() {
  if test -n "$container_id"; then
    docker rm -f "$container_id" >/dev/null 2>&1 || true
  elif test -f "$build_root/container.cid"; then
    docker rm -f "$(cat "$build_root/container.cid")" >/dev/null 2>&1 || true
  fi
  case "$build_root" in
    /home/dombarker/project-offloads/v7-tag73-aeneas-build.*)
      rm -rf -- "$build_root" ;;
    *)
      echo "refusing unsafe cleanup target: $build_root" >&2 ;;
  esac
}
trap cleanup EXIT

mkdir -p "$build_root/aeneas"
git -C "$aeneas_source" archive "$aeneas_commit" | tar -x -C "$build_root/aeneas"
git -C "$build_root/aeneas" init -q
git -C "$build_root/aeneas" add -A
git -C "$build_root/aeneas" -c user.name=Codex -c user.email=codex@local \
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
if test -n "$extra_patch"; then
  git -C "$build_root/aeneas" apply --check "$extra_patch"
  git -C "$build_root/aeneas" apply "$extra_patch"
fi
if test -n "$extra_patch_two"; then
  git -C "$build_root/aeneas" apply --check "$extra_patch_two"
  git -C "$build_root/aeneas" apply "$extra_patch_two"
fi
if test -n "$extra_patch_three"; then
  git -C "$build_root/aeneas" apply --check "$extra_patch_three"
  git -C "$build_root/aeneas" apply "$extra_patch_three"
fi
if test -n "$extra_patch_four"; then
  git -C "$build_root/aeneas" apply --check "$extra_patch_four"
  git -C "$build_root/aeneas" apply "$extra_patch_four"
fi
if test -n "$extra_patch_five"; then
  git -C "$build_root/aeneas" apply --check "$extra_patch_five"
  git -C "$build_root/aeneas" apply "$extra_patch_five"
fi
if test -n "$extra_patch_six"; then
  git -C "$build_root/aeneas" apply --check "$extra_patch_six"
  git -C "$build_root/aeneas" apply "$extra_patch_six"
fi
if test -n "$extra_patch_seven"; then
  git -C "$build_root/aeneas" apply --check "$extra_patch_seven"
  git -C "$build_root/aeneas" apply "$extra_patch_seven"
fi
if test -n "$extra_patch_eight"; then
  git -C "$build_root/aeneas" apply --check "$extra_patch_eight"
  git -C "$build_root/aeneas" apply "$extra_patch_eight"
fi
if test -n "$extra_patch_nine"; then
  git -C "$build_root/aeneas" apply --check "$extra_patch_nine"
  git -C "$build_root/aeneas" apply "$extra_patch_nine"
fi
if test -n "$extra_patch_ten"; then
  git -C "$build_root/aeneas" apply --check "$extra_patch_ten"
  git -C "$build_root/aeneas" apply "$extra_patch_ten"
fi
git -C "$build_root/aeneas" diff --check
git -C "$build_root/aeneas" add -A
test "$(git -C "$build_root/aeneas" write-tree)" = "$patched_tree"
printf 'patched Aeneas tree: %s\n' "$patched_tree"

mkdir -p "$build_root/charon" "$build_root/output"
git -C "$charon_source" archive "$charon_commit" | tar -x -C "$build_root/charon"

docker run --platform linux/amd64 \
  --cidfile "$build_root/container.cid" \
  --memory-reservation=18g --memory=20g --memory-swap=20g \
  -e AENEAS_BUILD_VERSION="$version_tag" \
  -v "$build_root:/work" "$image" bash -lc '
    set -euo pipefail
    export OPAMJOBS=2 DUNEJOBS=2
    sudo apt-get update -qq
    sudo apt-get install -y -qq libgmp-dev pkg-config build-essential time
    /usr/bin/time -v -o /work/output/docker-build.time bash -lc '\''
      set -euo pipefail
      export OPAMJOBS=2 DUNEJOBS=2
      opam install -y dune menhir easy_logging ppx_deriving unionFind visitors \
        yojson zarith core_unix ocamlgraph progress domainslib \
        ppx_deriving_yojson ppxlib
      cd /work/charon
      opam exec -- dune build @install --profile release -j 2
      opam exec -- dune install --prefix "$(opam var prefix)"
      cd /work/aeneas/src
      AENEAS_VERSION="$AENEAS_BUILD_VERSION" \
        OCAMLPARAM=_,ccopt=-static \
        opam exec -- dune build main.exe --profile release -j 2
      cp _build/default/main.exe \
        /work/output/aeneas-d860ac47-tag73-fixed-field
    '\''
  '
container_id=$(cat "$build_root/container.cid")
docker inspect --format \
  'exit={{.State.ExitCode}} oom_killed={{.State.OOMKilled}} memory={{.HostConfig.Memory}} memory_reservation={{.HostConfig.MemoryReservation}} memory_swap={{.HostConfig.MemorySwap}}' \
  "$container_id" > "$build_root/output/docker-cgroup.txt"
docker rm "$container_id" >/dev/null
container_id=

mkdir -p "$output_dir"
cp "$build_root/output/aeneas-d860ac47-tag73-fixed-field" "$output_bin"
cp "$build_root/output/docker-build.time" "$output_dir/"
cp "$build_root/output/docker-cgroup.txt" "$output_dir/"
chmod 0755 "$output_bin"
file "$output_bin" | rg 'ELF 64-bit.*x86-64.*statically linked'
test "$("$output_bin" -version)" = "aeneas $version_tag"
sha256sum "$output_bin" | tee "$output_dir/binary.sha256"
printf 'isolated patched Aeneas build: PASS\n'
