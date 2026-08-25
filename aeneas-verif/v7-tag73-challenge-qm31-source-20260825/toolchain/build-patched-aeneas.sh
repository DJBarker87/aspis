#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
bundle_dir=$(cd "$script_dir/.." && pwd)
repo_root=$(cd "$bundle_dir/../.." && pwd)

readonly aeneas_commit=b59d5188c082f704a418c7cb4e52ad69328002d1
readonly charon_commit=cb50ff16b9f1066b8a97dc06da704de2da2fa41c
readonly image=ocaml/opam@sha256:42f6e13e9aceedc701eefdb89fca9fd1868c8cadd1144b334ca799474eadb702
readonly expected_patch_sha=5abaafc2d345511dda0eb96cd40154daff137f79dc4bcfa8247a45acea639c9c
readonly expected_tree=5a843e70672e4139232b2fdcb52a0c1fbd4b1619
readonly expected_binary_sha=4632746db1bf6c3953f2971078965a2a5a8ad6cf5f75636b46b397bc50c550b5

aeneas_source=${AENEAS_SOURCE_ROOT:-/home/dombarker/project-offloads/aeneas-d860-v6-src}
charon_source=${CHARON_SOURCE_ROOT:-/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon}
output_dir=${OUTPUT_DIR:-/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-toolchain}
output_bin="$output_dir/aeneas-b59d5188-lean432-extended-static"
patch_file="$repo_root/aeneas-verif/lean432/aeneas-b59d5188-lean432.patch"

[[ $(git -C "$aeneas_source" rev-parse "$aeneas_commit") == "$aeneas_commit" ]]
[[ $(git -C "$charon_source" rev-parse "$charon_commit") == "$charon_commit" ]]
echo "$expected_patch_sha  $patch_file" | sha256sum -c -

build_root=$(mktemp -d)
trap 'rm -rf -- "$build_root"' EXIT
git clone --quiet --no-local --no-checkout "$aeneas_source" "$build_root/aeneas"
git -C "$build_root/aeneas" checkout --quiet --detach "$aeneas_commit"
git -C "$build_root/aeneas" apply --check --unidiff-zero "$patch_file"
git -C "$build_root/aeneas" apply --unidiff-zero "$patch_file"
git -C "$build_root/aeneas" diff --check
git -C "$build_root/aeneas" add -A
[[ $(git -C "$build_root/aeneas" write-tree) == "$expected_tree" ]]
mkdir -p "$build_root/charon" "$build_root/output"
git -C "$charon_source" archive "$charon_commit" | tar -x -C "$build_root/charon"

# This build is deliberately separate from the 12-GiB Lean replay.  Setting
# memory-swap equal to memory gives the container no additional swap budget.
docker run --rm --platform linux/amd64 \
  --memory=24g --memory-swap=24g \
  -v "$build_root:/work" "$image" bash -lc '
    set -euo pipefail
    export OPAMJOBS=2 DUNEJOBS=2
    sudo apt-get update -qq
    sudo apt-get install -y -qq libgmp-dev pkg-config build-essential
    opam install -y dune menhir easy_logging ppx_deriving unionFind visitors \
      yojson zarith core_unix ocamlgraph progress domainslib \
      ppx_deriving_yojson ppxlib
    cd /work/charon
    opam exec -- dune build @install --profile release -j 2
    opam exec -- dune install --prefix "$(opam var prefix)"
    cd /work/aeneas/src
    AENEAS_VERSION=b59d5188-lean432-extended \
      OCAMLPARAM=_,ccopt=-static \
      opam exec -- dune build main.exe --profile release -j 2
    cp _build/default/main.exe \
      /work/output/aeneas-b59d5188-lean432-extended-static
  '

mkdir -p "$output_dir"
cp "$build_root/output/aeneas-b59d5188-lean432-extended-static" "$output_bin"
chmod 0755 "$output_bin"
echo "$expected_binary_sha  $output_bin" | sha256sum -c -
file "$output_bin" | rg 'ELF 64-bit.*x86-64.*statically linked'
[[ $("$output_bin" -version) == 'aeneas b59d5188-lean432-extended' ]]
echo "isolated patched static Aeneas build: PASS"

