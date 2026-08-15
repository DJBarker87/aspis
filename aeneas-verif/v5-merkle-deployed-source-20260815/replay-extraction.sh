#!/usr/bin/env bash
set -euo pipefail

readonly bundle="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly root="$(cd "$bundle/../.." && pwd -P)"
readonly deployed_commit="06788d44d30ea8cbd391899dddaf6f0acc6e4a3f"
readonly charon_commit="cb50ff16b9f1066b8a97dc06da704de2da2fa41c"
readonly aeneas_base_commit="b59d5188c082f704a418c7cb4e52ad69328002d1"
readonly aeneas_extended_commit="35b05b92fa1c7a989bbae2982e2ea5f68c5e2bbb"
readonly reconstructed_aeneas_version="aspis-v5-merkle-6be49429"
readonly charon_repo="${CHARON_REPO:?set CHARON_REPO to pinned Charon source}"
readonly aeneas_repo="${AENEAS_REPO:?set AENEAS_REPO to pinned or reconstructed Aeneas source}"
readonly charon_bin="${CHARON_BIN:?set CHARON_BIN to pinned Charon cb50ff16}"
readonly aeneas_bin="${AENEAS_BIN:?set AENEAS_BIN to the patched Aeneas executable}"
readonly replay_dir="${V5_MERKLE_REPLAY_OUT:-$(mktemp -d /private/tmp/v5-merkle-source-replay.XXXXXX)}"
readonly checkout="$replay_dir/repo"
readonly generated="$replay_dir/generated"

canonical_file() {
  local file=$1
  (cd "$(dirname "$file")" && printf '%s/%s\n' "$(pwd -P)" "$(basename "$file")")
}

[[ "$(git -C "$charon_repo" rev-parse HEAD)" == "$charon_commit" ]] || {
  echo "Charon source mismatch: expected $charon_commit" >&2
  exit 1
}
git -C "$charon_repo" diff --quiet HEAD -- || {
  echo "Charon source has tracked changes" >&2
  exit 1
}
[[ "$(canonical_file "$charon_bin")" == \
  "$(canonical_file "$charon_repo/charon/target/release/charon")" ]] || {
  echo "CHARON_BIN is not the binary built in CHARON_REPO" >&2
  exit 1
}

readonly aeneas_head="$(git -C "$aeneas_repo" rev-parse HEAD)"
case "$aeneas_head" in
  "$aeneas_extended_commit")
    git -C "$aeneas_repo" diff --quiet HEAD -- src || {
      echo "Aeneas compiler source has tracked changes" >&2
      exit 1
    }
    ;;
  "$aeneas_base_commit")
    # This is the documented reconstruction route: the pinned base plus the
    # bundled extraction-only compiler changes. Other tracked changes fail.
    [[ "$(shasum -a 256 "$aeneas_repo/src/PrePasses.ml" | awk '{print $1}')" == \
      "fb81d25fb5391d20fe45067c2cc7ae5bc5b2dc969ca39b61b3afa9a932092348" ]]
    [[ "$(shasum -a 256 "$aeneas_repo/src/interp/InterpBorrowsCore.ml" | awk '{print $1}')" == \
      "d47ac2aab7a3781882d3dcc31da80fb685a8a0431c7d2a5dcc3fa354b4cdafe7" ]]
    [[ "$(shasum -a 256 "$aeneas_repo/src/interp/Invariants.ml" | awk '{print $1}')" == \
      "f89c9ba6eb88dbd2a8bd2bcb72c3ef49705a49d3bd8dee1e0188af3c8b0dadf8" ]]
    [[ "$(shasum -a 256 "$aeneas_repo/src/llbc/RegionsHierarchy.ml" | awk '{print $1}')" == \
      "472ed27baee90f424ee259519770cf81089ae4f021896a2afb161aca02906e46" ]]
    git -C "$aeneas_repo" diff --quiet HEAD -- . \
      ':(exclude)src/PrePasses.ml' \
      ':(exclude)src/interp/InterpBorrowsCore.ml' \
      ':(exclude)src/interp/Invariants.ml' \
      ':(exclude)src/llbc/RegionsHierarchy.ml' || {
        echo "Aeneas reconstruction has unexpected tracked changes" >&2
        exit 1
      }
    ;;
  *)
    echo "Aeneas source mismatch: expected $aeneas_extended_commit or patched $aeneas_base_commit" >&2
    exit 1
    ;;
esac
[[ "$(canonical_file "$aeneas_bin")" == \
  "$(canonical_file "$aeneas_repo/src/_build/default/main.exe")" ]] || {
  echo "AENEAS_BIN is not the binary built in AENEAS_REPO" >&2
  exit 1
}

readonly aeneas_version="$($aeneas_bin -version)"
case "$aeneas_version" in
  "aeneas 35b05b92"|"aeneas $reconstructed_aeneas_version") ;;
  *)
    echo "Aeneas binary version mismatch: $aeneas_version" >&2
    exit 1
    ;;
esac
readonly aeneas_metadata_version="${aeneas_version#aeneas }"

[[ -x "$charon_bin" && -x "$aeneas_bin" ]] || {
  echo "extraction tool is not executable" >&2
  exit 1
}

mkdir -p "$checkout" "$generated"
git -C "$root" archive "$deployed_commit" | tar -x -C "$checkout"

check_hash() {
  local expected=$1
  local file=$2
  local actual
  actual=$(shasum -a 256 "$checkout/$file" | awk '{print $1}')
  [[ "$actual" == "$expected" ]] || {
    echo "source hash mismatch: $file" >&2
    exit 1
  }
}

check_hash 76aa94ce9db033715c04e42effe4fe67807b7a2409dcae6595332be8f1cf9747 \
  crates/aspis-core/src/merkle.rs
check_hash 178968bf12967eead324f07e8e0047c5e018874998540e103afad2dcea33cfdb \
  crates/aspis-core/src/state_only_private_openings.rs
check_hash f0edc31d07d30f5b19fcaf872fba18678d13d1ba5fac1199f1f4d2be74c74f9b \
  crates/aspis-core/src/state_only_private_merkle.rs
check_hash 916c14930d419bc0cd794a3d1e01c4e45fea9f4dbbc1f44f89f71caf3ff63c49 \
  programs/aspis-verifier/src/v5_private_openings.rs

git -C "$checkout" apply --check "$bundle/source-adapter.patch"
git -C "$checkout" apply "$bundle/source-adapter.patch"
git -C "$checkout" apply --check "$bundle/immediate-return-adapter.patch"
git -C "$checkout" apply "$bundle/immediate-return-adapter.patch"
mkdir -p "$checkout/aeneas-verif/v5-merkle-deployed-source-20260815"
cp -R "$bundle/harness" \
  "$checkout/aeneas-verif/v5-merkle-deployed-source-20260815/harness"

readonly harness="$checkout/aeneas-verif/v5-merkle-deployed-source-20260815/harness"
cargo check --manifest-path "$harness/Cargo.toml" --release

(
  cd "$harness"
  CARGO_TARGET_DIR="$replay_dir/charon-target" "$charon_bin" cargo \
    --preset aeneas \
    --start-from 'v5_merkle_fixed_hash_adapter::private_openings::verify_v5_private_openings' \
    --opaque 'v5_merkle_fixed_hash_adapter::merkle::fixed_hashv' \
    --dest-file "$replay_dir/V5MerkleDeployedSource.llbc" -- --release
)

"$aeneas_bin" -backend lean -namespace V5MerkleDeployedSource \
  -dest "$generated" -split-files -gen-lib-entry -emit-json \
  -no-progress-bar -abort-on-error "$replay_dir/V5MerkleDeployedSource.llbc"

rg -F "\"aeneas_version\": \"$aeneas_metadata_version\"" \
  "$generated/translation.json" >/dev/null
rg -F '"charon_version": "0.1.223"' "$generated/translation.json" >/dev/null

# Source comments contain the caller-selected replay directory, and the JSON
# records the equivalent Aeneas build label. Normalize only those two fields,
# then bind every generated body and the complete external-definition template.
normalized_generated_hash() {
  local file=$1
  SOURCE_ROOT="$checkout" perl -pe \
    's/\Q$ENV{SOURCE_ROOT}\E/<SOURCE_ROOT>/g; s/"aeneas_version": "[^"]+"/"aeneas_version": "<AENEAS_VERSION>"/g' \
    "$generated/$file" | shasum -a 256 | awk '{print $1}'
}

check_generated_hash() {
  local expected=$1
  local file=$2
  local actual
  actual=$(normalized_generated_hash "$file")
  [[ "$actual" == "$expected" ]] || {
    echo "generated output mismatch: $file" >&2
    echo "expected $expected" >&2
    echo "actual   $actual" >&2
    exit 1
  }
}

check_generated_hash \
  14e596a45dbc079713a5a5e69cfc3b021c76d6a9861d1995c79b0162628900a8 \
  Types.lean
check_generated_hash \
  8bdc2cb7aeb51d8b0aebaacc26d8076c015fa46faa9dbf0dea03d374824d0856 \
  FunsExternal_Template.lean
check_generated_hash \
  941d4fb39098ce5c4f44d5b56edfebc9cc5a0e62e6dc386f78d90917e7c07e49 \
  Funs.lean
check_generated_hash \
  a6d558656baacdd57ae0e31d9eca17702a1c4ba1e97eef6b22f360a0f6812ae9 \
  V5MerkleDeployedSource.lean
check_generated_hash \
  27191a40f1eb90425a11a40a6d03e451233ddad69ecc4cdfeafe2925237d7d53 \
  translation.json

for definition in \
  'def merkle.Radix4BinaryCapTopology.new' \
  'def merkle.verify_radix4_binary_cap_with_matched_topology' \
  'state_only_private_openings.verify_state_only_private_opening_from_proof_with_topology' \
  'def private_openings.verify_v5_private_openings_from_proof' \
  'def private_openings.verify_v5_private_openings'; do
  rg -F "$definition" "$generated/Funs.lean" >/dev/null
done

echo "V5 deployed Merkle source extraction: PASS"
echo "V5_MERKLE_REPLAY_OUT=$replay_dir"
