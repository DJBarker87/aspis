#!/usr/bin/env bash
set -euo pipefail

readonly bundle="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly root="$(cd "$bundle/../.." && pwd -P)"
readonly deployed_commit="06788d44d30ea8cbd391899dddaf6f0acc6e4a3f"
readonly charon_bin="${CHARON_BIN:?set CHARON_BIN to pinned Charon cb50ff16}"
readonly aeneas_bin="${AENEAS_BIN:?set AENEAS_BIN to the patched Aeneas executable}"
readonly replay_dir="${V5_MERKLE_REPLAY_OUT:-$(mktemp -d /private/tmp/v5-merkle-source-replay.XXXXXX)}"
readonly checkout="$replay_dir/repo"
readonly generated="$replay_dir/generated"

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
