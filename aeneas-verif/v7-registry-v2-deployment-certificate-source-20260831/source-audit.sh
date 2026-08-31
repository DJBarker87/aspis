#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(CDPATH= cd -- "$script_dir/../.." && pwd)

check_hash() {
  expected=$1
  path=$2
  actual=$(shasum -a 256 "$path" | awk '{print $1}')
  test "$actual" = "$expected"
  printf '%s  %s\n' "$actual" "${path#"$repo_root/"}"
}

check_hash b0bf5c9c7c0cbe532ccdedde1fb8692b0691d1aafa8b17c69a9f43183442fc84 \
  "$repo_root/programs/aspis-registry/src/processor.rs"
check_hash 663a47babc8fdb06e3635b81151fa1d87bf0657078c08c7df88d2d1fa34017b9 \
  "$repo_root/programs/aspis-registry/src/processor_tests.rs"
check_hash 99c166a1f6641631937450fe7e59e08cb6422e588d8c49b90f66f9a4cb85ed8a \
  "$repo_root/programs/aspis-pool/src/registry.rs"
check_hash 124c28d21857b2e009c19674f04f0f4d50e7feaa61a62f3900532f20b5267cb2 \
  "$repo_root/crates/aspis-statement/src/pool_v1/verifier_registry.rs"
check_hash a1d2fc87435e98734f74a0fb1f070f1eaa5e5fe19266967092a7ea7849f8a91d \
  "$repo_root/Cargo.lock"
check_hash 5e5809f7d20714267d7e0872a3b6350bae6bf3174b21501a3caccc36895c480d \
  "$script_dir/harness/src/lib.rs"

rg -n 'authenticate_immutable_loader_v3_deployment_v2|find_program_address|size_of_programdata_metadata|hash\(&data\[metadata_bytes\.\.' \
  "$repo_root/programs/aspis-registry/src/processor.rs"
rg -n 'registry\.policy_binding != policy\.policy_binding|entry\.policy_binding != policy\.policy_binding' \
  "$repo_root/programs/aspis-pool/src/registry.rs"

echo 'V7 Registry V2 deployment certificate source audit: PASS'
