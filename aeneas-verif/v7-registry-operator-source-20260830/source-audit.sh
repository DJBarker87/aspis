#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(CDPATH= cd -- "$script_dir/../.." && pwd)
cd "$repo_root"

shasum -a 256 -c "$script_dir/evidence/source-sha256.txt"

rg -q 'POOL_V1_VERIFIER_REGISTRY_SEED.*aspis-verifier-registry-v1' \
  programs/aspis-registry/src/processor.rs
rg -q 'POOL_V1_VERIFIER_ENTRY_SEED.*aspis-verifier-entry-v1' \
  programs/aspis-registry/src/processor.rs
rg -q 'require_payer_and_system_program' programs/aspis-registry/src/processor.rs
rg -q 'commit_registry_and_entry' programs/aspis-registry/src/processor.rs
rg -q 'POOL_V1_VERIFIER_REGISTRY_FLAG_IMMUTABLE' \
  programs/aspis-registry/src/processor.rs
rg -q 'bpf_loader_upgradeable::id' programs/aspis-pool/src/pair_forest_dispatch.rs
rg -q 'loader_v4::id' programs/aspis-pool/src/pair_forest_dispatch.rs
rg -q 'returned_data.len\(\) != POOL_V1_PAIR_FOREST_TERMINAL_RESULT_BYTES' \
  programs/aspis-pool/src/pair_forest_dispatch.rs
rg -q 'authenticate_verifier_selection_v1' programs/aspis-pool/src/registry.rs

if rg -n 'ProgramData|upgrade_authority|executable_code_hash' \
    programs/aspis-registry/src/processor.rs \
    programs/aspis-pool/src/registry.rs \
    programs/aspis-pool/src/pair_forest_dispatch.rs; then
  echo 'unexpected ProgramData/code-hash claim entered the audited V1 path' >&2
  exit 1
fi

echo 'V7 registry/operator production source audit: PASS'
