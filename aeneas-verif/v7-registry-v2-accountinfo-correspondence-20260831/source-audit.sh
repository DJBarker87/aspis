#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(cd "$script_dir/../.." && pwd)

cd "$repo_root"

cat <<'HASHES' | sha256sum -c -
0b5a2824cb6b9a31971d75dd5bb0fcc224aece6873ac12f54b6a81822275ce0b  programs/aspis-pool/src/pair_forest.rs
99c166a1f6641631937450fe7e59e08cb6422e588d8c49b90f66f9a4cb85ed8a  programs/aspis-pool/src/registry.rs
124c28d21857b2e009c19674f04f0f4d50e7feaa61a62f3900532f20b5267cb2  crates/aspis-statement/src/pool_v1/verifier_registry.rs
80a229493dd09740b5437f128e3dff11b7feeca72dd6b1e5f47aa571d3e6e6f2  aeneas-verif/v7-registry-v2-accountinfo-correspondence-20260831/extraction/V7RegistryV2ProductionCodecs.llbc
e3f0912aef4c2a9acdb4827285e41be431ede0bc7926ba1c30836e4c0e2be636  aeneas-verif/v7-registry-v2-accountinfo-correspondence-20260831/extraction/V7RegistryV2ProductionReadonly.llbc
1771b84afbd469f009835d6e37a511232326eb3de4b4f3d59da7d3fd124b6b8e  aeneas-verif/v7-registry-v2-accountinfo-correspondence-20260831/toolchain/specialize-production-callbacks-for-extraction.patch
HASHES

jq -e '.has_errors == false and .charon_version == "0.1.223"' \
  "$script_dir/extraction/V7RegistryV2ProductionCodecs.llbc" >/dev/null
jq -e '.has_errors == false and .charon_version == "0.1.223"' \
  "$script_dir/extraction/V7RegistryV2ProductionReadonly.llbc" >/dev/null

rg -q 'pub\(crate\) fn process_pair_forest_terminal_with_verifier_v1' \
  programs/aspis-pool/src/pair_forest.rs
rg -q 'fn require_readonly_registry_account' \
  programs/aspis-pool/src/registry.rs
rg -q 'account.owner != registry_program' programs/aspis-pool/src/registry.rs
rg -q 'account.executable' programs/aspis-pool/src/registry.rs
rg -q 'account.is_writable' programs/aspis-pool/src/registry.rs
rg -q 'account.is_signer' programs/aspis-pool/src/registry.rs
rg -q 'decode_verifier_registry_v2' \
  crates/aspis-statement/src/pool_v1/verifier_registry.rs
rg -q 'decode_verifier_registry_entry_v2' \
  crates/aspis-statement/src/pool_v1/verifier_registry.rs

echo 'V7 Registry V2 AccountInfo source audit: PASS'
