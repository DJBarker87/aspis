#!/usr/bin/env bash
set -euo pipefail

fail() {
  echo "FAIL: $*" >&2
  exit 1
}

require_command() {
  command -v "$1" >/dev/null 2>&1 || fail "required command is unavailable: $1"
}

for command_name in bash git jq wc; do
  require_command "$command_name"
done

if command -v sha256sum >/dev/null 2>&1; then
  sha_file() { sha256sum "$1" | awk '{print $1}'; }
  sha_stdin() { sha256sum | awk '{print $1}'; }
elif command -v shasum >/dev/null 2>&1; then
  sha_file() { shasum -a 256 "$1" | awk '{print $1}'; }
  sha_stdin() { shasum -a 256 | awk '{print $1}'; }
else
  fail "sha256sum or shasum is required"
fi

readonly BUNDLE=$(cd "$(dirname "$0")" && pwd)
readonly ROOT=$(cd "$BUNDLE/../.." && pwd)
git -C "$ROOT" rev-parse --git-dir >/dev/null 2>&1 \
  || fail "preflight bundle is not inside the Aspis git repository"
readonly MANIFEST="$BUNDLE/manifest.json"
[[ -f "$MANIFEST" ]] || fail "preflight manifest is missing"

jq -e '
  .schema == "aspis.v7.one-tx-candidate-preflight.v1" and
  .status == "INPUTS_FROZEN_EXECUTION_EVIDENCE_INCOMPLETE" and
  .authorization.build == true and
  .authorization.localSimulationOnly == true and
  .authorization.publicDevnetReadOnlyProbe == true and
  .authorization.sign == false and
  .authorization.submit == false and
  .authorization.deploy == false and
  .authorization.mainnet == false and
  (.programs | length == 2) and
  (.txv1Lifecycle.requiredCases | length == 11) and
  .txv1Lifecycle.caseBundleIncluded == false and
  .txv1Lifecycle.suiteExecutedForThisFreeze == false
' "$MANIFEST" >/dev/null || fail "manifest schema or fail-closed status changed"

readonly SOURCE_COMMIT=$(jq -er '.source.commit' "$MANIFEST")
readonly SOURCE_TREE=$(jq -er '.source.tree' "$MANIFEST")
readonly CARGO_LOCK_BLOB=$(jq -er '.source.cargoLockBlob' "$MANIFEST")
readonly POOL_TREE=$(jq -er '.source.poolTree' "$MANIFEST")
readonly VERIFIER_TREE=$(jq -er '.source.verifierTree' "$MANIFEST")

[[ "$(git -C "$ROOT" rev-parse "$SOURCE_COMMIT^{commit}")" == "$SOURCE_COMMIT" ]] \
  || fail "frozen source commit is unavailable"
[[ "$(git -C "$ROOT" rev-parse "$SOURCE_COMMIT^{tree}")" == "$SOURCE_TREE" ]] \
  || fail "frozen source tree changed"
[[ "$(git -C "$ROOT" rev-parse "$SOURCE_COMMIT:Cargo.lock")" == "$CARGO_LOCK_BLOB" ]] \
  || fail "frozen Cargo.lock blob changed"
[[ "$(git -C "$ROOT" rev-parse "$SOURCE_COMMIT:programs/aspis-pool")" == "$POOL_TREE" ]] \
  || fail "frozen Pool source tree changed"
[[ "$(git -C "$ROOT" rev-parse "$SOURCE_COMMIT:programs/aspis-verifier")" == "$VERIFIER_TREE" ]] \
  || fail "frozen verifier source tree changed"

while IFS=$'\t' read -r path expected; do
  [[ -n "$path" && -n "$expected" ]] || fail "malformed frozen-file entry"
  git -C "$ROOT" cat-file -e "$SOURCE_COMMIT:$path" 2>/dev/null \
    || fail "frozen source omits required path: $path"
  actual=$(git -C "$ROOT" show "$SOURCE_COMMIT:$path" | sha_stdin)
  [[ "$actual" == "$expected" ]] \
    || fail "frozen file hash changed: $path"
done < <(jq -r '.frozenFiles[] | [.path, .sha256] | @tsv' "$MANIFEST")

while IFS=$'\t' read -r manifest_path expected; do
  actual=$(git -C "$ROOT" show "$SOURCE_COMMIT:$manifest_path" | sha_stdin)
  [[ "$actual" == "$expected" ]] \
    || fail "program manifest hash changed: $manifest_path"
done < <(jq -r '.programs[] | [.manifest, .manifestSha256] | @tsv' "$MANIFEST")

readonly TOOLCHAIN_PROVENANCE=$(jq -er '.toolchain.frozenInventory.path' "$MANIFEST")
readonly TOOLCHAIN_PROVENANCE_SHA=$(jq -er '.toolchain.frozenInventory.sha256' "$MANIFEST")
readonly TOOLCHAIN_FILE_COUNT=$(jq -er '.toolchain.frozenInventory.toolchainFileCount' "$MANIFEST")
readonly CARGO_BUILD_SBF_SHA=$(jq -er '.toolchain.frozenInventory.cargoBuildSbfSha256' "$MANIFEST")

toolchain_actual=$(git -C "$ROOT" show "$SOURCE_COMMIT:$TOOLCHAIN_PROVENANCE" | sha_stdin)
[[ "$toolchain_actual" == "$TOOLCHAIN_PROVENANCE_SHA" ]] \
  || fail "frozen toolchain inventory hash changed"
jq -e \
  --argjson count "$TOOLCHAIN_FILE_COUNT" \
  --arg cargoBuildSbfSha256 "$CARGO_BUILD_SBF_SHA" \
  '(.toolchain_files | length) == $count and
   .cargo_build_sbf_sha256 == $cargoBuildSbfSha256 and
   .platform_tools_version == "v1.48" and
   (.cargo_build_sbf_version | startswith("solana-cargo-build-sbf 2.3.0\nplatform-tools v1.48"))' \
  < <(git -C "$ROOT" show "$SOURCE_COMMIT:$TOOLCHAIN_PROVENANCE") >/dev/null \
  || fail "frozen toolchain inventory contents changed"

readonly MEASURED_CASE=$(jq -er '.latestMeasuredCombinedCase.path' "$MANIFEST")
readonly POOL_SHA=$(jq -er '.programs[] | select(.name == "aspis-pool") | .expectedSha256' "$MANIFEST")
readonly POOL_BYTES=$(jq -er '.programs[] | select(.name == "aspis-pool") | .expectedBytes' "$MANIFEST")
readonly VERIFIER_SHA=$(jq -er '.programs[] | select(.name == "aspis-verifier") | .expectedSha256' "$MANIFEST")
readonly VERIFIER_BYTES=$(jq -er '.programs[] | select(.name == "aspis-verifier") | .expectedBytes' "$MANIFEST")
readonly MEASURED_CU=$(jq -er '.latestMeasuredCombinedCase.computeUnits' "$MANIFEST")
readonly MEASURED_TX_BYTES=$(jq -er '.latestMeasuredCombinedCase.transactionBytes' "$MANIFEST")

jq -e \
  --arg poolSha "$POOL_SHA" \
  --arg verifierSha "$VERIFIER_SHA" \
  --argjson poolBytes "$POOL_BYTES" \
  --argjson verifierBytes "$VERIFIER_BYTES" \
  --argjson units "$MEASURED_CU" \
  --argjson txBytes "$MEASURED_TX_BYTES" '
    .schema == "aspis.v7-pair-forest.combined-litesvm.v2" and
    .artifacts.pool.sha256 == $poolSha and
    .artifacts.pool.bytes == $poolBytes and
    .artifacts.verifier.sha256 == $verifierSha and
    .artifacts.verifier.bytes == $verifierBytes and
    .execution.network == "none" and
    .execution.runtime == "LiteSVM 0.16.0" and
    .execution.operation == "withdrawal" and
    .execution.outcome == "accepted" and
    .execution.compute_units == $units and
    .execution.compute_units < 1300000 and
    .execution.serialized_transaction_bytes == $txBytes and
    .execution.serialized_transaction_bytes < 4096 and
    .execution.return_data_bytes == 792 and
    .execution.simulation_equals_execution == true and
    .execution.selected_verifier_cpi_observed_in_logs == true and
    .atomicity.checkpoint_unchanged == true and
    .atomicity.entry_unchanged == true and
    .atomicity.lane_changed_exactly_on_success == true and
    .atomicity.nullifier_marker_changed_exactly_on_success == true and
    .atomicity.master_unchanged == true and
    .atomicity.proof_unchanged == true and
    .atomicity.registry_unchanged == true and
    .atomicity.rollover_page_changed_exactly_on_success == true and
    .atomicity.settled_history_equals_expected == true and
    .atomicity.settled_lane_equals_candidate == true and
    .atomicity.settled_marker_equals_expected == true and
    .atomicity.settled_rollover_page_equals_expected == true and
    .atomicity.withdrawal_mint_unchanged == true and
    (.atomicity.withdrawal_vault_amount_before - .atomicity.withdrawal_vault_amount_after) == 250 and
    (.atomicity.withdrawal_destination_amount_after - .atomicity.withdrawal_destination_amount_before) == 250
  ' < <(git -C "$ROOT" show "$SOURCE_COMMIT:$MEASURED_CASE") >/dev/null \
  || fail "latest measured combined case no longer satisfies the frozen predicates"

while IFS= read -r script_path; do
  temporary_script=$(mktemp "${TMPDIR:-/tmp}/aspis-v7-script.XXXXXX")
  git -C "$ROOT" show "$SOURCE_COMMIT:$script_path" >"$temporary_script"
  bash -n "$temporary_script" || {
    rm -f "$temporary_script"
    fail "shell syntax check failed: $script_path"
  }
  rm -f "$temporary_script"
done < <(jq -r '.frozenFiles[] | select(.path | startswith("scripts/")) | .path' "$MANIFEST")

jq -n \
  --arg schema "aspis.v7.one-tx-candidate-input-audit.v1" \
  --arg sourceCommit "$SOURCE_COMMIT" \
  --arg sourceTree "$SOURCE_TREE" \
  --arg poolSha256 "$POOL_SHA" \
  --arg verifierSha256 "$VERIFIER_SHA" \
  --argjson measuredWorstCaseCu "$MEASURED_CU" \
  --argjson measuredWorstCaseTxBytes "$MEASURED_TX_BYTES" \
  --arg toolchainInventorySha256 "$TOOLCHAIN_PROVENANCE_SHA" \
  --argjson requiredTxv1Cases 11 '
  {
    schema: $schema,
    sourceCommit: $sourceCommit,
    sourceTree: $sourceTree,
    frozenFileHashesMatch: true,
    frozenToolchainInventoryMatches: true,
    programFeatureManifestsMatch: true,
    currentSourceMeasuredWorstCase: {
      classification: "REAL_COMBINED_LITESVM_CURRENT_SOURCE_WORST_CASE",
      poolSha256: $poolSha256,
      verifierSha256: $verifierSha256,
      computeUnits: $measuredWorstCaseCu,
      transactionBytes: $measuredWorstCaseTxBytes,
      predicatesMatch: true
    },
    requiredTxv1Cases: $requiredTxv1Cases,
    reproducibleBuildExecuted: false,
    disposableAgaveSuiteExecuted: false,
    publicDevnetTransactionSigned: false,
    publicDevnetTransactionSubmitted: false,
    releaseReady: false,
    remainingGates: [
      "two byte-identical clean Linux SBF builds from the frozen source",
      "eleven-case Agave 4.2+ TxV1 simulation-only bundle and replay",
      "public-devnet finalized TxV1 execution activation before any RPC simulation"
    ],
    toolchainInventorySha256: $toolchainInventorySha256
  }'
