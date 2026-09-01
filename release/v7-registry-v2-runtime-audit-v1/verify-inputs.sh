#!/usr/bin/env bash
set -euo pipefail

readonly ROOT=$(cd "$(dirname "$0")/../.." && pwd)
readonly RELEASE_DIR="$ROOT/release/v7-registry-v2-runtime-audit-v1"
readonly MANIFEST="$RELEASE_DIR/manifest.json"

fail() {
  echo "FAIL: $*" >&2
  exit 1
}

require_command() {
  command -v "$1" >/dev/null 2>&1 || fail "required command is unavailable: $1"
}

for command_name in awk cmp git jq mktemp rm sort stat tr wc; do
  require_command "$command_name"
done

if command -v sha256sum >/dev/null 2>&1; then
  sha_file() { sha256sum "$1" | awk '{print $1}'; }
  verify_inventory() { sha256sum -c "$1"; }
elif command -v shasum >/dev/null 2>&1; then
  sha_file() { shasum -a 256 "$1" | awk '{print $1}'; }
  verify_inventory() { shasum -a 256 -c "$1"; }
else
  fail "sha256sum or shasum is required"
fi

file_bytes() {
  if stat -c %s "$1" >/dev/null 2>&1; then
    stat -c %s "$1"
  else
    stat -f %z "$1"
  fi
}

[[ -f "$MANIFEST" ]] || fail "missing release audit manifest"
jq -e '.schema == "aspis.v7.registry-v2-runtime-audit-inputs.v1"' "$MANIFEST" >/dev/null

readonly EVIDENCE_COMMIT=$(jq -er '.releaseEvidence.commit' "$MANIFEST")
readonly EVIDENCE_TREE=$(jq -er '.releaseEvidence.tree' "$MANIFEST")
readonly SOURCE_PARENT=$(jq -er '.releaseEvidence.productionSourceParent' "$MANIFEST")
readonly BUNDLE_RELATIVE=$(jq -er '.releaseEvidence.bundle' "$MANIFEST")
readonly BUNDLE="$ROOT/$BUNDLE_RELATIVE"
readonly INVENTORY="$ROOT/$(jq -er '.releaseEvidence.inventory' "$MANIFEST")"

git -C "$ROOT" cat-file -e "$EVIDENCE_COMMIT^{commit}"
git -C "$ROOT" cat-file -e "$SOURCE_PARENT^{commit}"
[[ "$(git -C "$ROOT" rev-parse "$EVIDENCE_COMMIT^{tree}")" == "$EVIDENCE_TREE" ]] \
  || fail "release evidence tree differs from the frozen tree"
[[ -d "$BUNDLE" && -f "$INVENTORY" ]] || fail "Registry V2 evidence bundle is incomplete"
[[ "$(sha_file "$INVENTORY")" == "$(jq -er '.releaseEvidence.inventorySha256' "$MANIFEST")" ]] \
  || fail "bundle inventory digest differs from the frozen audit manifest"

for source_path in Cargo.lock programs/aspis-pool programs/aspis-verifier programs/aspis-registry; do
  [[ "$(git -C "$ROOT" rev-parse "$EVIDENCE_COMMIT:$source_path")" == \
      "$(git -C "$ROOT" rev-parse "$SOURCE_PARENT:$source_path")" ]] \
    || fail "$source_path changed between the production-source parent and evidence commit"
done

[[ "$(git -C "$ROOT" rev-parse "$EVIDENCE_COMMIT:Cargo.lock")" == \
    "$(jq -er '.source.cargoLockBlob' "$MANIFEST")" ]] || fail "Cargo.lock blob differs"
[[ "$(file_bytes "$ROOT/Cargo.lock")" == \
    "$(jq -er '.source.cargoLockBytes' "$MANIFEST")" ]] || fail "Cargo.lock byte length differs"
[[ "$(sha_file "$ROOT/Cargo.lock")" == "$(jq -er '.source.cargoLockSha256' "$MANIFEST")" ]] \
  || fail "Cargo.lock digest differs"

while IFS=$'\t' read -r name path expected_tree; do
  [[ "$(git -C "$ROOT" rev-parse "$EVIDENCE_COMMIT:$path")" == "$expected_tree" ]] \
    || fail "$name source tree differs"
done < <(jq -r '
  ["aspis-pool", "programs/aspis-pool", .source.poolTree],
  ["aspis-verifier", "programs/aspis-verifier", .source.verifierTree],
  ["aspis-registry", "programs/aspis-registry", .source.registryTree],
  ["wallet", "crates/aspis-pool-wallet-v1", .source.walletTree]
  | @tsv
' "$MANIFEST")

while IFS=$'\t' read -r name relative expected_sha expected_bytes; do
  file="$ROOT/$relative"
  [[ -f "$file" ]] || fail "missing program manifest: $relative"
  [[ "$(sha_file "$file")" == "$expected_sha" ]] || fail "$name manifest digest differs"
  if [[ -n "$expected_bytes" ]]; then
    [[ "$(wc -c <"$file" | tr -d ' ')" == "$expected_bytes" ]] \
      || fail "$name file byte length differs"
  fi
done < <(jq -r '
  (.programs[] | [.name, .manifest, .manifestSha256, ""]),
  ["txv1-builder", "crates/aspis-pool-wallet-v1/src/lane_forest_transaction_v1.rs",
    .source.txv1BuilderSha256, "45394"]
  | @tsv
' "$MANIFEST")

(
  cd "$BUNDLE"
  verify_inventory "MANIFEST.sha256" >/dev/null
)

while IFS=$'\t' read -r name output expected_sha expected_bytes; do
  artifact="$BUNDLE/artifacts/$output"
  [[ -f "$artifact" ]] || fail "missing frozen SBF: $output"
  [[ "$(sha_file "$artifact")" == "$expected_sha" ]] || fail "$name SBF digest differs"
  [[ "$(wc -c <"$artifact" | tr -d ' ')" == "$expected_bytes" ]] \
    || fail "$name SBF byte length differs"
done < <(jq -r '.programs[] | [.name, .output, .expectedSha256, .expectedBytes] | @tsv' "$MANIFEST")

readonly ROWS=$(mktemp "${TMPDIR:-/tmp}/aspis-v7-registry-v2-audit.XXXXXX")
cleanup() {
  rm -f "$ROWS"
}
trap cleanup EXIT

while IFS=$'\t' read -r file expected_sha scenario operation outcome cu tx_bytes replay_cu schedule_cu selected_verifier; do
  ledger="$BUNDLE/$file"
  [[ -f "$ledger" ]] || fail "missing terminal ledger: $file"
  [[ "$(sha_file "$ledger")" == "$expected_sha" ]] || fail "$file digest differs"
  jq -e \
    --arg scenario "$scenario" \
    --arg operation "$operation" \
    --arg outcome "$outcome" \
    --argjson cu "$cu" \
    --argjson tx_bytes "$tx_bytes" \
    --argjson schedule_cu "$schedule_cu" '
      .schema == "aspis.v7-pair-forest.registry-v2-combined-litesvm.v3" and
      .scenario == $scenario and
      .execution.operation == $operation and
      .execution.outcome == $outcome and
      .execution.compute_units == $cu and
      .execution.serialized_transaction_bytes == $tx_bytes and
      .execution.instruction_bytes == 320 and
      .execution.transaction_format == "true Solana TxV1 / VersionedMessage::V1" and
      .execution.runtime == "LiteSVM 0.16.0" and
      .execution.network == "none" and
      .execution.runtime_compute_limit == 1400000 and
      .execution.runtime_limit_is_diagnostic_override == false and
      .execution.simulation_equals_execution == true and
      .execution.txv1_declared_compute_unit_limit == 1400000 and
      .execution.txv1_4096_target_headroom_bytes == (4096 - $tx_bytes) and
      (.execution.selected_verifier_cpi_observed_in_logs | type == "boolean") and
      .artifacts.pool.sha256 == "0e94c98d28437f0b01dce546fdefaad21dc10772a4d46991c2a573d8129cd4f6" and
      .artifacts.production_verifier.sha256 == "97df12937d46e25a2eeefeac16ce31925fd473c672d6b656548be9220adbcc6d" and
      .artifacts.registry.sha256 == "0f14c7b74ec6cbe3b3f637b0f24c7e8cdc46fd09f5b2e495fd51ada16ad8f11b" and
      .registry_v2_governance.initialize.compute_units == 106065 and
      .registry_v2_governance.initialize.serialized_transaction_bytes == 504 and
      .registry_v2_governance.schedule.compute_units == $schedule_cu and
      .registry_v2_governance.schedule.serialized_transaction_bytes == 617 and
      .registry_v2_governance.activate.compute_units == 12794 and
      .registry_v2_governance.activate.serialized_transaction_bytes == 373 and
      .registry_v2_governance.freeze.compute_units == 4914 and
      .registry_v2_governance.freeze.serialized_transaction_bytes == 340 and
      .registry_v2_governance.final_registry_immutable == true and
      .registry_v2_governance.final_authority_zero == true and
      .authenticated_path.registry_family == "ASR2/ASE2 immutable deployment" and
      .authenticated_path.registry_code_certificate_matches_loaded_programdata == true and
      .authenticated_path.verifier_code_certificate_matches_loaded_programdata == true
    ' "$ledger" >/dev/null || fail "$file does not match its frozen execution row"

  if [[ "$selected_verifier" == "production" ]]; then
    jq -e '
      .artifacts.selected_verifier.kind == "production Tag-73 verifier" and
      .artifacts.selected_verifier.sha256 == "97df12937d46e25a2eeefeac16ce31925fd473c672d6b656548be9220adbcc6d"
    ' "$ledger" >/dev/null || fail "$file did not select the frozen production verifier"
  elif [[ "$selected_verifier" == "result-double" ]]; then
    jq -e '
      .artifacts.selected_verifier.kind == "test-only result double" and
      .artifacts.selected_verifier.sha256 == "3693edf83f100ca90229a8aa0406182d71fd56b6480a1fa7366c4caff4ad5c29"
    ' "$ledger" >/dev/null || fail "$file did not select the frozen result double"
  else
    fail "$file has an unknown selected verifier class: $selected_verifier"
  fi

  if [[ "$outcome" == "accepted" ]]; then
    jq -e '
      .classification == "REAL COMBINED STRICT-WORK ACCEPTANCE CU" and
      .execution.error == null and
      .execution.return_data_bytes == 792 and
      .execution.selected_verifier_cpi_observed_in_logs == true and
      .atomicity.settled_lane_equals_candidate == true and
      .atomicity.settled_history_equals_expected == true and
      .atomicity.settled_marker_equals_expected == true
    ' "$ledger" >/dev/null || fail "$file acceptance/state assertions differ"
  else
    jq -e '
      .classification == "REAL COMBINED FAIL-CLOSED REJECTION CU" and
      .execution.error != null and
      .atomicity.failure_all_accounts_byte_exact == true
    ' "$ledger" >/dev/null || fail "$file rejection/rollback assertions differ"
  fi

  if [[ "$replay_cu" != "-" ]]; then
    jq -e --argjson replay_cu "$replay_cu" '
      .execution.replay.compute_units == $replay_cu and
      .execution.replay.error != null and
      .atomicity.replay_preserved_settled_state_byte_exact == true
    ' "$ledger" >/dev/null || fail "$file replay gate differs"
  fi

  jq -cn \
    --arg file "$file" \
    --arg scenario "$scenario" \
    --arg operation "$operation" \
    --arg outcome "$outcome" \
    --argjson computeUnits "$cu" \
    --argjson serializedTransactionBytes "$tx_bytes" \
    --arg replayComputeUnits "$replay_cu" '
      {
        file: $file,
        scenario: $scenario,
        operation: $operation,
        outcome: $outcome,
        computeUnits: $computeUnits,
        serializedTransactionBytes: $serializedTransactionBytes
      } +
      (if $replayComputeUnits == "-" then {} else
        {replayComputeUnits: ($replayComputeUnits | tonumber)} end)
    ' >>"$ROWS"
done < <(jq -r '.terminalCases[] | [
  .file, .sha256, .scenario, .operation, .outcome, .computeUnits,
  .serializedTransactionBytes, (.replayComputeUnits // "-"),
  (.scheduleComputeUnits // 929136), (.selectedVerifier // "production")
] | @tsv' "$MANIFEST")

readonly CASE_COUNT=$(wc -l <"$ROWS" | tr -d ' ')
[[ "$CASE_COUNT" == "11" ]] || fail "expected exactly eleven terminal rows"
readonly WORST_CU=$(jq -s 'map(.computeUnits) | max' "$ROWS")
readonly LARGEST_TX=$(jq -s 'map(.serializedTransactionBytes) | max' "$ROWS")
(( WORST_CU < 1300000 )) || fail "frozen combined CU exceeds the 1.3M release target"
(( LARGEST_TX < 4096 )) || fail "frozen transaction reaches the TxV1 ceiling"

jq -n \
  --arg evidenceCommit "$EVIDENCE_COMMIT" \
  --arg evidenceTree "$EVIDENCE_TREE" \
  --arg sourceParent "$SOURCE_PARENT" \
  --arg bundle "$BUNDLE_RELATIVE" \
  --arg bundleInventorySha256 "$(sha_file "$INVENTORY")" \
  --argjson cases "$(jq -s '.' "$ROWS")" \
  --argjson worstCombinedCu "$WORST_CU" \
  --argjson largestTerminalTransactionBytes "$LARGEST_TX" '
  {
    schema: "aspis.v7.registry-v2-runtime-input-audit.v1",
    evidenceCommit: $evidenceCommit,
    evidenceTree: $evidenceTree,
    productionSourceParent: $sourceParent,
    productionInputsUnchangedFromParent: true,
    bundle: $bundle,
    bundleInventorySha256: $bundleInventorySha256,
    checkedTerminalCases: $cases,
    worstCombinedCu: $worstCombinedCu,
    largestTerminalTransactionBytes: $largestTerminalTransactionBytes,
    headroom: {
      to1300000Cu: (1300000 - $worstCombinedCu),
      to4096Bytes: (4096 - $largestTerminalTransactionBytes)
    },
    provenance: {
      measurement: "REAL COMBINED LITESVM 0.16.0 EXECUTION; NOT A COMPONENT SUM",
      sbf: "ONE PINNED LINUX BUILD; DUAL A/B REPRODUCTION STILL REQUIRED",
      publicCluster: "NO DEVNET OR MAINNET RECEIPT",
      deployment: false,
      signing: false,
      submission: false
    },
    pass: true
  }
'
