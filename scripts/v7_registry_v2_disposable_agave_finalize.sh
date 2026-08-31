#!/usr/bin/env bash
set -euo pipefail

# Execute the frozen Registry V2 eleven-case TxV1 corpus against one fresh,
# disposable Agave validator per case. Every transaction is signed by an
# ephemeral local payer, simulated, and then submitted byte-for-byte unchanged.
# No key file survives this script and no public RPC endpoint is accepted.

readonly FEATURE_ID="txv1aq4pp281K9um3tnPgkfX8UqtFT6wcVW3hNezGLL"
readonly REQUIRED_CASES=(
  transfer-same-page
  transfer-rollover
  withdrawal-same-page
  withdrawal-rollover
  strict-proof-mutation-rejection
  wrong-registry-release-rejection
  stale-selected-lane-rejection
  replay-nullifier-rejection
  malformed-result-rejection
  mutated-result-rejection
  failed-withdrawal-cpi-rollback
)

fail() {
  echo "FAIL: $*" >&2
  exit 1
}

if [[ $# -ne 3 ]]; then
  echo "usage: $0 <agave-4.2+-bin-dir> <materialized-case-bundle-dir> <new-evidence-dir>" >&2
  exit 2
fi

readonly AGAVE_BIN_DIR=$1
readonly BUNDLE_DIR=$2
readonly EVIDENCE_DIR=$3
readonly REPO_ROOT=$(cd "$(dirname "$0")/.." && pwd)
readonly BUNDLE_MANIFEST="$BUNDLE_DIR/bundle.json"
readonly BUNDLE_VERIFY="$REPO_ROOT/scripts/v7_txv1_bundle_verify.sh"
readonly SUITE_MATERIALIZE="$REPO_ROOT/scripts/v7_registry_v2_agave_finalized_suite_materialize.sh"
readonly SIGNER_ROOT="$REPO_ROOT/results/v7-pair-forest-combined-rejection-litesvm-20260828/harness"
readonly SIGNER_MANIFEST="$SIGNER_ROOT/Cargo.toml"
readonly RPC_PORT=${ASPIS_TXV1_LOCAL_RPC_PORT:-18899}
readonly RPC_URL="http://127.0.0.1:$RPC_PORT"

for command_name in cargo curl jq openssl shasum; do
  command -v "$command_name" >/dev/null || fail "missing required command: $command_name"
done
for binary in solana solana-keygen solana-test-validator; do
  [[ -x "$AGAVE_BIN_DIR/$binary" ]] || fail "missing executable: $AGAVE_BIN_DIR/$binary"
done
[[ -f "$BUNDLE_MANIFEST" ]] || fail "missing bundle manifest: $BUNDLE_MANIFEST"
[[ -f "$SIGNER_MANIFEST" ]] || fail "signed TxV1 evidence helper is unavailable"
[[ -x "$BUNDLE_VERIFY" ]] || fail "offline bundle validator is unavailable"
[[ -x "$SUITE_MATERIALIZE" ]] || fail "finalized suite materializer is unavailable"
[[ ! -e "$EVIDENCE_DIR" ]] || fail "refusing to overwrite evidence directory: $EVIDENCE_DIR"

jq -e '
  .schema == "aspis.v7.registry-v2-disposable-agave-txv1-bundle.v1" and
  .generatorSchema == "aspis.v7.registry-v2-deterministic-agave-bundle-generator.v1" and
  .programSourceCommit == "7179f7c550fe0461f4251dea5268af73876da91d" and
  .programSourceTree == "72d8ccd295994277bcb5f9df922c2a1483ac0443" and
  .poolSbfSha256 == "0e94c98d28437f0b01dce546fdefaad21dc10772a4d46991c2a573d8129cd4f6" and
  .poolSbfBytes == 534608 and
  .verifierSbfSha256 == "97df12937d46e25a2eeefeac16ce31925fd473c672d6b656548be9220adbcc6d" and
  .verifierSbfBytes == 1819480 and
  .registrySbfSha256 == "0f14c7b74ec6cbe3b3f637b0f24c7e8cdc46fd09f5b2e495fd51ada16ad8f11b" and
  .registrySbfBytes == 189824 and
  .resultDoubleSbfSha256 == "3693edf83f100ca90229a8aa0406182d71fd56b6480a1fa7366c4caff4ad5c29" and
  .resultDoubleSbfBytes == 20816 and
  .sbfBindingComplete == true and .executionReady == true and
  .warpSlot == 150 and .computeUnitCeiling == 1300000 and
  .transactionByteCeilingExclusive == 4096 and
  .allNegativeCasesRequireRollback == true and
  .signed == false and .submitted == false and .deployed == false and
  (.cases | type == "array" and length == 11)
' "$BUNDLE_MANIFEST" >/dev/null || fail "bundle manifest has the wrong or incomplete release binding"
"$BUNDLE_VERIFY" "$BUNDLE_DIR" --materialized >/dev/null

readonly VERSION_OUTPUT=$(NO_DNA=1 "$AGAVE_BIN_DIR/solana" --version)
readonly CORE_VERSION=$(sed -E 's/.* ([0-9]+\.[0-9]+\.[^ ]+).*/\1/' <<<"$VERSION_OUTPUT")
readonly CORE_MAJOR=${CORE_VERSION%%.*}
readonly CORE_REST=${CORE_VERSION#*.}
readonly CORE_MINOR=${CORE_REST%%.*}
if (( CORE_MAJOR < 4 || (CORE_MAJOR == 4 && CORE_MINOR < 2) )); then
  fail "Agave 4.2+ required; found: $VERSION_OUTPUT"
fi

for case_name in "${REQUIRED_CASES[@]}"; do
  jq -e --arg name "$case_name" '[.cases[] | select(.name == $name)] | length == 1' \
    "$BUNDLE_MANIFEST" >/dev/null || fail "bundle omits or duplicates required case: $case_name"
done
jq -e --argjson expected "${#REQUIRED_CASES[@]}" '.cases | length == $expected' \
  "$BUNDLE_MANIFEST" >/dev/null || fail "bundle must contain exactly the reviewed case set"

validate_bundle_relative_path() {
  local path=$1
  if [[ -z "$path" || "$path" == /* || "$path" == ".." || "$path" == ../* \
      || "$path" == */../* || "$path" == */.. ]]; then
    fail "unsafe bundle path: $path"
  fi
}

readonly POOL_PROGRAM=$(jq -er '.poolProgram' "$BUNDLE_MANIFEST")
readonly VERIFIER_PROGRAM=$(jq -er '.verifierProgram' "$BUNDLE_MANIFEST")
readonly REGISTRY_PROGRAM=$(jq -er '.registryProgram' "$BUNDLE_MANIFEST")
readonly POOL_SBF_RELATIVE=$(jq -er '.poolSbf' "$BUNDLE_MANIFEST")
readonly VERIFIER_SBF_RELATIVE=$(jq -er '.verifierSbf' "$BUNDLE_MANIFEST")
readonly REGISTRY_SBF_RELATIVE=$(jq -er '.registrySbf' "$BUNDLE_MANIFEST")
readonly RESULT_DOUBLE_SBF_RELATIVE=$(jq -er '.resultDoubleSbf' "$BUNDLE_MANIFEST")
for relative in "$POOL_SBF_RELATIVE" "$VERIFIER_SBF_RELATIVE" \
  "$REGISTRY_SBF_RELATIVE" "$RESULT_DOUBLE_SBF_RELATIVE"; do
  validate_bundle_relative_path "$relative"
done
readonly POOL_SBF="$BUNDLE_DIR/$POOL_SBF_RELATIVE"
readonly VERIFIER_SBF="$BUNDLE_DIR/$VERIFIER_SBF_RELATIVE"
readonly REGISTRY_SBF="$BUNDLE_DIR/$REGISTRY_SBF_RELATIVE"
readonly RESULT_DOUBLE_SBF="$BUNDLE_DIR/$RESULT_DOUBLE_SBF_RELATIVE"
readonly WARP_SLOT=$(jq -er '.warpSlot' "$BUNDLE_MANIFEST")
for artifact in "$POOL_SBF" "$VERIFIER_SBF" "$REGISTRY_SBF" "$RESULT_DOUBLE_SBF"; do
  [[ -f "$artifact" ]] || fail "bundle omits SBF artifact: $artifact"
done

mkdir -p "$EVIDENCE_DIR"
readonly WORK_DIR=$(mktemp -d "${TMPDIR:-/tmp}/aspis-v7-registry-v2-finalized.XXXXXX")
VALIDATOR_PID=""
cleanup() {
  if [[ -n "$VALIDATOR_PID" ]]; then
    kill "$VALIDATOR_PID" 2>/dev/null || true
    wait "$VALIDATOR_PID" 2>/dev/null || true
  fi
  case "$WORK_DIR" in
    */aspis-v7-registry-v2-finalized.*) rm -rf -- "$WORK_DIR" ;;
    *) echo "refusing to remove unexpected temporary path: $WORK_DIR" >&2 ;;
  esac
}
trap cleanup EXIT

NO_DNA=1 "$AGAVE_BIN_DIR/solana-keygen" new \
  --no-bip39-passphrase --silent --force --outfile "$WORK_DIR/local-test-payer.json"
readonly LOCAL_TEST_PAYER=$(NO_DNA=1 "$AGAVE_BIN_DIR/solana-keygen" pubkey "$WORK_DIR/local-test-payer.json")

CARGO_NET_OFFLINE=true CARGO_BUILD_JOBS=1 cargo build --release --offline --locked \
  --manifest-path "$SIGNER_MANIFEST" --bin build_signed_txv1_request \
  >"$EVIDENCE_DIR/signed-helper-build.log" 2>&1
readonly SIGNER_TARGET_DIR=${CARGO_TARGET_DIR:-$SIGNER_ROOT/target}
readonly SIGNER_BINARY="$SIGNER_TARGET_DIR/release/build_signed_txv1_request"
[[ -x "$SIGNER_BINARY" ]] || fail "signed TxV1 helper build omitted its binary"
shasum -a 256 "$SIGNER_BINARY" >"$EVIDENCE_DIR/signed-helper.sha256"
shasum -a 256 "$SIGNER_MANIFEST" "$SIGNER_ROOT/Cargo.lock" \
  "$SIGNER_ROOT/src/bin/build_signed_txv1_request.rs" \
  >"$EVIDENCE_DIR/signed-helper-inputs.sha256"

rpc() {
  curl --fail-with-body --silent --show-error --max-time 60 \
    -H 'content-type: application/json' --data-binary "$1" "$RPC_URL"
}

stop_validator() {
  if [[ -n "$VALIDATOR_PID" ]]; then
    kill "$VALIDATOR_PID"
    wait "$VALIDATOR_PID" || true
    VALIDATOR_PID=""
  fi
}

run_case() {
  local case_name=$1
  local case_json="$WORK_DIR/$case_name.case.json"
  local case_input_relative case_input expected_outcome expected_file_relative expected_file
  local selected_verifier_relative selected_verifier_sha selected_verifier_sbf selected_verifier_loader
  local validator_account_file override_loader
  local ledger="$WORK_DIR/$case_name-ledger"
  local validator_log="$EVIDENCE_DIR/$case_name.validator.log"
  local -a validator_args
  local slot blockhash account_addresses before_json signed_request simulation_response
  local send_response signature status_response confirmation_status landed_error transaction_response
  local after_json simulation_units landed_units return_data_length expected_log
  local rollback_equal actual_matches_expected simulation_matches_expected actual_state_changed
  local simulation_runtime_metadata_valid actual_runtime_metadata_valid task_poll

  jq -e --arg name "$case_name" '.cases[] | select(.name == $name)' \
    "$BUNDLE_MANIFEST" >"$case_json"
  jq -e '
    (.input | type == "string" and length > 0) and
    (.inputSha256 | test("^[0-9a-f]{64}$")) and
    (.expectedOutcome == "success" or .expectedOutcome == "failure") and
    (.expectedLogContains | type == "array" and length > 0) and
    (.selectedVerifier.loader == "upgradeable-none") and
    (.rollbackRequired == (.expectedOutcome == "failure"))
  ' "$case_json" >/dev/null || fail "case manifest is incomplete: $case_name"
  case_input_relative=$(jq -er '.input' "$case_json")
  validate_bundle_relative_path "$case_input_relative"
  case_input="$BUNDLE_DIR/$case_input_relative"
  expected_outcome=$(jq -er '.expectedOutcome' "$case_json")
  [[ -f "$case_input" ]] || fail "missing case input for $case_name"
  [[ "$(shasum -a 256 "$case_input" | awk '{print $1}')" == "$(jq -er '.inputSha256' "$case_json")" ]] \
    || fail "case input hash differs for $case_name"

  selected_verifier_relative=$(jq -er '.selectedVerifier.file' "$case_json")
  selected_verifier_sha=$(jq -er '.selectedVerifier.fileSha256' "$case_json")
  selected_verifier_loader=$(jq -er '.selectedVerifier.loader' "$case_json")
  validate_bundle_relative_path "$selected_verifier_relative"
  selected_verifier_sbf="$BUNDLE_DIR/$selected_verifier_relative"
  [[ "$selected_verifier_loader" == "upgradeable-none" \
      && -f "$selected_verifier_sbf" \
      && "$(shasum -a 256 "$selected_verifier_sbf" | awk '{print $1}')" == "$selected_verifier_sha" ]] \
    || fail "selected verifier binding differs for $case_name"

  validator_args=(
    --reset --quiet --ledger "$ledger" --bind-address 127.0.0.1 --rpc-port "$RPC_PORT"
    --warp-slot "$WARP_SLOT" --mint "$LOCAL_TEST_PAYER"
    --bpf-program "$POOL_PROGRAM" "$POOL_SBF"
    --upgradeable-program "$REGISTRY_PROGRAM" "$REGISTRY_SBF" none
    --upgradeable-program "$VERIFIER_PROGRAM" "$selected_verifier_sbf" none
  )
  while IFS=$'\t' read -r address relative_path expected_sha; do
    validate_bundle_relative_path "$relative_path"
    [[ -f "$BUNDLE_DIR/$relative_path" ]] || fail "missing genesis account: $relative_path"
    [[ "$(shasum -a 256 "$BUNDLE_DIR/$relative_path" | awk '{print $1}')" == "$expected_sha" ]] \
      || fail "genesis account hash differs: $relative_path"
    validator_account_file="$WORK_DIR/$case_name-genesis-$address.json"
    jq --arg pubkey "$address" '. as $account | {pubkey: $pubkey, account: $account}' \
      "$BUNDLE_DIR/$relative_path" >"$validator_account_file"
    validator_args+=(--account "$address" "$validator_account_file")
  done < <(jq -r '.genesisAccounts[] | select(.loadAtGenesis) | [.address, .file, .fileSha256] | @tsv' "$case_json")
  while IFS=$'\t' read -r address relative_path expected_sha override_loader; do
    validate_bundle_relative_path "$relative_path"
    [[ -f "$BUNDLE_DIR/$relative_path" ]] || fail "missing program override: $relative_path"
    [[ "$(shasum -a 256 "$BUNDLE_DIR/$relative_path" | awk '{print $1}')" == "$expected_sha" ]] \
      || fail "program override differs: $relative_path"
    case "$override_loader" in
      bpf) validator_args+=(--bpf-program "$address" "$BUNDLE_DIR/$relative_path") ;;
      upgradeable-none) validator_args+=(--upgradeable-program "$address" "$BUNDLE_DIR/$relative_path" none) ;;
      *) fail "unknown program override loader: $override_loader" ;;
    esac
  done < <(jq -r '.programOverrides[]? | [.address, .file, .fileSha256, .loader] | @tsv' "$case_json")

  NO_DNA=1 "$AGAVE_BIN_DIR/solana-test-validator" "${validator_args[@]}" \
    >"$validator_log" 2>&1 &
  VALIDATOR_PID=$!
  for task_poll in $(seq 1 150); do
    if rpc '{"jsonrpc":"2.0","id":1,"method":"getHealth"}' \
      | jq -e '.result == "ok"' >/dev/null 2>&1; then
      break
    fi
    sleep 0.2
  done
  rpc '{"jsonrpc":"2.0","id":1,"method":"getHealth"}' | jq -e '.result == "ok"' >/dev/null
  rpc "{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"getAccountInfo\",\"params\":[\"$FEATURE_ID\",{\"encoding\":\"base64\",\"commitment\":\"finalized\"}]}" \
    | jq -e '.result.value != null and (.result.value.data[0] | startswith("AQ"))' >/dev/null \
    || fail "TxV1 was not active for $case_name"

  slot=$(rpc '{"jsonrpc":"2.0","id":3,"method":"getSlot","params":[{"commitment":"finalized"}]}' | jq -er '.result')
  blockhash=$(rpc "{\"jsonrpc\":\"2.0\",\"id\":4,\"method\":\"getLatestBlockhash\",\"params\":[{\"commitment\":\"finalized\",\"minContextSlot\":$slot}]}" | jq -er '.result.value.blockhash')
  jq --arg blockhash "$blockhash" --argjson slot "$slot" \
    '.recentBlockhash = $blockhash | .minContextSlot = $slot' \
    "$case_input" >"$WORK_DIR/$case_name.input.json"
  account_addresses=$(jq -c '.postStateAccounts // []' "$WORK_DIR/$case_name.input.json")
  jq -e 'length > 0' <<<"$account_addresses" >/dev/null || fail "protected account list is empty"
  before_json=$(rpc "$(jq -nc --argjson addresses "$account_addresses" '{jsonrpc:"2.0",id:5,method:"getMultipleAccounts",params:[$addresses,{encoding:"base64",commitment:"finalized"}]}')")
  jq . <<<"$before_json" >"$EVIDENCE_DIR/$case_name.before.json"

  signed_request=$(NO_DNA=1 "$SIGNER_BINARY" \
    "$WORK_DIR/$case_name.input.json" "$WORK_DIR/local-test-payer.json")
  jq -e '
    .schema == "aspis.v7.txv1-signed-local-request.v1" and .signed == true and
    .summary.computeUnitLimit == 1300000 and
    .serializedTransactionBytes < 4096 and .summary.headroomTo4096Bytes > 0 and
    (.signature | type == "string" and length > 0) and
    (.signedWireSha256 | test("^[0-9a-f]{64}$"))
  ' <<<"$signed_request" >/dev/null || fail "signed request preflight failed for $case_name"
  jq . <<<"$signed_request" >"$EVIDENCE_DIR/$case_name.signed-request.json"

  simulation_response=$(rpc "$(jq -c '.simulationRequest' <<<"$signed_request")")
  jq . <<<"$simulation_response" >"$EVIDENCE_DIR/$case_name.simulation.json"
  jq -e '.error | not' <<<"$simulation_response" >/dev/null
  simulation_units=$(jq -er '.result.value.unitsConsumed' <<<"$simulation_response")
  (( simulation_units <= 1300000 )) || fail "simulation CU exceeded the release ceiling"
  if [[ "$expected_outcome" == "success" ]]; then
    jq -e '.result.value.err == null' <<<"$simulation_response" >/dev/null
  else
    jq -e '.result.value.err != null' <<<"$simulation_response" >/dev/null
  fi

  send_response=$(rpc "$(jq -c '.sendRequest' <<<"$signed_request")")
  jq . <<<"$send_response" >"$EVIDENCE_DIR/$case_name.send.json"
  jq -e '.error | not' <<<"$send_response" >/dev/null
  signature=$(jq -er '.result' <<<"$send_response")
  [[ "$signature" == "$(jq -er '.signature' <<<"$signed_request")" ]] \
    || fail "submitted signature differs from the exact simulated transaction"

  status_response='null'
  confirmation_status=''
  for task_poll in $(seq 1 400); do
    status_response=$(rpc "$(jq -nc --arg signature "$signature" '{jsonrpc:"2.0",id:6,method:"getSignatureStatuses",params:[[$signature],{searchTransactionHistory:true}]}')")
    confirmation_status=$(jq -r '.result.value[0].confirmationStatus // empty' <<<"$status_response")
    [[ "$confirmation_status" == "finalized" ]] && break
    sleep 0.1
  done
  [[ "$confirmation_status" == "finalized" ]] || fail "transaction did not finalize: $case_name"
  jq . <<<"$status_response" >"$EVIDENCE_DIR/$case_name.finalized-status.json"
  landed_error=$(jq -c '.result.value[0].err' <<<"$status_response")
  if [[ "$expected_outcome" == "success" ]]; then
    [[ "$landed_error" == "null" ]] || fail "honest transaction finalized with an error"
  else
    [[ "$landed_error" != "null" ]] || fail "negative transaction unexpectedly finalized successfully"
  fi

  transaction_response='null'
  for task_poll in $(seq 1 100); do
    transaction_response=$(rpc "$(jq -nc --arg signature "$signature" '{jsonrpc:"2.0",id:7,method:"getTransaction",params:[$signature,{encoding:"json",commitment:"finalized",maxSupportedTransactionVersion:1}]}')")
    jq -e '.result != null' <<<"$transaction_response" >/dev/null && break
    sleep 0.1
  done
  jq -e '.result != null' <<<"$transaction_response" >/dev/null || fail "finalized transaction unavailable"
  jq . <<<"$transaction_response" >"$EVIDENCE_DIR/$case_name.transaction.json"
  landed_units=$(jq -er '.result.meta.computeUnitsConsumed' <<<"$transaction_response")
  (( landed_units <= 1300000 )) || fail "landed CU exceeded the release ceiling"
  if [[ "$expected_outcome" == "success" ]]; then
    jq -e '.result.meta.err == null' <<<"$transaction_response" >/dev/null
  else
    jq -e '.result.meta.err != null' <<<"$transaction_response" >/dev/null
  fi
  while IFS= read -r expected_log; do
    jq -e --arg expected "$expected_log" \
      '.result.meta.logMessages | any(contains($expected))' <<<"$transaction_response" >/dev/null \
      || fail "landed log omitted '$expected_log' for $case_name"
  done < <(jq -r '.expectedLogContains[]' "$case_json")

  after_json=$(rpc "$(jq -nc --argjson addresses "$account_addresses" '{jsonrpc:"2.0",id:8,method:"getMultipleAccounts",params:[$addresses,{encoding:"base64",commitment:"finalized"}]}')")
  jq . <<<"$after_json" >"$EVIDENCE_DIR/$case_name.after.json"
  rollback_equal=$(jq -n \
    --argjson before "$(jq '.result.value' <<<"$before_json")" \
    --argjson after "$(jq '.result.value' <<<"$after_json")" '$before == $after')

  if [[ "$expected_outcome" == "success" ]]; then
    expected_file_relative=$(jq -er '.expectedSimulationAccountsFile' "$case_json")
    validate_bundle_relative_path "$expected_file_relative"
    expected_file="$BUNDLE_DIR/$expected_file_relative"
    [[ -f "$expected_file" ]] || fail "missing frozen expected state: $expected_file_relative"
    simulation_matches_expected=$(jq -n \
      --argjson actual "$(jq '.result.value.accounts' <<<"$simulation_response")" \
      --argjson expected "$(jq . "$expected_file")" '
      def program_state: map(if . == null then null else del(.rentEpoch) end);
      ($actual | program_state) == ($expected | program_state)')
    actual_matches_expected=$(jq -n \
      --argjson actual "$(jq '.result.value' <<<"$after_json")" \
      --argjson expected "$(jq . "$expected_file")" '
      def program_state: map(if . == null then null else del(.rentEpoch) end);
      ($actual | program_state) == ($expected | program_state)')
    simulation_runtime_metadata_valid=$(jq -n \
      --argjson actual "$(jq '.result.value.accounts' <<<"$simulation_response")" '
      all($actual[]; . == null or .rentEpoch == 0 or .rentEpoch == 18446744073709551615)')
    actual_runtime_metadata_valid=$(jq -n \
      --argjson actual "$(jq '.result.value' <<<"$after_json")" '
      all($actual[]; . == null or .rentEpoch == 0 or .rentEpoch == 18446744073709551615)')
    [[ "$simulation_matches_expected" == "true" && "$actual_matches_expected" == "true" \
        && "$simulation_runtime_metadata_valid" == "true" \
        && "$actual_runtime_metadata_valid" == "true" ]] \
      || fail "honest protected post-state differs from the frozen expectation"
    [[ "$rollback_equal" == "false" ]] || fail "honest transaction did not change protected state"
    jq -e --arg pool "$POOL_PROGRAM" '.result.meta.returnData.programId == $pool' \
      <<<"$transaction_response" >/dev/null
    return_data_length=$(jq -r '.result.meta.returnData.data[0]' <<<"$transaction_response" \
      | openssl base64 -d -A | wc -c | tr -d ' ')
    [[ "$return_data_length" == "792" ]] || fail "landed ASR8 return length differs"
    actual_state_changed=true
  else
    [[ "$rollback_equal" == "true" ]] || fail "negative transaction changed protected state"
    simulation_matches_expected=null
    actual_matches_expected=null
    simulation_runtime_metadata_valid=null
    actual_runtime_metadata_valid=null
    return_data_length=null
    actual_state_changed=false
  fi

  jq -n \
    --arg case "$case_name" --arg expected "$expected_outcome" --arg version "$VERSION_OUTPUT" \
    --arg localTestPayer "$LOCAL_TEST_PAYER" --arg signature "$signature" \
    --arg signedWireSha256 "$(jq -er '.signedWireSha256' <<<"$signed_request")" \
    --argjson packetBytes "$(jq -er '.serializedTransactionBytes' <<<"$signed_request")" \
    --argjson headroom "$(jq -er '.summary.headroomTo4096Bytes' <<<"$signed_request")" \
    --argjson simulationUnits "$simulation_units" --argjson landedUnits "$landed_units" \
    --argjson landedError "$landed_error" --argjson rollbackPreserved "$rollback_equal" \
    --argjson actualStateChanged "$actual_state_changed" \
    --argjson simulationMatchesExpected "$simulation_matches_expected" \
    --argjson actualMatchesExpected "$actual_matches_expected" \
    --argjson simulationRuntimeMetadataValid "$simulation_runtime_metadata_valid" \
    --argjson actualRuntimeMetadataValid "$actual_runtime_metadata_valid" \
    --argjson returnDataBytes "$return_data_length" '
    {
      schema: "aspis.v7.registry-v2-disposable-agave-txv1-finalized-case.v1",
      case: $case,
      expectedOutcome: $expected,
      agave: $version,
      cluster: "disposable-local-validator",
      localTestPayer: $localTestPayer,
      signature: $signature,
      signed: true,
      submitted: true,
      finalized: true,
      sameSignedBytesSimulatedAndSubmitted: true,
      packetBytes: $packetBytes,
      transactionHeadroomTo4096Bytes: $headroom,
      signedWireSha256: $signedWireSha256,
      simulationUnitsConsumed: $simulationUnits,
      landedUnitsConsumed: $landedUnits,
      landedError: $landedError,
      protectedStateRollbackPreserved:
        (if $expected == "failure" then $rollbackPreserved else null end),
      protectedStateChangedOnSuccess:
        (if $expected == "success" then $actualStateChanged else null end),
      simulationMatchesFrozenExpectedState:
        (if $expected == "success" then $simulationMatchesExpected else null end),
      landedStateMatchesFrozenExpectedState:
        (if $expected == "success" then $actualMatchesExpected else null end),
      simulationRuntimeMetadataValid: $simulationRuntimeMetadataValid,
      landedRuntimeMetadataValid: $actualRuntimeMetadataValid,
      returnDataBytes: $returnDataBytes,
      localEphemeralKeyOnly: true,
      realFundsUsed: false,
      publicClusterUsed: false,
      deployed: false,
      receipts: {
        signedRequest: ($case + ".signed-request.json"),
        simulation: ($case + ".simulation.json"),
        send: ($case + ".send.json"),
        finalizedStatus: ($case + ".finalized-status.json"),
        transaction: ($case + ".transaction.json"),
        protectedStateBefore: ($case + ".before.json"),
        protectedStateAfter: ($case + ".after.json"),
        validatorLog: ($case + ".validator.log")
      }
    }' >"$EVIDENCE_DIR/$case_name.case.json"

  stop_validator
}

for case_name in "${REQUIRED_CASES[@]}"; do
  echo "signed/finalized local lifecycle: $case_name"
  run_case "$case_name"
done

"$SUITE_MATERIALIZE" "$VERSION_OUTPUT" "$LOCAL_TEST_PAYER" "$BUNDLE_DIR" "$EVIDENCE_DIR"
echo "disposable Agave signed/finalized Registry V2 suite PASS: $EVIDENCE_DIR/suite.json"
