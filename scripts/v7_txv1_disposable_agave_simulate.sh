#!/usr/bin/env bash
set -euo pipefail

# Historical filename retained so old release automation resolves the same
# path. This runner now proves a real local lifecycle: each signed transaction
# is simulated, the exact same bytes are submitted to a disposable validator,
# and its finalized status and protected post-state are checked.

readonly FEATURE_ID="txv1aq4pp281K9um3tnPgkfX8UqtFT6wcVW3hNezGLL"
readonly REQUIRED_CASES=(
  transfer-same-page
  transfer-rollover
  withdrawal-same-page
  withdrawal-rollover
  stale-selected-lane-rejection
  replay-nullifier-rejection
  wrong-checkpoint-rejection
  wrong-registry-release-rejection
  malformed-proof-rejection
  mutated-proof-rejection
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
readonly SIGNER_MANIFEST="$REPO_ROOT/results/v7-pair-forest-combined-rejection-litesvm-20260828/harness/Cargo.toml"
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
[[ ! -e "$EVIDENCE_DIR" ]] || fail "refusing to overwrite evidence directory: $EVIDENCE_DIR"

jq -e '
  .schema == "aspis.v7.disposable-agave-txv1-bundle.v1" and
  .programSourceCommit == "6bc7d3caf181be23a8a6ac7769497c965cd7273d" and
  .programSourceTree == "aae627375ad1f4f48ac4eae8e0c585c6c0680bab" and
  .poolSourceTree == "cd7df911f651f84f408053fd934421aa88c7a9ca" and
  .verifierSourceTree == "e7370c020cac1e51ca9e41092dcf6ecbf095bd99" and
  .poolSbfSha256 == "0bbe441f0e13c2f61e2369674628b06c9d538192514b4e9a92d229479956586d" and
  .poolSbfBytes == 526056 and
  .verifierSbfSha256 == "c43960303f2d67606362dc09d74f3a7983dcfcbe0665984a385a0efa7ddc5e47" and
  .verifierSbfBytes == 1812264 and
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

validate_bundle_relative_path() {
  local path=$1
  if [[ -z "$path" || "$path" == /* || "$path" == ".." || "$path" == ../* \
      || "$path" == */../* || "$path" == */.. ]]; then
    fail "unsafe bundle path: $path"
  fi
}

readonly POOL_PROGRAM=$(jq -er '.poolProgram' "$BUNDLE_MANIFEST")
readonly VERIFIER_PROGRAM=$(jq -er '.verifierProgram' "$BUNDLE_MANIFEST")
readonly POOL_SBF_RELATIVE=$(jq -er '.poolSbf' "$BUNDLE_MANIFEST")
readonly VERIFIER_SBF_RELATIVE=$(jq -er '.verifierSbf' "$BUNDLE_MANIFEST")
validate_bundle_relative_path "$POOL_SBF_RELATIVE"
validate_bundle_relative_path "$VERIFIER_SBF_RELATIVE"
readonly POOL_SBF="$BUNDLE_DIR/$POOL_SBF_RELATIVE"
readonly VERIFIER_SBF="$BUNDLE_DIR/$VERIFIER_SBF_RELATIVE"
readonly WARP_SLOT=$(jq -er '.warpSlot' "$BUNDLE_MANIFEST")
[[ -f "$POOL_SBF" && -f "$VERIFIER_SBF" ]] || fail "bundle omits the SBF artifacts"

mkdir -p "$EVIDENCE_DIR"
readonly WORK_DIR=$(mktemp -d "${TMPDIR:-/tmp}/aspis-v7-txv1-lifecycle.XXXXXX")
VALIDATOR_PID=""
cleanup() {
  if [[ -n "$VALIDATOR_PID" ]]; then
    kill "$VALIDATOR_PID" 2>/dev/null || true
    wait "$VALIDATOR_PID" 2>/dev/null || true
  fi
  case "$WORK_DIR" in
    */aspis-v7-txv1-lifecycle.*) rm -rf -- "$WORK_DIR" ;;
    *) echo "refusing to remove unexpected temporary path: $WORK_DIR" >&2 ;;
  esac
}
trap cleanup EXIT

NO_DNA=1 "$AGAVE_BIN_DIR/solana-keygen" new \
  --no-bip39-passphrase --silent --force --outfile "$WORK_DIR/local-test-payer.json"
readonly LOCAL_TEST_PAYER=$(NO_DNA=1 "$AGAVE_BIN_DIR/solana-keygen" pubkey "$WORK_DIR/local-test-payer.json")

CARGO_NET_OFFLINE=true cargo build --release --offline --locked \
  --manifest-path "$SIGNER_MANIFEST" --bin build_signed_txv1_request \
  >"$EVIDENCE_DIR/signed-helper-build.log" 2>&1
readonly SIGNER_BINARY="$REPO_ROOT/results/v7-pair-forest-combined-rejection-litesvm-20260828/harness/target/release/build_signed_txv1_request"
[[ -x "$SIGNER_BINARY" ]] || fail "signed TxV1 helper build omitted its binary"
shasum -a 256 "$SIGNER_BINARY" >"$EVIDENCE_DIR/signed-helper.sha256"
shasum -a 256 "$SIGNER_MANIFEST" \
  "$REPO_ROOT/results/v7-pair-forest-combined-rejection-litesvm-20260828/harness/Cargo.lock" \
  "$REPO_ROOT/results/v7-pair-forest-combined-rejection-litesvm-20260828/harness/src/bin/build_signed_txv1_request.rs" \
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
  local validator_account_file
  local ledger="$WORK_DIR/$case_name-ledger"
  local validator_log="$EVIDENCE_DIR/$case_name.validator.log"
  local -a validator_args
  local slot blockhash account_addresses before_json signed_request simulation_response
  local send_response signature status_response confirmation_status landed_error transaction_response
  local after_json simulation_units landed_units return_data_length expected_log
  local rollback_equal actual_matches_expected simulation_matches_expected actual_state_changed
  local actual_exact_matches_expected simulation_exact_matches_expected
  local actual_runtime_metadata_valid simulation_runtime_metadata_valid
  local task_poll

  jq -e --arg name "$case_name" '.cases[] | select(.name == $name)' \
    "$BUNDLE_MANIFEST" >"$case_json"
  case_input_relative=$(jq -er '.input' "$case_json")
  validate_bundle_relative_path "$case_input_relative"
  case_input="$BUNDLE_DIR/$case_input_relative"
  expected_outcome=$(jq -er '.expectedOutcome' "$case_json")
  [[ -f "$case_input" ]] || fail "missing case input for $case_name"
  [[ "$(shasum -a 256 "$case_input" | awk '{print $1}')" == "$(jq -er '.inputSha256' "$case_json")" ]] \
    || fail "case input hash differs for $case_name"

  validator_args=(
    --reset --quiet --ledger "$ledger" --bind-address 127.0.0.1 --rpc-port "$RPC_PORT"
    --warp-slot "$WARP_SLOT" --mint "$LOCAL_TEST_PAYER"
    --bpf-program "$POOL_PROGRAM" "$POOL_SBF"
    --bpf-program "$VERIFIER_PROGRAM" "$VERIFIER_SBF"
  )
  while IFS=$'\t' read -r address relative_path expected_sha; do
    validate_bundle_relative_path "$relative_path"
    [[ -f "$BUNDLE_DIR/$relative_path" ]] || fail "missing genesis account: $relative_path"
    [[ "$(shasum -a 256 "$BUNDLE_DIR/$relative_path" | awk '{print $1}')" == "$expected_sha" ]] \
      || fail "genesis account hash differs: $relative_path"
    # The frozen fixture deliberately uses the RPC account-value shape so its
    # protected-state bytes can be compared directly.  Agave's genesis loader
    # requires the CLI wrapper {pubkey, account}, even though --account already
    # receives that address.  Wrap the byte-exact account value with only that
    # authenticated address in a task-owned temporary copy; never rewrite or
    # weaken the hash binding of the frozen fixture itself.
    validator_account_file="$WORK_DIR/$case_name-genesis-$address.json"
    jq --arg pubkey "$address" '. as $account | {pubkey: $pubkey, account: $account}' \
      "$BUNDLE_DIR/$relative_path" >"$validator_account_file"
    jq -e --arg pubkey "$address" \
      '.pubkey == $pubkey and (.account | type == "object")' \
      "$validator_account_file" >/dev/null \
      || fail "temporary Agave account adapter lost its authenticated pubkey"
    validator_args+=(--account "$address" "$validator_account_file")
  done < <(jq -r '.genesisAccounts[] | select(.loadAtGenesis) | [.address, .file, .fileSha256] | @tsv' "$case_json")
  while IFS=$'\t' read -r address relative_path expected_sha; do
    validate_bundle_relative_path "$relative_path"
    [[ "$(shasum -a 256 "$BUNDLE_DIR/$relative_path" | awk '{print $1}')" == "$expected_sha" ]] \
      || fail "program override differs: $relative_path"
    validator_args+=(--bpf-program "$address" "$BUNDLE_DIR/$relative_path")
  done < <(jq -r '.programOverrides[]? | [.address, .file, .fileSha256] | @tsv' "$case_json")

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
  account_addresses=$(jq -c '.postStateAccounts' "$WORK_DIR/$case_name.input.json")
  jq -e 'length > 0' <<<"$account_addresses" >/dev/null || fail "protected account list is empty"
  before_json=$(rpc "$(jq -nc --argjson addresses "$account_addresses" '{jsonrpc:"2.0",id:5,method:"getMultipleAccounts",params:[$addresses,{encoding:"base64",commitment:"finalized"}]}')")

  signed_request=$(NO_DNA=1 "$SIGNER_BINARY" \
    "$WORK_DIR/$case_name.input.json" "$WORK_DIR/local-test-payer.json")
  jq -e '
    .schema == "aspis.v7.txv1-signed-local-request.v1" and .signed == true and
    .summary.computeUnitLimit == 1300000 and
    .serializedTransactionBytes < 4096 and
    .summary.headroomTo4096Bytes > 0 and
    (.signature | type == "string" and length > 0) and
    (.signedWireSha256 | test("^[0-9a-f]{64}$"))
  ' <<<"$signed_request" >/dev/null || fail "signed request preflight failed for $case_name"

  simulation_response=$(rpc "$(jq -c '.simulationRequest' <<<"$signed_request")")
  jq -e '.error | not' <<<"$simulation_response" >/dev/null
  simulation_units=$(jq -er '.result.value.unitsConsumed' <<<"$simulation_response")
  (( simulation_units <= 1300000 )) || fail "simulation CU exceeded the release ceiling"
  if [[ "$expected_outcome" == "success" ]]; then
    jq -e '.result.value.err == null' <<<"$simulation_response" >/dev/null
  else
    jq -e '.result.value.err != null' <<<"$simulation_response" >/dev/null
  fi

  send_response=$(rpc "$(jq -c '.sendRequest' <<<"$signed_request")")
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
  rollback_equal=$(jq -n \
    --argjson before "$(jq '.result.value' <<<"$before_json")" \
    --argjson after "$(jq '.result.value' <<<"$after_json")" '$before == $after')

  if [[ "$expected_outcome" == "success" ]]; then
    expected_file_relative=$(jq -er '.expectedSimulationAccountsFile' "$case_json")
    validate_bundle_relative_path "$expected_file_relative"
    expected_file="$BUNDLE_DIR/$expected_file_relative"
    simulation_exact_matches_expected=$(jq -n \
      --argjson actual "$(jq '.result.value.accounts' <<<"$simulation_response")" \
      --argjson expected "$(jq . "$expected_file")" '$actual == $expected')
    actual_exact_matches_expected=$(jq -n \
      --argjson actual "$(jq '.result.value' <<<"$after_json")" \
      --argjson expected "$(jq . "$expected_file")" '$actual == $expected')
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
    jq -n \
      --arg case "$case_name" \
      --argjson simulationActual "$(jq '.result.value.accounts' <<<"$simulation_response")" \
      --argjson landedActual "$(jq '.result.value' <<<"$after_json")" \
      --argjson expected "$(jq . "$expected_file")" '
      def program_state: map(if . == null then null else del(.rentEpoch) end);
      {
        schema: "aspis.v7.disposable-agave-state-comparison.v2",
        case: $case,
        simulationMatchesFrozenExpectedExactly: ($simulationActual == $expected),
        landedMatchesFrozenExpectedExactly: ($landedActual == $expected),
        simulationMatchesFrozenExpectedProgramState:
          (($simulationActual | program_state) == ($expected | program_state)),
        landedMatchesFrozenExpectedProgramState:
          (($landedActual | program_state) == ($expected | program_state)),
        programStateComparisonExcludesRuntimeMetadata: ["rentEpoch"],
        acceptedRuntimeRentEpochValues: [0, 18446744073709551615],
        simulationRuntimeMetadataValid:
          (all($simulationActual[]; . == null or .rentEpoch == 0 or .rentEpoch == 18446744073709551615)),
        landedRuntimeMetadataValid:
          (all($landedActual[]; . == null or .rentEpoch == 0 or .rentEpoch == 18446744073709551615)),
        simulationActual: $simulationActual,
        landedActual: $landedActual,
        frozenExpected: $expected
      }' >"$EVIDENCE_DIR/$case_name.state-comparison.json"
    [[ "$simulation_matches_expected" == "true" && "$actual_matches_expected" == "true" \
        && "$simulation_runtime_metadata_valid" == "true" \
        && "$actual_runtime_metadata_valid" == "true" ]] \
      || fail "honest program-controlled post-state differs from the frozen expectation"
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
    simulation_exact_matches_expected=null
    actual_exact_matches_expected=null
    simulation_runtime_metadata_valid=null
    actual_runtime_metadata_valid=null
    actual_state_changed=false
  fi

  jq -n \
    --arg case "$case_name" --arg expected "$expected_outcome" --arg version "$VERSION_OUTPUT" \
    --arg localTestPayer "$LOCAL_TEST_PAYER" --arg signature "$signature" \
    --argjson signedRequest "$signed_request" --argjson simulation "$simulation_response" \
    --argjson send "$send_response" --argjson finalizedStatus "$status_response" \
    --argjson transaction "$transaction_response" --argjson before "$before_json" \
    --argjson after "$after_json" --argjson simulationUnits "$simulation_units" \
    --argjson landedUnits "$landed_units" --argjson rollbackPreserved "$rollback_equal" \
    --argjson actualStateChanged "$actual_state_changed" \
    --argjson simulationMatchesExpected "$simulation_matches_expected" \
    --argjson actualMatchesExpected "$actual_matches_expected" \
    --argjson simulationExactMatchesExpected "$simulation_exact_matches_expected" \
    --argjson actualExactMatchesExpected "$actual_exact_matches_expected" \
    --argjson simulationRuntimeMetadataValid "$simulation_runtime_metadata_valid" \
    --argjson actualRuntimeMetadataValid "$actual_runtime_metadata_valid" '
    {
      schema: "aspis.v7.disposable-agave-txv1-finalized-case.v2",
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
      packetBytes: $signedRequest.serializedTransactionBytes,
      signedWireSha256: $signedRequest.signedWireSha256,
      simulationUnitsConsumed: $simulationUnits,
      landedUnitsConsumed: $landedUnits,
      protectedStateRollbackPreserved: $rollbackPreserved,
      protectedStateChangedOnSuccess: $actualStateChanged,
      simulationMatchesFrozenExpectedExactly: $simulationExactMatchesExpected,
      landedMatchesFrozenExpectedExactly: $actualExactMatchesExpected,
      simulationMatchesFrozenExpectedProgramState: $simulationMatchesExpected,
      landedMatchesFrozenExpectedProgramState: $actualMatchesExpected,
      programStateComparisonExcludesRuntimeMetadata: ["rentEpoch"],
      acceptedRuntimeRentEpochValues: [0, 18446744073709551615],
      simulationRuntimeMetadataValid: $simulationRuntimeMetadataValid,
      landedRuntimeMetadataValid: $actualRuntimeMetadataValid,
      signedRequest: $signedRequest,
      simulationResponse: $simulation,
      sendResponse: $send,
      finalizedStatus: $finalizedStatus,
      transactionResponse: $transaction,
      protectedStateBefore: $before,
      protectedStateAfter: $after
    }' >"$EVIDENCE_DIR/$case_name.json"

  stop_validator
}

for case_name in "${REQUIRED_CASES[@]}"; do
  echo "signed/finalized local lifecycle: $case_name"
  run_case "$case_name"
done

case_files=()
for case_name in "${REQUIRED_CASES[@]}"; do
  case_files+=("$EVIDENCE_DIR/$case_name.json")
done
jq -n \
  --arg version "$VERSION_OUTPUT" --arg localTestPayer "$LOCAL_TEST_PAYER" \
  --arg poolSha256 "$(shasum -a 256 "$POOL_SBF" | awk '{print $1}')" \
  --arg verifierSha256 "$(shasum -a 256 "$VERIFIER_SBF" | awk '{print $1}')" \
  --arg bundleSha256 "$(shasum -a 256 "$BUNDLE_MANIFEST" | awk '{print $1}')" \
  --argjson warpSlot "$WARP_SLOT" --slurpfile cases <(jq -s '.' "${case_files[@]}") '
  {
    schema: "aspis.v7.disposable-agave-txv1-finalized-suite.v2",
    agave: $version,
    cluster: "disposable-local-validator",
    localTestPayer: $localTestPayer,
    poolSbfSha256: $poolSha256,
    verifierSbfSha256: $verifierSha256,
    bundleSha256: $bundleSha256,
    warpSlot: $warpSlot,
    computeUnitCeiling: 1300000,
    transactionByteCeilingExclusive: 4096,
    cases: $cases[0],
    allCasesSigned: ($cases[0] | all(.signed == true)),
    allCasesSubmitted: ($cases[0] | all(.submitted == true)),
    allCasesFinalized: ($cases[0] | all(.finalized == true)),
    allPacketsUnder4096: ($cases[0] | all(.packetBytes < 4096)),
    allLandedComputeUnder1300000: ($cases[0] | all(.landedUnitsConsumed <= 1300000)),
    allNegativeCasesRolledBack: ($cases[0] | map(select(.expectedOutcome == "failure")) | all(.protectedStateRollbackPreserved == true)),
    allHonestCasesMatchFrozenProgramState: ($cases[0] | map(select(.expectedOutcome == "success")) | all(.landedMatchesFrozenExpectedProgramState == true)),
    allHonestRuntimeMetadataValid: ($cases[0] | map(select(.expectedOutcome == "success")) | all(.simulationRuntimeMetadataValid == true and .landedRuntimeMetadataValid == true)),
    programStateComparisonExcludesRuntimeMetadata: ["rentEpoch"],
    publicClusterUsed: false,
    deployed: false
  }' >"$EVIDENCE_DIR/suite.json"

jq -e '
  (.cases | length) == 11 and .allCasesSigned and .allCasesSubmitted and
  .allCasesFinalized and .allPacketsUnder4096 and .allLandedComputeUnder1300000 and
  .allNegativeCasesRolledBack and .allHonestCasesMatchFrozenProgramState and
  .allHonestRuntimeMetadataValid and
  (.publicClusterUsed | not) and (.deployed | not)
' "$EVIDENCE_DIR/suite.json" >/dev/null || fail "final suite summary did not close"

echo "disposable Agave signed/finalized eleven-case suite PASS: $EVIDENCE_DIR/suite.json"
