#!/usr/bin/env bash
set -euo pipefail

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

if [[ $# -ne 3 ]]; then
  echo "usage: $0 <agave-4.2+-bin-dir> <case-bundle-dir> <evidence-dir>" >&2
  exit 2
fi

readonly AGAVE_BIN_DIR=$1
readonly BUNDLE_DIR=$2
readonly EVIDENCE_DIR=$3
readonly REPO_ROOT=$(cd "$(dirname "$0")/.." && pwd)
readonly BUNDLE_MANIFEST="$BUNDLE_DIR/bundle.json"
readonly BUNDLE_VERIFY="$REPO_ROOT/scripts/v7_txv1_bundle_verify.sh"
readonly SUITE_MATERIALIZE="$REPO_ROOT/scripts/v7_txv1_agave_suite_materialize.sh"
readonly RPC_PORT=${ASPIS_TXV1_LOCAL_RPC_PORT:-18899}
readonly RPC_URL="http://127.0.0.1:$RPC_PORT"

for command in cargo curl jq openssl shasum; do
  command -v "$command" >/dev/null || {
    echo "missing required command: $command" >&2
    exit 2
  }
done
for binary in solana solana-test-validator; do
  [[ -x "$AGAVE_BIN_DIR/$binary" ]] || {
    echo "missing executable: $AGAVE_BIN_DIR/$binary" >&2
    exit 2
  }
done
[[ -f "$BUNDLE_MANIFEST" ]] || {
  echo "missing bundle manifest: $BUNDLE_MANIFEST" >&2
  exit 2
}
jq -e '
  .schema == "aspis.v7.registry-v2-disposable-agave-txv1-bundle.v1" and
  .generatorSchema == "aspis.v7.registry-v2-deterministic-agave-bundle-generator.v1" and
  .programSourceCommit == "7179f7c550fe0461f4251dea5268af73876da91d" and
  .programSourceTree == "72d8ccd295994277bcb5f9df922c2a1483ac0443" and
  (.poolProgram | type == "string" and length > 0) and
  (.verifierProgram | type == "string" and length > 0) and
  (.registryProgram | type == "string" and length > 0) and
  (.poolSbf | type == "string" and length > 0) and
  (.poolSbfSha256 | test("^[0-9a-f]{64}$")) and
  (.poolSbfBytes | type == "number" and . > 0) and
  (.verifierSbf | type == "string" and length > 0) and
  (.verifierSbfSha256 | test("^[0-9a-f]{64}$")) and
  (.verifierSbfBytes | type == "number" and . > 0) and
  (.registrySbf | type == "string" and length > 0) and
  (.registrySbfSha256 | test("^[0-9a-f]{64}$")) and
  (.registrySbfBytes | type == "number" and . > 0) and
  (.resultDoubleSbf | type == "string" and length > 0) and
  (.resultDoubleSbfSha256 | test("^[0-9a-f]{64}$")) and
  (.resultDoubleSbfBytes | type == "number" and . > 0) and
  .sbfBindingComplete == true and .executionReady == true and
  .warpSlot == 150 and
  .computeUnitCeiling == 1300000 and
  .transactionByteCeilingExclusive == 4096 and
  .allNegativeCasesRequireRollback == true and
  .signed == false and .submitted == false and .deployed == false and
  (.cases | type == "array")
' "$BUNDLE_MANIFEST" >/dev/null || {
  echo "bundle manifest has the wrong or incomplete schema" >&2
  exit 2
}
if [[ -e "$EVIDENCE_DIR" ]]; then
  echo "refusing to overwrite evidence directory: $EVIDENCE_DIR" >&2
  exit 2
fi

readonly VERSION_OUTPUT=$(NO_DNA=1 "$AGAVE_BIN_DIR/solana" --version)
readonly CORE_VERSION=$(sed -E 's/.* ([0-9]+\.[0-9]+\.[^ ]+).*/\1/' <<<"$VERSION_OUTPUT")
readonly CORE_MAJOR=${CORE_VERSION%%.*}
readonly CORE_REST=${CORE_VERSION#*.}
readonly CORE_MINOR=${CORE_REST%%.*}
if (( CORE_MAJOR < 4 || (CORE_MAJOR == 4 && CORE_MINOR < 2) )); then
  echo "Agave 4.2+ required; found: $VERSION_OUTPUT" >&2
  exit 2
fi

validate_bundle_relative_path() {
  local path=$1
  if [[ -z "$path" || "$path" == /* || "$path" == ".." || "$path" == ../* || "$path" == */../* || "$path" == */.. ]]; then
    echo "bundle path must be nonempty, relative, and contain no parent traversal: $path" >&2
    return 1
  fi
}

for case_name in "${REQUIRED_CASES[@]}"; do
  jq -e --arg name "$case_name" '[.cases[] | select(.name == $name)] | length == 1' "$BUNDLE_MANIFEST" >/dev/null || {
    echo "bundle omits required case: $case_name" >&2
    exit 2
  }
done
jq -e --argjson expected "${#REQUIRED_CASES[@]}" '.cases | length == $expected' \
  "$BUNDLE_MANIFEST" >/dev/null || {
  echo "bundle must contain exactly the required case set" >&2
  exit 2
}

readonly POOL_PROGRAM=$(jq -er '.poolProgram' "$BUNDLE_MANIFEST")
readonly VERIFIER_PROGRAM=$(jq -er '.verifierProgram' "$BUNDLE_MANIFEST")
readonly REGISTRY_PROGRAM=$(jq -er '.registryProgram' "$BUNDLE_MANIFEST")
readonly POOL_SBF_RELATIVE=$(jq -er '.poolSbf' "$BUNDLE_MANIFEST")
readonly VERIFIER_SBF_RELATIVE=$(jq -er '.verifierSbf' "$BUNDLE_MANIFEST")
readonly REGISTRY_SBF_RELATIVE=$(jq -er '.registrySbf' "$BUNDLE_MANIFEST")
readonly RESULT_DOUBLE_SBF_RELATIVE=$(jq -er '.resultDoubleSbf' "$BUNDLE_MANIFEST")
validate_bundle_relative_path "$POOL_SBF_RELATIVE"
validate_bundle_relative_path "$VERIFIER_SBF_RELATIVE"
validate_bundle_relative_path "$REGISTRY_SBF_RELATIVE"
validate_bundle_relative_path "$RESULT_DOUBLE_SBF_RELATIVE"
readonly POOL_SBF="$BUNDLE_DIR/$POOL_SBF_RELATIVE"
readonly VERIFIER_SBF="$BUNDLE_DIR/$VERIFIER_SBF_RELATIVE"
readonly REGISTRY_SBF="$BUNDLE_DIR/$REGISTRY_SBF_RELATIVE"
readonly RESULT_DOUBLE_SBF="$BUNDLE_DIR/$RESULT_DOUBLE_SBF_RELATIVE"
readonly WARP_SLOT=$(jq -er '.warpSlot' "$BUNDLE_MANIFEST")
[[ -f "$POOL_SBF" && -f "$VERIFIER_SBF" && -f "$REGISTRY_SBF" && -f "$RESULT_DOUBLE_SBF" ]] || {
  echo "bundle is missing one or more SBF artifacts" >&2
  exit 2
}
[[ "$(wc -c <"$POOL_SBF" | tr -d ' ')" == "$(jq -er '.poolSbfBytes' "$BUNDLE_MANIFEST")" \
    && "$(shasum -a 256 "$POOL_SBF" | awk '{print $1}')" == "$(jq -er '.poolSbfSha256' "$BUNDLE_MANIFEST")" ]] \
  || { echo "Pool SBF differs from the bundle binding" >&2; exit 2; }
[[ "$(wc -c <"$VERIFIER_SBF" | tr -d ' ')" == "$(jq -er '.verifierSbfBytes' "$BUNDLE_MANIFEST")" \
    && "$(shasum -a 256 "$VERIFIER_SBF" | awk '{print $1}')" == "$(jq -er '.verifierSbfSha256' "$BUNDLE_MANIFEST")" ]] \
  || { echo "verifier SBF differs from the bundle binding" >&2; exit 2; }
[[ "$(wc -c <"$REGISTRY_SBF" | tr -d ' ')" == "$(jq -er '.registrySbfBytes' "$BUNDLE_MANIFEST")" \
    && "$(shasum -a 256 "$REGISTRY_SBF" | awk '{print $1}')" == "$(jq -er '.registrySbfSha256' "$BUNDLE_MANIFEST")" ]] \
  || { echo "Registry SBF differs from the bundle binding" >&2; exit 2; }
[[ "$(wc -c <"$RESULT_DOUBLE_SBF" | tr -d ' ')" == "$(jq -er '.resultDoubleSbfBytes' "$BUNDLE_MANIFEST")" \
    && "$(shasum -a 256 "$RESULT_DOUBLE_SBF" | awk '{print $1}')" == "$(jq -er '.resultDoubleSbfSha256' "$BUNDLE_MANIFEST")" ]] \
  || { echo "result-double SBF differs from the bundle binding" >&2; exit 2; }
[[ -x "$BUNDLE_VERIFY" ]] || {
  echo "offline bundle validator is unavailable: $BUNDLE_VERIFY" >&2
  exit 2
}
[[ -x "$SUITE_MATERIALIZE" ]] || {
  echo "Agave suite materializer is unavailable: $SUITE_MATERIALIZE" >&2
  exit 2
}
"$BUNDLE_VERIFY" "$BUNDLE_DIR" --materialized >/dev/null

mkdir -p "$EVIDENCE_DIR"
readonly WORK_DIR=$(mktemp -d "${TMPDIR:-/tmp}/aspis-v7-txv1-preflight.XXXXXX")
VALIDATOR_PID=""
cleanup() {
  if [[ -n "$VALIDATOR_PID" ]]; then
    kill "$VALIDATOR_PID" 2>/dev/null || true
    wait "$VALIDATOR_PID" 2>/dev/null || true
  fi
  case "$WORK_DIR" in
    */aspis-v7-txv1-preflight.*) rm -rf -- "$WORK_DIR" ;;
    *) echo "refusing to remove unexpected temporary path: $WORK_DIR" >&2 ;;
  esac
}
trap cleanup EXIT

rpc() {
  curl --fail-with-body --silent --show-error \
    --max-time 60 \
    -H 'content-type: application/json' \
    --data-binary "$1" \
    "$RPC_URL"
}

run_case() {
  local case_name=$1
  local case_json="$WORK_DIR/$case_name.case.json"
  local case_input case_input_relative
  local selected_verifier_relative selected_verifier_sha selected_verifier_sbf
  local validator_account_file override_loader
  local ledger="$WORK_DIR/$case_name-ledger"
  local validator_log="$EVIDENCE_DIR/$case_name.validator.log"
  local -a validator_args
  local slot blockhash account_addresses before_json preflight_json response_json after_json
  local expected_outcome units return_data_length rollback_equal state_unchanged
  local expected_file_relative expected_file expected_log
  local simulation_matches_expected simulation_runtime_metadata_valid
  local failed_snapshots_discarded

  rollback_equal=null
  simulation_runtime_metadata_valid=null
  failed_snapshots_discarded=null

  jq -e --arg name "$case_name" '.cases[] | select(.name == $name)' \
    "$BUNDLE_MANIFEST" >"$case_json"
  jq -e '
    (.input | type == "string" and length > 0) and
    (.inputSha256 | test("^[0-9a-f]{64}$")) and
    (.expectedOutcome == "success" or .expectedOutcome == "failure") and
    (.expectedLogContains | type == "array" and length > 0 and all(type == "string" and length > 0)) and
    (.genesisAccounts | type == "array" and length > 0 and all(
      (.address | type == "string" and length > 0) and
      (.file | type == "string" and length > 0) and
      (.fileSha256 | test("^[0-9a-f]{64}$"))
    )) and
    (.programOverrides | type == "array" and all(
      (.address | type == "string" and length > 0) and
      (.file | type == "string" and length > 0) and
      (.fileSha256 | test("^[0-9a-f]{64}$"))
    )) and
    (.rollbackRequired == (.expectedOutcome == "failure")) and
    (if .expectedOutcome == "success" then
      (.expectedSimulationAccountsSha256 | test("^[0-9a-f]{64}$")) and
      .rollbackRequired == false
    else .rollbackRequired == true end)
  ' "$case_json" >/dev/null || {
    echo "case manifest is incomplete or malformed: $case_name" >&2
    return 1
  }
  case_input_relative=$(jq -er '.input' "$case_json")
  validate_bundle_relative_path "$case_input_relative"
  case_input="$BUNDLE_DIR/$case_input_relative"
  expected_outcome=$(jq -er '.expectedOutcome' "$case_json")
  [[ -f "$case_input" ]] || {
    echo "missing case input for $case_name: $case_input" >&2
    return 1
  }
  [[ "$(shasum -a 256 "$case_input" | awk '{print $1}')" == "$(jq -er '.inputSha256' "$case_json")" ]] || {
    echo "case input hash differs for $case_name" >&2
    return 1
  }
  selected_verifier_relative=$(jq -er '.selectedVerifier.file' "$case_json")
  selected_verifier_sha=$(jq -er '.selectedVerifier.fileSha256' "$case_json")
  validate_bundle_relative_path "$selected_verifier_relative"
  selected_verifier_sbf="$BUNDLE_DIR/$selected_verifier_relative"
  [[ -f "$selected_verifier_sbf" \
      && "$(shasum -a 256 "$selected_verifier_sbf" | awk '{print $1}')" == "$selected_verifier_sha" ]] || {
    echo "selected verifier binding differs for $case_name" >&2
    return 1
  }

  validator_args=(
    --reset
    --quiet
    --ledger "$ledger"
    --bind-address 127.0.0.1
    --rpc-port "$RPC_PORT"
    --warp-slot "$WARP_SLOT"
    --bpf-program "$POOL_PROGRAM" "$POOL_SBF"
    --upgradeable-program "$REGISTRY_PROGRAM" "$REGISTRY_SBF" none
    --upgradeable-program "$VERIFIER_PROGRAM" "$selected_verifier_sbf" none
  )
  while IFS=$'\t' read -r address relative_path expected_sha; do
    validate_bundle_relative_path "$relative_path"
    [[ -f "$BUNDLE_DIR/$relative_path" ]] || {
      echo "missing genesis account for $case_name: $relative_path" >&2
      return 1
    }
    [[ "$(shasum -a 256 "$BUNDLE_DIR/$relative_path" | awk '{print $1}')" == "$expected_sha" ]] || {
      echo "genesis account hash differs for $case_name: $relative_path" >&2
      return 1
    }
    validator_account_file="$WORK_DIR/$case_name-genesis-$address.json"
    jq --arg pubkey "$address" '. as $account | {pubkey: $pubkey, account: $account}' \
      "$BUNDLE_DIR/$relative_path" >"$validator_account_file"
    jq -e --arg pubkey "$address" \
      '.pubkey == $pubkey and (.account | type == "object")' \
      "$validator_account_file" >/dev/null || {
      echo "temporary Agave account adapter lost its authenticated pubkey" >&2
      return 1
    }
    validator_args+=(--account "$address" "$validator_account_file")
  done < <(jq -r '.genesisAccounts[] | select(.loadAtGenesis) | [.address, .file, .fileSha256] | @tsv' "$case_json")
  while IFS=$'\t' read -r address relative_path expected_sha override_loader; do
    validate_bundle_relative_path "$relative_path"
    [[ -f "$BUNDLE_DIR/$relative_path" ]] || {
      echo "missing program override for $case_name: $relative_path" >&2
      return 1
    }
    [[ "$(shasum -a 256 "$BUNDLE_DIR/$relative_path" | awk '{print $1}')" == "$expected_sha" ]] || {
      echo "program override hash differs for $case_name: $relative_path" >&2
      return 1
    }
    case "$override_loader" in
      bpf) validator_args+=(--bpf-program "$address" "$BUNDLE_DIR/$relative_path") ;;
      upgradeable-none) validator_args+=(--upgradeable-program "$address" "$BUNDLE_DIR/$relative_path" none) ;;
      *) echo "unknown program override loader: $override_loader" >&2; return 1 ;;
    esac
  done < <(jq -r '.programOverrides[]? | [.address, .file, .fileSha256, .loader] | @tsv' "$case_json")

  NO_DNA=1 "$AGAVE_BIN_DIR/solana-test-validator" "${validator_args[@]}" \
    >"$validator_log" 2>&1 &
  VALIDATOR_PID=$!
  for _ in $(seq 1 100); do
    if rpc '{"jsonrpc":"2.0","id":1,"method":"getHealth"}' \
      | jq -e '.result == "ok"' >/dev/null 2>&1; then
      break
    fi
    sleep 0.2
  done
  rpc '{"jsonrpc":"2.0","id":1,"method":"getHealth"}' \
    | jq -e '.result == "ok"' >/dev/null

  rpc "{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"getAccountInfo\",\"params\":[\"$FEATURE_ID\",{\"encoding\":\"base64\",\"commitment\":\"finalized\"}]}" \
    | jq -e '.result.value != null and (.result.value.data[0] | startswith("AQ"))' >/dev/null || {
      echo "disposable validator did not activate TxV1 at genesis" >&2
      return 1
    }

  slot=$(rpc '{"jsonrpc":"2.0","id":3,"method":"getSlot","params":[{"commitment":"finalized"}]}' | jq -er '.result')
  blockhash=$(rpc "{\"jsonrpc\":\"2.0\",\"id\":4,\"method\":\"getLatestBlockhash\",\"params\":[{\"commitment\":\"finalized\",\"minContextSlot\":$slot}]}" | jq -er '.result.value.blockhash')
  jq --arg blockhash "$blockhash" --argjson slot "$slot" \
    '.recentBlockhash = $blockhash | .minContextSlot = $slot' \
    "$case_input" >"$WORK_DIR/$case_name.input.json"

  account_addresses=$(jq -c '.postStateAccounts // []' "$WORK_DIR/$case_name.input.json")
  jq -e 'length > 0' <<<"$account_addresses" >/dev/null || {
    echo "case must request protected post-state accounts: $case_name" >&2
    return 1
  }
  before_json=$(rpc "$(jq -nc --argjson addresses "$account_addresses" '{jsonrpc:"2.0",id:5,method:"getMultipleAccounts",params:[$addresses,{encoding:"base64",commitment:"finalized"}]}')")
  jq . <<<"$before_json" >"$EVIDENCE_DIR/$case_name.before.json"

  preflight_json=$(cd "$REPO_ROOT" && CARGO_BUILD_JOBS=1 CARGO_NET_OFFLINE=true NO_DNA=1 cargo run \
    --quiet --release --locked --offline \
    --manifest-path crates/aspis-pool-wallet-v1/Cargo.toml \
    --features eight-lane-plumbing-v2 \
    --example tx_v1_simulation_request -- \
    "$WORK_DIR/$case_name.input.json")
  jq . <<<"$preflight_json" >"$EVIDENCE_DIR/$case_name.preflight.json"
  jq -e '.summary.compute_unit_limit == 1300000 and .summary.serialized_transaction_bytes < 4096' \
    <<<"$preflight_json" >/dev/null || {
    echo "TxV1 preflight limits failed for $case_name" >&2
    return 1
  }
  response_json=$(rpc "$(jq -c '.simulationRequest' <<<"$preflight_json")")
  jq . <<<"$response_json" >"$EVIDENCE_DIR/$case_name.response.json"
  jq -e '.error | not' <<<"$response_json" >/dev/null || {
    echo "simulateTransaction RPC error for $case_name; see $case_name.response.json" >&2
    return 1
  }
  units=$(jq -er '.result.value.unitsConsumed' <<<"$response_json") || {
    echo "simulateTransaction omitted unitsConsumed for $case_name" >&2
    return 1
  }
  (( units <= 1300000 )) || {
    echo "simulation exceeded 1,300,000 CU for $case_name: $units" >&2
    return 1
  }
  while IFS= read -r expected_log; do
    jq -e --arg expected "$expected_log" \
      '.result.value.logs | any(contains($expected))' <<<"$response_json" >/dev/null || {
      echo "simulation omitted expected log for $case_name: $expected_log" >&2
      return 1
    }
  done < <(jq -r '.expectedLogContains[]' "$case_json")

  if [[ "$expected_outcome" == "success" ]]; then
    jq -e '.result.value.err == null' <<<"$response_json" >/dev/null || {
      echo "honest simulation failed for $case_name; see $case_name.response.json" >&2
      return 1
    }
    jq -e --arg pool "$POOL_PROGRAM" '.result.value.returnData.programId == $pool' \
      <<<"$response_json" >/dev/null
    return_data_length=$(jq -r '.result.value.returnData.data[0]' <<<"$response_json" \
      | openssl base64 -d -A | wc -c | tr -d ' ')
    [[ "$return_data_length" == "792" ]]
    expected_file_relative=$(jq -er '.expectedSimulationAccountsFile' "$case_json")
    validate_bundle_relative_path "$expected_file_relative"
    expected_file="$BUNDLE_DIR/$expected_file_relative"
    [[ -f "$expected_file" ]] || {
      echo "missing frozen expected account state for $case_name" >&2
      return 1
    }
    simulation_matches_expected=$(jq -n \
      --argjson actual "$(jq '.result.value.accounts' <<<"$response_json")" \
      --argjson expected "$(jq . "$expected_file")" '
      def program_state: map(if . == null then null else del(.rentEpoch) end);
      ($actual | program_state) == ($expected | program_state)')
    simulation_runtime_metadata_valid=$(jq -n \
      --argjson actual "$(jq '.result.value.accounts' <<<"$response_json")" '
      all($actual[]; . == null or .rentEpoch == 0 or .rentEpoch == 18446744073709551615)')
    [[ "$simulation_matches_expected" == "true" \
        && "$simulation_runtime_metadata_valid" == "true" ]] || {
      echo "honest simulated program state differs from the frozen expectation: $case_name" >&2
      return 1
    }
  elif [[ "$expected_outcome" == "failure" ]]; then
    jq -e '.result.value.err != null' <<<"$response_json" >/dev/null || {
      echo "negative simulation unexpectedly succeeded for $case_name" >&2
      return 1
    }
    failed_snapshots_discarded=$(jq -r \
      '.result.value.accounts | length > 0 and all(. == null)' <<<"$response_json")
    [[ "$failed_snapshots_discarded" == "true" ]] || {
      echo "failed simulation returned an unexpected partial account snapshot for $case_name" >&2
      return 1
    }
  else
    echo "invalid expectedOutcome for $case_name" >&2
    return 1
  fi

  after_json=$(rpc "$(jq -nc --argjson addresses "$account_addresses" '{jsonrpc:"2.0",id:6,method:"getMultipleAccounts",params:[$addresses,{encoding:"base64",commitment:"finalized"}]}')")
  state_unchanged=$(jq -n \
    --argjson before "$(jq '.result.value' <<<"$before_json")" \
    --argjson after "$(jq '.result.value' <<<"$after_json")" \
    '$before == $after')
  [[ "$state_unchanged" == "true" ]]

  jq -n \
    --arg case "$case_name" \
    --arg expected "$expected_outcome" \
    --arg version "$VERSION_OUTPUT" \
    --argjson preflight "$preflight_json" \
    --argjson response "$response_json" \
    --argjson before "$before_json" \
    --argjson after "$after_json" \
    --argjson rollback "$rollback_equal" \
    --argjson runtimeMetadataValid "$simulation_runtime_metadata_valid" \
    --argjson failedSnapshotsDiscarded "$failed_snapshots_discarded" \
    '{
      schema: "aspis.v7.disposable-agave-txv1-simulation-case.v1",
      case: $case,
      expectedOutcome: $expected,
      agave: $version,
      signed: false,
      submitted: false,
      simulationOnly: true,
      packetBytes: $preflight.summary.serialized_transaction_bytes,
      transactionHeadroomTo4096Bytes: $preflight.summary.headroom_to_4096_bytes,
      unitsConsumed: $response.result.value.unitsConsumed,
      protectedStateRollbackPreserved:
        (if $expected == "failure" then $rollback else null end),
      simulationRuntimeMetadataValid: $runtimeMetadataValid,
      failedSimulationReturnedNoAccountSnapshots:
        (if $expected == "failure" then $failedSnapshotsDiscarded else null end),
      negativeRollbackDirectlyObserved: (if $expected == "failure" then false else null end),
      negativeFailClosedSimulationObserved:
        (if $expected == "failure" then
          ($response.result.value.err != null and $failedSnapshotsDiscarded and
           ($before.result.value == $after.result.value))
         else null end),
      honestProgramStateMatchesFrozenExpected:
        (if $expected == "success" then true else null end),
      preflight: $preflight,
      response: $response,
      actualLedgerStateBefore: $before,
      actualLedgerStateAfter: $after,
      actualLedgerStateUnchanged: true
    }' >"$EVIDENCE_DIR/$case_name.case.json"

  kill "$VALIDATOR_PID"
  wait "$VALIDATOR_PID" || true
  VALIDATOR_PID=""
}

for case_name in "${REQUIRED_CASES[@]}"; do
  echo "simulate-only: $case_name"
  run_case "$case_name"
done

"$SUITE_MATERIALIZE" "$VERSION_OUTPUT" "$BUNDLE_DIR" "$EVIDENCE_DIR"
