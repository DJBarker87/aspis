#!/usr/bin/env bash
set -euo pipefail

fail() {
  echo "FAIL: $*" >&2
  exit 1
}

readonly ACK="I_ACKNOWLEDGE_256_DISPOSABLE_SEQUENTIAL_DEPOSITS"
[[ $# -eq 1 ]] || fail "usage: $0 <new-sequential-evidence-dir>"
readonly EVIDENCE_DIR=$1
readonly REPO_ROOT=$(cd "$(dirname "$0")/.." && pwd)
readonly CONFIG=${ASPIS_TXV1_HARNESS_CONFIG:-}
readonly RPC_URL=${ASPIS_TXV1_DISPOSABLE_RPC_URL:-}
readonly PAYER_KEYPAIR=${ASPIS_TXV1_DISPOSABLE_PAYER_KEYPAIR:-}
readonly SOURCE_AUTHORITY_KEYPAIR=${ASPIS_TXV1_DISPOSABLE_SOURCE_AUTHORITY_KEYPAIR:-}
readonly INITIALIZE_BUILDER=${ASPIS_V7_LIVE_POOL_INITIALIZE_BUILDER:-}
readonly SECRET_BUILDER=${ASPIS_V7_LIVE_OPERATION_SECRET_BUILDER:-}
readonly DEPOSIT_BUILDER=${ASPIS_V7_LIVE_POOL_DEPOSIT_BUILDER:-}
readonly BUILD_MANIFEST=${ASPIS_V7_DEPOSIT_AUDIT_BUILD_MANIFEST:-}

[[ "${ASPIS_V7_PAIR_FOREST_DEPOSIT_CU_AUDIT:-}" == "$ACK" ]] \
  || fail "missing exact sequential-deposit acknowledgement"
[[ "$RPC_URL" =~ ^http://127\.0\.0\.1:[0-9]+$ ]] || fail "disposable RPC is required"
[[ "$CONFIG" == /* && -f "$CONFIG" ]] || fail "absolute audit configuration is required"
[[ -f "$PAYER_KEYPAIR" && -f "$SOURCE_AUTHORITY_KEYPAIR" ]] \
  || fail "task-owned signing keys are unavailable"
[[ -x "$INITIALIZE_BUILDER" && -x "$SECRET_BUILDER" && -x "$DEPOSIT_BUILDER" ]] \
  || fail "prebuilt focused builders are required"
[[ "$BUILD_MANIFEST" == /* && -f "$BUILD_MANIFEST" ]] || fail "SBF build manifest is required"
[[ "$EVIDENCE_DIR" == /* && "$EVIDENCE_DIR" != / && ! -e "$EVIDENCE_DIR" ]] \
  || fail "evidence directory must be new, absolute and non-root"

mkdir -p "$EVIDENCE_DIR/measurements"
cp "$BUILD_MANIFEST" "$EVIDENCE_DIR/pool-audit-build.json"
readonly WORK_DIR=$(mktemp -d "${TMPDIR:-/tmp}/aspis-v7-deposit-cu.XXXXXX")
cleanup() {
  case "$WORK_DIR" in
    */aspis-v7-deposit-cu.*) rm -rf -- "$WORK_DIR" ;;
    *) echo "refusing unexpected cleanup path: $WORK_DIR" >&2 ;;
  esac
}
trap cleanup EXIT

rpc() {
  curl --fail-with-body --silent --show-error --max-time 60 \
    -H 'content-type: application/json' --data-binary "$1" "$RPC_URL"
}

rpc_account() {
  local address=$1 output=$2 request_id=$3
  rpc "$(jq -nc --arg address "$address" --argjson id "$request_id" \
    '{jsonrpc:"2.0",id:$id,method:"getAccountInfo",params:[$address,{encoding:"base64",commitment:"finalized"}]}')" \
    | jq --arg requestedAddress "$address" '. + {requestedAddress:$requestedAddress}' >"$output"
}

account_value_hash() {
  jq -cS '.result.value' "$1" | shasum -a 256 | awk '{print $1}'
}

token_amount() {
  local -a token_bytes
  mapfile -t token_bytes < <(jq -er '.result.value.data[0]' "$1" | openssl base64 -d -A \
    | od -An -v -tu1 | tr -s ' ' '\n' | sed '/^$/d')
  [[ ${#token_bytes[@]} -ge 72 ]] || fail "short SPL token account: $1"
  local amount=0 multiplier=1 index
  for index in $(seq 64 71); do
    amount=$((amount + token_bytes[index] * multiplier))
    multiplier=$((multiplier * 256))
  done
  printf '%s\n' "$amount"
}

finalized_transaction() {
  local signature=$1 output=$2 request_id=$3 status finalized=false
  for _ in $(seq 1 600); do
    status=$(rpc "$(jq -nc --arg signature "$signature" --argjson id "$request_id" \
      '{jsonrpc:"2.0",id:$id,method:"getSignatureStatuses",params:[[$signature],{searchTransactionHistory:true}]}')")
    if jq -e '.result.value[0] != null and .result.value[0].confirmationStatus == "finalized"' \
      <<<"$status" >/dev/null; then
      finalized=true
      break
    fi
    sleep 0.1
  done
  [[ "$finalized" == true ]] || fail "transaction did not finalize: $signature"
  rpc "$(jq -nc --arg signature "$signature" --argjson id "$((request_id + 1))" \
    '{jsonrpc:"2.0",id:$id,method:"getTransaction",params:[$signature,{encoding:"json",commitment:"finalized",maxSupportedTransactionVersion:1}]}')" \
    | jq . >"$output"
}

is_measurement_index() {
  case "$1" in
    0|1|2|3|7|15|255) return 0 ;;
    *) return 1 ;;
  esac
}

# Create one fresh eight-lane Pool through the real instruction.
slot=$(rpc '{"jsonrpc":"2.0","id":1,"method":"getSlot","params":[{"commitment":"finalized"}]}' | jq -er '.result')
blockhash=$(rpc "$(jq -nc --argjson slot "$slot" \
  '{jsonrpc:"2.0",id:2,method:"getLatestBlockhash",params:[{commitment:"finalized",minContextSlot:$slot}]}')" \
  | jq -er '.result.value.blockhash')
jq -n --arg config "$CONFIG" --arg payer "$PAYER_KEYPAIR" --arg hash "$blockhash" \
  --argjson slot "$slot" \
  '{schema:"aspis.v7.live-pool-initialize-input.v1",config:$config,payerKeypair:$payer,
    recentBlockhash:$hash,minContextSlot:$slot,requestId:100}' >"$WORK_DIR/initialize-input.json"
"$INITIALIZE_BUILDER" "$WORK_DIR/initialize-input.json" >"$EVIDENCE_DIR/initialize-signed-request.json"
jq -e '.operation == "initialize" and .serializedTransactionBytes < 1232 and
  (.initializedAccounts | length) == 10' "$EVIDENCE_DIR/initialize-signed-request.json" >/dev/null \
  || fail "initialize request is invalid"
initialize_sim=$(rpc "$(jq -c '.simulationRequest' "$EVIDENCE_DIR/initialize-signed-request.json")")
jq . <<<"$initialize_sim" >"$EVIDENCE_DIR/initialize-simulation.json"
jq -e '.result.value.err == null' <<<"$initialize_sim" >/dev/null || fail "initialize simulation failed"
initialize_send=$(rpc "$(jq -c '.sendRequest' "$EVIDENCE_DIR/initialize-signed-request.json")")
initialize_signature=$(jq -er '.result' <<<"$initialize_send")
[[ "$initialize_signature" == "$(jq -er '.signature' "$EVIDENCE_DIR/initialize-signed-request.json")" ]] \
  || fail "initialize signed wire changed"
finalized_transaction "$initialize_signature" "$EVIDENCE_DIR/initialize-finalized-transaction.json" 110
jq -e '.result.meta.err == null' "$EVIDENCE_DIR/initialize-finalized-transaction.json" >/dev/null \
  || fail "initialize landed with an error"

account_index=0
while IFS= read -r address; do
  rpc_account "$address" "$WORK_DIR/account-$account_index.json" "$((200 + account_index))"
  jq -e '.result.value != null' "$WORK_DIR/account-$account_index.json" >/dev/null \
    || fail "initialized account missing: $address"
  account_index=$((account_index + 1))
done < <(jq -r '.initializedAccounts[]' "$EVIDENCE_DIR/initialize-signed-request.json")

readonly MASTER_FILE="$WORK_DIR/account-0.json"
readonly VAULT_ADDRESS=$(jq -er '.requestedAddress' "$WORK_DIR/account-9.json")
readonly SOURCE_ADDRESS=$(jq -er '.disposableLiveGenesis.sourceTokenAccount' "$CONFIG")
declare -a lane_addresses lane_initial_hashes
for lane_id in $(seq 0 7); do
  lane_addresses[$lane_id]=$(jq -er '.requestedAddress' "$WORK_DIR/account-$((lane_id + 1)).json")
  lane_initial_hashes[$lane_id]=$(account_value_hash "$WORK_DIR/account-$((lane_id + 1)).json")
done
rpc_account "$SOURCE_ADDRESS" "$WORK_DIR/source-initial.json" 220
rpc_account "$VAULT_ADDRESS" "$WORK_DIR/vault-initial.json" 221
readonly SOURCE_INITIAL_AMOUNT=$(token_amount "$WORK_DIR/source-initial.json")
readonly VAULT_INITIAL_AMOUNT=$(token_amount "$WORK_DIR/vault-initial.json")
[[ "$SOURCE_INITIAL_AMOUNT" -eq 256000 ]] || fail "sequential source amount must be exactly 256000"

readonly ROWS="$EVIDENCE_DIR/sequential-deposits.jsonl"
: >"$ROWS"
for source_index in $(seq 0 255); do
  secret="$WORK_DIR/deposit-$source_index-secret.json"
  public="$WORK_DIR/deposit-$source_index-public.json"
  "$SECRET_BUILDER" transfer "$secret" 0 >"$public"
  [[ "$(stat -c %a "$secret")" == 600 ]] || fail "secret mode is not 0600"
  jq -e '.depositLane == 0 and .secretValuesPrinted == false' "$public" >/dev/null \
    || fail "deposit did not route to lane zero"

  slot=$(rpc "$(jq -nc --argjson id "$((3000 + source_index))" \
    '{jsonrpc:"2.0",id:$id,method:"getSlot",params:[{commitment:"finalized"}]}')" | jq -er '.result')
  blockhash=$(rpc "$(jq -nc --argjson id "$((4000 + source_index))" --argjson slot "$slot" \
    '{jsonrpc:"2.0",id:$id,method:"getLatestBlockhash",params:[{commitment:"finalized",minContextSlot:$slot}]}')" \
    | jq -er '.result.value.blockhash')
  lane_files=$(printf '%s\n' "$WORK_DIR"/account-{1,2,3,4,5,6,7,8}.json | jq -R . | jq -s .)
  jq -n --arg config "$CONFIG" --arg payer "$PAYER_KEYPAIR" \
    --arg sourceAuthority "$SOURCE_AUTHORITY_KEYPAIR" --arg hash "$blockhash" \
    --argjson slot "$slot" --arg master "$MASTER_FILE" --argjson lanes "$lane_files" \
    --arg secrets "$secret" --argjson sourceIndex "$source_index" \
    '{schema:"aspis.v7.live-pool-sequential-deposit-input.v1",config:$config,payerKeypair:$payer,
      sourceAuthorityKeypair:$sourceAuthority,recentBlockhash:$hash,minContextSlot:$slot,
      requestId:(10000+$sourceIndex),masterAccount:$master,laneAccounts:$lanes,
      secretsFile:$secrets,expectedNextLeafIndex:$sourceIndex}' >"$WORK_DIR/deposit-input.json"
  "$DEPOSIT_BUILDER" "$WORK_DIR/deposit-input.json" >"$WORK_DIR/signed-request.json"
  rm -f -- "$secret"

  expected_mode=same-page
  [[ "$source_index" -eq 0 ]] && expected_mode=genesis
  [[ "$source_index" -eq 255 ]] && expected_mode=rollover
  jq -e --argjson sourceIndex "$source_index" --arg mode "$expected_mode" '
    .operation == "deposit" and .selectedLane == 0 and .sourceNextLeafIndex == $sourceIndex and
    .successorNextLeafIndex == ($sourceIndex + 1) and .pageMode == $mode and
    .serializedTransactionBytes < 1232 and (.signedWireSha256 | test("^[0-9a-f]{64}$"))' \
    "$WORK_DIR/signed-request.json" >/dev/null || fail "invalid deposit request at index $source_index"

  lane_address=$(jq -er '.laneAccount' "$WORK_DIR/signed-request.json")
  current_page_address=$(jq -er '.currentPageAccount' "$WORK_DIR/signed-request.json")
  successor_page_address=$(jq -er '.successorPageAccount' "$WORK_DIR/signed-request.json")
  rpc_account "$lane_address" "$WORK_DIR/lane-before.json" "$((20000 + source_index))"
  rpc_account "$current_page_address" "$WORK_DIR/current-page-before.json" "$((21000 + source_index))"
  rpc_account "$successor_page_address" "$WORK_DIR/successor-page-before.json" "$((22000 + source_index))"
  rpc_account "$SOURCE_ADDRESS" "$WORK_DIR/source-before.json" "$((23000 + source_index))"
  rpc_account "$VAULT_ADDRESS" "$WORK_DIR/vault-before.json" "$((24000 + source_index))"

  simulation=$(rpc "$(jq -c '.simulationRequest' "$WORK_DIR/signed-request.json")")
  jq -e '.result.value.err == null and .result.value.unitsConsumed < 1400000' <<<"$simulation" >/dev/null \
    || fail "deposit simulation failed or hit the ceiling at index $source_index"
  send=$(rpc "$(jq -c '.sendRequest' "$WORK_DIR/signed-request.json")")
  signature=$(jq -er '.result' <<<"$send")
  [[ "$signature" == "$(jq -er '.signature' "$WORK_DIR/signed-request.json")" ]] \
    || fail "submitted deposit wire changed at index $source_index"
  finalized_transaction "$signature" "$WORK_DIR/finalized-transaction.json" "$((25000 + 2 * source_index))"
  jq -e '.result.meta.err == null' "$WORK_DIR/finalized-transaction.json" >/dev/null \
    || fail "deposit landed with error at index $source_index"

  rpc_account "$lane_address" "$WORK_DIR/account-1.json" "$((26000 + source_index))"
  rpc_account "$current_page_address" "$WORK_DIR/current-page-after.json" "$((27000 + source_index))"
  rpc_account "$successor_page_address" "$WORK_DIR/successor-page-after.json" "$((28000 + source_index))"
  rpc_account "$SOURCE_ADDRESS" "$WORK_DIR/source-after.json" "$((29000 + source_index))"
  rpc_account "$VAULT_ADDRESS" "$WORK_DIR/vault-after.json" "$((30000 + source_index))"

  simulated_cu=$(jq -er '.result.value.unitsConsumed' <<<"$simulation")
  landed_cu=$(jq -er '.result.meta.computeUnitsConsumed' "$WORK_DIR/finalized-transaction.json")
  [[ "$simulated_cu" -eq "$landed_cu" ]] || fail "simulation/landed CU mismatch at $source_index"
  source_before=$(token_amount "$WORK_DIR/source-before.json")
  source_after=$(token_amount "$WORK_DIR/source-after.json")
  vault_before=$(token_amount "$WORK_DIR/vault-before.json")
  vault_after=$(token_amount "$WORK_DIR/vault-after.json")
  ((source_before - source_after == 1000 && vault_after - vault_before == 1000)) \
    || fail "custody delta mismatch at index $source_index"

  jq -nc --argjson sourceIndex "$source_index" --arg mode "$expected_mode" \
    --argjson bytes "$(jq -er '.serializedTransactionBytes' "$WORK_DIR/signed-request.json")" \
    --arg wireHash "$(jq -er '.signedWireSha256' "$WORK_DIR/signed-request.json")" \
    --arg signature "$signature" --argjson slot "$(jq -er '.result.slot' "$WORK_DIR/finalized-transaction.json")" \
    --argjson simulatedCu "$simulated_cu" --argjson landedCu "$landed_cu" \
    --arg laneBefore "$(account_value_hash "$WORK_DIR/lane-before.json")" \
    --arg laneAfter "$(account_value_hash "$WORK_DIR/account-1.json")" \
    --arg currentPageBefore "$(account_value_hash "$WORK_DIR/current-page-before.json")" \
    --arg currentPageAfter "$(account_value_hash "$WORK_DIR/current-page-after.json")" \
    --arg successorPageBefore "$(account_value_hash "$WORK_DIR/successor-page-before.json")" \
    --arg successorPageAfter "$(account_value_hash "$WORK_DIR/successor-page-after.json")" \
    --arg sourceBeforeHash "$(account_value_hash "$WORK_DIR/source-before.json")" \
    --arg sourceAfterHash "$(account_value_hash "$WORK_DIR/source-after.json")" \
    --arg vaultBeforeHash "$(account_value_hash "$WORK_DIR/vault-before.json")" \
    --arg vaultAfterHash "$(account_value_hash "$WORK_DIR/vault-after.json")" \
    --argjson sourceBefore "$source_before" --argjson sourceAfter "$source_after" \
    --argjson vaultBefore "$vault_before" --argjson vaultAfter "$vault_after" \
    '{sourceIndex:$sourceIndex,successorIndex:($sourceIndex+1),pageMode:$mode,
      serializedTransactionBytes:$bytes,signedWireSha256:$wireHash,simulationSubmissionByteIdentical:true,
      signature:$signature,finalizedSlot:$slot,simulatedCu:$simulatedCu,landedCu:$landedCu,
      accountHashes:{lane:{before:$laneBefore,after:$laneAfter},
        currentPage:{before:$currentPageBefore,after:$currentPageAfter},
        successorPage:{before:$successorPageBefore,after:$successorPageAfter},
        source:{before:$sourceBeforeHash,after:$sourceAfterHash},vault:{before:$vaultBeforeHash,after:$vaultAfterHash}},
      custody:{sourceBefore:$sourceBefore,sourceAfter:$sourceAfter,vaultBefore:$vaultBefore,vaultAfter:$vaultAfter},
      finalized:true,pass:true}' >>"$ROWS"

  if is_measurement_index "$source_index"; then
    measurement="$EVIDENCE_DIR/measurements/index-$(printf '%03d' "$source_index")"
    mkdir "$measurement"
    cp "$WORK_DIR/signed-request.json" "$measurement/signed-request.json"
    jq . <<<"$simulation" >"$measurement/simulation.json"
    cp "$WORK_DIR/finalized-transaction.json" "$measurement/finalized-transaction.json"
    for snapshot in lane-before account-1 current-page-before current-page-after \
      successor-page-before successor-page-after source-before source-after vault-before vault-after; do
      cp "$WORK_DIR/$snapshot.json" "$measurement/$snapshot.json"
    done
  fi
done

rpc_account "$SOURCE_ADDRESS" "$EVIDENCE_DIR/source-final.json" 40001
rpc_account "$VAULT_ADDRESS" "$EVIDENCE_DIR/vault-final.json" 40002
readonly SOURCE_FINAL_AMOUNT=$(token_amount "$EVIDENCE_DIR/source-final.json")
readonly VAULT_FINAL_AMOUNT=$(token_amount "$EVIDENCE_DIR/vault-final.json")
((SOURCE_FINAL_AMOUNT == 0 && VAULT_FINAL_AMOUNT - VAULT_INITIAL_AMOUNT == 256000)) \
  || fail "final aggregate custody conservation failed"

nonselected_unchanged=true
for lane_id in $(seq 1 7); do
  rpc_account "${lane_addresses[$lane_id]}" "$WORK_DIR/lane-$lane_id-final.json" "$((41000 + lane_id))"
  [[ "$(account_value_hash "$WORK_DIR/lane-$lane_id-final.json")" == "${lane_initial_hashes[$lane_id]}" ]] \
    || nonselected_unchanged=false
done
[[ "$nonselected_unchanged" == true ]] || fail "a non-selected lane changed"

jq -s --arg revision "$(git -C "$REPO_ROOT" rev-parse HEAD)" \
  --arg initializeSignature "$initialize_signature" \
  --argjson initializeSlot "$(jq -er '.result.slot' "$EVIDENCE_DIR/initialize-finalized-transaction.json")" \
  --argjson sourceInitial "$SOURCE_INITIAL_AMOUNT" --argjson sourceFinal "$SOURCE_FINAL_AMOUNT" \
  --argjson vaultInitial "$VAULT_INITIAL_AMOUNT" --argjson vaultFinal "$VAULT_FINAL_AMOUNT" '
  {schema:"aspis.v7.pair-forest-sequential-deposit-cu-audit.v1",repositoryRevision:$revision,
    classification:"DISPOSABLE FEATURE-ACTIVE DEPOSIT AUDIT",auditOnly:true,mainnetReady:false,
    feature:"pair-forest-deposit-invariant-audit",poolInitialized:{signature:$initializeSignature,slot:$initializeSlot},
    sequentialDeposits:length,allFinalized:(all(.[]; .finalized)),allPassed:(all(.[]; .pass)),
    simulationLandedCuExact:(all(.[]; .simulatedCu == .landedCu)),
    measuredSourceIndices:[0,1,2,3,7,15,255],
    measurements:[.[] | select(.sourceIndex == 0 or .sourceIndex == 1 or .sourceIndex == 2 or
      .sourceIndex == 3 or .sourceIndex == 7 or .sourceIndex == 15 or .sourceIndex == 255)],
    maximumLandedCu:(map(.landedCu)|max),maximumSerializedBytes:(map(.serializedTransactionBytes)|max),
    custody:{sourceInitial:$sourceInitial,sourceFinal:$sourceFinal,vaultInitial:$vaultInitial,
      vaultFinal:$vaultFinal,conserved:(($sourceInitial-$sourceFinal)==($vaultFinal-$vaultInitial))},
    selectedLane:0,nonSelectedLanesUnchanged:true,pageRolloverFinalized:(any(.[]; .pageMode == "rollover")),
    publicTestnetExecution:false,publicDevnetExecution:false,publicMainnetExecution:false}' \
  "$ROWS" >"$EVIDENCE_DIR/evidence.json"

jq -e '.sequentialDeposits == 256 and .allFinalized and .allPassed and
  .simulationLandedCuExact and .custody.conserved and .nonSelectedLanesUnchanged and
  .pageRolloverFinalized and (.measurements | length) == 7' "$EVIDENCE_DIR/evidence.json" >/dev/null \
  || fail "final sequential-deposit evidence invariant failed"

echo "SEQUENTIAL DEPOSIT CU AUDIT COMPLETE: $EVIDENCE_DIR/evidence.json"
