#!/usr/bin/env bash
set -euo pipefail

fail() {
  echo "FAIL: $*" >&2
  exit 1
}

[[ $# -eq 1 ]] || fail "usage: $0 <new-evidence-dir>"
readonly EVIDENCE_DIR=$1
readonly REPO_ROOT=$(cd "$(dirname "$0")/.." && pwd)
readonly CONFIG="$REPO_ROOT/config/v7-txv1-devnet-harness-20260901.json"
readonly RPC_URL=${ASPIS_TXV1_DISPOSABLE_RPC_URL:-}
readonly PAYER_KEYPAIR=${ASPIS_TXV1_DISPOSABLE_PAYER_KEYPAIR:-}
readonly SOURCE_AUTHORITY_KEYPAIR=${ASPIS_TXV1_DISPOSABLE_SOURCE_AUTHORITY_KEYPAIR:-}
readonly BUILDER=${ASPIS_V7_LIVE_POOL_INITIALIZE_BUILDER:-}
readonly SECRET_BUILDER=${ASPIS_V7_LIVE_OPERATION_SECRET_BUILDER:-}
readonly DEPOSIT_BUILDER=${ASPIS_V7_LIVE_POOL_DEPOSIT_BUILDER:-}

[[ "$RPC_URL" =~ ^http://127\.0\.0\.1:[0-9]+$ ]] || fail "disposable RPC is required"
[[ -f "$PAYER_KEYPAIR" && -x "$BUILDER" ]] || fail "ephemeral payer or prebuilt builder unavailable"
[[ "$EVIDENCE_DIR" == /* && "$EVIDENCE_DIR" != / && ! -e "$EVIDENCE_DIR" ]] \
  || fail "evidence directory must be new, absolute and non-root"
mkdir -p "$EVIDENCE_DIR"
readonly WORK_DIR=$(mktemp -d "${TMPDIR:-/tmp}/aspis-v7-live-init.XXXXXX")
cleanup() {
  case "$WORK_DIR" in
    */aspis-v7-live-init.*) rm -rf -- "$WORK_DIR" ;;
    *) echo "refusing unexpected cleanup path: $WORK_DIR" >&2 ;;
  esac
}
trap cleanup EXIT

rpc() {
  curl --fail-with-body --silent --show-error --max-time 60 \
    -H 'content-type: application/json' --data-binary "$1" "$RPC_URL"
}

account_data_hash() {
  jq -er '.result.value.data[0]' "$1" | openssl base64 -d -A | shasum -a 256 | awk '{print $1}'
}

slot=$(rpc '{"jsonrpc":"2.0","id":1,"method":"getSlot","params":[{"commitment":"finalized"}]}' | jq -er '.result')
blockhash=$(rpc "$(jq -nc --argjson slot "$slot" \
  '{jsonrpc:"2.0",id:2,method:"getLatestBlockhash",params:[{commitment:"finalized",minContextSlot:$slot}]}')" \
  | jq -er '.result.value.blockhash')
jq -n --arg config "$CONFIG" --arg payer "$PAYER_KEYPAIR" --arg hash "$blockhash" \
  --argjson slot "$slot" \
  '{schema:"aspis.v7.live-pool-initialize-input.v1",config:$config,payerKeypair:$payer,
    recentBlockhash:$hash,minContextSlot:$slot,requestId:100}' >"$WORK_DIR/input.json"
"$BUILDER" "$WORK_DIR/input.json" >"$EVIDENCE_DIR/signed-request.json"
jq -e '.schema == "aspis.v7.live-pool-signed-request.v1" and
  .operation == "initialize" and .serializedTransactionBytes < 1232 and
  (.signedWireSha256 | test("^[0-9a-f]{64}$")) and
  (.initializedAccounts | length) == 10' "$EVIDENCE_DIR/signed-request.json" >/dev/null \
  || fail "signed initialize request failed validation"

simulation=$(rpc "$(jq -c '.simulationRequest' "$EVIDENCE_DIR/signed-request.json")")
jq . <<<"$simulation" >"$EVIDENCE_DIR/simulation.json"
jq -e '.error | not' <<<"$simulation" >/dev/null
jq -e '.result.value.err == null' <<<"$simulation" >/dev/null || fail "initialize simulation failed"
send=$(rpc "$(jq -c '.sendRequest' "$EVIDENCE_DIR/signed-request.json")")
jq . <<<"$send" >"$EVIDENCE_DIR/send.json"
signature=$(jq -er '.result' <<<"$send")
[[ "$signature" == "$(jq -er '.signature' "$EVIDENCE_DIR/signed-request.json")" ]] \
  || fail "submitted transaction was not byte-identical"

finalized=false
for _ in $(seq 1 600); do
  status=$(rpc "$(jq -nc --arg signature "$signature" \
    '{jsonrpc:"2.0",id:300,method:"getSignatureStatuses",params:[[$signature],{searchTransactionHistory:true}]}')")
  if jq -e '.result.value[0] != null and .result.value[0].confirmationStatus == "finalized"' \
    <<<"$status" >/dev/null; then
    finalized=true
    break
  fi
  sleep 0.1
done
[[ "$finalized" == true ]] || fail "initialize did not finalize"
rpc "$(jq -nc --arg signature "$signature" \
  '{jsonrpc:"2.0",id:400,method:"getTransaction",params:[$signature,{encoding:"json",commitment:"finalized",maxSupportedTransactionVersion:1}]}')" \
  | jq . >"$EVIDENCE_DIR/finalized-transaction.json"
jq -e '.result != null and .result.meta.err == null' "$EVIDENCE_DIR/finalized-transaction.json" >/dev/null \
  || fail "finalized initialize failed"

account_index=0
while IFS= read -r address; do
  rpc "$(jq -nc --arg address "$address" \
    '{jsonrpc:"2.0",id:500,method:"getAccountInfo",params:[$address,{encoding:"base64",commitment:"finalized"}]}')" \
    | jq . >"$EVIDENCE_DIR/account-$account_index.json"
  jq -e '.result.value != null' "$EVIDENCE_DIR/account-$account_index.json" >/dev/null \
    || fail "initialized account missing: $address"
  account_index=$((account_index + 1))
done < <(jq -r '.initializedAccounts[]' "$EVIDENCE_DIR/signed-request.json")

if [[ -n "$SECRET_BUILDER" || -n "$DEPOSIT_BUILDER" ]]; then
  [[ -x "$SECRET_BUILDER" && -x "$DEPOSIT_BUILDER" ]] \
    || fail "both secret and deposit builders are required"
  mkdir "$EVIDENCE_DIR/deposit"
  "$SECRET_BUILDER" transfer "$WORK_DIR/operation-secrets.json" \
    >"$EVIDENCE_DIR/deposit/public-operation.json"
  [[ "$(stat -c %a "$WORK_DIR/operation-secrets.json")" == 600 ]] \
    || fail "operation secret file mode is not 0600"
  selected_lane=$(jq -er '.depositLane' "$EVIDENCE_DIR/deposit/public-operation.json")
  source_token=$(jq -er '.disposableLiveGenesis.sourceTokenAccount' "$CONFIG")
  rpc "$(jq -nc --arg address "$source_token" \
    '{jsonrpc:"2.0",id:600,method:"getAccountInfo",params:[$address,{encoding:"base64",commitment:"finalized"}]}')" \
    | jq . >"$EVIDENCE_DIR/deposit/source-before.json"
  cp "$EVIDENCE_DIR/account-$((selected_lane + 1)).json" "$EVIDENCE_DIR/deposit/lane-before.json"
  cp "$EVIDENCE_DIR/account-9.json" "$EVIDENCE_DIR/deposit/vault-before.json"
  slot_deposit=$(rpc '{"jsonrpc":"2.0","id":601,"method":"getSlot","params":[{"commitment":"finalized"}]}' | jq -er '.result')
  blockhash_deposit=$(rpc "$(jq -nc --argjson slot "$slot_deposit" \
    '{jsonrpc:"2.0",id:602,method:"getLatestBlockhash",params:[{commitment:"finalized",minContextSlot:$slot}]}')" \
    | jq -er '.result.value.blockhash')
  lane_files=$(for lane_index in $(seq 1 8); do printf '%s\n' "$EVIDENCE_DIR/account-$lane_index.json"; done | jq -Rsc 'split("\n")[:-1]')
  [[ -f "$SOURCE_AUTHORITY_KEYPAIR" ]] || fail "ephemeral source authority unavailable"
  jq -n --arg config "$CONFIG" --arg payer "$PAYER_KEYPAIR" \
    --arg sourceAuthority "$SOURCE_AUTHORITY_KEYPAIR" --arg hash "$blockhash_deposit" \
    --argjson slot "$slot_deposit" --arg master "$EVIDENCE_DIR/account-0.json" \
    --argjson lanes "$lane_files" --arg secrets "$WORK_DIR/operation-secrets.json" \
    '{schema:"aspis.v7.live-pool-deposit-input.v1",config:$config,payerKeypair:$payer,
      sourceAuthorityKeypair:$sourceAuthority,
      recentBlockhash:$hash,minContextSlot:$slot,requestId:700,masterAccount:$master,
      laneAccounts:$lanes,secretsFile:$secrets}' >"$WORK_DIR/deposit-input.json"
  "$DEPOSIT_BUILDER" "$WORK_DIR/deposit-input.json" >"$EVIDENCE_DIR/deposit/signed-request.json"
  jq -e --argjson lane "$selected_lane" '.operation == "deposit" and .selectedLane == $lane and
    .serializedTransactionBytes < 1232 and (.signedWireSha256 | test("^[0-9a-f]{64}$"))' \
    "$EVIDENCE_DIR/deposit/signed-request.json" >/dev/null || fail "deposit signed request invalid"
  deposit_simulation=$(rpc "$(jq -c '.simulationRequest' "$EVIDENCE_DIR/deposit/signed-request.json")")
  jq . <<<"$deposit_simulation" >"$EVIDENCE_DIR/deposit/simulation.json"
  jq -e '.error | not' <<<"$deposit_simulation" >/dev/null
  jq -e '.result.value.err == null' <<<"$deposit_simulation" >/dev/null || fail "deposit simulation failed"
  deposit_send=$(rpc "$(jq -c '.sendRequest' "$EVIDENCE_DIR/deposit/signed-request.json")")
  jq . <<<"$deposit_send" >"$EVIDENCE_DIR/deposit/send.json"
  deposit_signature=$(jq -er '.result' <<<"$deposit_send")
  [[ "$deposit_signature" == "$(jq -er '.signature' "$EVIDENCE_DIR/deposit/signed-request.json")" ]] \
    || fail "deposit submission changed signed wire"
  deposit_finalized=false
  for _ in $(seq 1 600); do
    deposit_status=$(rpc "$(jq -nc --arg signature "$deposit_signature" \
      '{jsonrpc:"2.0",id:800,method:"getSignatureStatuses",params:[[$signature],{searchTransactionHistory:true}]}')")
    if jq -e '.result.value[0] != null and .result.value[0].confirmationStatus == "finalized"' \
      <<<"$deposit_status" >/dev/null; then deposit_finalized=true; break; fi
    sleep 0.1
  done
  [[ "$deposit_finalized" == true ]] || fail "deposit did not finalize"
  rpc "$(jq -nc --arg signature "$deposit_signature" \
    '{jsonrpc:"2.0",id:900,method:"getTransaction",params:[$signature,{encoding:"json",commitment:"finalized",maxSupportedTransactionVersion:1}]}')" \
    | jq . >"$EVIDENCE_DIR/deposit/finalized-transaction.json"
  jq -e '.result != null and .result.meta.err == null' "$EVIDENCE_DIR/deposit/finalized-transaction.json" >/dev/null \
    || fail "finalized deposit failed"
  for item in "lane:$((selected_lane + 1))" "vault:9"; do
    name=${item%%:*}; initialized_index=${item##*:}; address=$(jq -er ".initializedAccounts[$initialized_index]" "$EVIDENCE_DIR/signed-request.json")
    rpc "$(jq -nc --arg address "$address" \
      '{jsonrpc:"2.0",id:901,method:"getAccountInfo",params:[$address,{encoding:"base64",commitment:"finalized"}]}')" \
      | jq . >"$EVIDENCE_DIR/deposit/$name-after.json"
  done
  rpc "$(jq -nc --arg address "$source_token" \
    '{jsonrpc:"2.0",id:902,method:"getAccountInfo",params:[$address,{encoding:"base64",commitment:"finalized"}]}')" \
    | jq . >"$EVIDENCE_DIR/deposit/source-after.json"
  deposit_simulated_cu=$(jq -er '.result.value.unitsConsumed' "$EVIDENCE_DIR/deposit/simulation.json")
  deposit_landed_cu=$(jq -er '.result.meta.computeUnitsConsumed' "$EVIDENCE_DIR/deposit/finalized-transaction.json")
  deposit_slot=$(jq -er '.result.slot' "$EVIDENCE_DIR/deposit/finalized-transaction.json")
  lane_before_hash=$(account_data_hash "$EVIDENCE_DIR/deposit/lane-before.json")
  lane_after_hash=$(account_data_hash "$EVIDENCE_DIR/deposit/lane-after.json")
  vault_before_hash=$(account_data_hash "$EVIDENCE_DIR/deposit/vault-before.json")
  vault_after_hash=$(account_data_hash "$EVIDENCE_DIR/deposit/vault-after.json")
  source_before_hash=$(account_data_hash "$EVIDENCE_DIR/deposit/source-before.json")
  source_after_hash=$(account_data_hash "$EVIDENCE_DIR/deposit/source-after.json")
  jq -n --arg signature "$deposit_signature" --argjson slot "$deposit_slot" \
    --argjson lane "$selected_lane" --argjson simulatedCu "$deposit_simulated_cu" \
    --argjson landedCu "$deposit_landed_cu" --arg laneBefore "$lane_before_hash" \
    --arg laneAfter "$lane_after_hash" --arg vaultBefore "$vault_before_hash" \
    --arg vaultAfter "$vault_after_hash" --arg sourceBefore "$source_before_hash" \
    --arg sourceAfter "$source_after_hash" --slurpfile request "$EVIDENCE_DIR/deposit/signed-request.json" \
    '{schema:"aspis.v7.live-pool-deposit-finalized.v1",signature:$signature,slot:$slot,
      selectedLane:$lane,simulatedCu:$simulatedCu,landedCu:$landedCu,
      serializedTransactionBytes:$request[0].serializedTransactionBytes,
      signedWireSha256:$request[0].signedWireSha256,byteIdenticalSimulationSubmission:true,
      accountDataSha256:{lane:{before:$laneBefore,after:$laneAfter},
        vault:{before:$vaultBefore,after:$vaultAfter},source:{before:$sourceBefore,after:$sourceAfter}},
      secretValuesRecorded:false,secretDestroyedByCleanup:true,finalized:true,auditOnly:true,
      disposable:true,mainnetReady:false}' >"$EVIDENCE_DIR/deposit/deposit-finalized.json"
fi

simulated_cu=$(jq -er '.result.value.unitsConsumed' "$EVIDENCE_DIR/simulation.json")
landed_cu=$(jq -er '.result.meta.computeUnitsConsumed' "$EVIDENCE_DIR/finalized-transaction.json")
slot_landed=$(jq -er '.result.slot' "$EVIDENCE_DIR/finalized-transaction.json")
jq -n --arg signature "$signature" --argjson slot "$slot_landed" \
  --argjson simulatedCu "$simulated_cu" --argjson landedCu "$landed_cu" \
  --slurpfile request "$EVIDENCE_DIR/signed-request.json" \
  '{schema:"aspis.v7.live-pool-initialize-finalized.v1",operation:"initialize",
    signature:$signature,slot:$slot,simulatedCu:$simulatedCu,landedCu:$landedCu,
    byteIdenticalSimulationSubmission:true,serializedTransactionBytes:$request[0].serializedTransactionBytes,
    signedWireSha256:$request[0].signedWireSha256,initializedAccounts:$request[0].initializedAccounts,
    finalized:true,auditOnly:true,disposable:true,mainnetReady:false}' \
  >"$EVIDENCE_DIR/initialize-finalized.json"
echo "FINALIZED DISPOSABLE LIVE POOL INITIALIZE: $signature"
