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
readonly BUILDER=${ASPIS_V7_LIVE_POOL_INITIALIZE_BUILDER:-}

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
