#!/usr/bin/env bash
set -euo pipefail

# Child command for v7_txv1_disposable_feature_cluster.sh. It uploads one
# caller-mined ASJA+Tag-73 payload through the ordinary ASPU lifecycle and
# records exact signed-wire simulation/submission/finalization evidence.

fail() {
  echo "FAIL: $*" >&2
  exit 1
}

if [[ $# -ne 3 ]]; then
  echo "usage: $0 <task-proof-keypair> <proof-payload.bin> <new-evidence-dir>" >&2
  exit 2
fi

readonly PROOF_KEYPAIR=$1
readonly PROOF_PAYLOAD=$2
readonly EVIDENCE_DIR=$3
readonly REPO_ROOT=$(cd "$(dirname "$0")/.." && pwd)
readonly BUILDER_MANIFEST="$REPO_ROOT/tools/v7-txv1-honest-proof/Cargo.toml"
readonly RPC_URL=${ASPIS_TXV1_DISPOSABLE_RPC_URL:-}
readonly PAYER_KEYPAIR=${ASPIS_TXV1_DISPOSABLE_PAYER_KEYPAIR:-}
readonly PAYER_PUBKEY=${ASPIS_TXV1_DISPOSABLE_PAYER_PUBKEY:-}
readonly VERIFIER_PROGRAM="7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue"

[[ "$RPC_URL" =~ ^http://127\.0\.0\.1:[0-9]+$ ]] || fail "disposable loopback RPC is required"
[[ -f "$PAYER_KEYPAIR" && -n "$PAYER_PUBKEY" ]] || fail "ephemeral cluster payer is unavailable"
[[ -f "$PROOF_KEYPAIR" && -f "$PROOF_PAYLOAD" ]] || fail "proof keypair or payload is unavailable"
[[ "$EVIDENCE_DIR" == /* && "$EVIDENCE_DIR" != / && ! -e "$EVIDENCE_DIR" ]] \
  || fail "evidence directory must be a new absolute non-root path"
for command_name in cargo curl jq od openssl seq shasum tail tr wc; do
  command -v "$command_name" >/dev/null || fail "missing required command: $command_name"
done

mkdir -p "$EVIDENCE_DIR/transactions"
readonly WORK_DIR=$(mktemp -d "${TMPDIR:-/tmp}/aspis-v7-proof-upload.XXXXXX")
cleanup() {
  case "$WORK_DIR" in
    */aspis-v7-proof-upload.*) rm -rf -- "$WORK_DIR" ;;
    *) echo "refusing to remove unexpected temporary path: $WORK_DIR" >&2 ;;
  esac
}
trap cleanup EXIT

rpc() {
  curl --fail-with-body --silent --show-error --max-time 60 \
    -H 'content-type: application/json' --data-binary "$1" "$RPC_URL"
}

slot=$(rpc '{"jsonrpc":"2.0","id":1,"method":"getSlot","params":[{"commitment":"finalized"}]}' \
  | jq -er '.result')
blockhash=$(rpc "$(jq -nc --argjson slot "$slot" \
  '{jsonrpc:"2.0",id:2,method:"getLatestBlockhash",params:[{commitment:"finalized",minContextSlot:$slot}]}')" \
  | jq -er '.result.value.blockhash')
payload_bytes=$(wc -c <"$PROOF_PAYLOAD" | tr -d ' ')
space=$((40 + payload_bytes))
rent_lamports=$(rpc "$(jq -nc --argjson space "$space" \
  '{jsonrpc:"2.0",id:3,method:"getMinimumBalanceForRentExemption",params:[$space,{commitment:"finalized"}]}')" \
  | jq -er '.result')

jq -n --arg blockhash "$blockhash" --argjson slot "$slot" --argjson rent "$rent_lamports" \
  --arg payer "$PAYER_KEYPAIR" --arg proof "$PROOF_KEYPAIR" --arg payload "$PROOF_PAYLOAD" \
  '{schema:"aspis.v7.txv1-proof-upload-input.v1",recentBlockhash:$blockhash,
    minContextSlot:$slot,requestId:1000,rentLamports:$rent,
    payerKeypair:$payer,proofKeypair:$proof,proofPayload:$payload}' \
  >"$WORK_DIR/input.json"

NO_DNA=1 CARGO_BUILD_JOBS=2 cargo build --quiet --release --locked --offline \
  --manifest-path "$BUILDER_MANIFEST" --bin build_proof_upload_requests
readonly BUILDER="$REPO_ROOT/tools/v7-txv1-honest-proof/target/release/build_proof_upload_requests"
[[ -x "$BUILDER" ]] || fail "proof upload request builder is unavailable"
NO_DNA=1 "$BUILDER" "$WORK_DIR/input.json" >"$EVIDENCE_DIR/signed-requests.json"
jq -e --argjson payloadBytes "$payload_bytes" '
  .schema == "aspis.v7.txv1-proof-upload-signed-requests.v1" and
  .proofPayloadBytes == $payloadBytes and .uploadChunkBytes == 960 and
  .requestCount == (.requests | length) and .requestCount > 2 and
  all(.requests[]; .serializedTransactionBytes < 1232 and
    (.signedWireSha256 | test("^[0-9a-f]{64}$")))
' "$EVIDENCE_DIR/signed-requests.json" >/dev/null || fail "signed upload plan failed validation"

proof_account=$(jq -er '.proofAccount' "$EVIDENCE_DIR/signed-requests.json")
request_count=$(jq -er '.requestCount' "$EVIDENCE_DIR/signed-requests.json")
for request_index in $(seq 0 $((request_count - 1))); do
  name=$(jq -er ".requests[$request_index].name" "$EVIDENCE_DIR/signed-requests.json")
  simulation=$(rpc "$(jq -c ".requests[$request_index].simulationRequest" \
    "$EVIDENCE_DIR/signed-requests.json")")
  jq . <<<"$simulation" >"$EVIDENCE_DIR/transactions/$name.simulation.json"
  jq -e '.error | not' <<<"$simulation" >/dev/null
  jq -e '.result.value.err == null' <<<"$simulation" >/dev/null \
    || fail "simulation rejected $name"
  send=$(rpc "$(jq -c ".requests[$request_index].sendRequest" \
    "$EVIDENCE_DIR/signed-requests.json")")
  jq . <<<"$send" >"$EVIDENCE_DIR/transactions/$name.send.json"
  jq -e '.error | not' <<<"$send" >/dev/null
  signature=$(jq -er '.result' <<<"$send")
  [[ "$signature" == "$(jq -er ".requests[$request_index].signature" \
    "$EVIDENCE_DIR/signed-requests.json")" ]] || fail "submitted signature changed for $name"
  finalized=false
  for _ in $(seq 1 300); do
    status=$(rpc "$(jq -nc --arg signature "$signature" \
      '{jsonrpc:"2.0",id:4000,method:"getSignatureStatuses",params:[[$signature],{searchTransactionHistory:true}]}')")
    if jq -e '.result.value[0].confirmationStatus == "finalized"' <<<"$status" >/dev/null; then
      finalized=true
      break
    fi
    sleep 0.1
  done
  [[ "$finalized" == true ]] || fail "transaction did not finalize: $name"
  landed=$(rpc "$(jq -nc --arg signature "$signature" \
    '{jsonrpc:"2.0",id:5000,method:"getTransaction",params:[$signature,{encoding:"json",commitment:"finalized",maxSupportedTransactionVersion:1}]}')")
  jq . <<<"$landed" >"$EVIDENCE_DIR/transactions/$name.finalized.json"
  jq -e '.result != null and .result.meta.err == null' <<<"$landed" >/dev/null \
    || fail "landed transaction failed: $name"
done

rpc "$(jq -nc --arg proof "$proof_account" \
  '{jsonrpc:"2.0",id:6000,method:"getAccountInfo",params:[$proof,{encoding:"base64",commitment:"finalized"}]}')" \
  | jq . >"$EVIDENCE_DIR/proof-account-finalized.json"
jq -e --arg owner "$VERIFIER_PROGRAM" --argjson space "$space" '
  .result.value != null and .result.value.owner == $owner and
  .result.value.executable == false and .result.value.space == $space
' "$EVIDENCE_DIR/proof-account-finalized.json" >/dev/null \
  || fail "final proof account shape is wrong"
jq -er '.result.value.data[0]' "$EVIDENCE_DIR/proof-account-finalized.json" \
  | openssl base64 -d -A >"$WORK_DIR/proof-account.bin"
magic=$(od -An -tx1 -N4 "$WORK_DIR/proof-account.bin" | tr -d ' \n')
[[ "$magic" == 41535055 ]] || fail "proof account magic is not ASPU"
authority_hex=$(od -An -tx1 -j8 -N32 "$WORK_DIR/proof-account.bin" | tr -d ' \n')
[[ "$authority_hex" == "$(printf '00%.0s' {1..32})" ]] || fail "proof account was not sealed"
tail -c +41 "$WORK_DIR/proof-account.bin" >"$WORK_DIR/landed-payload.bin"
[[ "$(shasum -a 256 "$WORK_DIR/landed-payload.bin" | awk '{print $1}')" == \
    "$(shasum -a 256 "$PROOF_PAYLOAD" | awk '{print $1}')" ]] \
  || fail "landed proof payload differs"

jq -n --arg proofAccount "$proof_account" --arg payer "$PAYER_PUBKEY" \
  --arg payloadSha "$(shasum -a 256 "$PROOF_PAYLOAD" | awk '{print $1}')" \
  --arg accountSha "$(shasum -a 256 "$WORK_DIR/proof-account.bin" | awk '{print $1}')" \
  --argjson payloadBytes "$payload_bytes" --argjson requestCount "$request_count" \
  --slurpfile requests "$EVIDENCE_DIR/signed-requests.json" '
  {schema:"aspis.v7.txv1-proof-upload-finalized.v1",proofAccount:$proofAccount,
    payer:$payer,proofPayload:{bytes:$payloadBytes,sha256:$payloadSha},
    proofAccountSha256:$accountSha,transactions:$requests[0].requests,
    requestCount:$requestCount,allSimulatedBeforeSubmission:true,
    allSubmittedByteIdentically:true,allFinalized:true,sealed:true,
    keypairCommitted:false,realFundsUsed:false}
' >"$EVIDENCE_DIR/proof-upload.json"

echo "FINALIZED DISPOSABLE PROOF UPLOAD: $proof_account"
