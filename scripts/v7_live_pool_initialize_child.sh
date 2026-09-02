#!/usr/bin/env bash
set -euo pipefail

fail() {
  echo "FAIL: $*" >&2
  exit 1
}

[[ $# -eq 1 ]] || fail "usage: $0 <new-evidence-dir>"
readonly EVIDENCE_DIR=$1
readonly REPO_ROOT=$(cd "$(dirname "$0")/.." && pwd)
readonly CONFIG=${ASPIS_TXV1_HARNESS_CONFIG:-$REPO_ROOT/config/v7-txv1-devnet-harness-20260901.json}
readonly RPC_URL=${ASPIS_TXV1_DISPOSABLE_RPC_URL:-}
readonly PAYER_KEYPAIR=${ASPIS_TXV1_DISPOSABLE_PAYER_KEYPAIR:-}
readonly SOURCE_AUTHORITY_KEYPAIR=${ASPIS_TXV1_DISPOSABLE_SOURCE_AUTHORITY_KEYPAIR:-}
readonly BUILDER=${ASPIS_V7_LIVE_POOL_INITIALIZE_BUILDER:-}
readonly SECRET_BUILDER=${ASPIS_V7_LIVE_OPERATION_SECRET_BUILDER:-}
readonly DEPOSIT_BUILDER=${ASPIS_V7_LIVE_POOL_DEPOSIT_BUILDER:-}
readonly CHECKPOINT_BUILDER=${ASPIS_V7_LIVE_POOL_CHECKPOINT_BUILDER:-}
readonly MATERIALIZER=${ASPIS_V7_LIVE_PROOF_MATERIALIZER:-}
readonly PROVER=${ASPIS_V7_LIVE_POOL_PROVER:-}
readonly PROOF_UPLOAD_CHILD=${ASPIS_V7_PROOF_UPLOAD_CHILD:-}
readonly TERMINAL_BUILDER=${ASPIS_V7_LIVE_TERMINAL_BUILDER:-${ASPIS_V7_LIVE_TRANSFER_TERMINAL_BUILDER:-}}
readonly PROOF_CLOSE_BUILDER=${ASPIS_V7_LIVE_PROOF_CLOSE_BUILDER:-}
readonly AGAVE_BIN_DIR=${ASPIS_TXV1_DISPOSABLE_AGAVE_BIN_DIR:-}
readonly OPERATION=${ASPIS_V7_LIVE_OPERATION:-transfer}
readonly CIPHERTEXT_CASE=${ASPIS_V7_LIVE_CIPHERTEXT_CASE:-canonical}
readonly WITHDRAWAL_CPI_CASE=${ASPIS_V7_LIVE_WITHDRAWAL_CPI_CASE:-none}
readonly SELECTED_LANE_CASE=${ASPIS_V7_LIVE_SELECTED_LANE_CASE:-none}

[[ "$RPC_URL" =~ ^http://127\.0\.0\.1:[0-9]+$ ]] || fail "disposable RPC is required"
[[ "$OPERATION" == transfer || "$OPERATION" == withdrawal ]] \
  || fail "ASPIS_V7_LIVE_OPERATION must be transfer or withdrawal"
[[ "$CIPHERTEXT_CASE" == canonical || "$CIPHERTEXT_CASE" == malformed-magic ]] \
  || fail "ASPIS_V7_LIVE_CIPHERTEXT_CASE must be canonical or malformed-magic"
[[ "$WITHDRAWAL_CPI_CASE" == none || "$WITHDRAWAL_CPI_CASE" == compute-exhaustion ]] \
  || fail "ASPIS_V7_LIVE_WITHDRAWAL_CPI_CASE must be none or compute-exhaustion"
if [[ "$WITHDRAWAL_CPI_CASE" != none ]]; then
  [[ "$OPERATION" == withdrawal && "$CIPHERTEXT_CASE" == canonical ]] \
    || fail "withdrawal CPI failure testing requires canonical withdrawal mode"
fi
[[ "$SELECTED_LANE_CASE" == none || "$SELECTED_LANE_CASE" == stale-after-deposit ]] \
  || fail "ASPIS_V7_LIVE_SELECTED_LANE_CASE must be none or stale-after-deposit"
if [[ "$SELECTED_LANE_CASE" != none ]]; then
  [[ "$OPERATION" == transfer && "$CIPHERTEXT_CASE" == canonical && "$WITHDRAWAL_CPI_CASE" == none ]] \
    || fail "selected-lane testing requires canonical transfer mode"
fi
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

account_values_hash() {
  jq -cS '.result.value' "$1" | shasum -a 256 | awk '{print $1}'
}

account_values_fee_normalized_hash() {
  local file=$1 payer_index=$2
  jq -cS --argjson payerIndex "$payer_index" \
    '.result.value | .[$payerIndex].lamports = 0' "$file" \
    | shasum -a 256 | awk '{print $1}'
}

assert_failed_transaction_fee_only() {
  local before=$1 after=$2 payer_index=$3 fee=$4
  jq -ne --argjson payerIndex "$payer_index" \
    --slurpfile before "$before" --slurpfile after "$after" '
      ($before[0].result.value | .[$payerIndex].lamports = 0) ==
        ($after[0].result.value | .[$payerIndex].lamports = 0)' >/dev/null \
    || return 1
  local before_lamports after_lamports
  before_lamports=$(jq -er --argjson payerIndex "$payer_index" \
    '.result.value[$payerIndex].lamports | tostring' "$before")
  after_lamports=$(jq -er --argjson payerIndex "$payer_index" \
    '.result.value[$payerIndex].lamports | tostring' "$after")
  ((before_lamports - after_lamports == fee))
}

token_amount() {
  local bytes
  bytes=$(jq -er '.result.value.data[0]' "$1" | openssl base64 -d -A \
    | od -An -v -tu1 | tr -s ' ' '\n' | sed '/^$/d')
  mapfile -t token_bytes <<<"$bytes"
  [[ ${#token_bytes[@]} -ge 72 ]] || fail "short SPL token account: $1"
  local amount=0 multiplier=1 index
  for index in $(seq 64 71); do
    amount=$((amount + token_bytes[index] * multiplier))
    multiplier=$((multiplier * 256))
  done
  printf '%s\n' "$amount"
}

token_state() {
  jq -er '.result.value.data[0]' "$1" | openssl base64 -d -A \
    | od -An -j108 -N1 -tu1 | tr -d '[:space:]'
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
    | jq --arg requestedAddress "$address" '. + {requestedAddress:$requestedAddress}' \
    >"$EVIDENCE_DIR/account-$account_index.json"
  jq -e '.result.value != null' "$EVIDENCE_DIR/account-$account_index.json" >/dev/null \
    || fail "initialized account missing: $address"
  account_index=$((account_index + 1))
done < <(jq -r '.initializedAccounts[]' "$EVIDENCE_DIR/signed-request.json")

if [[ -n "$SECRET_BUILDER" || -n "$DEPOSIT_BUILDER" ]]; then
  [[ -x "$SECRET_BUILDER" && -x "$DEPOSIT_BUILDER" && -x "$CHECKPOINT_BUILDER" ]] \
    || fail "secret, deposit and checkpoint builders are all required"
  mkdir "$EVIDENCE_DIR/deposit"
  "$SECRET_BUILDER" "$OPERATION" "$WORK_DIR/operation-secrets.json" \
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
      | jq --arg requestedAddress "$address" '. + {requestedAddress:$requestedAddress}' \
      >"$EVIDENCE_DIR/deposit/$name-after.json"
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

  mkdir "$EVIDENCE_DIR/checkpoint"
  master_address=$(jq -er '.initializedAccounts[0]' "$EVIDENCE_DIR/signed-request.json")
  rpc "$(jq -nc --arg address "$master_address" \
    '{jsonrpc:"2.0",id:1000,method:"getAccountInfo",params:[$address,{encoding:"base64",commitment:"finalized"}]}')" \
    | jq --arg requestedAddress "$master_address" '. + {requestedAddress:$requestedAddress}' \
    >"$EVIDENCE_DIR/checkpoint/master-before.json"
  checkpoint_context_slot=$(rpc '{"jsonrpc":"2.0","id":1001,"method":"getSlot","params":[{"commitment":"finalized"}]}' | jq -er '.result')
  checkpoint_blockhash=$(rpc "$(jq -nc --argjson slot "$checkpoint_context_slot" \
    '{jsonrpc:"2.0",id:1002,method:"getLatestBlockhash",params:[{commitment:"finalized",minContextSlot:$slot}]}')" \
    | jq -er '.result.value.blockhash')
  jq -n --arg config "$CONFIG" --arg payer "$PAYER_KEYPAIR" --arg hash "$checkpoint_blockhash" \
    --argjson slot "$checkpoint_context_slot" --arg master "$EVIDENCE_DIR/checkpoint/master-before.json" \
    '{schema:"aspis.v7.live-pool-checkpoint-input.v1",config:$config,payerKeypair:$payer,
      recentBlockhash:$hash,minContextSlot:$slot,requestId:1100,masterAccount:$master}' \
    >"$WORK_DIR/checkpoint-input.json"
  "$CHECKPOINT_BUILDER" "$WORK_DIR/checkpoint-input.json" >"$EVIDENCE_DIR/checkpoint/signed-request.json"
  checkpoint_simulation=$(rpc "$(jq -c '.simulationRequest' "$EVIDENCE_DIR/checkpoint/signed-request.json")")
  jq . <<<"$checkpoint_simulation" >"$EVIDENCE_DIR/checkpoint/simulation.json"
  jq -e '.error | not' <<<"$checkpoint_simulation" >/dev/null
  jq -e '.result.value.err == null' <<<"$checkpoint_simulation" >/dev/null || fail "checkpoint simulation failed"
  checkpoint_send=$(rpc "$(jq -c '.sendRequest' "$EVIDENCE_DIR/checkpoint/signed-request.json")")
  jq . <<<"$checkpoint_send" >"$EVIDENCE_DIR/checkpoint/send.json"
  checkpoint_signature=$(jq -er '.result' <<<"$checkpoint_send")
  [[ "$checkpoint_signature" == "$(jq -er '.signature' "$EVIDENCE_DIR/checkpoint/signed-request.json")" ]] \
    || fail "checkpoint submission changed signed wire"
  checkpoint_finalized=false
  for _ in $(seq 1 600); do
    checkpoint_status=$(rpc "$(jq -nc --arg signature "$checkpoint_signature" \
      '{jsonrpc:"2.0",id:1200,method:"getSignatureStatuses",params:[[$signature],{searchTransactionHistory:true}]}')")
    if jq -e '.result.value[0] != null and .result.value[0].confirmationStatus == "finalized"' \
      <<<"$checkpoint_status" >/dev/null; then checkpoint_finalized=true; break; fi
    sleep 0.1
  done
  [[ "$checkpoint_finalized" == true ]] || fail "checkpoint did not finalize"
  rpc "$(jq -nc --arg signature "$checkpoint_signature" \
    '{jsonrpc:"2.0",id:1300,method:"getTransaction",params:[$signature,{encoding:"json",commitment:"finalized",maxSupportedTransactionVersion:1}]}')" \
    | jq . >"$EVIDENCE_DIR/checkpoint/finalized-transaction.json"
  checkpoint_address=$(jq -er '.checkpointAccount' "$EVIDENCE_DIR/checkpoint/signed-request.json")
  rpc "$(jq -nc --arg address "$checkpoint_address" \
    '{jsonrpc:"2.0",id:1301,method:"getAccountInfo",params:[$address,{encoding:"base64",commitment:"finalized"}]}')" \
    | jq --arg requestedAddress "$checkpoint_address" '. + {requestedAddress:$requestedAddress}' \
    >"$EVIDENCE_DIR/checkpoint/checkpoint-account.json"
  rpc "$(jq -nc --arg address "$master_address" \
    '{jsonrpc:"2.0",id:1302,method:"getAccountInfo",params:[$address,{encoding:"base64",commitment:"finalized"}]}')" \
    | jq --arg requestedAddress "$master_address" '. + {requestedAddress:$requestedAddress}' \
    >"$EVIDENCE_DIR/checkpoint/master-after.json"
  for lane_index in $(seq 0 7); do
    lane_address=$(jq -er ".initializedAccounts[$((lane_index + 1))]" "$EVIDENCE_DIR/signed-request.json")
    rpc "$(jq -nc --arg address "$lane_address" \
      '{jsonrpc:"2.0",id:1303,method:"getAccountInfo",params:[$address,{encoding:"base64",commitment:"finalized"}]}')" \
      | jq --arg requestedAddress "$lane_address" '. + {requestedAddress:$requestedAddress}' \
      >"$EVIDENCE_DIR/checkpoint/lane-$lane_index.json"
  done
  checkpoint_simulated_cu=$(jq -er '.result.value.unitsConsumed' "$EVIDENCE_DIR/checkpoint/simulation.json")
  checkpoint_landed_cu=$(jq -er '.result.meta.computeUnitsConsumed' "$EVIDENCE_DIR/checkpoint/finalized-transaction.json")
  checkpoint_slot=$(jq -er '.result.slot' "$EVIDENCE_DIR/checkpoint/finalized-transaction.json")
  jq -n --arg signature "$checkpoint_signature" --argjson slot "$checkpoint_slot" \
    --arg checkpointAccount "$checkpoint_address" --argjson simulatedCu "$checkpoint_simulated_cu" \
    --argjson landedCu "$checkpoint_landed_cu" --slurpfile request "$EVIDENCE_DIR/checkpoint/signed-request.json" \
    '{schema:"aspis.v7.live-pool-checkpoint-finalized.v1",signature:$signature,slot:$slot,
      checkpointAccount:$checkpointAccount,simulatedCu:$simulatedCu,landedCu:$landedCu,
      serializedTransactionBytes:$request[0].serializedTransactionBytes,
      signedWireSha256:$request[0].signedWireSha256,byteIdenticalSimulationSubmission:true,
      finalized:true,auditOnly:true,disposable:true,mainnetReady:false}' \
    >"$EVIDENCE_DIR/checkpoint/checkpoint-finalized.json"

  if [[ -n "$MATERIALIZER" || -n "$PROVER" ]]; then
    [[ -x "$MATERIALIZER" && -x "$PROVER" && -x "$AGAVE_BIN_DIR/solana-keygen" ]] \
      || fail "materializer, prover and pinned solana-keygen are required"
    mkdir "$EVIDENCE_DIR/live-proof-inputs"
    registry_address=$(jq -er '.identitySet.bindingAccounts[] | select(.name == "registry") | .id' "$CONFIG")
    entry_address=$(jq -er '.identitySet.bindingAccounts[] | select(.name == "entry") | .id' "$CONFIG")
    for binding in "registry:$registry_address" "entry:$entry_address"; do
      binding_name=${binding%%:*}; binding_address=${binding##*:}
      rpc "$(jq -nc --arg address "$binding_address" \
        '{jsonrpc:"2.0",id:1400,method:"getAccountInfo",params:[$address,{encoding:"base64",commitment:"finalized"}]}')" \
        | jq --arg requestedAddress "$binding_address" '. + {requestedAddress:$requestedAddress}' \
        >"$EVIDENCE_DIR/live-proof-inputs/$binding_name.json"
    done
    mint_account=""
    vault_account=""
    destination_account=""
    if [[ "$OPERATION" == withdrawal ]]; then
      mint_address=$(jq -er '.disposableLiveGenesis.mint.id' "$CONFIG")
      vault_address=$(jq -er '.initializedAccounts[9]' "$EVIDENCE_DIR/signed-request.json")
      destination_address=$(jq -er '.disposableLiveGenesis.withdrawalDestinationTokenAccount' "$CONFIG")
      for custody_binding in "mint:$mint_address" "vault:$vault_address" \
        "destination:$destination_address"; do
        custody_name=${custody_binding%%:*}; custody_address=${custody_binding##*:}
        rpc "$(jq -nc --arg address "$custody_address" \
          '{jsonrpc:"2.0",id:1404,method:"getAccountInfo",params:[$address,{encoding:"base64",commitment:"finalized"}]}')" \
          | jq --arg requestedAddress "$custody_address" '. + {requestedAddress:$requestedAddress}' \
          >"$EVIDENCE_DIR/live-proof-inputs/$custody_name.json"
        jq -e '.result.value != null' "$EVIDENCE_DIR/live-proof-inputs/$custody_name.json" >/dev/null \
          || fail "withdrawal custody account missing: $custody_name"
      done
      mint_account="$EVIDENCE_DIR/live-proof-inputs/mint.json"
      vault_account="$EVIDENCE_DIR/live-proof-inputs/vault.json"
      destination_account="$EVIDENCE_DIR/live-proof-inputs/destination.json"
    fi
    deposit_blockhash_finalized=$(rpc "$(jq -nc --argjson slot "$deposit_slot" \
      '{jsonrpc:"2.0",id:1401,method:"getBlock",params:[$slot,{encoding:"json",transactionDetails:"none",rewards:false,maxSupportedTransactionVersion:1}]}')" \
      | jq -er '.result.blockhash')
    checkpoint_blockhash_finalized=$(rpc "$(jq -nc --argjson slot "$checkpoint_slot" \
      '{jsonrpc:"2.0",id:1402,method:"getBlock",params:[$slot,{encoding:"json",transactionDetails:"none",rewards:false,maxSupportedTransactionVersion:1}]}')" \
      | jq -er '.result.blockhash')
    genesis_hash=$(rpc '{"jsonrpc":"2.0","id":1403,"method":"getGenesisHash"}' | jq -er '.result')
    provider_set_digest=$(printf '%s' "$genesis_hash" | shasum -a 256 | awk '{print $1}')
    proof_keypair="$WORK_DIR/live-proof-account.json"
    NO_DNA=1 "$AGAVE_BIN_DIR/solana-keygen" new --no-bip39-passphrase --silent \
      --force --outfile "$proof_keypair"
    proof_pubkey=$(NO_DNA=1 "$AGAVE_BIN_DIR/solana-keygen" pubkey "$proof_keypair")
    initial_lanes=$(for lane_index in $(seq 1 8); do printf '%s\n' "$EVIDENCE_DIR/account-$lane_index.json"; done | jq -Rsc 'split("\n")[:-1]')
    checkpoint_lanes=$(for lane_index in $(seq 0 7); do printf '%s\n' "$EVIDENCE_DIR/checkpoint/lane-$lane_index.json"; done | jq -Rsc 'split("\n")[:-1]')
    jq -n --arg programId "$(jq -er '.identitySet.programs[] | select(.name == "pool") | .id' "$CONFIG")" \
      --arg proofAccount "$proof_pubkey" --arg provider "$provider_set_digest" \
      --arg initialMaster "$EVIDENCE_DIR/account-0.json" --argjson initialLanes "$initial_lanes" \
      --arg afterDepositLane "$EVIDENCE_DIR/deposit/lane-after.json" \
      --arg checkpointMaster "$EVIDENCE_DIR/checkpoint/master-after.json" \
      --argjson checkpointLanes "$checkpoint_lanes" \
      --arg checkpointAccount "$EVIDENCE_DIR/checkpoint/checkpoint-account.json" \
      --arg registry "$EVIDENCE_DIR/live-proof-inputs/registry.json" \
      --arg entry "$EVIDENCE_DIR/live-proof-inputs/entry.json" \
      --arg mintAccount "$mint_account" --arg vaultAccount "$vault_account" \
      --arg destinationAccount "$destination_account" \
      --arg secrets "$WORK_DIR/operation-secrets.json" --argjson depositSlot "$deposit_slot" \
      --arg depositBlockhash "$deposit_blockhash_finalized" --arg depositSignature "$deposit_signature" \
      --argjson checkpointSlot "$checkpoint_slot" --arg checkpointBlockhash "$checkpoint_blockhash_finalized" \
      '{schema:"aspis.v7.live-proof-materialization-input.v1",programId:$programId,
        proofAccount:$proofAccount,providerSetDigestHex:$provider,initialMaster:$initialMaster,
        initialLanes:$initialLanes,afterDepositLane:$afterDepositLane,
        checkpointMaster:$checkpointMaster,checkpointLanes:$checkpointLanes,
        checkpointAccount:$checkpointAccount,registryAccount:$registry,registryEntryAccount:$entry,
        mintAccount:(if $mintAccount == "" then null else $mintAccount end),
        vaultAccount:(if $vaultAccount == "" then null else $vaultAccount end),
        destinationAccount:(if $destinationAccount == "" then null else $destinationAccount end),
        secretsFile:$secrets,depositSlot:$depositSlot,depositBlockhash:$depositBlockhash,
        depositSignature:$depositSignature,checkpointSlot:$checkpointSlot,
        checkpointBlockhash:$checkpointBlockhash}' >"$WORK_DIR/materialize-input.json"
    "$MATERIALIZER" "$WORK_DIR/materialize-input.json" "$EVIDENCE_DIR/live-proof-bundle" \
      >"$EVIDENCE_DIR/live-proof-materialized.json"
    "$PROVER" "$EVIDENCE_DIR/live-proof-bundle/live-bundle.json" \
      "$EVIDENCE_DIR/live-proof" "$WORK_DIR/live-proof-nonce-ledger" \
      >"$EVIDENCE_DIR/live-proof.stdout.json"
    jq -e '.deterministicFixtureEntropy == false and .verifierBypass == false and
      .trustedResultAccount == false and .proof.powValid == true' \
      "$EVIDENCE_DIR/live-proof/proof.json" >/dev/null || fail "genuine live proof output invalid"
    jq -n --arg proofAccount "$proof_pubkey" --arg keypairLocation \
      'task-owned mktemp; destroyed by parent cleanup trap' --slurpfile proof "$EVIDENCE_DIR/live-proof/proof.json" \
      '{schema:"aspis.v7.genuine-live-proof-finalized-input.v1",proofAccount:$proofAccount,
        proofKeypairLocation:$keypairLocation,keypairCommitted:false,keypairPrinted:false,
        keypairCleanupRequired:true,proof:$proof[0],mainnetReady:false}' \
      >"$EVIDENCE_DIR/genuine-live-proof.json"
    if [[ -n "$PROOF_UPLOAD_CHILD" ]]; then
      [[ -x "$PROOF_UPLOAD_CHILD" ]] || fail "proof upload child is not executable"
      "$PROOF_UPLOAD_CHILD" "$proof_keypair" "$EVIDENCE_DIR/live-proof/proof-payload.bin" \
        "$EVIDENCE_DIR/proof-upload" >"$EVIDENCE_DIR/proof-upload.stdout"
      jq -e '.allSimulatedBeforeSubmission == true and .allSubmittedByteIdentically == true and
        .allFinalized == true and .sealed == true and .proofAccount == $proof' \
        --arg proof "$proof_pubkey" "$EVIDENCE_DIR/proof-upload/proof-upload.json" >/dev/null \
        || fail "genuine live proof upload failed validation"
      if [[ -n "$TERMINAL_BUILDER" ]]; then
        [[ -x "$TERMINAL_BUILDER" ]] || fail "terminal TxV1 builder is unavailable"
        readonly TERMINAL_EVIDENCE="$EVIDENCE_DIR/terminal-$OPERATION"
        mkdir "$TERMINAL_EVIDENCE"
        terminal_context_slot=$(rpc '{"jsonrpc":"2.0","id":1500,"method":"getSlot","params":[{"commitment":"finalized"}]}' | jq -er '.result')
        terminal_blockhash=$(rpc "$(jq -nc --argjson slot "$terminal_context_slot" \
          '{jsonrpc:"2.0",id:1501,method:"getLatestBlockhash",params:[{commitment:"finalized",minContextSlot:$slot}]}')" \
          | jq -er '.result.value.blockhash')
        calibrated_compute_limit=1300000
        calibration_token_entry_cu=null
        terminal_compute_unit_limit=null
        if [[ "$WITHDRAWAL_CPI_CASE" == compute-exhaustion ]]; then
          jq -n --arg schema aspis.v7.live-terminal-input.v1 \
            --arg bundle "$EVIDENCE_DIR/live-proof-bundle/live-bundle.json" \
            --arg asq8 "$EVIDENCE_DIR/live-proof/asq8.bin" --arg payer "$PAYER_KEYPAIR" \
            --arg blockhash "$terminal_blockhash" --argjson slot "$terminal_context_slot" \
            '{schema:$schema,bundle:$bundle,asq8:$asq8,payerKeypair:$payer,
              recentBlockhash:$blockhash,minContextSlot:$slot,requestId:1590,
              carrierTestMode:null,withdrawalCpiTestMode:null,computeUnitLimit:null}' \
            >"$WORK_DIR/terminal-calibration-input.json"
          "$TERMINAL_BUILDER" "$WORK_DIR/terminal-calibration-input.json" \
            >"$TERMINAL_EVIDENCE/calibration-signed-request.json"
          calibration_simulation=$(rpc "$(jq -c '.simulationRequest' \
            "$TERMINAL_EVIDENCE/calibration-signed-request.json")")
          jq . <<<"$calibration_simulation" >"$TERMINAL_EVIDENCE/calibration-simulation.json"
          jq -e '.error | not' <<<"$calibration_simulation" >/dev/null
          jq -e '.result.value.err == null and .result.value.unitsConsumed < 1300000 and
            any(.result.value.logs[]; contains("Program 7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue success")) and
            any(.result.value.logs[]; contains("Program TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA success"))' \
            <<<"$calibration_simulation" >/dev/null \
            || fail "withdrawal CPI calibration did not complete the genuine verifier and token CPI"
          calibration_token_entry_cu=$(jq -r '.result.value.logs[]' <<<"$calibration_simulation" \
            | sed -nE 's/^Program TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA consumed [0-9]+ of ([0-9]+) compute units$/\1/p')
          [[ "$calibration_token_entry_cu" =~ ^[0-9]+$ && "$calibration_token_entry_cu" -gt 60 ]] \
            || fail "could not derive the calibrated SPL token entry budget"
          calibrated_compute_limit=$((1300000 - calibration_token_entry_cu + 60))
          terminal_compute_unit_limit=$calibrated_compute_limit
          [[ "$calibrated_compute_limit" -ge 1150000 && "$calibrated_compute_limit" -lt 1300000 ]] \
            || fail "calibrated withdrawal CPI failure limit is outside the fail-closed range"
        fi
        terminal_schema=aspis.v7.live-terminal-input.v1
        carrier_test_mode=null
        if [[ "$CIPHERTEXT_CASE" == malformed-magic ]]; then
          terminal_schema=aspis.v7.live-terminal-malformed-carrier-test-input.v1
          carrier_test_mode='"malformed-magic"'
        fi
        withdrawal_cpi_test_mode=null
        if [[ "$WITHDRAWAL_CPI_CASE" == compute-exhaustion ]]; then
          terminal_schema=aspis.v7.live-terminal-withdrawal-cpi-failure-test-input.v1
          withdrawal_cpi_test_mode='"compute-exhaustion"'
        fi
        jq -n --arg schema "$terminal_schema" \
          --argjson carrierTestMode "$carrier_test_mode" \
          --argjson withdrawalCpiTestMode "$withdrawal_cpi_test_mode" \
          --argjson computeUnitLimit "$terminal_compute_unit_limit" \
          --arg bundle "$EVIDENCE_DIR/live-proof-bundle/live-bundle.json" \
          --arg asq8 "$EVIDENCE_DIR/live-proof/asq8.bin" --arg payer "$PAYER_KEYPAIR" \
          --arg blockhash "$terminal_blockhash" --argjson slot "$terminal_context_slot" \
          '{schema:$schema,bundle:$bundle,asq8:$asq8,payerKeypair:$payer,
            recentBlockhash:$blockhash,minContextSlot:$slot,requestId:1600,
            carrierTestMode:$carrierTestMode,withdrawalCpiTestMode:$withdrawalCpiTestMode,
            computeUnitLimit:$computeUnitLimit}' \
          >"$WORK_DIR/terminal-input.json"
        "$TERMINAL_BUILDER" "$WORK_DIR/terminal-input.json" \
          >"$TERMINAL_EVIDENCE/signed-request.json"
        jq -e --arg operation "$OPERATION" --arg carrierCase "$CIPHERTEXT_CASE" \
          --arg withdrawalCpiCase "$WITHDRAWAL_CPI_CASE" \
          --argjson expectedComputeUnitLimit "$calibrated_compute_limit" '
          .operation == $operation and
          .instructionCount == 2 and .terminalInstructionCount == 1 and
          (if $carrierCase == "canonical" then
            .ciphertextCarrierRealHpke == true and .ciphertextCarrierCanonical == true and
              .carrierTestMode == null
           else
            .ciphertextCarrierRealHpke == false and .ciphertextCarrierCanonical == false and
              .carrierTestMode == "malformed-magic"
           end) and
          (if $withdrawalCpiCase == "none" then
             .withdrawalCpiTestMode == null and .computeUnitLimit == 1300000
           else
             .withdrawalCpiTestMode == "compute-exhaustion" and
               .computeUnitLimit == $expectedComputeUnitLimit
           end) and .serializedTransactionBytes < 4096 and
          .serializedTransactionBytes <= 3500' "$TERMINAL_EVIDENCE/signed-request.json" >/dev/null \
          || fail "terminal TxV1 preflight failed"
        if [[ "$SELECTED_LANE_CASE" == stale-after-deposit ]]; then
          readonly STALING_EVIDENCE="$TERMINAL_EVIDENCE/staling-deposit"
          mkdir "$STALING_EVIDENCE"
          "$SECRET_BUILDER" transfer "$WORK_DIR/staling-deposit-secrets.json" "$selected_lane" \
            >"$STALING_EVIDENCE/public-operation.json"
          [[ "$(stat -c %a "$WORK_DIR/staling-deposit-secrets.json")" == 600 ]] \
            || fail "staling deposit secret file mode is not 0600"
          jq -e --argjson lane "$selected_lane" '
            .operation == "transfer" and .depositLane == $lane and
            .outputLane == $lane and .requiredLane == $lane
          ' "$STALING_EVIDENCE/public-operation.json" >/dev/null \
            || fail "staling deposit was not routed to the selected live lane"
          rpc "$(jq -nc --arg address "$master_address" \
            '{jsonrpc:"2.0",id:1570,method:"getAccountInfo",params:[$address,{encoding:"base64",commitment:"finalized"}]}')" \
            | jq --arg requestedAddress "$master_address" '. + {requestedAddress:$requestedAddress}' \
            >"$STALING_EVIDENCE/master-before.json"
          staling_lane_files='[]'
          for lane_index in $(seq 0 7); do
            lane_address=$(jq -er ".initializedAccounts[$((lane_index + 1))]" "$EVIDENCE_DIR/signed-request.json")
            lane_file="$STALING_EVIDENCE/lane-$lane_index-before.json"
            rpc "$(jq -nc --arg address "$lane_address" \
              '{jsonrpc:"2.0",id:1571,method:"getAccountInfo",params:[$address,{encoding:"base64",commitment:"finalized"}]}')" \
              | jq --arg requestedAddress "$lane_address" '. + {requestedAddress:$requestedAddress}' \
              >"$lane_file"
            staling_lane_files=$(jq -nc --argjson files "$staling_lane_files" --arg file "$lane_file" \
              '$files + [$file]')
          done
          rpc "$(jq -nc --arg address "$source_token" \
            '{jsonrpc:"2.0",id:1572,method:"getAccountInfo",params:[$address,{encoding:"base64",commitment:"finalized"}]}')" \
            | jq --arg requestedAddress "$source_token" '. + {requestedAddress:$requestedAddress}' \
            >"$STALING_EVIDENCE/source-before.json"
          staling_vault_address=$(jq -er '.initializedAccounts[9]' "$EVIDENCE_DIR/signed-request.json")
          rpc "$(jq -nc --arg address "$staling_vault_address" \
            '{jsonrpc:"2.0",id:1573,method:"getAccountInfo",params:[$address,{encoding:"base64",commitment:"finalized"}]}')" \
            | jq --arg requestedAddress "$staling_vault_address" '. + {requestedAddress:$requestedAddress}' \
            >"$STALING_EVIDENCE/vault-before.json"
          staling_slot=$(rpc '{"jsonrpc":"2.0","id":1574,"method":"getSlot","params":[{"commitment":"finalized"}]}' | jq -er '.result')
          staling_blockhash=$(rpc "$(jq -nc --argjson slot "$staling_slot" \
            '{jsonrpc:"2.0",id:1575,method:"getLatestBlockhash",params:[{commitment:"finalized",minContextSlot:$slot}]}')" \
            | jq -er '.result.value.blockhash')
          jq -n --arg config "$CONFIG" --arg payer "$PAYER_KEYPAIR" \
            --arg sourceAuthority "$SOURCE_AUTHORITY_KEYPAIR" --arg hash "$staling_blockhash" \
            --argjson slot "$staling_slot" --arg master "$STALING_EVIDENCE/master-before.json" \
            --argjson lanes "$staling_lane_files" --arg secrets "$WORK_DIR/staling-deposit-secrets.json" \
            '{schema:"aspis.v7.live-pool-staling-deposit-input.v1",config:$config,
              payerKeypair:$payer,sourceAuthorityKeypair:$sourceAuthority,
              recentBlockhash:$hash,minContextSlot:$slot,requestId:1576,
              masterAccount:$master,laneAccounts:$lanes,secretsFile:$secrets}' \
            >"$WORK_DIR/staling-deposit-input.json"
          "$DEPOSIT_BUILDER" "$WORK_DIR/staling-deposit-input.json" \
            >"$STALING_EVIDENCE/signed-request.json"
          jq -e --argjson lane "$selected_lane" '
            .operation == "deposit" and .selectedLane == $lane and
            .serializedTransactionBytes < 1232
          ' "$STALING_EVIDENCE/signed-request.json" >/dev/null \
            || fail "staling deposit signed request invalid"
          staling_simulation=$(rpc "$(jq -c '.simulationRequest' "$STALING_EVIDENCE/signed-request.json")")
          jq . <<<"$staling_simulation" >"$STALING_EVIDENCE/simulation.json"
          jq -e '.error | not' <<<"$staling_simulation" >/dev/null
          jq -e '.result.value.err == null' <<<"$staling_simulation" >/dev/null \
            || fail "staling deposit simulation failed"
          staling_send=$(rpc "$(jq -c '.sendRequest' "$STALING_EVIDENCE/signed-request.json")")
          jq . <<<"$staling_send" >"$STALING_EVIDENCE/send.json"
          staling_signature=$(jq -er '.result' <<<"$staling_send")
          [[ "$staling_signature" == "$(jq -er '.signature' "$STALING_EVIDENCE/signed-request.json")" ]] \
            || fail "staling deposit submission changed signed wire"
          staling_finalized=false
          for _ in $(seq 1 600); do
            staling_status=$(rpc "$(jq -nc --arg signature "$staling_signature" \
              '{jsonrpc:"2.0",id:1577,method:"getSignatureStatuses",params:[[$signature],{searchTransactionHistory:true}]}')")
            if jq -e '.result.value[0] != null and .result.value[0].confirmationStatus == "finalized"' \
              <<<"$staling_status" >/dev/null; then staling_finalized=true; break; fi
            sleep 0.1
          done
          [[ "$staling_finalized" == true ]] || fail "staling deposit did not finalize"
          rpc "$(jq -nc --arg signature "$staling_signature" \
            '{jsonrpc:"2.0",id:1578,method:"getTransaction",params:[$signature,{encoding:"json",commitment:"finalized",maxSupportedTransactionVersion:1}]}')" \
            | jq . >"$STALING_EVIDENCE/finalized-transaction.json"
          jq -e '.result != null and .result.meta.err == null' \
            "$STALING_EVIDENCE/finalized-transaction.json" >/dev/null \
            || fail "staling deposit did not land successfully"
          selected_lane_address=$(jq -er ".initializedAccounts[$((selected_lane + 1))]" \
            "$EVIDENCE_DIR/signed-request.json")
          for item in "lane:$selected_lane_address" "source:$source_token" "vault:$staling_vault_address"; do
            item_name=${item%%:*}; item_address=${item#*:}
            rpc "$(jq -nc --arg address "$item_address" \
              '{jsonrpc:"2.0",id:1579,method:"getAccountInfo",params:[$address,{encoding:"base64",commitment:"finalized"}]}')" \
              | jq --arg requestedAddress "$item_address" '. + {requestedAddress:$requestedAddress}' \
              >"$STALING_EVIDENCE/$item_name-after.json"
          done
          staling_source_before=$(token_amount "$STALING_EVIDENCE/source-before.json")
          staling_source_after=$(token_amount "$STALING_EVIDENCE/source-after.json")
          staling_vault_before=$(token_amount "$STALING_EVIDENCE/vault-before.json")
          staling_vault_after=$(token_amount "$STALING_EVIDENCE/vault-after.json")
          [[ "$staling_source_before" == 1000 && "$staling_source_after" == 0 &&
            "$staling_vault_before" == 1000 && "$staling_vault_after" == 2000 ]] \
            || fail "staling deposit custody delta is not exactly 1,000"
          staling_simulated_cu=$(jq -er '.result.value.unitsConsumed' "$STALING_EVIDENCE/simulation.json")
          staling_landed_cu=$(jq -er '.result.meta.computeUnitsConsumed' "$STALING_EVIDENCE/finalized-transaction.json")
          [[ "$staling_simulated_cu" == "$staling_landed_cu" ]] \
            || fail "staling deposit simulation and landed CU differ"
          jq -n --arg signature "$staling_signature" \
            --argjson slot "$(jq -er '.result.slot' "$STALING_EVIDENCE/finalized-transaction.json")" \
            --argjson selectedLane "$selected_lane" --argjson simulatedCu "$staling_simulated_cu" \
            --argjson landedCu "$staling_landed_cu" \
            --arg laneBefore "$(account_data_hash "$STALING_EVIDENCE/lane-$selected_lane-before.json")" \
            --arg laneAfter "$(account_data_hash "$STALING_EVIDENCE/lane-after.json")" \
            --slurpfile request "$STALING_EVIDENCE/signed-request.json" \
            '{schema:"aspis.v7.live-selected-lane-staling-deposit-finalized.v1",
              signature:$signature,slot:$slot,selectedLane:$selectedLane,
              serializedTransactionBytes:$request[0].serializedTransactionBytes,
              signedWireSha256:$request[0].signedWireSha256,
              simulatedCu:$simulatedCu,landedCu:$landedCu,
              laneDataSha256:{before:$laneBefore,after:$laneAfter},
              sourceAmount:{before:1000,after:0},vaultAmount:{before:1000,after:2000},
              byteIdenticalSimulationSubmission:true,finalized:true,
              auditOnly:true,disposable:true,mainnetReady:false}' \
            >"$STALING_EVIDENCE/staling-deposit-finalized.json"
        fi
        protected_addresses=$(jq -nc --slurpfile init "$EVIDENCE_DIR/signed-request.json" \
          --slurpfile terminal "$TERMINAL_EVIDENCE/signed-request.json" \
          --arg checkpoint "$checkpoint_address" \
          '($init[0].initializedAccounts[0:10] + [$checkpoint] + $terminal[0].terminalAccounts) | unique')
        rpc "$(jq -nc --argjson addresses "$protected_addresses" \
          '{jsonrpc:"2.0",id:1601,method:"getMultipleAccounts",params:[$addresses,{encoding:"base64",commitment:"finalized"}]}')" \
          | jq . >"$TERMINAL_EVIDENCE/accounts-before.json"
        terminal_simulation=$(rpc "$(jq -c '.simulationRequest' "$TERMINAL_EVIDENCE/signed-request.json")")
        jq . <<<"$terminal_simulation" >"$TERMINAL_EVIDENCE/simulation.json"
        jq -e '.error | not' <<<"$terminal_simulation" >/dev/null
        if [[ "$SELECTED_LANE_CASE" == stale-after-deposit ]]; then
          jq -e '.result.value.err != null and .result.value.unitsConsumed < 1300000 and
            any(.result.value.logs[]; contains("Program 7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue invoke")) and
            any(.result.value.logs[]; contains("Program 5PjDJaGfSPJj4tFzMRCiuuAasKg5n8dJKXKenhuwZexx failed"))' \
            <<<"$terminal_simulation" >/dev/null \
            || fail "stale selected-lane simulation did not reach verifier and reject"
          stale_send=$(rpc "$(jq -c '.sendRequest' "$TERMINAL_EVIDENCE/signed-request.json")")
          jq . <<<"$stale_send" >"$TERMINAL_EVIDENCE/send.json"
          stale_signature=$(jq -er '.result' <<<"$stale_send")
          [[ "$stale_signature" == "$(jq -er '.signature' "$TERMINAL_EVIDENCE/signed-request.json")" ]] \
            || fail "stale selected-lane submission changed signed wire"
          stale_finalized=false
          for _ in $(seq 1 600); do
            stale_status=$(rpc "$(jq -nc --arg signature "$stale_signature" \
              '{jsonrpc:"2.0",id:1660,method:"getSignatureStatuses",params:[[$signature],{searchTransactionHistory:true}]}')")
            if jq -e '.result.value[0] != null and .result.value[0].confirmationStatus == "finalized"' \
              <<<"$stale_status" >/dev/null; then stale_finalized=true; break; fi
            sleep 0.1
          done
          [[ "$stale_finalized" == true ]] || fail "stale selected-lane rejection did not finalize"
          rpc "$(jq -nc --arg signature "$stale_signature" \
            '{jsonrpc:"2.0",id:1661,method:"getTransaction",params:[$signature,{encoding:"json",commitment:"finalized",maxSupportedTransactionVersion:1}]}')" \
            | jq . >"$TERMINAL_EVIDENCE/finalized-transaction.json"
          jq -e '.result != null and .result.meta.err != null and
            .result.meta.computeUnitsConsumed < 1300000 and
            any(.result.meta.logMessages[]; contains("Program 7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue invoke")) and
            any(.result.meta.logMessages[]; contains("Program 5PjDJaGfSPJj4tFzMRCiuuAasKg5n8dJKXKenhuwZexx failed"))' \
            "$TERMINAL_EVIDENCE/finalized-transaction.json" >/dev/null \
            || fail "landed stale selected-lane transaction did not reject after verifier invocation"
          [[ "$(jq -c '.result.value.err' "$TERMINAL_EVIDENCE/simulation.json")" == \
            "$(jq -c '.result.meta.err' "$TERMINAL_EVIDENCE/finalized-transaction.json")" ]] \
            || fail "stale selected-lane simulation and landed errors differ"
          [[ "$(jq -er '.result.value.unitsConsumed' "$TERMINAL_EVIDENCE/simulation.json")" == \
            "$(jq -er '.result.meta.computeUnitsConsumed' "$TERMINAL_EVIDENCE/finalized-transaction.json")" ]] \
            || fail "stale selected-lane simulation and landed CU differ"
          rpc "$(jq -nc --argjson addresses "$protected_addresses" \
            '{jsonrpc:"2.0",id:1662,method:"getMultipleAccounts",params:[$addresses,{encoding:"base64",commitment:"finalized"}]}')" \
            | jq . >"$TERMINAL_EVIDENCE/accounts-after.json"
          payer_pubkey=$(NO_DNA=1 "$AGAVE_BIN_DIR/solana-keygen" pubkey "$PAYER_KEYPAIR")
          payer_index=$(jq -en --argjson addresses "$protected_addresses" --arg payer "$payer_pubkey" \
            '$addresses | index($payer) // error("payer absent from protected account set")')
          stale_fee=$(jq -er '.result.meta.fee' "$TERMINAL_EVIDENCE/finalized-transaction.json")
          assert_failed_transaction_fee_only "$TERMINAL_EVIDENCE/accounts-before.json" \
            "$TERMINAL_EVIDENCE/accounts-after.json" "$payer_index" "$stale_fee" \
            || fail "stale selected-lane rejection changed state beyond its payer fee"
          jq -n --arg signature "$stale_signature" \
            --argjson slot "$(jq -er '.result.slot' "$TERMINAL_EVIDENCE/finalized-transaction.json")" \
            --argjson simulatedError "$(jq -c '.result.value.err' "$TERMINAL_EVIDENCE/simulation.json")" \
            --argjson landedError "$(jq -c '.result.meta.err' "$TERMINAL_EVIDENCE/finalized-transaction.json")" \
            --argjson simulatedCu "$(jq -er '.result.value.unitsConsumed' "$TERMINAL_EVIDENCE/simulation.json")" \
            --argjson landedCu "$(jq -er '.result.meta.computeUnitsConsumed' "$TERMINAL_EVIDENCE/finalized-transaction.json")" \
            --arg before "$(account_values_fee_normalized_hash "$TERMINAL_EVIDENCE/accounts-before.json" "$payer_index")" \
            --arg after "$(account_values_fee_normalized_hash "$TERMINAL_EVIDENCE/accounts-after.json" "$payer_index")" \
            --arg payer "$payer_pubkey" --argjson payerFeeLamports "$stale_fee" \
            --slurpfile request "$TERMINAL_EVIDENCE/signed-request.json" \
            --slurpfile staling "$STALING_EVIDENCE/staling-deposit-finalized.json" \
            '{schema:"aspis.v7.live-terminal-stale-selected-lane-rejection.v1",
              expected:"reject proof whose selected live-lane snapshot was superseded",
              actual:"finalized-rejected",signature:$signature,slot:$slot,
              serializedTransactionBytes:$request[0].serializedTransactionBytes,
              signedWireSha256:$request[0].signedWireSha256,selectedLane:$request[0].selectedLane,
              simulatedError:$simulatedError,landedError:$landedError,
              simulatedCu:$simulatedCu,landedCu:$landedCu,
              proofGeneratedBeforeStalingDeposit:true,
              stalingDepositSignature:$staling[0].signature,
              stalingDepositSlot:$staling[0].slot,
              selectedLaneChangedAfterProof:($staling[0].laneDataSha256.before != $staling[0].laneDataSha256.after),
              verifierInvoked:true,byteIdenticalSimulationSubmission:true,
              feeNormalizedProtectedStateBeforeSha256:$before,
              feeNormalizedProtectedStateAfterSha256:$after,
              stateUnchangedExceptPayerFee:true,payer:$payer,payerFeeLamports:$payerFeeLamports,
              finalized:true,auditOnly:true,disposable:true,mainnetReady:false}' \
            >"$TERMINAL_EVIDENCE/stale-selected-lane-rejection.json"
          exit 0
        fi
        if [[ "$WITHDRAWAL_CPI_CASE" == compute-exhaustion ]]; then
          [[ "$(token_state "$EVIDENCE_DIR/live-proof-inputs/destination.json")" == 1 ]] \
            || fail "withdrawal CPI test destination is not initialized"
          jq -e --argjson computeUnitLimit "$calibrated_compute_limit" '
            .result.value.err != null and .result.value.unitsConsumed <= $computeUnitLimit and
            any(.result.value.logs[]; contains("Program 7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue success")) and
            any(.result.value.logs[]; contains("Program TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA invoke")) and
            any(.result.value.logs[]; contains("Program TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA failed"))' \
            <<<"$terminal_simulation" >/dev/null \
            || fail "withdrawal simulation did not reach and fail the SPL token CPI"
          failed_send=$(rpc "$(jq -c '.sendRequest' "$TERMINAL_EVIDENCE/signed-request.json")")
          jq . <<<"$failed_send" >"$TERMINAL_EVIDENCE/send.json"
          failed_signature=$(jq -er '.result' <<<"$failed_send")
          [[ "$failed_signature" == "$(jq -er '.signature' "$TERMINAL_EVIDENCE/signed-request.json")" ]] \
            || fail "failed withdrawal CPI submission changed signed wire"
          failed_finalized=false
          for _ in $(seq 1 600); do
            failed_status=$(rpc "$(jq -nc --arg signature "$failed_signature" \
              '{jsonrpc:"2.0",id:1650,method:"getSignatureStatuses",params:[[$signature],{searchTransactionHistory:true}]}')")
            if jq -e '.result.value[0] != null and .result.value[0].confirmationStatus == "finalized"' \
              <<<"$failed_status" >/dev/null; then failed_finalized=true; break; fi
            sleep 0.1
          done
          [[ "$failed_finalized" == true ]] || fail "failed withdrawal CPI did not finalize"
          rpc "$(jq -nc --arg signature "$failed_signature" \
            '{jsonrpc:"2.0",id:1651,method:"getTransaction",params:[$signature,{encoding:"json",commitment:"finalized",maxSupportedTransactionVersion:1}]}')" \
            | jq . >"$TERMINAL_EVIDENCE/finalized-transaction.json"
          jq -e --argjson computeUnitLimit "$calibrated_compute_limit" '
            .result != null and .result.meta.err != null and
            .result.meta.computeUnitsConsumed <= $computeUnitLimit and
            any(.result.meta.logMessages[]; contains("Program 7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue success")) and
            any(.result.meta.logMessages[]; contains("Program TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA invoke")) and
            any(.result.meta.logMessages[]; contains("Program TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA failed"))' \
            "$TERMINAL_EVIDENCE/finalized-transaction.json" >/dev/null \
            || fail "landed withdrawal did not fail at the SPL token CPI"
          [[ "$(jq -c '.result.value.err' "$TERMINAL_EVIDENCE/simulation.json")" == \
            "$(jq -c '.result.meta.err' "$TERMINAL_EVIDENCE/finalized-transaction.json")" ]] \
            || fail "withdrawal CPI simulation and landed errors differ"
          [[ "$(jq -er '.result.value.unitsConsumed' "$TERMINAL_EVIDENCE/simulation.json")" == \
            "$(jq -er '.result.meta.computeUnitsConsumed' "$TERMINAL_EVIDENCE/finalized-transaction.json")" ]] \
            || fail "withdrawal CPI simulation and landed CU differ"
          rpc "$(jq -nc --argjson addresses "$protected_addresses" \
            '{jsonrpc:"2.0",id:1652,method:"getMultipleAccounts",params:[$addresses,{encoding:"base64",commitment:"finalized"}]}')" \
            | jq . >"$TERMINAL_EVIDENCE/accounts-after.json"
          payer_pubkey=$(NO_DNA=1 "$AGAVE_BIN_DIR/solana-keygen" pubkey "$PAYER_KEYPAIR")
          payer_index=$(jq -en --argjson addresses "$protected_addresses" --arg payer "$payer_pubkey" \
            '$addresses | index($payer) // error("payer absent from protected account set")')
          failed_fee=$(jq -er '.result.meta.fee' "$TERMINAL_EVIDENCE/finalized-transaction.json")
          assert_failed_transaction_fee_only "$TERMINAL_EVIDENCE/accounts-before.json" \
            "$TERMINAL_EVIDENCE/accounts-after.json" "$payer_index" "$failed_fee" \
            || fail "failed withdrawal CPI changed state beyond its payer fee"
          rpc "$(jq -nc --arg address "$vault_address" \
            '{jsonrpc:"2.0",id:1653,method:"getAccountInfo",params:[$address,{encoding:"base64",commitment:"finalized"}]}')" \
            | jq --arg requestedAddress "$vault_address" '. + {requestedAddress:$requestedAddress}' \
            >"$TERMINAL_EVIDENCE/vault-after.json"
          rpc "$(jq -nc --arg address "$destination_address" \
            '{jsonrpc:"2.0",id:1654,method:"getAccountInfo",params:[$address,{encoding:"base64",commitment:"finalized"}]}')" \
            | jq --arg requestedAddress "$destination_address" '. + {requestedAddress:$requestedAddress}' \
            >"$TERMINAL_EVIDENCE/destination-after.json"
          vault_before_amount=$(token_amount "$EVIDENCE_DIR/live-proof-inputs/vault.json")
          vault_after_amount=$(token_amount "$TERMINAL_EVIDENCE/vault-after.json")
          destination_before_amount=$(token_amount "$EVIDENCE_DIR/live-proof-inputs/destination.json")
          destination_after_amount=$(token_amount "$TERMINAL_EVIDENCE/destination-after.json")
          [[ "$vault_before_amount" == "$vault_after_amount" &&
            "$destination_before_amount" == "$destination_after_amount" ]] \
            || fail "failed withdrawal CPI changed custody balances"
          jq -n --arg signature "$failed_signature" \
            --argjson slot "$(jq -er '.result.slot' "$TERMINAL_EVIDENCE/finalized-transaction.json")" \
            --argjson simulatedError "$(jq -c '.result.value.err' "$TERMINAL_EVIDENCE/simulation.json")" \
            --argjson landedError "$(jq -c '.result.meta.err' "$TERMINAL_EVIDENCE/finalized-transaction.json")" \
            --argjson simulatedCu "$(jq -er '.result.value.unitsConsumed' "$TERMINAL_EVIDENCE/simulation.json")" \
            --argjson landedCu "$(jq -er '.result.meta.computeUnitsConsumed' "$TERMINAL_EVIDENCE/finalized-transaction.json")" \
            --argjson payerFeeLamports "$failed_fee" --arg payer "$payer_pubkey" \
            --argjson calibratedComputeUnitLimit "$calibrated_compute_limit" \
            --argjson calibrationTokenEntryCu "$calibration_token_entry_cu" \
            --arg before "$(account_values_fee_normalized_hash "$TERMINAL_EVIDENCE/accounts-before.json" "$payer_index")" \
            --arg after "$(account_values_fee_normalized_hash "$TERMINAL_EVIDENCE/accounts-after.json" "$payer_index")" \
            --argjson vaultAmount "$vault_after_amount" --argjson destinationAmount "$destination_after_amount" \
            --slurpfile request "$TERMINAL_EVIDENCE/signed-request.json" \
            '{schema:"aspis.v7.live-terminal-failed-withdrawal-cpi-rollback.v1",
              expected:"SPL token CPI failure with atomic rollback",actual:"finalized-rejected",
              failureFixture:"terminal-compute-limit-exhausts-inside-token-cpi",signature:$signature,slot:$slot,
              serializedTransactionBytes:$request[0].serializedTransactionBytes,
              signedWireSha256:$request[0].signedWireSha256,selectedLane:$request[0].selectedLane,
              simulatedError:$simulatedError,landedError:$landedError,
              simulatedCu:$simulatedCu,landedCu:$landedCu,
              calibratedComputeUnitLimit:$calibratedComputeUnitLimit,
              calibrationTokenEntryCu:$calibrationTokenEntryCu,
              calibrationSubmitted:false,
              verifierSucceededBeforeCpiFailure:true,byteIdenticalSimulationSubmission:true,
              feeNormalizedProtectedStateBeforeSha256:$before,
              feeNormalizedProtectedStateAfterSha256:$after,
              stateUnchangedExceptPayerFee:true,payer:$payer,payerFeeLamports:$payerFeeLamports,
              vaultAmountBeforeAndAfter:$vaultAmount,
              destinationAmountBeforeAndAfter:$destinationAmount,
              finalized:true,auditOnly:true,disposable:true,mainnetReady:false}' \
            >"$TERMINAL_EVIDENCE/failed-withdrawal-cpi-rollback.json"
          exit 0
        fi
        jq -e '.result.value.err == null and .result.value.unitsConsumed < 1300000' <<<"$terminal_simulation" >/dev/null \
          || fail "terminal $OPERATION simulation failed"
        terminal_send=$(rpc "$(jq -c '.sendRequest' "$TERMINAL_EVIDENCE/signed-request.json")")
        jq . <<<"$terminal_send" >"$TERMINAL_EVIDENCE/send.json"
        terminal_signature=$(jq -er '.result' <<<"$terminal_send")
        [[ "$terminal_signature" == "$(jq -er '.signature' "$TERMINAL_EVIDENCE/signed-request.json")" ]] \
          || fail "terminal submission changed signed wire"
        terminal_finalized=false
        for _ in $(seq 1 600); do
          terminal_status=$(rpc "$(jq -nc --arg signature "$terminal_signature" \
            '{jsonrpc:"2.0",id:1700,method:"getSignatureStatuses",params:[[$signature],{searchTransactionHistory:true}]}')")
          if jq -e '.result.value[0] != null and .result.value[0].confirmationStatus == "finalized"' \
            <<<"$terminal_status" >/dev/null; then terminal_finalized=true; break; fi
          sleep 0.1
        done
        [[ "$terminal_finalized" == true ]] || fail "terminal $OPERATION did not finalize"
        rpc "$(jq -nc --arg signature "$terminal_signature" \
          '{jsonrpc:"2.0",id:1800,method:"getTransaction",params:[$signature,{encoding:"json",commitment:"finalized",maxSupportedTransactionVersion:1}]}')" \
          | jq . >"$TERMINAL_EVIDENCE/finalized-transaction.json"
        jq -e '.result != null and .result.meta.err == null and .result.meta.computeUnitsConsumed < 1300000' \
          "$TERMINAL_EVIDENCE/finalized-transaction.json" >/dev/null || fail "landed terminal $OPERATION failed"
        rpc "$(jq -nc --argjson addresses "$protected_addresses" \
          '{jsonrpc:"2.0",id:1801,method:"getMultipleAccounts",params:[$addresses,{encoding:"base64",commitment:"finalized"}]}')" \
          | jq . >"$TERMINAL_EVIDENCE/accounts-after.json"
        replay_simulation=$(rpc "$(jq -c '.simulationRequest' "$TERMINAL_EVIDENCE/signed-request.json")")
        jq . <<<"$replay_simulation" >"$TERMINAL_EVIDENCE/replay-simulation.json"
        jq -e '.error | not' <<<"$replay_simulation" >/dev/null
        jq -e '.result.value.err != null' <<<"$replay_simulation" >/dev/null \
          || fail "landed nullifier replay was not rejected"
        rpc "$(jq -nc --argjson addresses "$protected_addresses" \
          '{jsonrpc:"2.0",id:1804,method:"getMultipleAccounts",params:[$addresses,{encoding:"base64",commitment:"finalized"}]}')" \
          | jq . >"$TERMINAL_EVIDENCE/accounts-after-replay-simulation.json"
        [[ "$(account_values_hash "$TERMINAL_EVIDENCE/accounts-after.json")" == \
          "$(account_values_hash "$TERMINAL_EVIDENCE/accounts-after-replay-simulation.json")" ]] \
          || fail "replay simulation changed finalized accounts"
        terminal_simulated_cu=$(jq -er '.result.value.unitsConsumed' "$TERMINAL_EVIDENCE/simulation.json")
        terminal_landed_cu=$(jq -er '.result.meta.computeUnitsConsumed' "$TERMINAL_EVIDENCE/finalized-transaction.json")
        terminal_slot=$(jq -er '.result.slot' "$TERMINAL_EVIDENCE/finalized-transaction.json")
        custody_json='null'
        if [[ "$OPERATION" == withdrawal ]]; then
          vault_before_amount=$(token_amount "$EVIDENCE_DIR/live-proof-inputs/vault.json")
          destination_before_amount=$(token_amount "$EVIDENCE_DIR/live-proof-inputs/destination.json")
          rpc "$(jq -nc --arg address "$vault_address" \
            '{jsonrpc:"2.0",id:1802,method:"getAccountInfo",params:[$address,{encoding:"base64",commitment:"finalized"}]}')" \
            | jq --arg requestedAddress "$vault_address" '. + {requestedAddress:$requestedAddress}' \
            >"$TERMINAL_EVIDENCE/vault-after.json"
          rpc "$(jq -nc --arg address "$destination_address" \
            '{jsonrpc:"2.0",id:1803,method:"getAccountInfo",params:[$address,{encoding:"base64",commitment:"finalized"}]}')" \
            | jq --arg requestedAddress "$destination_address" '. + {requestedAddress:$requestedAddress}' \
            >"$TERMINAL_EVIDENCE/destination-after.json"
          vault_after_amount=$(token_amount "$TERMINAL_EVIDENCE/vault-after.json")
          destination_after_amount=$(token_amount "$TERMINAL_EVIDENCE/destination-after.json")
          [[ $((vault_before_amount - vault_after_amount)) -eq 250 \
            && $((destination_after_amount - destination_before_amount)) -eq 250 ]] \
            || fail "withdrawal custody conservation failed"
          custody_json=$(jq -nc --argjson amount 250 --argjson vaultBefore "$vault_before_amount" \
            --argjson vaultAfter "$vault_after_amount" --argjson destinationBefore "$destination_before_amount" \
            --argjson destinationAfter "$destination_after_amount" \
            '{amount:$amount,vaultBefore:$vaultBefore,vaultAfter:$vaultAfter,
              destinationBefore:$destinationBefore,destinationAfter:$destinationAfter,
              vaultDelta:($vaultBefore-$vaultAfter),destinationDelta:($destinationAfter-$destinationBefore),
              conservation:true,destinationBinding:true}')
        fi
        jq -n --arg signature "$terminal_signature" --argjson slot "$terminal_slot" \
          --arg operation "$OPERATION" --argjson custody "$custody_json" \
          --argjson simulatedCu "$terminal_simulated_cu" --argjson landedCu "$terminal_landed_cu" \
          --arg beforeSha "$(shasum -a 256 "$TERMINAL_EVIDENCE/accounts-before.json" | awk '{print $1}')" \
          --arg afterSha "$(shasum -a 256 "$TERMINAL_EVIDENCE/accounts-after.json" | awk '{print $1}')" \
          --slurpfile request "$TERMINAL_EVIDENCE/signed-request.json" \
          '{schema:"aspis.v7.live-terminal-finalized.v1",operation:$operation,signature:$signature,slot:$slot,
            simulatedCu:$simulatedCu,landedCu:$landedCu,
            serializedTransactionBytes:$request[0].serializedTransactionBytes,
            signedWireSha256:$request[0].signedWireSha256,selectedLane:$request[0].selectedLane,
            instructionCount:2,terminalInstructionCount:1,byteIdenticalSimulationSubmission:true,
            ciphertextCarrierRealHpke:$request[0].ciphertextCarrierRealHpke,
            ciphertextCarrierCanonical:$request[0].ciphertextCarrierCanonical,
            carrierTestMode:$request[0].carrierTestMode,
            protectedAccountsBeforeJsonSha256:$beforeSha,
            protectedAccountsAfterJsonSha256:$afterSha,custody:$custody,
            finalized:true,auditOnly:true,disposable:true,mainnetReady:false}' \
          >"$TERMINAL_EVIDENCE/terminal-finalized.json"
        jq -n --argjson error "$(jq -c '.result.value.err' "$TERMINAL_EVIDENCE/replay-simulation.json")" \
          --arg before "$(account_values_hash "$TERMINAL_EVIDENCE/accounts-after.json")" \
          --arg after "$(account_values_hash "$TERMINAL_EVIDENCE/accounts-after-replay-simulation.json")" \
          '{schema:"aspis.v7.live-terminal-replay-rejection.v1",expected:"reject",
            actual:"rejected",error:$error,finalizedStateBeforeSha256:$before,
            finalizedStateAfterSha256:$after,stateUnchanged:true}' \
          >"$TERMINAL_EVIDENCE/replay-rejection.json"
        fresh_replay_slot=$(rpc '{"jsonrpc":"2.0","id":1850,"method":"getSlot","params":[{"commitment":"finalized"}]}' | jq -er '.result')
        fresh_replay_blockhash=$(rpc "$(jq -nc --argjson slot "$fresh_replay_slot" \
          '{jsonrpc:"2.0",id:1851,method:"getLatestBlockhash",params:[{commitment:"finalized",minContextSlot:$slot}]}')" \
          | jq -er '.result.value.blockhash')
        jq -n --arg bundle "$EVIDENCE_DIR/live-proof-bundle/live-bundle.json" \
          --arg asq8 "$EVIDENCE_DIR/live-proof/asq8.bin" --arg payer "$PAYER_KEYPAIR" \
          --arg blockhash "$fresh_replay_blockhash" --argjson slot "$fresh_replay_slot" \
          '{schema:"aspis.v7.live-terminal-input.v1",bundle:$bundle,asq8:$asq8,
            payerKeypair:$payer,recentBlockhash:$blockhash,minContextSlot:$slot,requestId:1852}' \
          >"$WORK_DIR/fresh-replay-input.json"
        "$TERMINAL_BUILDER" "$WORK_DIR/fresh-replay-input.json" \
          >"$TERMINAL_EVIDENCE/fresh-replay-signed-request.json"
        [[ "$(jq -er '.signedWireSha256' "$TERMINAL_EVIDENCE/fresh-replay-signed-request.json")" != \
          "$(jq -er '.signedWireSha256' "$TERMINAL_EVIDENCE/signed-request.json")" ]] \
          || fail "fresh replay unexpectedly reused original signed wire"
        fresh_replay_simulation=$(rpc "$(jq -c '.simulationRequest' "$TERMINAL_EVIDENCE/fresh-replay-signed-request.json")")
        jq . <<<"$fresh_replay_simulation" >"$TERMINAL_EVIDENCE/fresh-replay-simulation.json"
        jq -e '.error | not' <<<"$fresh_replay_simulation" >/dev/null
        jq -e '.result.value.err != null' <<<"$fresh_replay_simulation" >/dev/null \
          || fail "fresh-signature nullifier replay simulation was not rejected"
        fresh_replay_send=$(rpc "$(jq -c '.sendRequest' "$TERMINAL_EVIDENCE/fresh-replay-signed-request.json")")
        jq . <<<"$fresh_replay_send" >"$TERMINAL_EVIDENCE/fresh-replay-send.json"
        fresh_replay_signature=$(jq -er '.result' <<<"$fresh_replay_send")
        [[ "$fresh_replay_signature" == \
          "$(jq -er '.signature' "$TERMINAL_EVIDENCE/fresh-replay-signed-request.json")" ]] \
          || fail "fresh replay submission changed signed wire"
        fresh_replay_finalized=false
        for _ in $(seq 1 600); do
          fresh_replay_status=$(rpc "$(jq -nc --arg signature "$fresh_replay_signature" \
            '{jsonrpc:"2.0",id:1853,method:"getSignatureStatuses",params:[[$signature],{searchTransactionHistory:true}]}')")
          if jq -e '.result.value[0] != null and .result.value[0].confirmationStatus == "finalized"' \
            <<<"$fresh_replay_status" >/dev/null; then fresh_replay_finalized=true; break; fi
          sleep 0.1
        done
        [[ "$fresh_replay_finalized" == true ]] || fail "fresh nullifier replay did not finalize"
        rpc "$(jq -nc --arg signature "$fresh_replay_signature" \
          '{jsonrpc:"2.0",id:1854,method:"getTransaction",params:[$signature,{encoding:"json",commitment:"finalized",maxSupportedTransactionVersion:1}]}')" \
          | jq . >"$TERMINAL_EVIDENCE/fresh-replay-finalized-transaction.json"
        jq -e '.result != null and .result.meta.err != null' \
          "$TERMINAL_EVIDENCE/fresh-replay-finalized-transaction.json" >/dev/null \
          || fail "fresh nullifier replay did not land as a failed transaction"
        rpc "$(jq -nc --argjson addresses "$protected_addresses" \
          '{jsonrpc:"2.0",id:1855,method:"getMultipleAccounts",params:[$addresses,{encoding:"base64",commitment:"finalized"}]}')" \
          | jq . >"$TERMINAL_EVIDENCE/accounts-after-fresh-replay.json"
        payer_pubkey=$(NO_DNA=1 "$AGAVE_BIN_DIR/solana-keygen" pubkey "$PAYER_KEYPAIR")
        payer_index=$(jq -en --argjson addresses "$protected_addresses" --arg payer "$payer_pubkey" \
          '$addresses | index($payer) // error("payer absent from protected account set")')
        fresh_replay_fee=$(jq -er '.result.meta.fee' \
          "$TERMINAL_EVIDENCE/fresh-replay-finalized-transaction.json")
        assert_failed_transaction_fee_only "$TERMINAL_EVIDENCE/accounts-after.json" \
          "$TERMINAL_EVIDENCE/accounts-after-fresh-replay.json" "$payer_index" "$fresh_replay_fee" \
          || fail "failed fresh nullifier replay changed state beyond its payer fee"
        jq -n --arg signature "$fresh_replay_signature" \
          --argjson slot "$(jq -er '.result.slot' "$TERMINAL_EVIDENCE/fresh-replay-finalized-transaction.json")" \
          --argjson simulatedError "$(jq -c '.result.value.err' "$TERMINAL_EVIDENCE/fresh-replay-simulation.json")" \
          --argjson landedError "$(jq -c '.result.meta.err' "$TERMINAL_EVIDENCE/fresh-replay-finalized-transaction.json")" \
          --argjson simulatedCu "$(jq -er '.result.value.unitsConsumed' "$TERMINAL_EVIDENCE/fresh-replay-simulation.json")" \
          --argjson landedCu "$(jq -er '.result.meta.computeUnitsConsumed' "$TERMINAL_EVIDENCE/fresh-replay-finalized-transaction.json")" \
          --arg before "$(account_values_fee_normalized_hash "$TERMINAL_EVIDENCE/accounts-after.json" "$payer_index")" \
          --arg after "$(account_values_fee_normalized_hash "$TERMINAL_EVIDENCE/accounts-after-fresh-replay.json" "$payer_index")" \
          --arg payer "$payer_pubkey" --argjson payerFeeLamports "$fresh_replay_fee" \
          --slurpfile request "$TERMINAL_EVIDENCE/fresh-replay-signed-request.json" \
          '{schema:"aspis.v7.live-terminal-fresh-nullifier-replay-rejection.v1",
            expected:"reject",actual:"finalized-rejected",signature:$signature,slot:$slot,
            serializedTransactionBytes:$request[0].serializedTransactionBytes,
            signedWireSha256:$request[0].signedWireSha256,simulatedError:$simulatedError,
            landedError:$landedError,simulatedCu:$simulatedCu,landedCu:$landedCu,
            byteIdenticalSimulationSubmission:true,finalizedStateBeforeSha256:$before,
            finalizedStateAfterSha256:$after,stateUnchangedExceptPayerFee:true,
            payer:$payer,payerFeeLamports:$payerFeeLamports}' \
          >"$TERMINAL_EVIDENCE/fresh-nullifier-replay-rejection.json"
        if [[ -n "$PROOF_CLOSE_BUILDER" ]]; then
          [[ -x "$PROOF_CLOSE_BUILDER" ]] || fail "proof close builder is unavailable"
          mkdir "$EVIDENCE_DIR/proof-close"
          rpc "$(jq -nc --arg address "$proof_pubkey" \
            '{jsonrpc:"2.0",id:1900,method:"getAccountInfo",params:[$address,{encoding:"base64",commitment:"finalized"}]}')" \
            | jq --arg requestedAddress "$proof_pubkey" '. + {requestedAddress:$requestedAddress}' \
            >"$EVIDENCE_DIR/proof-close/proof-before.json"
          close_slot=$(rpc '{"jsonrpc":"2.0","id":1902,"method":"getSlot","params":[{"commitment":"finalized"}]}' | jq -er '.result')
          close_blockhash=$(rpc "$(jq -nc --argjson slot "$close_slot" \
            '{jsonrpc:"2.0",id:1903,method:"getLatestBlockhash",params:[{commitment:"finalized",minContextSlot:$slot}]}')" \
            | jq -er '.result.value.blockhash')
          verifier_program=$(jq -er '.identitySet.programs[] | select(.name == "verifier") | .id' "$CONFIG")
          jq -n --arg verifier "$verifier_program" --arg proof "$proof_keypair" \
            --arg payer "$PAYER_KEYPAIR" --arg blockhash "$close_blockhash" --argjson slot "$close_slot" \
            '{schema:"aspis.v7.live-proof-close-input.v1",verifierProgram:$verifier,
              proofKeypair:$proof,payerKeypair:$payer,recentBlockhash:$blockhash,
              minContextSlot:$slot,requestId:2000}' >"$WORK_DIR/proof-close-input.json"
          "$PROOF_CLOSE_BUILDER" "$WORK_DIR/proof-close-input.json" \
            >"$EVIDENCE_DIR/proof-close/signed-request.json"
          close_simulation=$(rpc "$(jq -c '.simulationRequest' "$EVIDENCE_DIR/proof-close/signed-request.json")")
          jq . <<<"$close_simulation" >"$EVIDENCE_DIR/proof-close/simulation.json"
          jq -e '.error | not' <<<"$close_simulation" >/dev/null
          jq -e '.result.value.err == null' <<<"$close_simulation" >/dev/null \
            || fail "proof close simulation failed"
          close_send=$(rpc "$(jq -c '.sendRequest' "$EVIDENCE_DIR/proof-close/signed-request.json")")
          jq . <<<"$close_send" >"$EVIDENCE_DIR/proof-close/send.json"
          close_signature=$(jq -er '.result' <<<"$close_send")
          [[ "$close_signature" == "$(jq -er '.signature' "$EVIDENCE_DIR/proof-close/signed-request.json")" ]] \
            || fail "proof close submission changed signed wire"
          close_finalized=false
          for _ in $(seq 1 600); do
            close_status=$(rpc "$(jq -nc --arg signature "$close_signature" \
              '{jsonrpc:"2.0",id:2100,method:"getSignatureStatuses",params:[[$signature],{searchTransactionHistory:true}]}')")
            if jq -e '.result.value[0] != null and .result.value[0].confirmationStatus == "finalized"' \
              <<<"$close_status" >/dev/null; then close_finalized=true; break; fi
            sleep 0.1
          done
          [[ "$close_finalized" == true ]] || fail "proof close did not finalize"
          rpc "$(jq -nc --arg signature "$close_signature" \
            '{jsonrpc:"2.0",id:2200,method:"getTransaction",params:[$signature,{encoding:"json",commitment:"finalized",maxSupportedTransactionVersion:1}]}')" \
            | jq . >"$EVIDENCE_DIR/proof-close/finalized-transaction.json"
          jq -e '.result != null and .result.meta.err == null' \
            "$EVIDENCE_DIR/proof-close/finalized-transaction.json" >/dev/null || fail "proof close landed failure"
          rpc "$(jq -nc --arg address "$proof_pubkey" \
            '{jsonrpc:"2.0",id:2201,method:"getAccountInfo",params:[$address,{encoding:"base64",commitment:"finalized"}]}')" \
            | jq --arg requestedAddress "$proof_pubkey" '. + {requestedAddress:$requestedAddress}' \
            >"$EVIDENCE_DIR/proof-close/proof-after.json"
          jq -e '.result.value == null or .result.value.lamports == 0' \
            "$EVIDENCE_DIR/proof-close/proof-after.json" >/dev/null || fail "proof close did not drain account"
          jq -n --arg signature "$close_signature" \
            --argjson slot "$(jq -er '.result.slot' "$EVIDENCE_DIR/proof-close/finalized-transaction.json")" \
            --argjson simulatedCu "$(jq -er '.result.value.unitsConsumed' "$EVIDENCE_DIR/proof-close/simulation.json")" \
            --argjson landedCu "$(jq -er '.result.meta.computeUnitsConsumed' "$EVIDENCE_DIR/proof-close/finalized-transaction.json")" \
            --argjson rentRefund "$(jq -er '.result.value.lamports' "$EVIDENCE_DIR/proof-close/proof-before.json")" \
            --slurpfile request "$EVIDENCE_DIR/proof-close/signed-request.json" \
            '{schema:"aspis.v7.live-proof-close-finalized.v1",signature:$signature,slot:$slot,
              simulatedCu:$simulatedCu,landedCu:$landedCu,serializedTransactionBytes:$request[0].serializedTransactionBytes,
              signedWireSha256:$request[0].signedWireSha256,byteIdenticalSimulationSubmission:true,
              proofAccount:$request[0].proofAccount,refundAccount:$request[0].refundAccount,
              proofAccountDrained:true,rentRefundLamports:$rentRefund,finalized:true}' \
            >"$EVIDENCE_DIR/proof-close/proof-close-finalized.json"
        fi
      fi
    fi
  fi
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
