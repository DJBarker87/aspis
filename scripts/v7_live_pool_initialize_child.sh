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
readonly CHECKPOINT_BUILDER=${ASPIS_V7_LIVE_POOL_CHECKPOINT_BUILDER:-}
readonly MATERIALIZER=${ASPIS_V7_LIVE_PROOF_MATERIALIZER:-}
readonly PROVER=${ASPIS_V7_LIVE_POOL_PROVER:-}
readonly PROOF_UPLOAD_CHILD=${ASPIS_V7_PROOF_UPLOAD_CHILD:-}
readonly TERMINAL_BUILDER=${ASPIS_V7_LIVE_TRANSFER_TERMINAL_BUILDER:-}
readonly AGAVE_BIN_DIR=${ASPIS_TXV1_DISPOSABLE_AGAVE_BIN_DIR:-}

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
      --arg secrets "$WORK_DIR/operation-secrets.json" --argjson depositSlot "$deposit_slot" \
      --arg depositBlockhash "$deposit_blockhash_finalized" --arg depositSignature "$deposit_signature" \
      --argjson checkpointSlot "$checkpoint_slot" --arg checkpointBlockhash "$checkpoint_blockhash_finalized" \
      '{schema:"aspis.v7.live-proof-materialization-input.v1",programId:$programId,
        proofAccount:$proofAccount,providerSetDigestHex:$provider,initialMaster:$initialMaster,
        initialLanes:$initialLanes,afterDepositLane:$afterDepositLane,
        checkpointMaster:$checkpointMaster,checkpointLanes:$checkpointLanes,
        checkpointAccount:$checkpointAccount,registryAccount:$registry,registryEntryAccount:$entry,
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
        mkdir "$EVIDENCE_DIR/terminal-transfer"
        terminal_context_slot=$(rpc '{"jsonrpc":"2.0","id":1500,"method":"getSlot","params":[{"commitment":"finalized"}]}' | jq -er '.result')
        terminal_blockhash=$(rpc "$(jq -nc --argjson slot "$terminal_context_slot" \
          '{jsonrpc:"2.0",id:1501,method:"getLatestBlockhash",params:[{commitment:"finalized",minContextSlot:$slot}]}')" \
          | jq -er '.result.value.blockhash')
        jq -n --arg bundle "$EVIDENCE_DIR/live-proof-bundle/live-bundle.json" \
          --arg asq8 "$EVIDENCE_DIR/live-proof/asq8.bin" --arg payer "$PAYER_KEYPAIR" \
          --arg blockhash "$terminal_blockhash" --argjson slot "$terminal_context_slot" \
          '{schema:"aspis.v7.live-transfer-terminal-input.v1",bundle:$bundle,asq8:$asq8,
            payerKeypair:$payer,recentBlockhash:$blockhash,minContextSlot:$slot,requestId:1600}' \
          >"$WORK_DIR/terminal-input.json"
        "$TERMINAL_BUILDER" "$WORK_DIR/terminal-input.json" \
          >"$EVIDENCE_DIR/terminal-transfer/signed-request.json"
        jq -e '.instructionCount == 2 and .terminalInstructionCount == 1 and
          .ciphertextCarrierRealHpke == true and .serializedTransactionBytes < 4096 and
          .serializedTransactionBytes <= 3500' "$EVIDENCE_DIR/terminal-transfer/signed-request.json" >/dev/null \
          || fail "terminal TxV1 preflight failed"
        protected_addresses=$(jq -nc --slurpfile init "$EVIDENCE_DIR/signed-request.json" \
          --slurpfile terminal "$EVIDENCE_DIR/terminal-transfer/signed-request.json" \
          --arg checkpoint "$checkpoint_address" \
          '($init[0].initializedAccounts[0:10] + [$checkpoint] + $terminal[0].terminalAccounts) | unique')
        rpc "$(jq -nc --argjson addresses "$protected_addresses" \
          '{jsonrpc:"2.0",id:1601,method:"getMultipleAccounts",params:[$addresses,{encoding:"base64",commitment:"finalized"}]}')" \
          | jq . >"$EVIDENCE_DIR/terminal-transfer/accounts-before.json"
        terminal_simulation=$(rpc "$(jq -c '.simulationRequest' "$EVIDENCE_DIR/terminal-transfer/signed-request.json")")
        jq . <<<"$terminal_simulation" >"$EVIDENCE_DIR/terminal-transfer/simulation.json"
        jq -e '.error | not' <<<"$terminal_simulation" >/dev/null
        jq -e '.result.value.err == null and .result.value.unitsConsumed < 1300000' <<<"$terminal_simulation" >/dev/null \
          || fail "terminal transfer simulation failed"
        terminal_send=$(rpc "$(jq -c '.sendRequest' "$EVIDENCE_DIR/terminal-transfer/signed-request.json")")
        jq . <<<"$terminal_send" >"$EVIDENCE_DIR/terminal-transfer/send.json"
        terminal_signature=$(jq -er '.result' <<<"$terminal_send")
        [[ "$terminal_signature" == "$(jq -er '.signature' "$EVIDENCE_DIR/terminal-transfer/signed-request.json")" ]] \
          || fail "terminal submission changed signed wire"
        terminal_finalized=false
        for _ in $(seq 1 600); do
          terminal_status=$(rpc "$(jq -nc --arg signature "$terminal_signature" \
            '{jsonrpc:"2.0",id:1700,method:"getSignatureStatuses",params:[[$signature],{searchTransactionHistory:true}]}')")
          if jq -e '.result.value[0] != null and .result.value[0].confirmationStatus == "finalized"' \
            <<<"$terminal_status" >/dev/null; then terminal_finalized=true; break; fi
          sleep 0.1
        done
        [[ "$terminal_finalized" == true ]] || fail "terminal transfer did not finalize"
        rpc "$(jq -nc --arg signature "$terminal_signature" \
          '{jsonrpc:"2.0",id:1800,method:"getTransaction",params:[$signature,{encoding:"json",commitment:"finalized",maxSupportedTransactionVersion:1}]}')" \
          | jq . >"$EVIDENCE_DIR/terminal-transfer/finalized-transaction.json"
        jq -e '.result != null and .result.meta.err == null and .result.meta.computeUnitsConsumed < 1300000' \
          "$EVIDENCE_DIR/terminal-transfer/finalized-transaction.json" >/dev/null || fail "landed terminal transfer failed"
        rpc "$(jq -nc --argjson addresses "$protected_addresses" \
          '{jsonrpc:"2.0",id:1801,method:"getMultipleAccounts",params:[$addresses,{encoding:"base64",commitment:"finalized"}]}')" \
          | jq . >"$EVIDENCE_DIR/terminal-transfer/accounts-after.json"
        terminal_simulated_cu=$(jq -er '.result.value.unitsConsumed' "$EVIDENCE_DIR/terminal-transfer/simulation.json")
        terminal_landed_cu=$(jq -er '.result.meta.computeUnitsConsumed' "$EVIDENCE_DIR/terminal-transfer/finalized-transaction.json")
        terminal_slot=$(jq -er '.result.slot' "$EVIDENCE_DIR/terminal-transfer/finalized-transaction.json")
        jq -n --arg signature "$terminal_signature" --argjson slot "$terminal_slot" \
          --argjson simulatedCu "$terminal_simulated_cu" --argjson landedCu "$terminal_landed_cu" \
          --arg beforeSha "$(shasum -a 256 "$EVIDENCE_DIR/terminal-transfer/accounts-before.json" | awk '{print $1}')" \
          --arg afterSha "$(shasum -a 256 "$EVIDENCE_DIR/terminal-transfer/accounts-after.json" | awk '{print $1}')" \
          --slurpfile request "$EVIDENCE_DIR/terminal-transfer/signed-request.json" \
          '{schema:"aspis.v7.live-transfer-terminal-finalized.v1",signature:$signature,slot:$slot,
            simulatedCu:$simulatedCu,landedCu:$landedCu,
            serializedTransactionBytes:$request[0].serializedTransactionBytes,
            signedWireSha256:$request[0].signedWireSha256,selectedLane:$request[0].selectedLane,
            instructionCount:2,terminalInstructionCount:1,byteIdenticalSimulationSubmission:true,
            ciphertextCarrierRealHpke:true,protectedAccountsBeforeJsonSha256:$beforeSha,
            protectedAccountsAfterJsonSha256:$afterSha,finalized:true,auditOnly:true,
            disposable:true,mainnetReady:false}' >"$EVIDENCE_DIR/terminal-transfer/terminal-finalized.json"
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
