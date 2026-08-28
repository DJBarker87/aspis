#!/usr/bin/env bash
set -euo pipefail

readonly RPC_URL="https://api.devnet.solana.com"
readonly ACK="I_ACKNOWLEDGE_TXV1_DEVNET_SIMULATION_IS_RPC_ONLY_AND_WILL_NOT_SUBMIT"

if [[ $# -ne 3 ]]; then
  echo "usage: $0 <preflight.json> <evidence.json> <simulation-ack>" >&2
  exit 2
fi

readonly PREFLIGHT=$1
readonly EVIDENCE=$2
readonly PROVIDED_ACK=$3
readonly REPO_ROOT=$(cd "$(dirname "$0")/.." && pwd)

if [[ "$PROVIDED_ACK" != "$ACK" ]]; then
  echo "refusing public-devnet simulation without the exact simulation-only acknowledgement" >&2
  exit 2
fi
if [[ ! -f "$PREFLIGHT" ]]; then
  echo "missing preflight: $PREFLIGHT" >&2
  exit 2
fi
if [[ -e "$EVIDENCE" ]]; then
  echo "refusing to overwrite evidence: $EVIDENCE" >&2
  exit 2
fi
for command in cargo curl jq; do
  command -v "$command" >/dev/null || {
    echo "missing required command: $command" >&2
    exit 2
  }
done

jq -e '
  .schema == "aspis.v7.txv1-simulation-preflight.v1" and
  .summary.compute_unit_limit == 1300000 and
  .summary.serialized_transaction_bytes < 4096 and
  .summary.placeholder_signatures_are_zero == true and
  .summary.simulation_only == true and
  .simulationRequest.method == "simulateTransaction" and
  .simulationRequest.params[1].sigVerify == false and
  .simulationRequest.params[1].replaceRecentBlockhash == false and
  .simulationRequest.params[1].commitment == "finalized" and
  .simulationRequest.params[1].minContextSlot == .summary.min_context_slot and
  (.simulationRequest.params[0] | type == "string" and length > 0)
' "$PREFLIGHT" >/dev/null || {
  echo "preflight does not satisfy the frozen simulation-only gates" >&2
  exit 2
}

readonly CAPABILITY_FILE=$(mktemp)
readonly RESPONSE_FILE=$(mktemp)
cleanup() {
  rm -f "$CAPABILITY_FILE" "$RESPONSE_FILE"
}
trap cleanup EXIT

(
  cd "$REPO_ROOT"
  NO_DNA=1 cargo run --quiet \
    --manifest-path crates/aspis-pool-wallet-v1/Cargo.toml \
    --features eight-lane-plumbing-v2 \
    --example tx_v1_devnet_probe
) >"$CAPABILITY_FILE"

jq -e '.executionActivated == true' "$CAPABILITY_FILE" >/dev/null || {
  echo "public devnet TxV1 is not finalized-active; no simulation request was sent" >&2
  cat "$CAPABILITY_FILE" >&2
  exit 3
}

jq -c '.simulationRequest' "$PREFLIGHT" |
  curl --fail-with-body --silent --show-error \
    --max-time 60 \
    -H 'content-type: application/json' \
    --data-binary @- \
    "$RPC_URL" >"$RESPONSE_FILE"

jq -e '.jsonrpc == "2.0" and (.error | not)' "$RESPONSE_FILE" >/dev/null || {
  echo "public-devnet simulation RPC failed" >&2
  cat "$RESPONSE_FILE" >&2
  exit 4
}
jq -e '(.result.value.unitsConsumed | type == "number" and . <= 1300000)' \
  "$RESPONSE_FILE" >/dev/null || {
  echo "public-devnet simulation omitted CU or exceeded the strict 1.3M-CU gate" >&2
  cat "$RESPONSE_FILE" >&2
  exit 5
}

mkdir -p "$(dirname "$EVIDENCE")"
jq -n \
  --slurpfile capability "$CAPABILITY_FILE" \
  --slurpfile preflight "$PREFLIGHT" \
  --slurpfile response "$RESPONSE_FILE" \
  '{
    schema: "aspis.v7.public-devnet-txv1-simulation.v1",
    network: "devnet",
    rpcUrl: "https://api.devnet.solana.com",
    mutation: false,
    signing: false,
    submission: false,
    capability: $capability[0],
    preflight: $preflight[0],
    simulationResponse: $response[0]
  }' >"$EVIDENCE"

echo "simulation-only evidence written: $EVIDENCE"
echo "No transaction was signed or submitted."
jq '{
  err: .result.value.err,
  unitsConsumed: .result.value.unitsConsumed,
  logs: .result.value.logs,
  returnData: .result.value.returnData
}' "$RESPONSE_FILE"
