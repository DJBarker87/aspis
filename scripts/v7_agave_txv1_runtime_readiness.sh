#!/usr/bin/env bash
set -euo pipefail

readonly FEATURE_ID="txv1aq4pp281K9um3tnPgkfX8UqtFT6wcVW3hNezGLL"
readonly FEATURE_OWNER="Feature111111111111111111111111111111111111"
readonly REQUIRED_COMMIT="ac82b5d438b0c2303dc7169f52c748977713a111"
readonly MEMORY_HIGH_REQUIRED="9663676416"
readonly MEMORY_MAX_REQUIRED="12884901888"
readonly MEMORY_SWAP_MAX_REQUIRED="0"

if [[ $# -ne 2 ]]; then
  echo "usage: $0 <official-agave-v4.2.0-bin-dir> <new-evidence-dir>" >&2
  exit 2
fi

readonly AGAVE_BIN_DIR=$1
readonly EVIDENCE_DIR=$2
readonly SOLANA_BIN="$AGAVE_BIN_DIR/solana"
readonly VALIDATOR_BIN="$AGAVE_BIN_DIR/solana-test-validator"
readonly RPC_PORT=${ASPIS_TXV1_LOCAL_RPC_PORT:-18942}
readonly RPC_URL="http://127.0.0.1:$RPC_PORT"

if [[ "$(uname -s)" != "Linux" || "$(uname -m)" != "x86_64" ]]; then
  echo "Agave readiness requires Linux x86_64" >&2
  exit 2
fi
if [[ -e "$EVIDENCE_DIR" ]]; then
  echo "refusing to overwrite evidence directory: $EVIDENCE_DIR" >&2
  exit 2
fi
for command in base64 curl jq od rg seq sha256sum sleep stat tr; do
  command -v "$command" >/dev/null || {
    echo "missing required command: $command" >&2
    exit 2
  }
done
for binary in "$SOLANA_BIN" "$VALIDATOR_BIN"; do
  [[ -x "$binary" ]] || {
    echo "missing required executable: $binary" >&2
    exit 2
  }
done

readonly CGROUP_RELATIVE=$(awk -F: '$1 == "0" { print $3; exit }' /proc/self/cgroup)
readonly CGROUP_DIR="/sys/fs/cgroup$CGROUP_RELATIVE"
[[ -r "$CGROUP_DIR/memory.high" && -r "$CGROUP_DIR/memory.max" &&
   -r "$CGROUP_DIR/memory.peak" && -r "$CGROUP_DIR/memory.swap.max" &&
   -r "$CGROUP_DIR/memory.swap.current" && -r "$CGROUP_DIR/memory.swap.peak" ]] || {
  echo "cgroup v2 memory controls are unavailable" >&2
  exit 2
}
readonly MEMORY_HIGH=$(<"$CGROUP_DIR/memory.high")
readonly MEMORY_MAX=$(<"$CGROUP_DIR/memory.max")
readonly MEMORY_SWAP_MAX=$(<"$CGROUP_DIR/memory.swap.max")
[[ "$MEMORY_HIGH" == "$MEMORY_HIGH_REQUIRED" ]] || {
  echo "readiness unit must use MemoryHigh=9G; found $MEMORY_HIGH" >&2
  exit 2
}
[[ "$MEMORY_MAX" == "$MEMORY_MAX_REQUIRED" ]] || {
  echo "readiness unit must use MemoryMax=12G; found $MEMORY_MAX" >&2
  exit 2
}
[[ "$MEMORY_SWAP_MAX" == "$MEMORY_SWAP_MAX_REQUIRED" ]] || {
  echo "readiness unit must use MemorySwapMax=0; found $MEMORY_SWAP_MAX" >&2
  exit 2
}

readonly SOLANA_VERSION=$(NO_DNA=1 "$SOLANA_BIN" --version)
readonly VALIDATOR_VERSION=$(NO_DNA=1 "$VALIDATOR_BIN" --version)
[[ "$SOLANA_VERSION" == *"4.2.0"* && "$SOLANA_VERSION" == *"ac82b5d"* ]] || {
  echo "solana CLI is not the frozen official Agave v4.2.0 release" >&2
  exit 2
}
[[ "$VALIDATOR_VERSION" == *"4.2.0"* && "$VALIDATOR_VERSION" == *"ac82b5d"* ]] || {
  echo "test-validator is not the frozen official Agave v4.2.0 release" >&2
  exit 2
}

mkdir -p "$EVIDENCE_DIR"
readonly WORK_DIR=$(mktemp -d "${TMPDIR:-/tmp}/aspis-v7-agave-readiness.XXXXXX")
readonly LEDGER_DIR="$WORK_DIR/ledger"
VALIDATOR_PID=""
cleanup() {
  if [[ -n "$VALIDATOR_PID" ]]; then
    kill "$VALIDATOR_PID" 2>/dev/null || true
    wait "$VALIDATOR_PID" 2>/dev/null || true
  fi
  case "$WORK_DIR" in
    /tmp/aspis-v7-agave-readiness.*|*/aspis-v7-agave-readiness.*)
      rm -rf -- "$WORK_DIR"
      ;;
    *)
      echo "refusing to remove unexpected temporary path: $WORK_DIR" >&2
      ;;
  esac
}
trap cleanup EXIT

rpc() {
  curl --fail-with-body --silent --show-error --max-time 30 \
    -H 'content-type: application/json' \
    --data-binary "$1" \
    "$RPC_URL"
}

NO_DNA=1 "$VALIDATOR_BIN" \
  --reset \
  --quiet \
  --ledger "$LEDGER_DIR" \
  --bind-address 127.0.0.1 \
  --rpc-port "$RPC_PORT" \
  --warp-slot 150 \
  >"$EVIDENCE_DIR/validator.log" 2>&1 &
VALIDATOR_PID=$!

healthy=false
for _ in $(seq 1 200); do
  if rpc '{"jsonrpc":"2.0","id":1,"method":"getHealth"}' \
    | jq -e '.result == "ok"' >/dev/null 2>&1; then
    healthy=true
    break
  fi
  if ! kill -0 "$VALIDATOR_PID" 2>/dev/null; then
    break
  fi
  sleep 0.2
done
[[ "$healthy" == true ]] || {
  echo "Agave test-validator did not become healthy" >&2
  exit 1
}

rpc '{"jsonrpc":"2.0","id":2,"method":"getHealth"}' >"$EVIDENCE_DIR/get-health.json"
rpc '{"jsonrpc":"2.0","id":3,"method":"getVersion"}' >"$EVIDENCE_DIR/get-version.json"
rpc '{"jsonrpc":"2.0","id":4,"method":"getGenesisHash"}' >"$EVIDENCE_DIR/get-genesis-hash.json"
rpc '{"jsonrpc":"2.0","id":5,"method":"getSlot","params":[{"commitment":"finalized"}]}' >"$EVIDENCE_DIR/get-slot.json"
rpc "{\"jsonrpc\":\"2.0\",\"id\":6,\"method\":\"getAccountInfo\",\"params\":[\"$FEATURE_ID\",{\"encoding\":\"base64\",\"commitment\":\"finalized\"}]}" \
  >"$EVIDENCE_DIR/txv1-feature-account.json"
NO_DNA=1 "$SOLANA_BIN" feature status "$FEATURE_ID" --url "$RPC_URL" \
  >"$EVIDENCE_DIR/txv1-feature-status.txt"
NO_DNA=1 "$VALIDATOR_BIN" --help >"$EVIDENCE_DIR/solana-test-validator-help.txt"

jq -e '.result == "ok"' "$EVIDENCE_DIR/get-health.json" >/dev/null
jq -e '
  (.result."solana-core" | startswith("4.2.0")) and
  (.result."feature-set" | type == "number")
' "$EVIDENCE_DIR/get-version.json" >/dev/null || {
  echo "runtime RPC does not report Agave 4.2.0" >&2
  exit 1
}
jq -e --arg owner "$FEATURE_OWNER" '
  .result.value != null and
  .result.value.owner == $owner and
  .result.value.executable == false and
  (.result.value.data[0] | startswith("AQ"))
' "$EVIDENCE_DIR/txv1-feature-account.json" >/dev/null || {
  echo "TxV1 feature is not active in the disposable validator" >&2
  exit 1
}
rg -q "$FEATURE_ID" "$EVIDENCE_DIR/txv1-feature-status.txt" || {
  echo "solana feature status omitted the TxV1 feature" >&2
  exit 1
}
rg -qi 'active' "$EVIDENCE_DIR/txv1-feature-status.txt" || {
  echo "solana feature status does not report TxV1 active" >&2
  exit 1
}

jq -er '.result.value.data[0]' "$EVIDENCE_DIR/txv1-feature-account.json" \
  | base64 --decode \
  | od -An -tx1 -v \
  | tr -d ' \n' \
  >"$EVIDENCE_DIR/txv1-feature-data.hex"

readonly MEMORY_CURRENT=$(<"$CGROUP_DIR/memory.current")
readonly MEMORY_PEAK=$(<"$CGROUP_DIR/memory.peak")
readonly MEMORY_SWAP_CURRENT=$(<"$CGROUP_DIR/memory.swap.current")
readonly MEMORY_SWAP_PEAK=$(<"$CGROUP_DIR/memory.swap.peak")
readonly SOLANA_SHA256=$(sha256sum "$SOLANA_BIN" | awk '{print $1}')
readonly VALIDATOR_SHA256=$(sha256sum "$VALIDATOR_BIN" | awk '{print $1}')
readonly GENESIS_HASH=$(jq -er '.result' "$EVIDENCE_DIR/get-genesis-hash.json")
readonly SLOT=$(jq -er '.result' "$EVIDENCE_DIR/get-slot.json")
readonly RPC_CORE_VERSION=$(jq -er '.result."solana-core"' "$EVIDENCE_DIR/get-version.json")
readonly FEATURE_SET=$(jq -er '.result."feature-set"' "$EVIDENCE_DIR/get-version.json")
readonly FEATURE_DATA_HEX=$(<"$EVIDENCE_DIR/txv1-feature-data.hex")

printf '%s\n' "$SOLANA_VERSION" >"$EVIDENCE_DIR/solana-version.txt"
printf '%s\n' "$VALIDATOR_VERSION" >"$EVIDENCE_DIR/solana-test-validator-version.txt"
jq -n \
  --arg schema "aspis.v7.agave-txv1-runtime-readiness.v1" \
  --arg commit "$REQUIRED_COMMIT" \
  --arg solana_version "$SOLANA_VERSION" \
  --arg solana_sha "$SOLANA_SHA256" \
  --arg validator_version "$VALIDATOR_VERSION" \
  --arg validator_sha "$VALIDATOR_SHA256" \
  --arg rpc_core_version "$RPC_CORE_VERSION" \
  --argjson feature_set "$FEATURE_SET" \
  --arg genesis_hash "$GENESIS_HASH" \
  --argjson slot "$SLOT" \
  --arg feature_id "$FEATURE_ID" \
  --arg feature_owner "$FEATURE_OWNER" \
  --arg feature_data_hex "$FEATURE_DATA_HEX" \
  --arg cgroup "$CGROUP_RELATIVE" \
  --argjson memory_high "$MEMORY_HIGH" \
  --argjson memory_max "$MEMORY_MAX" \
  --argjson memory_swap_max "$MEMORY_SWAP_MAX" \
  --argjson memory_current "$MEMORY_CURRENT" \
  --argjson memory_peak "$MEMORY_PEAK" \
  --argjson memory_swap_current "$MEMORY_SWAP_CURRENT" \
  --argjson memory_swap_peak "$MEMORY_SWAP_PEAK" '
    {
      schema: $schema,
      release: {
        tag: "v4.2.0",
        commit: $commit,
        solanaVersion: $solana_version,
        solanaSha256: $solana_sha,
        validatorVersion: $validator_version,
        validatorSha256: $validator_sha
      },
      rpc: {
        healthy: true,
        coreVersion: $rpc_core_version,
        featureSet: $feature_set,
        genesisHash: $genesis_hash,
        finalizedSlot: $slot,
        boundToLoopback: true
      },
      txv1: {
        featureId: $feature_id,
        featureOwner: $feature_owner,
        featureDataHex: $feature_data_hex,
        activeAtGenesis: true,
        transactionVersion: 1,
        maximumSerializedBytes: 4096,
        capabilitySource: "official Agave v4.2.0 runtime plus active feature account"
      },
      cgroup: {
        path: $cgroup,
        memoryHighBytes: $memory_high,
        memoryMaxBytes: $memory_max,
        memorySwapMaxBytes: $memory_swap_max,
        memoryCurrentBytesAtCapture: $memory_current,
        memoryPeakBytesAtCapture: $memory_peak,
        memorySwapCurrentBytesAtCapture: $memory_swap_current,
        memorySwapPeakBytesAtCapture: $memory_swap_peak
      },
      lifecycleSuiteExecuted: false,
      programDeployed: false,
      transactionSigned: false,
      transactionSubmitted: false,
      readyForMaterializedElevenCaseSimulation: true
    }
  ' >"$EVIDENCE_DIR/readiness.json"

(
  cd "$EVIDENCE_DIR"
  sha256sum \
    get-genesis-hash.json \
    get-health.json \
    get-slot.json \
    get-version.json \
    readiness.json \
    solana-test-validator-help.txt \
    solana-test-validator-version.txt \
    solana-version.txt \
    txv1-feature-account.json \
    txv1-feature-data.hex \
    txv1-feature-status.txt \
    validator.log \
    >SHA256SUMS
)

echo "Agave v4.2.0 TxV1 runtime readiness: PASS"
echo "feature: $FEATURE_ID active"
echo "maximum TxV1 bytes: 4096"
echo "program deployments: 0"
echo "signed/submitted transactions: 0/0"
