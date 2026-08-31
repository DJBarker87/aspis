#!/usr/bin/env bash
set -euo pipefail

readonly FEATURE_ID="txv1aq4pp281K9um3tnPgkfX8UqtFT6wcVW3hNezGLL"
readonly FEATURE_OWNER="Feature111111111111111111111111111111111111"

fail() {
  echo "FAIL: $*" >&2
  exit 1
}

if [[ $# -ne 3 ]]; then
  cat >&2 <<'USAGE'
usage: scripts/v7_txv1_4k_feature_gate.sh \
  <solana-cli> <rpc-url> <new-evidence-directory>

This is a read-only TxV1/4-KiB capability gate. It calls getHealth,
getVersion, getSlot and getAccountInfo plus `solana feature status`; it never
builds, signs, deploys, simulates or submits a transaction.
USAGE
  exit 2
fi

readonly SOLANA_BIN=$1
readonly RPC_URL=$2
readonly EVIDENCE_DIR=$3
[[ -x "$SOLANA_BIN" ]] || fail "solana CLI is not executable: $SOLANA_BIN"
[[ "$EVIDENCE_DIR" == /* && "$EVIDENCE_DIR" != "/" ]] \
  || fail "evidence directory must be an explicit absolute non-root path"
[[ ! -e "$EVIDENCE_DIR" ]] || fail "refusing to overwrite evidence directory: $EVIDENCE_DIR"

for command_name in awk curl grep jq mkdir; do
  command -v "$command_name" >/dev/null || fail "missing required command: $command_name"
done

if command -v sha256sum >/dev/null 2>&1; then
  sha_file() { sha256sum "$1" | awk '{print $1}'; }
elif command -v shasum >/dev/null 2>&1; then
  sha_file() { shasum -a 256 "$1" | awk '{print $1}'; }
else
  fail "sha256sum or shasum is required"
fi

readonly VERSION_OUTPUT=$(NO_DNA=1 "$SOLANA_BIN" --version)
readonly VERSION_NUMBER=$(awk '{for (i=1; i<=NF; i++) if ($i ~ /^[0-9]+\.[0-9]+\.[0-9]+/) {print $i; exit}}' <<<"$VERSION_OUTPUT")
[[ -n "$VERSION_NUMBER" ]] || fail "cannot parse solana CLI version: $VERSION_OUTPUT"
readonly VERSION_MAJOR=${VERSION_NUMBER%%.*}
readonly VERSION_REST=${VERSION_NUMBER#*.}
readonly VERSION_MINOR=${VERSION_REST%%.*}
if (( VERSION_MAJOR < 4 || (VERSION_MAJOR == 4 && VERSION_MINOR < 2) )); then
  fail "Agave/Solana CLI 4.2+ is required: $VERSION_OUTPUT"
fi

mkdir -p "$EVIDENCE_DIR"
printf '%s\n' "$VERSION_OUTPUT" >"$EVIDENCE_DIR/solana-version.txt"

rpc() {
  local request=$1
  local output=$2
  curl --fail-with-body --silent --show-error --max-time 30 \
    -H 'content-type: application/json' \
    --data-binary "$request" \
    "$RPC_URL" >"$output"
}

rpc '{"jsonrpc":"2.0","id":1,"method":"getHealth"}' \
  "$EVIDENCE_DIR/get-health.json"
rpc '{"jsonrpc":"2.0","id":2,"method":"getVersion"}' \
  "$EVIDENCE_DIR/get-version.json"
rpc '{"jsonrpc":"2.0","id":3,"method":"getSlot","params":[{"commitment":"finalized"}]}' \
  "$EVIDENCE_DIR/get-finalized-slot.json"
rpc "{\"jsonrpc\":\"2.0\",\"id\":4,\"method\":\"getAccountInfo\",\"params\":[\"$FEATURE_ID\",{\"encoding\":\"base64\",\"commitment\":\"finalized\"}]}" \
  "$EVIDENCE_DIR/txv1-feature-account.json"

NO_DNA=1 "$SOLANA_BIN" feature status "$FEATURE_ID" \
  --url "$RPC_URL" >"$EVIDENCE_DIR/txv1-feature-status.txt"

jq -e '.result == "ok"' "$EVIDENCE_DIR/get-health.json" >/dev/null \
  || fail "RPC health gate failed"
jq -e '.result."solana-core" | type == "string" and length > 0' \
  "$EVIDENCE_DIR/get-version.json" >/dev/null || fail "RPC omitted the core version"
jq -e '.result | type == "number" and . >= 0' \
  "$EVIDENCE_DIR/get-finalized-slot.json" >/dev/null || fail "RPC omitted a finalized slot"
jq -e --arg owner "$FEATURE_OWNER" '
  .result.value != null and
  .result.value.owner == $owner and
  .result.value.executable == false and
  (.result.value.data[0] | type == "string" and startswith("AQ"))
' "$EVIDENCE_DIR/txv1-feature-account.json" >/dev/null \
  || fail "TxV1 feature account is absent, malformed or inactive"
grep -q "$FEATURE_ID" "$EVIDENCE_DIR/txv1-feature-status.txt" \
  || fail "feature-status output omitted the TxV1 feature"
# Match `active` as its own table field. A plain substring test would also
# match `inactive`, which is exactly the state this gate must reject.
grep -Eqi '(^|[[:space:]|])active([[:space:]|]|$)' \
  "$EVIDENCE_DIR/txv1-feature-status.txt" \
  || fail "TxV1 feature is not active"

readonly FINALIZED_SLOT=$(jq -er '.result' "$EVIDENCE_DIR/get-finalized-slot.json")
readonly RPC_CORE_VERSION=$(jq -er '.result."solana-core"' "$EVIDENCE_DIR/get-version.json")
readonly FEATURE_SET=$(jq -er '.result."feature-set"' "$EVIDENCE_DIR/get-version.json")
readonly FEATURE_ACCOUNT_SHA=$(sha_file "$EVIDENCE_DIR/txv1-feature-account.json")
readonly SOLANA_SHA=$(sha_file "$SOLANA_BIN")

jq -n \
  --arg rpcUrl "$RPC_URL" \
  --arg cliVersion "$VERSION_OUTPUT" \
  --arg cliSha256 "$SOLANA_SHA" \
  --arg rpcCoreVersion "$RPC_CORE_VERSION" \
  --argjson featureSet "$FEATURE_SET" \
  --argjson finalizedSlot "$FINALIZED_SLOT" \
  --arg featureId "$FEATURE_ID" \
  --arg featureOwner "$FEATURE_OWNER" \
  --arg featureAccountResponseSha256 "$FEATURE_ACCOUNT_SHA" '
  {
    schema: "aspis.v7.txv1-4k-read-only-feature-gate.v1",
    rpcUrl: $rpcUrl,
    cli: {version: $cliVersion, sha256: $cliSha256},
    rpc: {
      healthy: true,
      coreVersion: $rpcCoreVersion,
      featureSet: $featureSet,
      finalizedSlot: $finalizedSlot
    },
    txv1: {
      featureId: $featureId,
      featureOwner: $featureOwner,
      featureAccountResponseSha256: $featureAccountResponseSha256,
      activeAtFinalizedCommitment: true,
      transactionVersion: 1,
      maximumSerializedBytes: 4096
    },
    readOnly: true,
    simulated: false,
    signed: false,
    submitted: false,
    deployed: false,
    pass: true
  }
' >"$EVIDENCE_DIR/gate.json"

echo "TxV1/4-KiB read-only feature gate PASS: $EVIDENCE_DIR/gate.json"
