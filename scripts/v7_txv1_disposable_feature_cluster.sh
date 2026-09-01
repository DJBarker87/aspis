#!/usr/bin/env bash
set -euo pipefail

# Start one task-owned Agave 4.2+ validator with the frozen audit binaries and
# the runtime's TxV1 feature active at genesis. An optional child command runs
# with the RPC URL and ephemeral payer path in its environment. The ledger and
# signing key are always destroyed by the EXIT trap.

readonly FEATURE_ID="txv1aq4pp281K9um3tnPgkfX8UqtFT6wcVW3hNezGLL"
readonly FEATURE_OWNER="Feature111111111111111111111111111111111111"
readonly AGAVE_GENESIS_PROGRAM_OWNER="BPFLoaderUpgradeab1e11111111111111111111111"
readonly DISPOSABLE_ACK="I_ACKNOWLEDGE_AUDIT_ONLY_IDENTITIES_AND_DISPOSABLE_FUNDS"
readonly REPO_ROOT=$(cd "$(dirname "$0")/.." && pwd)
readonly CONFIG="$REPO_ROOT/config/v7-txv1-devnet-harness-20260901.json"

fail() {
  echo "FAIL: $*" >&2
  exit 1
}

usage() {
  cat >&2 <<'USAGE'
usage: scripts/v7_txv1_disposable_feature_cluster.sh \
  <agave-4.2+-bin-dir> <new-evidence-dir> \
  I_ACKNOWLEDGE_AUDIT_ONLY_IDENTITIES_AND_DISPOSABLE_FUNDS [-- command ...]

The command is optional. When supplied it receives:
  ASPIS_TXV1_DISPOSABLE_RPC_URL
  ASPIS_TXV1_DISPOSABLE_PAYER_KEYPAIR
  ASPIS_TXV1_DISPOSABLE_PAYER_PUBKEY

The keypair is task-owned temporary material. Do not print or copy it.
USAGE
  exit 2
}

[[ $# -ge 3 ]] || usage
readonly AGAVE_BIN_DIR=$1
readonly EVIDENCE_DIR=$2
readonly ACK=$3
shift 3
if [[ $# -gt 0 ]]; then
  [[ $1 == -- ]] || usage
  shift
fi

[[ "$ACK" == "$DISPOSABLE_ACK" ]] || fail "missing exact disposable-test acknowledgement"
[[ "$EVIDENCE_DIR" == /* && "$EVIDENCE_DIR" != / ]] \
  || fail "evidence directory must be an explicit absolute non-root path"
[[ ! -e "$EVIDENCE_DIR" ]] || fail "refusing to overwrite evidence: $EVIDENCE_DIR"
[[ -f "$CONFIG" ]] || fail "missing harness configuration"
jq -e '.mainnetReady == false and .identitySet.auditOnly == true and
  .identitySet.productionApproved == false' "$CONFIG" >/dev/null \
  || fail "configuration does not identify an audit-only disposable identity set"

for command_name in awk curl date find git grep jq od openssl sed seq shasum sort xargs; do
  command -v "$command_name" >/dev/null || fail "missing required command: $command_name"
done
for binary in solana solana-keygen solana-test-validator; do
  [[ -x "$AGAVE_BIN_DIR/$binary" ]] || fail "missing executable: $AGAVE_BIN_DIR/$binary"
done

readonly VERSION_OUTPUT=$(NO_DNA=1 "$AGAVE_BIN_DIR/solana" --version)
readonly CORE_VERSION=$(sed -E 's/.* ([0-9]+\.[0-9]+\.[^ ]+).*/\1/' <<<"$VERSION_OUTPUT")
readonly CORE_MAJOR=${CORE_VERSION%%.*}
readonly CORE_REST=${CORE_VERSION#*.}
readonly CORE_MINOR=${CORE_REST%%.*}
if (( CORE_MAJOR < 4 || (CORE_MAJOR == 4 && CORE_MINOR < 2) )); then
  fail "Agave 4.2+ required; found: $VERSION_OUTPUT"
fi

readonly RPC_PORT=${ASPIS_TXV1_LOCAL_RPC_PORT:-18901}
[[ "$RPC_PORT" =~ ^[0-9]+$ ]] || fail "RPC port must be numeric"
readonly RPC_URL="http://127.0.0.1:$RPC_PORT"
readonly WORK_DIR=$(mktemp -d "${TMPDIR:-/tmp}/aspis-v7-txv1-feature-cluster.XXXXXX")
readonly LEDGER="$WORK_DIR/ledger"
readonly PAYER="$WORK_DIR/disposable-payer.json"
readonly SOURCE_AUTHORITY="$WORK_DIR/disposable-source-authority.json"
VALIDATOR_PID=""

cleanup() {
  if [[ -n "$VALIDATOR_PID" ]]; then
    kill "$VALIDATOR_PID" 2>/dev/null || true
    wait "$VALIDATOR_PID" 2>/dev/null || true
  fi
  case "$WORK_DIR" in
    */aspis-v7-txv1-feature-cluster.*) rm -rf -- "$WORK_DIR" ;;
    *) echo "refusing to remove unexpected temporary path: $WORK_DIR" >&2 ;;
  esac
}
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

mkdir -p "$EVIDENCE_DIR/program-accounts" "$EVIDENCE_DIR/program-binary-hashes"
NO_DNA=1 "$AGAVE_BIN_DIR/solana-keygen" new --no-bip39-passphrase --silent \
  --force --outfile "$PAYER"
readonly PAYER_PUBKEY=$(NO_DNA=1 "$AGAVE_BIN_DIR/solana-keygen" pubkey "$PAYER")
NO_DNA=1 "$AGAVE_BIN_DIR/solana-keygen" new --no-bip39-passphrase --silent \
  --force --outfile "$SOURCE_AUTHORITY"
readonly SOURCE_AUTHORITY_PUBKEY=$(NO_DNA=1 "$AGAVE_BIN_DIR/solana-keygen" pubkey "$SOURCE_AUTHORITY")

if [[ -n "${ASPIS_TXV1_LIVE_GENESIS_PREPARER:-}" ]]; then
  [[ -x "$ASPIS_TXV1_LIVE_GENESIS_PREPARER" ]] \
    || fail "live genesis preparer is not executable"
  readonly LIVE_GENESIS_DIR="$WORK_DIR/live-genesis"
  "$ASPIS_TXV1_LIVE_GENESIS_PREPARER" "$REPO_ROOT" "$CONFIG" \
    "$PAYER_PUBKEY" "$SOURCE_AUTHORITY_PUBKEY" "$LIVE_GENESIS_DIR" >"$EVIDENCE_DIR/live-genesis.json"
  jq -e '.schema == "aspis.v7.disposable-live-genesis.v1" and .auditOnly == true' \
    "$EVIDENCE_DIR/live-genesis.json" >/dev/null \
    || fail "live genesis preparer returned an invalid manifest"
fi

declare -a VALIDATOR_ARGS=(
  --reset --quiet --ledger "$LEDGER" --bind-address 127.0.0.1
  --rpc-port "$RPC_PORT" --warp-slot 150 --mint "$PAYER_PUBKEY"
)
if [[ -n "${ASPIS_TXV1_LIVE_GENESIS_PREPARER:-}" ]]; then
  while IFS=$'\t' read -r address account_file; do
    [[ "$account_file" == "$LIVE_GENESIS_DIR"/* && -f "$account_file" ]] \
      || fail "live genesis account escaped task directory"
    VALIDATOR_ARGS+=(--account "$address" "$account_file")
  done < <(jq -r '.accounts[] | [.address,.file] | @tsv' \
    "$EVIDENCE_DIR/live-genesis.json")
fi
while IFS=$'\t' read -r name id loader relative expected_sha; do
  artifact="$REPO_ROOT/$relative"
  [[ -f "$artifact" ]] || fail "missing frozen $name binary: $relative"
  [[ "$(shasum -a 256 "$artifact" | awk '{print $1}')" == "$expected_sha" ]] \
    || fail "frozen $name binary hash mismatch"
  case "$loader" in
    BPFLoader2111111111111111111111111111111111)
      VALIDATOR_ARGS+=(--bpf-program "$id" "$artifact") ;;
    BPFLoaderUpgradeab1e11111111111111111111111)
      VALIDATOR_ARGS+=(--upgradeable-program "$id" "$artifact" none) ;;
    *) fail "unsupported loader for $name: $loader" ;;
  esac
done < <(jq -r '.identitySet.programs[] | [.name,.id,.loader,.binary,.sha256] | @tsv' "$CONFIG")

jq -n --arg ledgerTemplate '${TMPDIR:-/tmp}/aspis-v7-txv1-feature-cluster.XXXXXX/ledger' \
  --arg rpcUrl "$RPC_URL" --argjson warpSlot 150 \
  --arg featureId "$FEATURE_ID" --arg activationMechanism \
  'Agave test-validator default genesis feature set; feature is not passed to --deactivate-feature' \
  '{ledgerTemplate:$ledgerTemplate,rpcUrl:$rpcUrl,bindAddress:"127.0.0.1",
    reset:true,warpSlot:$warpSlot,featureId:$featureId,
    activationMechanism:$activationMechanism,existingLedgerAllowed:false,
    cleanup:"EXIT/INT/TERM trap removes only the validated mktemp task directory"}' \
  >"$EVIDENCE_DIR/ledger-configuration.json"

NO_DNA=1 "$AGAVE_BIN_DIR/solana-test-validator" "${VALIDATOR_ARGS[@]}" \
  >"$EVIDENCE_DIR/validator.log" 2>&1 &
VALIDATOR_PID=$!

rpc() {
  curl --fail-with-body --silent --show-error --max-time 60 \
    -H 'content-type: application/json' --data-binary "$1" "$RPC_URL"
}

for _ in $(seq 1 150); do
  if rpc '{"jsonrpc":"2.0","id":1,"method":"getHealth"}' \
    2>/dev/null | jq -e '.result == "ok"' >/dev/null 2>&1; then
    break
  fi
  sleep 0.2
done
rpc '{"jsonrpc":"2.0","id":1,"method":"getHealth"}' \
  | jq . >"$EVIDENCE_DIR/get-health.json"
rpc '{"jsonrpc":"2.0","id":2,"method":"getGenesisHash"}' \
  | jq . >"$EVIDENCE_DIR/get-genesis-hash.json"
rpc '{"jsonrpc":"2.0","id":3,"method":"getVersion"}' \
  | jq . >"$EVIDENCE_DIR/get-version.json"
rpc '{"jsonrpc":"2.0","id":4,"method":"getSlot","params":[{"commitment":"finalized"}]}' \
  | jq . >"$EVIDENCE_DIR/get-finalized-slot.json"
rpc "{\"jsonrpc\":\"2.0\",\"id\":5,\"method\":\"getAccountInfo\",\"params\":[\"$FEATURE_ID\",{\"encoding\":\"base64\",\"commitment\":\"finalized\"}]}" \
  | jq . >"$EVIDENCE_DIR/txv1-feature-account.json"

NO_DNA=1 "$AGAVE_BIN_DIR/solana" feature status --display-all --url "$RPC_URL" \
  >"$EVIDENCE_DIR/runtime-feature-set.txt"
grep -F "$FEATURE_ID" "$EVIDENCE_DIR/runtime-feature-set.txt" \
  >"$EVIDENCE_DIR/txv1-feature-status.txt" \
  || fail "TxV1 feature is missing from runtime feature status"

feature_data=$(jq -er --arg owner "$FEATURE_OWNER" '
  select(.result.value != null and .result.value.owner == $owner and
    .result.value.executable == false) | .result.value.data[0]
' "$EVIDENCE_DIR/txv1-feature-account.json") \
  || fail "TxV1 feature account is absent or malformed"
declare -a feature_octets
feature_octets=($(printf '%s' "$feature_data" | openssl base64 -d -A | od -An -tu1))
[[ ${#feature_octets[@]} -eq 9 && ${feature_octets[0]} -eq 1 ]] \
  || fail "TxV1 feature account is not canonically activated"
activation_slot=0
for byte_index in {1..8}; do
  activation_slot=$((activation_slot + feature_octets[byte_index] * (1 << (8 * (byte_index - 1)))))
done
[[ $activation_slot -eq 0 ]] || fail "TxV1 feature was not activated at genesis"

while IFS=$'\t' read -r name id configured_loader expected_sha; do
  rpc "{\"jsonrpc\":\"2.0\",\"id\":6,\"method\":\"getAccountInfo\",\"params\":[\"$id\",{\"encoding\":\"base64\",\"commitment\":\"finalized\"}]}" \
    | jq . >"$EVIDENCE_DIR/program-accounts/$name.json"
  jq -e --arg owner "$AGAVE_GENESIS_PROGRAM_OWNER" \
    '.result.value != null and .result.value.executable == true and .result.value.owner == $owner' \
    "$EVIDENCE_DIR/program-accounts/$name.json" >/dev/null \
    || fail "$name program account observed Agave genesis loader/executable gate failed"
  dumped="$WORK_DIR/$name.so"
  NO_DNA=1 "$AGAVE_BIN_DIR/solana" program dump --url "$RPC_URL" "$id" "$dumped" \
    >"$EVIDENCE_DIR/program-binary-hashes/$name.dump.log" 2>&1
  actual_sha=$(shasum -a 256 "$dumped" | awk '{print $1}')
  printf '%s  %s.so\n' "$actual_sha" "$name" \
    >"$EVIDENCE_DIR/program-binary-hashes/$name.sha256"
  [[ "$actual_sha" == "$expected_sha" ]] || fail "$name deployed binary hash mismatch"
done < <(jq -r '.identitySet.programs[] | [.name,.id,.loader,.sha256] | @tsv' "$CONFIG")

jq -n --arg generatedAt "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
  --arg revision "$(git -C "$REPO_ROOT" rev-parse HEAD)" \
  --arg agave "$VERSION_OUTPUT" --arg rpcUrl "$RPC_URL" \
  --arg genesisHash "$(jq -er '.result' "$EVIDENCE_DIR/get-genesis-hash.json")" \
  --arg coreVersion "$(jq -er '.result."solana-core"' "$EVIDENCE_DIR/get-version.json")" \
  --argjson runtimeFeatureSet "$(jq -er '.result."feature-set"' "$EVIDENCE_DIR/get-version.json")" \
  --arg featureId "$FEATURE_ID" --argjson activationSlot "$activation_slot" \
  --arg payerPubkey "$PAYER_PUBKEY" --slurpfile config "$CONFIG" \
  '{schema:"aspis.v7.txv1-disposable-feature-cluster.v1",generatedAt:$generatedAt,
    repository:{revision:$revision},classification:"DISPOSABLE FEATURE-ACTIVE CLUSTER READY",
    agave:{version:$agave,coreVersion:$coreVersion,runtimeFeatureSet:$runtimeFeatureSet},
    cluster:{kind:"disposable-local-validator",rpcUrl:$rpcUrl,genesisHash:$genesisHash,
      feature:{id:$featureId,active:true,activationSlot:$activationSlot}},
    identities:{auditOnly:true,explicitlyAcknowledged:true,
      configuredPrograms:$config[0].identitySet.programs,
      observedAgaveGenesisProgramOwner:"BPFLoaderUpgradeab1e11111111111111111111111",
      loaderDistinctionRecorded:true},
    wallet:{pubkey:$payerPubkey,ephemeral:true,keypairCommitted:false,cleanupRequired:true},
    localFinalizedLifecycleComplete:false,publicFinalizedDevnetLifecycleComplete:false,
    publicDevnetFeatureActive:false,mainnetReady:false,realFundsUsed:false}' \
  >"$EVIDENCE_DIR/cluster.json"

if [[ $# -gt 0 ]]; then
  export ASPIS_TXV1_DISPOSABLE_RPC_URL="$RPC_URL"
  export ASPIS_TXV1_DISPOSABLE_PAYER_KEYPAIR="$PAYER"
  export ASPIS_TXV1_DISPOSABLE_PAYER_PUBKEY="$PAYER_PUBKEY"
  export ASPIS_TXV1_DISPOSABLE_SOURCE_AUTHORITY_KEYPAIR="$SOURCE_AUTHORITY"
  export ASPIS_TXV1_DISPOSABLE_AGAVE_BIN_DIR="$AGAVE_BIN_DIR"
  "$@" >"$EVIDENCE_DIR/child.stdout" 2>"$EVIDENCE_DIR/child.stderr"
fi

(
  cd "$EVIDENCE_DIR"
  find . -type f ! -name SHA256SUMS -print0 | sort -z \
    | xargs -0 shasum -a 256 >SHA256SUMS
)
echo "DISPOSABLE FEATURE-ACTIVE CLUSTER READY: $EVIDENCE_DIR/cluster.json"
