#!/usr/bin/env bash
set -euo pipefail

fail() {
  echo "FAIL: $*" >&2
  exit 1
}

readonly CLUSTER_ACK="I_ACKNOWLEDGE_AUDIT_ONLY_IDENTITIES_AND_DISPOSABLE_FUNDS"
readonly DEPOSIT_ACK="I_ACKNOWLEDGE_256_DISPOSABLE_SEQUENTIAL_DEPOSITS"
[[ $# -eq 6 ]] || fail "usage: $0 <agave-bin-dir> <pool-audit-so-relative-to-repo> <build-manifest.json> <focused-builder-dir> <new-evidence-dir> I_ACKNOWLEDGE_256_DISPOSABLE_SEQUENTIAL_DEPOSITS"
readonly AGAVE_BIN_DIR=$1
readonly POOL_BINARY_RELATIVE=$2
readonly BUILD_MANIFEST=$3
readonly BUILDER_DIR=$4
readonly EVIDENCE_DIR=$5
readonly ACK=$6
readonly REPO_ROOT=$(cd "$(dirname "$0")/.." && pwd)
readonly BASE_CONFIG="$REPO_ROOT/config/v7-txv1-devnet-harness-20260901.json"

[[ "$ACK" == "$DEPOSIT_ACK" ]] || fail "missing exact sequential-deposit acknowledgement"
[[ "$POOL_BINARY_RELATIVE" != /* && "$POOL_BINARY_RELATIVE" != *..* ]] \
  || fail "Pool artifact must be a safe repository-relative path"
readonly POOL_BINARY="$REPO_ROOT/$POOL_BINARY_RELATIVE"
[[ -f "$POOL_BINARY" && -f "$BUILD_MANIFEST" ]] || fail "Pool audit artifact or manifest missing"
[[ "$BUILD_MANIFEST" == /* ]] || fail "build manifest path must be absolute"
[[ "$EVIDENCE_DIR" == /* && "$EVIDENCE_DIR" != / && ! -e "$EVIDENCE_DIR" ]] \
  || fail "evidence directory must be new, absolute and non-root"
for builder in prepare-live-genesis build-live-pool-initialize create-live-operation-secrets build-live-pool-deposit; do
  [[ -x "$BUILDER_DIR/$builder" ]] || fail "missing focused builder: $builder"
done

readonly WORK_DIR=$(mktemp -d "${TMPDIR:-/tmp}/aspis-v7-deposit-cu-config.XXXXXX")
cleanup() {
  case "$WORK_DIR" in
    */aspis-v7-deposit-cu-config.*) rm -rf -- "$WORK_DIR" ;;
    *) echo "refusing unexpected cleanup path: $WORK_DIR" >&2 ;;
  esac
}
trap cleanup EXIT

readonly POOL_SHA=$(shasum -a 256 "$POOL_BINARY" | awk '{print $1}')
readonly MANIFEST_SHA=$(jq -er '.artifact.sha256' "$BUILD_MANIFEST")
readonly MANIFEST_FEATURE=$(jq -er '.feature' "$BUILD_MANIFEST")
[[ "$POOL_SHA" == "$MANIFEST_SHA" && "$MANIFEST_FEATURE" == "pair-forest-deposit-invariant-audit" ]] \
  || fail "Pool artifact does not match its deposit-audit build manifest"
readonly AUDIT_CONFIG="$WORK_DIR/config.json"
jq --arg binary "$POOL_BINARY_RELATIVE" --arg sha "$POOL_SHA" '
  .identitySet.programs |= map(if .name == "pool" then .binary=$binary | .sha256=$sha else . end) |
  .depositInvariantAudit={enabled:true,defaultOff:true,feature:"pair-forest-deposit-invariant-audit",
    productionApproved:false}' "$BASE_CONFIG" >"$AUDIT_CONFIG"

export ASPIS_TXV1_HARNESS_CONFIG="$AUDIT_CONFIG"
export ASPIS_V7_PAIR_FOREST_DEPOSIT_CU_AUDIT="$DEPOSIT_ACK"
export ASPIS_TXV1_LIVE_GENESIS_PREPARER="$BUILDER_DIR/prepare-live-genesis"
export ASPIS_V7_LIVE_POOL_INITIALIZE_BUILDER="$BUILDER_DIR/build-live-pool-initialize"
export ASPIS_V7_LIVE_OPERATION_SECRET_BUILDER="$BUILDER_DIR/create-live-operation-secrets"
export ASPIS_V7_LIVE_POOL_DEPOSIT_BUILDER="$BUILDER_DIR/build-live-pool-deposit"
export ASPIS_V7_DEPOSIT_AUDIT_BUILD_MANIFEST="$BUILD_MANIFEST"

"$REPO_ROOT/scripts/v7_txv1_disposable_feature_cluster.sh" \
  "$AGAVE_BIN_DIR" "$EVIDENCE_DIR" "$CLUSTER_ACK" -- \
  "$REPO_ROOT/scripts/v7_pair_forest_deposit_cu_child.sh" "$EVIDENCE_DIR/sequential-deposits"
