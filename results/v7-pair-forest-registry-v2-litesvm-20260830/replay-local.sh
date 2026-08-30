#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "usage: $0 <new-output-directory>" >&2
  exit 2
fi

ROOT=$(git rev-parse --show-toplevel)
cd "$ROOT"

OUT=$1
if [[ -e "$OUT" ]]; then
  echo "refusing to overwrite $OUT" >&2
  exit 2
fi
mkdir -p "$OUT"

BUNDLE=results/v7-pair-forest-registry-v2-litesvm-20260830
HARNESS=results/v7-pair-forest-combined-rejection-litesvm-20260828/harness
FIXTURES=results/v7-pair-forest-combined-rejection-litesvm-20260828/evidence

NO_DNA=1 cargo build --release --manifest-path "$HARNESS/Cargo.toml" --locked --offline
BIN="$HARNESS/target/release/aspis-v7-pair-forest-combined-rejection"
POOL="$BUNDLE/artifacts/aspis_pool.so"
VERIFIER="$BUNDLE/artifacts/aspis_verifier.so"
REGISTRY="$BUNDLE/artifacts/aspis_registry.so"
DOUBLE="$BUNDLE/artifacts/aspis_pair_forest_result_double.so"

run_case() {
  local name=$1
  local proof=$2
  local scenario=$3
  local populated=$4
  local operation=$5
  "$BIN" "$POOL" "$VERIFIER" "$REGISTRY" "$DOUBLE" \
    "$OUT/$name.json" "$proof" "$scenario" 1400000 asq8 \
    "$populated" "$operation"
}

TRANSFER="$FIXTURES/v7-pair-forest-transfer-strict-work-canonical-fixed.bin"
TRANSFER_ROLLOVER="$FIXTURES/transfer-rollover-strict-canonical.bin"
WITHDRAWAL="$FIXTURES/withdrawal-same-page-counter0-strict-canonical.bin"
WITHDRAWAL_ROLLOVER="$FIXTURES/withdrawal-rollover-counter0-strict-canonical.bin"

run_case transfer-same-success "$TRANSFER" success 13 transfer
run_case transfer-rollover-success "$TRANSFER_ROLLOVER" success 255 transfer
run_case withdrawal-same-success "$WITHDRAWAL" success 13 withdrawal
run_case withdrawal-rollover-success "$WITHDRAWAL_ROLLOVER" success 255 withdrawal
run_case proof-rejection "$TRANSFER" proof-rejection 13 transfer
run_case wrong-release "$TRANSFER" wrong-release 13 transfer
run_case stale-lane "$TRANSFER" stale-lane 13 transfer
run_case replay-nullifier "$TRANSFER" replay 13 transfer
run_case malformed-result "$TRANSFER" malformed-result 13 transfer
run_case mutated-result "$TRANSFER" mutated-result 13 transfer
run_case withdrawal-cpi-failure "$WITHDRAWAL" withdrawal-cpi-failure 13 withdrawal

for ledger in "$OUT"/*.json; do
  jq -e '.schema == "aspis.v7-pair-forest.registry-v2-combined-litesvm.v3"' \
    "$ledger" >/dev/null
done

echo "Registry V2 combined replay PASS: $OUT"
