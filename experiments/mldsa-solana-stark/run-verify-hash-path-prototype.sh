#!/usr/bin/env bash

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
CRATE_DIR="${ROOT_DIR}/experiments/mldsa-solana-stark/verify-hash-path-prototype"
OUT_DIR="${ROOT_DIR}/results/mldsa-solana-stark"
OUT_JSON="${OUT_DIR}/verify-hash-path-prototype.json"

mkdir -p "${OUT_DIR}"

cargo run \
  --manifest-path "${CRATE_DIR}/Cargo.toml" \
  --release \
  -- \
  --out "${OUT_JSON}"

echo "wrote ${OUT_JSON}"
