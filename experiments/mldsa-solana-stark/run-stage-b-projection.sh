#!/usr/bin/env bash

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
CRATE_DIR="${ROOT_DIR}/experiments/mldsa-solana-stark/stage-b-projection"
OUT_DIR="${ROOT_DIR}/results/mldsa-solana-stark"
OUT_JSON="${OUT_DIR}/stage-b-projection.json"

mkdir -p "${OUT_DIR}"

cargo run \
  --manifest-path "${CRATE_DIR}/Cargo.toml" \
  --release \
  -- \
  --out "${OUT_JSON}"

echo "wrote ${OUT_JSON}"
