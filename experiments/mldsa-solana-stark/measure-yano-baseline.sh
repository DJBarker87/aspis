#!/usr/bin/env bash

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
YANO_DIR="${ROOT_DIR}/third_party/solana-pqzk-fullchain"
PROVER_DIR="${YANO_DIR}/crates/stark-prover"
OUT_DIR="${ROOT_DIR}/results/mldsa-solana-stark"
OUT_JSON="${OUT_DIR}/yano-baseline.json"
FIXED_DIGEST="000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"

mkdir -p "${OUT_DIR}"

winterfell_version="$(rg -n -A2 'name = \"winterfell\"' "${YANO_DIR}/Cargo.lock" | awk -F'"' '/version = / { print $2; exit }')"
winter_air_version="$(rg -n -A2 'name = \"winter-air\"' "${YANO_DIR}/Cargo.lock" | awk -F'"' '/version = / { print $2; exit }')"
winter_verifier_version="$(rg -n -A2 'name = \"winter-verifier\"' "${YANO_DIR}/Cargo.lock" | awk -F'"' '/version = / { print $2; exit }')"

pushd "${PROVER_DIR}" >/dev/null
cargo run -p stark-prover --release -- gen "${FIXED_DIGEST}" >/tmp/mldsa_yano_prover.log 2>&1
proof_bytes="$(wc -c < proof.bin | tr -d ' ')"
popd >/dev/null

finalize_mean="$(awk -F': ' '/Mean CU/ { print $2; exit }' "${YANO_DIR}/examples/benchmarks/statistics.txt" | tr -d ',')"
finalize_median="$(awk -F': ' '/Median CU/ { print $2; exit }' "${YANO_DIR}/examples/benchmarks/statistics.txt" | sed -n '1p' | tr -d ',')"
finalize_min="$(awk -F': ' '/Minimum CU/ { print $2; exit }' "${YANO_DIR}/examples/benchmarks/statistics.txt" | tr -d ',')"
finalize_max="$(awk -F': ' '/Maximum CU/ { print $2; exit }' "${YANO_DIR}/examples/benchmarks/statistics.txt" | sed -n '1p' | tr -d ',')"
verify_mean="$(awk -F': ' '/Mean CU/ { print $2 }' "${YANO_DIR}/examples/benchmarks/statistics.txt" | sed -n '2p' | tr -d ',')"
verify_median="$(awk -F': ' '/Median CU/ { print $2 }' "${YANO_DIR}/examples/benchmarks/statistics.txt" | sed -n '2p' | tr -d ',')"
verify_min="$(awk -F': ' '/Minimum CU/ { print $2 }' "${YANO_DIR}/examples/benchmarks/statistics.txt" | sed -n '2p' | tr -d ',')"
verify_max="$(awk -F': ' '/Maximum CU/ { print $2 }' "${YANO_DIR}/examples/benchmarks/statistics.txt" | sed -n '2p' | tr -d ',')"

cat > "${OUT_JSON}" <<EOF
{
  "source": {
    "vendored_path": "third_party/solana-pqzk-fullchain",
    "fixed_digest_hex": "${FIXED_DIGEST}"
  },
  "winterfell": {
    "winterfell": "${winterfell_version}",
    "winter_air": "${winter_air_version}",
    "winter_verifier": "${winter_verifier_version}"
  },
  "local_measurement": {
    "proof_bytes": ${proof_bytes}
  },
  "published_benchmark_summary": {
    "n_runs": 100,
    "finalize_sig": {
      "mean_cu": ${finalize_mean},
      "median_cu": ${finalize_median},
      "min_cu": ${finalize_min},
      "max_cu": ${finalize_max}
    },
    "verify_stark": {
      "mean_cu": ${verify_mean},
      "median_cu": ${verify_median},
      "min_cu": ${verify_min},
      "max_cu": ${verify_max}
    }
  },
  "solana_side_parameters": {
    "body_chunk_bytes": 900,
    "finalize_sig_cu_limit": 700000,
    "verify_stark_cu_limit": 1400000,
    "max_account_bytes": 10240,
    "max_chat_payload": 10068,
    "max_sig_payload": 10156,
    "slh_dsa_signature_bytes": 7856
  }
}
EOF

echo "wrote ${OUT_JSON}"
cat "${OUT_JSON}"
