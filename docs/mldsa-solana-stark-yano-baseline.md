# ML-DSA Solana STARK Yano Baseline

This note freezes the currently vendored `third_party/solana-pqzk-fullchain` snapshot as the comparison
baseline for the `ML-DSA` project.

## Verified Local Facts

- Baseline path: `third_party/solana-pqzk-fullchain`
- Public repo referenced by the vendored snapshot: `pqzk-labs/solana-pqzk-fullchain`
- Proof system dependency in the vendored lockfile:
  - `winterfell 0.12.0`
  - `winter-air 0.12.3`
  - `winter-verifier 0.12.3`
- Published benchmark summary in the vendored snapshot:
  - `finalize_sig`: mean `501,263`, median `499,946`, min `467,360`, max `543,534`
  - `verify_stark`: mean `1,104,510`, median `1,110,510`, min `988,312`, max `1,190,982`
- Solana-side engineering choices in the vendored snapshot:
  - staged upload chunk size: `900` bytes
  - requested CU limits: `700,000` for signature phase, `1,400,000` for STARK phase
  - account caps:
    - `MAX_ACCOUNT_BYTES = 10,240`
    - `MAX_CHAT_PAYLOAD = 10,068`
    - `MAX_SIG_PAYLOAD = 10,156`
- SLH-DSA signature size in the vendored snapshot: `7,856` bytes

## Local Reproduction Hook

Use:

```bash
experiments/mldsa-solana-stark/measure-yano-baseline.sh
```

This script reruns the vendored `stark-prover` with a fixed digest, measures the produced `proof.bin`,
and writes a machine-readable summary to:

```text
results/mldsa-solana-stark/yano-baseline.json
```

## Current Comparison Discipline

- Compare `ML-DSA` only against this pinned baseline and only on explicit metrics:
  - proof bytes
  - verifier CU
  - CU per proof byte
  - signature bytes
- Do not describe this as “same workload.” Yano's current public artifact uses:
  - native on-chain `SLH-DSA` verification
  - a minimal affine-counter AIR bound to `SHA256(cipher)`
- The `ML-DSA` project changes the proven computation materially. Any comparison must say so.

## Open Checks Still Required

- The vendored snapshot does not by itself prove the exact upstream git commit
- The public ePrint text and the current public repo may drift; comparison claims must cite the exact
  artifact actually used
