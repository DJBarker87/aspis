# ML-DSA Solana STARK Stage A Gate

## Status

`AMBER`

## Verified Evidence

- Claim boundary is now frozen in `docs/mldsa-solana-stark-claim-boundary.md`
- Source set is frozen in `docs/mldsa-solana-stark-source-manifest.md`
- `FIPS 204 Algorithm 8 ML-DSA.Verify_internal` call graph is pinned in
  `docs/mldsa-solana-stark-spec-map.md`
- Vendored Yano baseline artifact is frozen in `docs/mldsa-solana-stark-yano-baseline.md`
- Reproduced local Yano proof size:
  - `4211` bytes
- Published Yano `verify_stark` summary in the vendored snapshot:
  - mean `1,104,510` CU
  - median `1,110,510` CU
  - max `1,190,982` CU
- Solana reference limits currently being targeted:
  - `1,400,000` CU per transaction
  - `1232`-byte transaction size

## What This Means

- The current public Yano-style path is not already dead on arrival:
  - a small Winterfell proof can fit under the current Solana CU cap
  - staged upload is already part of the baseline design
- The current public Yano-style path is also not evidence that `ML-DSA-44` will fit:
  - the reproduced `4211`-byte proof is for a minimal affine AIR
  - `ML-DSA.Verify_internal` adds SHAKE-heavy hashing, decoding, NTT work, hint logic, and norm checks
- The project is therefore alive, but only as a measured feasibility study

## Gate Decision

- Proceed to Stage B
- Do not make any on-chain feasibility claim yet
- Do not open `ML-DSA-65`

## Immediate Next Work

1. Build the no-proof direct evaluator for `ML-DSA-44 Verify_internal`
2. Lock a pinned vector corpus for valid and invalid `sigVer` cases
3. Measure trace width and trace length before attempting proof generation
4. Stop immediately if the hash path already makes proof-size plausibility collapse
