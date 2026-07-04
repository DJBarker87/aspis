# ML-DSA Solana STARK Experiments

Scoped execution folder for the bounded `ML-DSA-44 via Winterfell 0.12 on Solana` project.

## Current Purpose

- Freeze the claim boundary
- Reproduce the vendored Yano baseline
- Prepare the source manifest and vector plan before starting AIR work
- Measure SHAKE-heavy Stage B feasibility before full AIR/prover work

## Commands

- Re-measure the vendored Yano baseline:

  ```bash
  experiments/mldsa-solana-stark/measure-yano-baseline.sh
  ```

- Measure the SHAKE-only `ExpandA` prototype:

  ```bash
  experiments/mldsa-solana-stark/run-shake-expanda-prototype.sh
  ```

- Measure the no-proof `ML-DSA-44` verification hash-path prototype:

  ```bash
  experiments/mldsa-solana-stark/run-verify-hash-path-prototype.sh
  ```

- Run the Stage B combined row / proof-size projection:

  ```bash
  experiments/mldsa-solana-stark/run-stage-b-projection.sh
  ```

## Outputs

- `results/mldsa-solana-stark/yano-baseline.json`
- `results/mldsa-solana-stark/shake-expanda-prototype.json`
- `results/mldsa-solana-stark/verify-hash-path-prototype.json`
- `results/mldsa-solana-stark/stage-b-projection.json`
