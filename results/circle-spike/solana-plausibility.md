# Circle Solana plausibility

Generated: 2026-04-20T08:17:59.777736+00:00

Compilation status: `failed`.

- Command: `cargo-build-sbf --manifest-path programs/circle-p3-verifier/Cargo.toml --sbf-out-dir target/circle-p3-sbf`
- Stdout: `results/circle-spike/raw/sbf/build.stdout`
- Stderr: `results/circle-spike/raw/sbf/build.stderr`

## Proof sizes

- `fibonacci8` proof_bytes=`29363` exceeds_tx_limit=`true` min_tx_count=`24` upload_chunks_512b=`58`
- `square8` proof_bytes=`22066` exceeds_tx_limit=`true` min_tx_count=`18` upload_chunks_512b=`44`
- `affine-pair16` proof_bytes=`39028` exceeds_tx_limit=`true` min_tx_count=`32` upload_chunks_512b=`77`

## Cost projection

- Predicted CU: `7267870` feasible=`false` budget_fraction=`5.191` transport_pressure=`31.679`
- Verification core CU: `7221369`
- Transport overhead CU: `45150`
- Query soundness lower bound: `28.00` bits target=`100.00` meets_target=`false`
- Feasibility reasons:
  - predicted CU exceeds the transaction compute budget
  - query-controlled soundness lower bound 28.0 bits is below the 100.0-bit target

## Blockers

- error: failed to get `p3-air` as a dependency of package `circle-p3-core v0.1.0 (/Users/dominic/ZK/crates/circle-p3-core)`
- feature `edition2024` is required
- The package requires the Cargo feature called `edition2024`, but that feature is not stabilized in this version of Cargo (1.84.0 (12fe57a9d 2025-04-07)).
