# Phase 1 Cost Model

## Goal
Build a machine-calibrated Phase 1 measurement stack for transparent-proof verification costs on Solana, with explicit separation between directly measured surfaces, structure-derived features, and proxy estimates.

## Repo Baseline
Workspace was empty at `/Users/dominic/ZK`. Phase 1 is a from-scratch scaffold: no pre-existing on-chain program, verifier entrypoint, benchmark harness, upload path, allocator tuning, or vendored proof-system dependency was present to reuse.
Historical baseline preserved from prior PoC context: `verify_stark` mean 1104510 CU, max 1190982 CU over 100 runs.

## Methodology
Phase 1 uses a local `solana-test-validator` plus SBF probe program to isolate marginal surfaces. CU is taken from transaction simulation. Feature attributions are stored per record as `direct_measurement`, `derived_structure`, or `estimated_proxy`.

## Benchmark Surfaces
- Hash syscall: hash call count and hashed bytes.
- Merkle path: total authentication levels across paths.
- Proof parsing: proof bytes and segment count using fixed-header vs varint framing.
- Field arithmetic: add/sub, mul, inversion, extension-mul proxies.
- Heap frame: requested heap and touched scratch bytes.
- Account I/O: readonly and writable account counts plus bytes read/written.
- Upload path: chunk count, bytes uploaded, optional rolling-hash checks.
- Synthetic verifier: coarse aggregate profile assembled from the surfaces above.

## Measured Variables
- transaction CU from local simulation
- transaction byte size
- hash call count per benchmark definition
- hashed bytes per benchmark definition
- proof bytes uploaded and parsed
- upload chunk count
- heap frame request bytes
- readonly and writable account counts
- account data bytes read/written by benchmark construction

## Inferred Variables
- total merkle levels = path_count * path_depth
- heap_pages_32k from requested heap frame
- proof transport pressure from upload bytes vs 1232-byte transaction cap
- dominant contributor ordering from additive fitted coefficients
- verification-core vs transport decomposition from secondary additive fits
- coefficient uncertainty bands from deterministic bootstrap resampling

## Fitted Model
Chosen fit: `huber_irls` over 186 successful records. RMSE 59021.4 CU, MAE 9606.9 CU, p95 abs error 1728.1 CU.
- `intercept`: 722.843969 CU per unit (stderr 116.198384)
- `sha_calls`: 148.723834 CU per unit (stderr 41.654802)
- `sha_bytes`: 0.794906 CU per unit (stderr 0.094055)
- `merkle_levels`: 366.535890 CU per unit (stderr 38.404014)
- `proof_bytes`: 7.093797 CU per unit (stderr 0.092228)
- `heap_pages_32k`: 83783.893619 CU per unit (stderr 328.965920)
- `account_data_bytes_written`: 898.161145 CU per unit (stderr 2.107752)
- `field_add_sub_ops`: 36.971365 CU per unit (stderr 0.059115)
- `field_mul_ops`: 491.373901 CU per unit (stderr 0.948191)
- `field_inv_ops`: 11270.192376 CU per unit (stderr 22.756593)
- `extension_mul_ops`: 3175.453734 CU per unit (stderr 2.844574)
- Verification-core secondary fit: `huber_irls` with RMSE 88370.7 CU and p95 abs error 113019.7 CU.
- Transport secondary fit: `huber_irls` with RMSE 223.6 CU and p95 abs error 370.0 CU.

## Prediction Error
OLS RMSE 52297.5 CU vs Huber RMSE 59021.4 CU. Chosen model uncertainty band uses ±59021.4 CU as a first-pass residual envelope.
Bootstrap summaries for selected coefficients (deterministic resampling):
- `intercept`: mean 271.464, p05 -4368.434, p50 720.278, p95 749.558, sign_stable=false
- `sha_calls`: mean 168.332, p05 136.645, p50 152.050, p95 239.423, sign_stable=true
- `sha_bytes`: mean 0.816, p05 0.639, p50 0.789, p95 1.116, sign_stable=true
- `merkle_levels`: mean 372.057, p05 323.093, p50 365.577, p95 539.317, sign_stable=true
- `proof_bytes`: mean 7.210, p05 7.086, p50 7.094, p95 8.053, sign_stable=true
- `heap_pages_32k`: mean 84068.340, p05 83744.128, p50 83784.224, p95 87030.528, sign_stable=true
- `account_data_bytes_written`: mean 662.270, p05 18.782, p50 897.819, p95 898.986, sign_stable=true
- `field_add_sub_ops`: mean 37.004, p05 36.965, p50 36.972, p95 37.434, sign_stable=true
- `field_mul_ops`: mean 491.962, p05 491.339, p50 491.377, p95 497.986, sign_stable=true
- `field_inv_ops`: mean 11283.100, p05 11269.355, p50 11270.284, p95 11427.780, sign_stable=true
- `extension_mul_ops`: mean 3177.274, p05 3175.349, p50 3175.465, p95 3195.446, sign_stable=true

## Dominant Cost Drivers
- `hypothetical-fri-profile`: field_inv_ops (1081938.5 CU), field_mul_ops (754750.3 CU), extension_mul_ops (609687.1 CU); core 3361952.6 CU, transport 10823.4 CU
- `hypothetical-circle-profile`: field_inv_ops (540969.2 CU), field_mul_ops (503166.9 CU), extension_mul_ops (304843.6 CU); core 1894046.2 CU, transport 6524.0 CU
- `hypothetical-whir-profile`: field_mul_ops (440271.0 CU), field_inv_ops (360646.2 CU), heap_pages_32k (251351.7 CU); core 1519600.4 CU, transport 5361.6 CU

## Safe Operating Region
Profiles are provisionally comfortable when predicted CU stays below roughly 85% of the 1.4M cap, upload transport pressure stays below 1.0 per transaction chunk, and requested heap stays below 256 KiB.
Circle sweep explored 48 scenarios; 0 were feasible under current limits. Lowest predicted point was `circle-p4608-c640-q3` at 1524640.7 CU.

## Failure Modes
- heap_pressure: observed ({"InstructionError":[1,"InvalidInstructionData"]})
- transaction_size_friction: observed (serialized transaction 1335 exceeds limit 1232)
- compute_unit_exhaustion: observed ({"InstructionError":[2,"ComputationalBudgetExceeded"]})
- stack_pressure: unknown (No production verifier or recursive stack-heavy probe was present. The scaffold keeps stack pressure explicit via the documented 4096-byte frame limit, but does not force a stack overflow probe yet.)

## Limitations / Confounders
- No production verifier was present in the repo, so coarse end-to-end extraction targets a synthetic verifier probe rather than a semantic proof verifier.
- Validator version drift can move CU, allocator behavior, and syscall pricing.
- Local validator cache warmth and account-layout choices can shift measurements.
- Field-op counts are microkernel proxies, not dynamic counts from a live verifier.
- Heap behavior depends on the Solana allocator and the request-heap-frame instruction; this stack measures observed transaction cost, not allocator internals.

## Recommended Next Experiments
- Replace the synthetic verifier probe with a real verifier path while preserving the current feature schema.
- Run orthogonal sweeps that isolate transport bytes/chunks from core hash and Merkle structure.
- Add version-pinned cross-validator runs to quantify Agave/Solana drift.
- Score spend-circuit-shaped profiles once statement-specific field-op proxies are available.

_Generated 2026-04-19T13:01:13.842218+00:00 UTC from `cargo xtask phase1`._