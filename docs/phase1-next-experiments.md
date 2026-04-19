# Phase 1 Follow-on Experiments

## Goal
Run the next serious Phase 1 experiments against the existing scaffold: compare the scorer to a real Winterfell verifier path, score spend-shaped Circle and WHIR profiles, and execute orthogonal sweeps for previously dropped coefficients.

## Real Verifier Path
Measured external `verify_stark` baseline: mean 1104506.47 CU, median 1110513.50 CU, min 988312, max 1190982 over 100 runs.
Locally generated proof size: 4211 bytes; predicted verifier cost: 1099681.6 CU; measured minus predicted: 4824.8 CU (0.44% abs error).
Query soundness for the real verifier profile: 68.0-128.0 bits at q=30 and blowup 16. The proven lower bound misses the 128-bit target, while the conjectured upper bound lands on it.
Field inversion proxy: prior query-scaled estimate 27 -> corrected execution-structure estimate 4 (transition divisions 1, boundary-group divisions 2, DEEP batch inversion 1, recursive FRI layer inversions 0).
Field multiplication proxy audit: dominant remainder Horner multiplications 216 + queried x-coordinate lifts 27 -> proxy 243. Extension-field multiplications remain 0 because this proof stays on Winterfell's base-field path.
Diagnostic backsolve: matching the measured mean under the current additive model would require about 252.8 `field_mul_ops` proxy units.
Measured here: proof bytes from a local proof.bin and external verify-only/finalize-only CSV baselines. Inferred here: Merkle levels, account bytes, and verifier-kernel field proxies from proof structure and verifier layout.

## Base Spend-Screen Scores
- `spend-circle-profile`: 2166297.6 CU (1.547x budget), feasible=false, query soundness 10.0-20.0 bits vs 128-bit target, top contributors: field_mul_ops 699716.4 CU, extension_mul_ops 647792.6 CU, heap_pages_32k 251351.7 CU.
- `spend-whir-profile`: 1749910.3 CU (1.250x budget), feasible=false, query soundness 7.7-15.7 bits vs 128-bit target, top contributors: field_mul_ops 560166.2 CU, extension_mul_ops 438212.6 CU, heap_pages_32k 251351.7 CU.
These are the raw structured-screen outputs from the base additive model before the orthogonal account-I/O replacement pass. They are derived from an explicit spend-statement arithmetization rather than hand-entered verifier proxy counts, but they remain screening inputs rather than a production circuit.
Spend field inversion counts now follow verifier structure in the screening model: transition divisor divisions + boundary constraint groups + DEEP batch inversions + low-degree batch-inversion rounds, rather than scaling directly with q.

## Query Semantics
In the spend sweeps, `q` is a literal absolute proof-query count in the current model. It is not a query-round count, not an internally batched effective-query estimate, and not a hidden security-normalized parameter.
Circle now maps q to lower/upper query soundness using official FRI formulas: proven `rate^(q/2)` as the lower bound and conjectured ethSTARK-style `rate^q` as the upper bound, with query grinding bits added directly. WHIR now maps q to lower/upper query soundness using the official Plonky3 WHIR soundness model: Johnson-bound as the lower bound and capacity-bound as the upper bound, with configured PoW bits added directly to the query term.
Interpretation: low-q points are no longer unlabeled cost screens; they now fail explicitly because their query-controlled soundness stays far below the 128-bit target.
- q3 sweep envelope: 1422489.3 to 1714850.2 CU across all spend-screen scenarios; feasible_points=0.
- q4 sweep envelope: 1521066.6 to 1831192.5 CU across all spend-screen scenarios; feasible_points=0.
- q5 sweep envelope: 1619643.8 to 1947534.8 CU across all spend-screen scenarios; feasible_points=0.
- q6 sweep envelope: 2049320.0 to 2063877.1 CU across all spend-screen scenarios; feasible_points=0.

## Security-Qualified Joint Sweep
This second sweep varies rate, grinding, security target (100/120/128 bits), and inferred cost scenarios jointly before scoring verifier cost. It is a security-qualified screen, not just a low-q cost sweep.
- Best Circle / fri_proven / t100 point: `qualified-circle-t100-r32-g32-fri_proven-m31_mul_0p75` -> scenario `m31_mul_0p75`, rate 1/32, grinding 32 bits, q_min 28, q_total 28, 3726162.7 CU (2.662x budget), assumption_feasible=false, lower-bound-feasible=false.
- Best Circle / fri_conjectured / t100 point: `qualified-circle-t100-r32-g32-fri_conjectured-m31_mul_0p75` -> scenario `m31_mul_0p75`, rate 1/32, grinding 32 bits, q_min 14, q_total 14, 2437117.0 CU (1.741x budget), assumption_feasible=false, lower-bound-feasible=false.
- Best WHIR / whir_johnson_full / t100 point: `qualified-whir-t100-r16-g32-whir_johnson_full-fenzi_whir_core_0p8_plus_m31_mul_0p75` -> scenario `fenzi_whir_core_0p8_plus_m31_mul_0p75`, rate 1/16, grinding 32 bits, q_min 36, q_total 56, 4279371.7 CU (3.057x budget), assumption_feasible=false, lower-bound-feasible=false.
- Best WHIR / whir_capacity_full / t100 point: `qualified-whir-t100-r16-g32-whir_capacity_full-fenzi_whir_core_0p8_plus_m31_mul_0p75` -> scenario `fenzi_whir_core_0p8_plus_m31_mul_0p75`, rate 1/16, grinding 32 bits, q_min 18, q_total 28, 2526934.5 CU (1.805x budget), assumption_feasible=false, lower-bound-feasible=false.
- Best Circle / fri_proven / t120 point: `qualified-circle-t120-r32-g32-fri_proven-m31_mul_0p75` -> scenario `m31_mul_0p75`, rate 1/32, grinding 32 bits, q_min 36, q_total 36, 4462760.2 CU (3.188x budget), assumption_feasible=false, lower-bound-feasible=false.
- Best Circle / fri_conjectured / t120 point: `qualified-circle-t120-r32-g32-fri_conjectured-m31_mul_0p75` -> scenario `m31_mul_0p75`, rate 1/32, grinding 32 bits, q_min 18, q_total 18, 2805415.8 CU (2.004x budget), assumption_feasible=false, lower-bound-feasible=false.
- Best WHIR / whir_johnson_full / t120 point: `qualified-whir-t120-r16-g32-whir_johnson_full-fenzi_whir_core_0p8_plus_m31_mul_0p75` -> scenario `fenzi_whir_core_0p8_plus_m31_mul_0p75`, rate 1/16, grinding 32 bits, q_min 46, q_total 72, 5281542.7 CU (3.773x budget), assumption_feasible=false, lower-bound-feasible=false.
- Best WHIR / whir_capacity_full / t120 point: `qualified-whir-t120-r16-g32-whir_capacity_full-fenzi_whir_core_0p8_plus_m31_mul_0p75` -> scenario `fenzi_whir_core_0p8_plus_m31_mul_0p75`, rate 1/16, grinding 32 bits, q_min 23, q_total 36, 3027932.4 CU (2.163x budget), assumption_feasible=false, lower-bound-feasible=false.
- Best Circle / fri_proven / t128 point: `qualified-circle-t128-r32-g32-fri_proven-m31_mul_0p75` -> scenario `m31_mul_0p75`, rate 1/32, grinding 32 bits, q_min 39, q_total 39, 4739071.8 CU (3.385x budget), assumption_feasible=false, lower-bound-feasible=false.
- Best Circle / fri_conjectured / t128 point: `qualified-circle-t128-r32-g32-fri_conjectured-m31_mul_0p75` -> scenario `m31_mul_0p75`, rate 1/32, grinding 32 bits, q_min 20, q_total 20, 2989565.2 CU (2.135x budget), assumption_feasible=false, lower-bound-feasible=false.
- Best WHIR / whir_johnson_full / t128 point: `qualified-whir-t128-r16-g32-whir_johnson_full-fenzi_whir_core_0p8_plus_m31_mul_0p75` -> scenario `fenzi_whir_core_0p8_plus_m31_mul_0p75`, rate 1/16, grinding 32 bits, q_min 50, q_total 78, 5657061.9 CU (4.041x budget), assumption_feasible=false, lower-bound-feasible=false.
- Best WHIR / whir_capacity_full / t128 point: `qualified-whir-t128-r16-g32-whir_capacity_full-fenzi_whir_core_0p8_plus_m31_mul_0p75` -> scenario `fenzi_whir_core_0p8_plus_m31_mul_0p75`, rate 1/16, grinding 32 bits, q_min 25, q_total 39, 3215704.9 CU (2.297x budget), assumption_feasible=false, lower-bound-feasible=false.
- Security-qualified feasible points for `Circle/fri_conjectured/t100`: 0.
- Security-qualified feasible points for `Circle/fri_conjectured/t120`: 0.
- Security-qualified feasible points for `Circle/fri_conjectured/t128`: 0.
- Security-qualified feasible points for `Circle/fri_proven/t100`: 0.
- Security-qualified feasible points for `Circle/fri_proven/t120`: 0.
- Security-qualified feasible points for `Circle/fri_proven/t128`: 0.
- Security-qualified feasible points for `WHIR/whir_capacity_full/t100`: 0.
- Security-qualified feasible points for `WHIR/whir_capacity_full/t120`: 0.
- Security-qualified feasible points for `WHIR/whir_capacity_full/t128`: 0.
- Security-qualified feasible points for `WHIR/whir_johnson_full/t100`: 0.
- Security-qualified feasible points for `WHIR/whir_johnson_full/t120`: 0.
- Security-qualified feasible points for `WHIR/whir_johnson_full/t128`: 0.

## Refined Spend Scoring
Spend rescoring keeps the base additive structure and replaces account-I/O coefficients with orthogonal sweep terms. The inversion coefficient is applied only if the Winterfell-aligned inversion sweep completes without failures.
Orthogonal account-I/O coefficients used for spend rescoring: ro_account_count 209.000, rw_account_count 224.000, account_data_bytes_read 0.281250, account_data_bytes_written 10.000000.
Recovered inversion coefficient: field_inv_ops 11280.250 CU/op from `huber_irls`. It was not applied to the refined spend scorer because 2 inversion sweep runs still failed.
- Refined `spend-circle-profile`: 1942566.3 CU (1.388x budget), feasible=false, query soundness 10.0-20.0 bits vs 128-bit target, top contributors: field_mul_ops 699716.4 CU, extension_mul_ops 647792.6 CU, heap_pages_32k 251351.7 CU.
- Refined `spend-whir-profile`: 1526035.0 CU (1.090x budget), feasible=false, query soundness 7.7-15.7 bits vs 128-bit target, top contributors: field_mul_ops 560166.2 CU, extension_mul_ops 438212.6 CU, heap_pages_32k 251351.7 CU.
- Best Circle sweep point: `spend-circle-p5632-c640-q3` -> 1700293.0 CU (1.214x budget), feasible=false, feasible_points=0, query soundness 6.0-12.0 bits.
- Best WHIR sweep point: `spend-whir-p5120-c640-q3` -> 1422489.3 CU (1.016x budget), feasible=false, feasible_points=0, query soundness 5.8-11.8 bits.

## Orthogonal Sweeps
Executed 128 local orthogonal records across aggregate uploads, account I/O, and inversion microkernels.
- Upload aggregate fit: `huber_irls`; selected features: upload_bytes, upload_chunks; RMSE 0.0 CU.
- Account I/O fit: `huber_irls`; selected features: ro_account_count, rw_account_count, account_data_bytes_read, account_data_bytes_written; RMSE 0.0 CU.
- Field inversion fit: `huber_irls`; selected features: field_inv_ops; RMSE 0.0 CU.
  Failed inversion runs: 2.

## Version Manifest
- `solana-test-validator --version` -> `solana-test-validator 2.3.0 (src:a2e21dda; feat:3640012085, client:Agave)`
- `cargo-build-sbf --version` -> `solana-cargo-build-sbf 2.3.0
platform-tools v1.48
rustc 1.84.1`
- `rustc --version` -> `rustc 1.93.0 (254b59607 2026-01-19)`
- `cargo --version` -> `cargo 1.93.0 (083ac5135 2025-12-15)`
- Not executed: Cross-version validator drift was not executed here; set up alternate Agave/Solana binaries and rerun `cargo xtask phase1-next` under those toolchains.

## Baseline Context
Base Phase 1 chosen model remains `huber_irls` with RMSE 59021.4 CU and p95 abs error 1728.1 CU across 186 successful records.

## Unknowns
- The real-verifier comparison still relies on source-backed field-op proxies rather than an instrumented Winterfell verifier kernel.
- Cross-version validator drift is recorded but not yet measured across multiple Agave/Solana binaries.
- Spend-shaped profiles remain hypothesis inputs until a concrete spend circuit is arithmetized and proved.

_Generated 2026-04-19T16:30:13.283525+00:00 UTC from `cargo xtask phase1-next`._