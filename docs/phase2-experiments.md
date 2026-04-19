# Phase 2 Experiments

## Goal
Run the highest expected-value CU-reduction experiments for a WHIR-shaped transparent verifier on Solana using real SBF measurements, fixed-layout proof parsing, and the existing Phase 1 scorer.

## Discovery Summary
- Workspace root still centers on the Phase 1 scaffold: `xtask`, `programs/phase1-probe`, `crates/svm-cost-model`, `examples/phase1`, and `phase1_results`.
- No dedicated Phase 2 crate tree existed at the workspace root. This run reuses the existing SBF probe and extends it with shared Phase 2 arithmetic and skeleton-verifier logic.
- Vendored `third_party/solana-pqzk-fullchain` remains the main local source of on-chain verifier, custom heap, and Winterfell/FRI stack-discipline reference code.
- Baseline commands already present before this work: `cargo xtask phase1`, `cargo xtask phase1-next`, and `cargo run -p svm-cost-model --bin phase1-score -- phase1_results/summary.json <profile>`.

## Baseline
- Phase 1 chosen model: `huber_irls` with RMSE 59021.4 CU.
- Current WHIR spend floor from the existing Phase 1 report is still above the 1.4M CU transaction cap.
- Phase 2 run config: query_count=4, fold_arity=4, proof_bytes=5120, merkle_depth=16, merkle_paths=8, upload_chunk_size=640, verify_repeat=12.

## Experiment Design
- Experiment A: five M31 reduction kernels measured on host and SBF across raw mul, square, mul-add, short inner product, Horner, denominator chain, and a verifier-shaped fold step.
- Experiment B: CM31/QM31 schoolbook vs Karatsuba kernels measured in isolation and inside the skeleton verifier, plus eager-QM31 vs late-lift-QM31 policy comparison.
- Experiment C: raw-fiber vs local-interpolant fold representation comparison on the same statement digest, query schedule, proof size target, and Merkle schedule.
- Experiment D: a higher-fidelity WHIR query evaluator that reuses the winning kernels on derived WHIR schedules from the Phase 1 spend model, with explicit round-by-round query counts and separate opening/selector denominator chains.
- Transport is included in end-to-end totals by measuring upload CU separately and adding it to verify CU.

## Measured vs Inferred vs Unknown
- Measured directly: host timings, SBF CU, proof bytes, upload chunk count, fixed heap-frame request, and Phase 2 instrumentation counters from the shared host/SBF code path.
- Inferred for Phase 1 scorer projection: `field_mul_ops`, `extension_mul_ops`, and `field_inv_ops` are projected from Phase 2 counters into the coarser Phase 1 feature schema.
- Unknown: code-size deltas per arithmetic kernel, native WHIR transcript/proof-layout interaction effects beyond the current statement-bound proxy, and multi-validator drift beyond the local Agave toolchain.

## Experiment A Results
- Raw mul winner on SBF: `reference_canonical`.
- Verifier-shaped fold-step winner on SBF: `reference_canonical`. This is the recommended new base-field kernel baseline.
- Measured arithmetic records: 210.

## Experiment B Results
- Extension kernel winner on the skeleton-shaped accumulator workload: `karatsuba`.
- Lift-policy winner in the end-to-end skeleton matrix: `late_lift_qm31`.
- Measured extension records: 108.

## Experiment C Results
- Fold-mode winner in the end-to-end skeleton matrix: `local_interpolant`.
- The fold-mode comparison is explicitly a narrow experimental packaging study: transcript/challenge derivation stays fixed across modes, while the proof payload switches between raw local values and prepackaged local coefficients.
- Measured end-to-end records: 64.

## Higher-Fidelity WHIR Query Evaluator
- Best measured higher-fidelity variant: `reference_karatsuba_late`.
- This evaluator is still experimental rather than a production verifier, but it now uses the Phase 1 WHIR round schedule, the same query-count regimes behind the old 2.5M / 3.2M / 5.7M bounds, concrete Spend statement row breakdowns to derive semantically meaningful query records, eight-point local evaluation, and explicit opening/selector denominator chains.
- whir_t100_capacity_full: direct/schoolbook/eager 528729 CU -> reference/schoolbook/eager 481389 CU -> reference/karatsuba/eager 476956 CU -> reference/karatsuba/late 458043 CU.
- whir_t128_capacity_full: direct/schoolbook/eager 697986 CU -> reference/schoolbook/eager 632049 CU -> reference/karatsuba/eager 625903 CU -> reference/karatsuba/late 599602 CU.
- whir_t128_johnson_full: direct/schoolbook/eager 1291130 CU -> reference/schoolbook/eager 1160804 CU -> reference/karatsuba/eager 1148039 CU -> reference/karatsuba/late 1095421 CU.
- Measured higher-fidelity records: 96.

## Optional Experiment Results
- Minimal-subtree / multiproof Merkle mode and heap-streaming audit were not executed in this run. The config surface already reserves `MerkleProofMode` for that follow-up.

## Predicted vs Measured Comparison
- Each end-to-end skeleton variant is scored with the Phase 1 chosen model plus the Phase 1 core/transport component models when present.
- The current Phase 1 coefficients materially over-predict this narrow M31/QM31 skeleton path because the scorer was fit on coarser verifier proxies, not these explicit field kernels. Treat the absolute error here as a calibration diagnostic, not as a replacement for the measured CU.
- Best variant `karatsuba_late_lift_qm31_local_interpolant`: measured total 667770 CU, predicted 10251583.6 CU, abs error 9583813.6 CU, rel error 1435.20%.
- Higher-fidelity `reference_karatsuba_late` on `whir_t100_capacity_full`: measured total 458043 CU, legacy bound 4193302.7 CU, measured-feature prediction 15309429.8 CU.

## Combined Best-Case Configuration
- `reference_canonical` + `karatsuba` + `late_lift_qm31` + `local_interpolant`.
- Best measured skeleton variant: `karatsuba_late_lift_qm31_local_interpolant`.

## Estimated Total CU Savings
- Estimated savings versus the current 1.45M-CU working point: 467606.7 CU.
- Estimated post-change total: 982393.3 CU.
- Estimated remaining headroom against the 1.4M cap: 417606.7 CU.

## Open Risks
- The high-fidelity WHIR path is now bound to the concrete Spend statement shape, but it still is not a native WHIR prover/verifier transcript, so proof-layout and transcript costs can still move when the real query evaluator lands.
- The fold-mode experiment keeps challenge derivation fixed across layouts to isolate verifier work; that is useful for measurement but not yet a production-complete proof-layout commitment story.

## Recommended Next Steps Toward SpendV0
- Port the same winning kernels and late-lift policy into a native WHIR prover/verifier transcript path so the current statement-bound proxy can be replaced by real proof bytes and challenge flow.
- Execute the reserved minimal-subtree Merkle experiment to see whether proof-byte and hash-call savings survive fixed-layout parsing on SBF.
- Replace the fixed local-neighborhood proxy with the exact packaged local-interpolant payload emitted by the eventual WHIR prover so the fold-mode result can be re-measured without transcript-isolation shortcuts.

_Generated 2026-04-19T19:00:40.433565+00:00 UTC from `cargo xtask phase2-experiments`._