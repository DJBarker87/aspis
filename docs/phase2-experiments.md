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
- Merkle multiproof / `minimal_subtree` was executed via `cargo xtask phase2-multiproof`.
- Prover-emitted-style multiproof payload parsing was executed via `cargo xtask phase2-multiproof-payload`.
- Proof-carried fold payload comparison was executed via `cargo xtask phase2-fold-payload`.
- Multiplication taxonomy was executed via `cargo xtask phase2-mul-taxonomy`.
- External prover interoperability and dynamic operand-pattern tagging remain scaffolded.
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

## WHIR Transcript Path
- Executed: transcript absorption/challenge derivation, commitment OOD checks, per-round query PoW checks, folding verification across all rounds, final-round query verification, and transcript consistency checks on SBF.
- Executed: repo-local valid/invalid proof validation. Valid proofs were accepted; deliberately wrong challenge, missing-query, incorrect-folding, and truncated proofs were rejected.
- Scaffolded: external proof interop with the official Plonky3 WHIR prover/verifier was not executed because `/tmp/plonky3-official` at commit `0f87f2b543a01880274965c410bf804c124f5046` does not contain the referenced `whir/src/verifier/mod.rs` entrypoint or a runnable end-to-end WHIR prover/verifier surface.
- Honest caveat: the current PoW step checks transcript-bound witness consistency inside the verifier path, not full prover-side grinding cost.

### Query-Only vs Transcript-Inclusive
- whir_t100_capacity_full: query-only 461144 +- 0 CU -> transcript-inclusive 764562 +- 0 CU (delta +303418 CU).
- whir_t128_capacity_full: query-only 603811 +- 0 CU -> transcript-inclusive 1014405 +- 0 CU (delta +410594 CU).
- whir_t128_johnson_full: query-only 1103645 +- 0 CU -> transcript-inclusive 1462367 +- 0 CU (delta +358722 CU).

### whir_t100_capacity_full
- parse: 1486 +- 0 CU.
- transcript setup: 38632 +- 0 CU.
- OOD: 12145 +- 0 CU.
- per-round queries: 620944 +- 0 CU.
- folding: 8269 +- 0 CU.
- final round: 59068 +- 0 CU.
- whir_t100_capacity_full: transcript-inclusive 764562 +- 0 CU leaves 635438 CU mean margin against the 1.4M cap.

### whir_t128_capacity_full
- parse: 1486 +- 0 CU.
- transcript setup: 19432 +- 0 CU.
- OOD: 12142 +- 0 CU.
- per-round queries: 862015 +- 0 CU.
- folding: 12816 +- 0 CU.
- final round: 75875 +- 0 CU.
- whir_t128_capacity_full: transcript-inclusive 1014405 +- 0 CU leaves 385595 CU mean margin against the 1.4M cap.

### whir_t128_johnson_full
- parse: 1486 +- 0 CU.
- transcript setup: 11669 +- 0 CU.
- OOD: 9744 +- 0 CU.
- folding: 6165 +- 0 CU.
- whir_t128_johnson_full: transcript-inclusive 1462367 +- 0 CU leaves -62367 CU mean margin against the 1.4M cap.

## WHIR Merkle Multiproof
- Executed: the full WHIR transcript verifier path was rerun with the same winning kernels and statement binding, comparing `separate_paths` against `minimal_subtree` Merkle verification on SBF.
- Executed: repo-local valid/invalid proof validation for both Merkle modes. Valid proofs were accepted; deliberately wrong challenge, missing-query, incorrect-folding, and truncated proofs were rejected.
- Executed: a no-heap control run for each variant and Johnson-only segment diagnostics that replay each round plus the final round from captured transcript checkpoints.
- Honest caveat: the repo-local synthetic proof now serializes mode-specific Merkle witness bytes, but total proof sizing is still profile-shaped from synthetic node counts rather than an external prover-emitted multiproof payload.

### Separate Paths vs Minimal Subtree
- whir_t100_capacity_full: total 764562 -> 707117 CU (delta -57445); per-round 620944 -> 596515 CU (delta -24429); proof 12356 -> 5668 bytes (delta -6688); upload 26438 -> 11951 CU (delta -14487); verify ok 10/10 -> 10/10.
- whir_t128_capacity_full: total 1014405 -> 932943 CU (delta -81462); per-round 862015 -> 827327 CU (delta -34688); proof 15468 -> 5932 bytes (delta -9536); upload 33059 -> 13096 CU (delta -19963); verify ok 10/10 -> 10/10.
- whir_t128_johnson_full: total 1462367 -> 1421156 CU (delta -41211); per-round trace incomplete; proof 29512 -> 9896 bytes (delta -19616); upload 62367 -> 21156 CU (delta -41211); verify ok 0/10 -> 0/10.

### whir_t100_capacity_full
- separate_paths: total 764562 +- 0 CU, per-round queries 620944 +- 0 CU, upload 26438 CU, proof 12356 bytes, verify ok 10/10.
- separate_paths phase breakdown: parse 1486 +- 0 CU, transcript setup 38632 +- 0 CU, OOD 12145 +- 0 CU, per-round queries 620944 +- 0 CU, folding 8269 +- 0 CU, final round 59068 +- 0 CU.
- separate_paths no-heap control: verify 737974 CU, total 764412 CU, status 1/1.
- minimal_subtree: total 707117 +- 0 CU, per-round queries 596515 +- 0 CU, upload 11951 CU, proof 5668 bytes, verify ok 10/10.
- minimal_subtree phase breakdown: parse 1484 +- 0 CU, transcript setup 38631 +- 0 CU, OOD 12147 +- 0 CU, per-round queries 596515 +- 0 CU, folding 8269 +- 0 CU, final round 40540 +- 0 CU.
- minimal_subtree no-heap control: verify 695016 CU, total 706967 CU, status 1/1.
- delta: total -57445 CU, proof delta -6688 bytes, upload delta -14487 CU.
- whir_t100_capacity_full: separate_paths leaves 635438 CU mean margin, minimal_subtree leaves 692883 CU mean margin against the 1.4M cap.

### whir_t128_capacity_full
- separate_paths: total 1014405 +- 0 CU, per-round queries 862015 +- 0 CU, upload 33059 CU, proof 15468 bytes, verify ok 10/10.
- separate_paths phase breakdown: parse 1486 +- 0 CU, transcript setup 19432 +- 0 CU, OOD 12142 +- 0 CU, per-round queries 862015 +- 0 CU, folding 12816 +- 0 CU, final round 75875 +- 0 CU.
- separate_paths no-heap control: verify 981196 CU, total 1014255 CU, status 1/1.
- minimal_subtree: total 932943 +- 0 CU, per-round queries 827327 +- 0 CU, upload 13096 CU, proof 5932 bytes, verify ok 10/10.
- minimal_subtree phase breakdown: parse 1484 +- 0 CU, transcript setup 19432 +- 0 CU, OOD 12145 +- 0 CU, per-round queries 827327 +- 0 CU, folding 12814 +- 0 CU, final round 49065 +- 0 CU.
- minimal_subtree no-heap control: verify 919697 CU, total 932793 CU, status 1/1.
- delta: total -81462 CU, proof delta -9536 bytes, upload delta -19963 CU.
- whir_t128_capacity_full: separate_paths leaves 385595 CU mean margin, minimal_subtree leaves 467057 CU mean margin against the 1.4M cap.

### whir_t128_johnson_full
- separate_paths: total 1462367 +- 0 CU, upload 62367 CU, proof 29512 bytes, verify ok 0/10.
- separate_paths phase breakdown: parse 1486 +- 0 CU, transcript setup 11669 +- 0 CU, OOD 9744 +- 0 CU, folding 6165 +- 0 CU.
- separate_paths no-heap control: verify 1400000 CU, total 1462367 CU, status 0/1.
- separate_paths no-heap error: `{"InstructionError":[1,"ProgramFailedToComplete"]}`.
- minimal_subtree: total 1421156 +- 0 CU, upload 21156 CU, proof 9896 bytes, verify ok 0/10.
- minimal_subtree phase breakdown: parse 1484 +- 0 CU, transcript setup 11670 +- 0 CU, OOD 9744 +- 0 CU, folding 6154 +- 0 CU.
- minimal_subtree no-heap control: verify 1400000 CU, total 1421156 CU, status 0/1.
- minimal_subtree no-heap error: `{"InstructionError":[1,"ProgramFailedToComplete"]}`.
- minimal_subtree diagnostic_round_0: 1400000 CU, status simulation_error.
- minimal_subtree diagnostic_round_0 error: `{"InstructionError":[2,"ProgramFailedToComplete"]}`.
- minimal_subtree diagnostic_final_round: 82039 CU, status ok.
- delta: total -41211 CU, proof delta -19616 bytes, upload delta -41211 CU.
- whir_t128_johnson_full: separate_paths leaves -62367 CU mean margin, minimal_subtree leaves -21156 CU mean margin against the 1.4M cap.

## WHIR Multiproof Payload
- Executed: a prover-emitted-style Merkle payload parser benchmark on SBF, comparing the existing flat-node witness bytes against a repo-local canonical payload that carries per-section metadata and canonical query/node ordering.
- Executed: both `separate_paths` and `minimal_subtree` payloads across the three transcript scenarios, with host validation plus valid/invalid parser checks.
- Honest caveat: this is still a repo-local canonical payload rather than an official Plonky3 prover-emitted multiproof format; the value here is parser and upload cost, not interoperability.

### Flat Nodes vs Canonical Payload
- whir_t100_capacity_full separate_paths: flat 8128 bytes -> canonical 10352 bytes (delta +2224), parse 226295 -> 306038 CU (delta +79743), total 242930 -> 327653 CU (delta +84723).
- whir_t100_capacity_full minimal_subtree: flat 1440 bytes -> canonical 1992 bytes (delta +552), parse 42785 -> 66188 CU (delta +23403), total 46406 -> 71052 CU (delta +24646).
- whir_t128_capacity_full separate_paths: flat 11328 bytes -> canonical 14396 bytes (delta +3068), parse 314095 -> 424689 CU (delta +110594), total 337165 -> 454128 CU (delta +116963).
- whir_t128_capacity_full minimal_subtree: flat 1792 bytes -> canonical 2476 bytes (delta +684), parse 52444 -> 82721 CU (delta +30277), total 56241 -> 87827 CU (delta +31586).
- whir_t128_johnson_full separate_paths: flat 22656 bytes -> canonical 28712 bytes (delta +6056), parse 624907 -> 844731 CU (delta +219824), total 671047 -> 902602 CU (delta +231555).
- whir_t128_johnson_full minimal_subtree: flat 3040 bytes -> canonical 4192 bytes (delta +1152), parse 86686 -> 141338 CU (delta +54652), total 93041 -> 150203 CU (delta +57162).
## WHIR Fold Payload
- Executed: a proof-carried fold representation comparison on the full transcript path, holding the winning arithmetic kernels and `minimal_subtree` Merkle mode fixed while comparing `raw_fibers` against `local_interpolant`.
- Honest caveat: this measures the current repo-local local-interpolant payload, not Fenzi's exact fold representation trick; it answers whether our present proof-carried fold encoding helps once the whole transcript path is included.

### Raw Fibers vs Local Interpolant
- whir_t100_capacity_full: raw 702910 -> local 706656 CU (delta +3746), proof 5668 -> 5668 bytes (delta +0), per-round 592782 -> 596515 CU (delta +3733).
- whir_t128_capacity_full: raw 927227 -> local 932436 CU (delta +5209), proof 5932 -> 5932 bytes (delta +0), per-round 822129 -> 827327 CU (delta +5198).
- whir_t128_johnson_full: raw 1420420 -> local 1420420 CU (delta +0), proof 9896 -> 9896 bytes (delta +0).

### whir_t100_capacity_full
- raw_fibers: total 702910 +- 0 CU, proof 5668 bytes.
- raw_fibers phase breakdown: parse 1482 +- 0 CU, transcript setup 38631 +- 0 CU, OOD 12144 +- 0 CU, per-round queries 592782 +- 0 CU, folding 8272 +- 0 CU, final round 40531 +- 0 CU.
- local_interpolant: total 706656 +- 0 CU, proof 5668 bytes.
- local_interpolant phase breakdown: parse 1484 +- 0 CU, transcript setup 38631 +- 0 CU, OOD 12147 +- 0 CU, per-round queries 596515 +- 0 CU, folding 8269 +- 0 CU, final round 40540 +- 0 CU.

### whir_t128_capacity_full
- raw_fibers: total 927227 +- 0 CU, proof 5932 bytes.
- raw_fibers phase breakdown: parse 1482 +- 0 CU, transcript setup 19432 +- 0 CU, OOD 12145 +- 0 CU, per-round queries 822129 +- 0 CU, folding 12808 +- 0 CU, final round 49064 +- 0 CU.
- local_interpolant: total 932436 +- 0 CU, proof 5932 bytes.
- local_interpolant phase breakdown: parse 1484 +- 0 CU, transcript setup 19432 +- 0 CU, OOD 12145 +- 0 CU, per-round queries 827327 +- 0 CU, folding 12814 +- 0 CU, final round 49065 +- 0 CU.

### whir_t128_johnson_full
- raw_fibers: total 1420420 +- 0 CU, proof 9896 bytes.
- raw_fibers phase breakdown: parse 1482 +- 0 CU, transcript setup 11670 +- 0 CU, OOD 9742 +- 0 CU, folding 6154 +- 0 CU.
- local_interpolant: total 1420420 +- 0 CU, proof 9896 bytes.
- local_interpolant phase breakdown: parse 1484 +- 0 CU, transcript setup 11670 +- 0 CU, OOD 9744 +- 0 CU, folding 6154 +- 0 CU.
## WHIR Multiplication Taxonomy
- Executed: a taxonomy pass over the real fold-payload transcript verifier counters, classifying multiply sites as `general`, `square`, `bary_weight`, `challenge_power`, `cm31_structured`, `qm31_structured`, and `general_extension`.
- Honest caveat: `zero/one/-one`, `sparse_const`, and `twiddle` remain zero in this report because the current instrumentation does not yet tag operand values dynamically; those classes need a deeper runtime wrapper pass if we want exact counts.

### whir_t100_capacity_full raw_fibers
- total 702910 +- 0 CU, proof 5668 bytes, structured share 29.7%.
- classified multiplies: general 2073, square 589, bary_weight 18, challenge_power 250, cm31_structured 72, qm31_structured 18, general_extension 170.

### whir_t100_capacity_full local_interpolant
- total 706656 +- 0 CU, proof 5668 bytes, structured share 32.5%.
- classified multiplies: general 2033, square 589, bary_weight 18, challenge_power 362, cm31_structured 72, qm31_structured 18, general_extension 170.

### whir_t128_capacity_full raw_fibers
- total 927227 +- 0 CU, proof 5932 bytes, structured share 29.5%.
- classified multiplies: general 2877, square 813, bary_weight 25, challenge_power 338, cm31_structured 100, qm31_structured 25, general_extension 236.

### whir_t128_capacity_full local_interpolant
- total 932436 +- 0 CU, proof 5932 bytes, structured share 32.3%.
- classified multiplies: general 2821, square 813, bary_weight 25, challenge_power 494, cm31_structured 100, qm31_structured 25, general_extension 236.

### whir_t128_johnson_full raw_fibers
- total 1420420 +- 0 CU, proof 9896 bytes, structured share 29.2%.
- classified multiplies: general 5741, square 1613, bary_weight 50, challenge_power 650, cm31_structured 200, qm31_structured 50, general_extension 472.

### whir_t128_johnson_full local_interpolant
- total 1420420 +- 0 CU, proof 9896 bytes, structured share 32.0%.
- classified multiplies: general 5629, square 1613, bary_weight 50, challenge_power 962, cm31_structured 200, qm31_structured 50, general_extension 472.

## WHIR Round-0 Investigation
- Executed: a dedicated round-0 replay on SBF for all three security regimes, both Merkle modes, both fold modes, and two round-0 variants: `baseline_round0` and `round_reuse_batch_inverse`.
- Executed: phase-level tracing inside round 0 (`parse`, `OOD`, `per_round_queries`, `folding`) plus a round-0 multiply taxonomy from the host counters.
- Prototype: `round_reuse_batch_inverse` keeps the existing proof-carried selector weights / local-interpolant representation, but replaces per-query denominator inversion with a round-local batched inversion over the combined CM31 denominators.

### whir_t100_capacity_full
- minimal_subtree / raw_fibers: round0 632170 +- 0 CU, 89.9% of full verifier, 106.6% of the full per-round bucket, structured share 29.7%; reuse 595076 CU (delta -37094), projected full 665816 CU, projected margin 734184 CU.
- minimal_subtree / local_interpolant: round0 635913 +- 0 CU, 90.0% of full verifier, 106.6% of the full per-round bucket, structured share 31.5%; reuse 598819 CU (delta -37094), projected full 669562 CU, projected margin 730438 CU.
- local_interpolant Merkle delta: separate_paths round0 660343 CU -> minimal_subtree 635913 CU (delta -24430).

### whir_t128_capacity_full
- minimal_subtree / raw_fibers: round0 844809 +- 0 CU, 91.1% of full verifier, 102.8% of the full per-round bucket, structured share 29.7%; reuse 792035 CU (delta -52774), projected full 874453 CU, projected margin 525547 CU.
- minimal_subtree / local_interpolant: round0 850009 +- 0 CU, 91.2% of full verifier, 102.7% of the full per-round bucket, structured share 31.4%; reuse 797235 CU (delta -52774), projected full 879662 CU, projected margin 520338 CU.
- local_interpolant Merkle delta: separate_paths round0 884696 CU -> minimal_subtree 850009 CU (delta -34687).

### whir_t128_johnson_full
- minimal_subtree / raw_fibers: round0 1400000 +- 0 CU, 98.6% of full verifier, structured share 29.6%, saturated at the 1.4M cap before the per-round trace closed; reuse 1400000 CU (delta +0), projected full 1420420 CU, projected margin -20420 CU.
- minimal_subtree / local_interpolant: round0 1400000 +- 0 CU, 98.6% of full verifier, structured share 31.3%, saturated at the 1.4M cap before the per-round trace closed; reuse 1400000 CU (delta +0), projected full 1420420 CU, projected margin -20420 CU.
- local_interpolant Merkle delta: separate_paths round0 1400000 CU -> minimal_subtree 1400000 CU (delta +0).

## WHIR Full-Path Round Reuse
- Executed: `minimal_subtree` full-transcript verifier runs for `whir_t128_capacity_full` and `whir_t100_johnson_full`, with both fold payloads (`raw_fibers`, `local_interpolant`) and both denominator strategies (`per_query_inversion`, `round_batch_inversion`).
- Executed: fresh query-only baselines for both scenarios, 10 SBF repetitions for `verify_sbf` and `total_sbf`, plus 10 traced repetitions for transcript phase breakdown.
- Executed: valid/invalid proof checks for each fold/reuse combination before timing. The proof bytes stayed constant across the reuse variants; only the verifier path changed.

### whir_t100_johnson_full
- query_only baseline: 812000 +- 0 CU.
- minimal_subtree / raw_fibers: baseline 1279892 +- 0 CU -> batched 1201267 +- 0 CU (delta -78625), margin 198733 CU.
- minimal_subtree / local_interpolant: baseline 1287287 +- 0 CU -> batched 1208662 +- 0 CU (delta -78625), margin 191338 CU.
- best measured stack: raw_fibers / round_batch_inversion at 1201267 CU total, 1186123 CU verify, margin 198733 CU, verify 10/10 ok, trace 10/10 complete.
- best-path phase means: transcript setup 11663, OOD 7343, per-round queries 1098228, folding 7928, final round 61925.

### whir_t128_capacity_full
- query_only baseline: 602252 +- 0 CU.
- minimal_subtree / raw_fibers: baseline 928373 +- 0 CU -> batched 874724 +- 0 CU (delta -53649), round-0 projection 874453 CU, projection delta +271, margin 525276 CU.
- minimal_subtree / local_interpolant: baseline 933578 +- 0 CU -> batched 879929 +- 0 CU (delta -53649), round-0 projection 879662 CU, projection delta +267, margin 520071 CU.
- best measured stack: raw_fibers / round_batch_inversion at 874724 CU total, 862238 CU verify, margin 525276 CU, verify 10/10 ok, trace 10/10 complete.
- best-path phase means: transcript setup 19425, OOD 12144, per-round queries 770128, folding 12462, final round 49043.

## WHIR Proof-Carried Round-Local Structure
- Executed: `minimal_subtree` full-transcript verifier runs for `whir_t128_capacity_full` and `whir_t100_johnson_full`, with both fold payloads (`raw_fibers`, `local_interpolant`), `round_batch_inversion`, and an A/B between `none` and `proof_carried_round_local` query supplements.
- Executed: 10 SBF repetitions for `verify_sbf` and `total_sbf`, plus 10 traced repetitions for phase breakdown, with valid/invalid proof checks before timing.
- Prototype: each transcript query carries a checked supplement for numerator evaluation, selector affine terms, selector weight sum, and both CM31 denominator products, so the verifier can skip the repeated round-local rebuild when the transcript bytes are correct.

### whir_t100_johnson_full
- minimal_subtree / raw_fibers: baseline 1204370 +- 0 CU -> proof-carried 1188500 +- 0 CU (delta -15870), per-round bucket -18396, verify -18320, proof bytes +1008, margin 211500 CU.
- minimal_subtree / local_interpolant: baseline 1211765 +- 0 CU -> proof-carried 1195942 +- 0 CU (delta -15823), per-round bucket -18349, verify -18273, proof bytes +1008, margin 204058 CU.
- best measured stack: raw_fibers / proof_carried_round_local at 1188500 CU total, 1170654 CU verify, margin 211500 CU, proof 8448 bytes, verify 10/10 ok, trace 10/10 complete.
- best-path phase means: transcript setup 11657, OOD 7343, per-round queries 1082673, folding 7915, final round 61964.

### whir_t128_capacity_full
- minimal_subtree / raw_fibers: baseline 876938 +- 0 CU -> proof-carried 852745 +- 0 CU (delta -24193), per-round bucket -16629, verify -24349, proof bytes +312, margin 547255 CU, prior round-0 share 85.4%.
- minimal_subtree / local_interpolant: baseline 882143 +- 0 CU -> proof-carried 857769 +- 0 CU (delta -24374), per-round bucket -16695, verify -24530, proof bytes +312, margin 542231 CU, prior round-0 share 85.5%.
- best measured stack: raw_fibers / proof_carried_round_local at 852745 CU total, 839893 CU verify, margin 547255 CU, proof 6244 bytes, verify 10/10 ok, trace 10/10 complete.
- best-path phase means: transcript setup 11657, OOD 12145, per-round queries 755475, folding 12472, final round 49042.
## Shipping Freeze
- Shipping recommendation: freeze `whir-m31-capacity-v0` on `whir_t128_capacity_full` now and treat Johnson as a separate round-0 research track.
- Exact measured shipping profile: `reference_canonical` + `karatsuba` + `late_lift_qm31` + `raw_fibers` + `minimal_subtree` + `flat_nodes`.
- Measured total: 927227 +- 0 CU, verify 914591 +- 0 CU, upload 12636 CU, proof 5932 bytes, remaining margin 472773 CU, verify ok 10/10.
- Why this freeze: query-only 603811 CU -> transcript separate-paths 1014405 CU -> minimal-subtree local 932943 CU -> minimal-subtree raw 927227 CU. `local_interpolant` is +5209 CU versus raw on the real full path.
- Payload decision: keep `flat_nodes` for now. For `whir_t128_capacity_full` at `minimal_subtree`, flat nodes are 1792 bytes / 56241 CU total; canonical payload is 2476 bytes / 87827 CU total (delta +31586 CU).
