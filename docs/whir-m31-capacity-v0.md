# WHIR M31 Capacity v0

## Decision
Freeze `whir-m31-capacity-v0` as the shipping profile now. This is the measured capacity profile that is already under Solana's current 1.4M CU cap on the full transcript path.

## Frozen Profile
- Scenario: `whir_t128_capacity_full` (`128` bits, `whir_capacity_full`).
- Arithmetic kernel: `reference_canonical`.
- Extension kernel: `karatsuba`.
- Lift policy: `late_lift_qm31`.
- Fold mode: `raw_fibers`.
- Merkle mode: `minimal_subtree`.
- Merkle payload baseline: `flat_nodes`.
- Statement binding: spend-shaped Phase 2 statement.
- Transcript path: full transcript path with Fiat-Shamir, OOD, folding, final round.

## Measurements
- Total: 927227 +- 0 CU.
- Verify: 914591 +- 0 CU.
- Upload: 12636 CU.
- Proof bytes: 5932.
- Margin against the 1.4M cap: 472773 CU.

## Stage Breakdown
- parse: 1482 +- 0 CU.
- transcript setup: 19432 +- 0 CU.
- OOD: 12145 +- 0 CU.
- per-round queries: 822129 +- 0 CU.
- folding: 12808 +- 0 CU.
- final round: 49064 +- 0 CU.

## Comparisons
- Query-only baseline: 603811 CU.
- Transcript-inclusive, separate paths: 1014405 CU.
- Transcript-inclusive, minimal_subtree + local_interpolant: 932943 CU.
- Transcript-inclusive, minimal_subtree + raw_fibers: 927227 CU.
- `local_interpolant` delta on the measured full path: +5209 CU.

## Payload Decision
- Flat nodes: 1792 bytes, parse 52444 CU, total 56241 CU.
- Canonical payload: 2476 bytes, parse 82721 CU, total 87827 CU.
- Shipping decision: keep `flat_nodes` until a real prover-emitted payload beats it on measured total CU.

## Branch Split
- Shipping branch: `ship/whir-m31-capacity-v0`.
- Research branch: `research/johnson-round0`.

## Research Order
1. freeze the shipping branch on the measured capacity profile and keep Johnson off the critical path
2. implement proof-carried round-0 structure for Johnson before any more broad end-to-end reruns
3. run a taxonomy-driven round-0 specialization pass while preserving late_lift_qm31
4. defer external prover-emitted payload interop until after the round-0 representation settles

## Reproduction
- `cargo xtask phase2-transcript`
- `cargo xtask phase2-multiproof`
- `cargo xtask phase2-fold-payload`
- `cargo xtask phase2-multiproof-payload`
- `cargo xtask phase2-freeze-capacity-v0`

_Generated 2026-04-19T21:16:30.931273+00:00 from `cargo xtask phase2-freeze-capacity-v0`._