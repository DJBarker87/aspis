# Native WHIR M31 v0

## Goal
Build a fixed-profile native multilinear opening prover/verifier slice over the M31 -> CM31 -> QM31 tower, with host proving, host verification, and an exact-profile Solana verifier using the SHA-256 syscall path.

## Discovery Summary
- Existing reusable scaffold: `xtask`, `programs/phase1-probe`, `crates/svm-cost-model`, Phase 2 manifests/results, and the vendored `solana-pqzk-fullchain` engineering reference.
- Existing reusable logic: validator orchestration, transaction simulation, staged uploads, JSON/CSV writing, and the Phase 2 M31/CM31/QM31 measurement kernels.
- Replaced from the proxy path: synthetic proof envelopes, seed-derived statement binding, and synthetic WHIR record layouts.

## Frozen Scope
- Dev profile: `whir-m31-dev-v0` with log_rows=8, rounds=4, q=4, fold_vars=2, heap=32768 bytes.
- Target profile: `whir-m31-solana-v0` with log_rows=12, rounds=6, q=8, fold_vars=2, heap=65536 bytes.
- Fixed hash mode: SHA-256.
- Fixed fold mode: local_interpolant.
- Fixed statement binding: SpendV0-shaped anchor/nullifiers/outputs/asset/fee digest.

## Arithmetic Design
- M31 uses direct reduction modulo 2^31 - 1.
- CM31 implements both schoolbook and Karatsuba multiplication over x^2 + 1.
- QM31 implements the target quartic tower over u^2 - 2 - i with non-residue (2, 1) in CM31.
- The host and verifier default to late-lift evaluation for round-0 M31 blocks.

## Proof Format
- `WhirEnvelopeV1` is fixed-shape for each profile and manually parsed.
- The envelope carries profile id, version fields, statement digest, per-round Merkle roots, the final QM31 value, and per-round query openings.
- Merkle proofs are separate-path proofs in v0.

## Prover Design
- The prover commits one Merkle root per folding round over local-interpolant blocks.
- Fiat-Shamir transcript challenges are QM31 pairs derived after each round root.
- Query indices are derived after all round roots and the final value are absorbed.

## Verifier Design
- The verifier replays the transcript, recomputes query indices, verifies Merkle paths, evaluates each opened local interpolant at the transcript challenge, and checks consistency against the next committed round or the final QM31 value.
- The host verifier is the semantic oracle for the Solana verifier and uses the same parser/core verification logic.

## On-Chain Verifier Design
- The Solana program exposes `init_upload`, `upload_chunk`, and `verify` only.
- Proofs are uploaded into a fixed-layout account with a rolling SHA-256 upload digest.
- Verification accepts only the two fixed profiles and only the exact envelope/hash/fold modes emitted by the host prover.

## Statement Binding Design
- The public binding schema is `SpendV0Binding { anchor, nullifiers, outputs, asset_id, fee }` with a canonical byte encoding and SHA-256 statement digest.
- The digest is checked on host and chain before proof verification proceeds.

## Executed vs Implemented-Only
- Dev profile executed: host prove=true, host verify=true, on-chain verify=Some(true).
- Target profile executed: host prove=true, host verify=true, on-chain verify=Some(true).

## Measurements
- Dev proof bytes: Some(4108); on-chain verify CU: Some(96118); upload CU: Some(9694).
- Target proof bytes: Some(18316); on-chain verify CU: Some(326021); upload CU: Some(38965).
- Previous Phase 2 proxy reference points: `whir_t100_capacity_full = 458,043 CU`, `whir_t128_capacity_full = 599,602 CU`, `whir_t128_johnson_full = 1,095,421 CU`.

## Corruption Tests
- `flip_merkle_sibling`: host_rejected=true, onchain_rejected=true, onchain_error={"InstructionError":[2,"InvalidInstructionData"]}.
- `flip_fold_coefficient`: host_rejected=true, onchain_rejected=true, onchain_error={"InstructionError":[2,"InvalidInstructionData"]}.
- `flip_query_opening`: host_rejected=true, onchain_rejected=true, onchain_error={"InstructionError":[2,"InvalidInstructionData"]}.
- `flip_statement_digest`: host_rejected=true, onchain_rejected=true, onchain_error={"InstructionError":[2,"InvalidInstructionData"]}.

## Biggest Remaining Gaps To SpendV0
- v0 proves transcript-bound local fold consistency for a fixed committed multilinear table, but it is not yet the full WHIR paper path or a full SpendV0 arithmetic relation.

## Next Steps
- replace the deterministic table witness with the first real SpendV0 arithmetic/witness slice while keeping the same statement binding
- measure and, if needed, tighten the target profile with a narrower Merkle proof representation once real proof bytes dominate upload cost
- formalize the v0 soundness delta against the full WHIR protocol and decide which missing checks must land before SpendV0

_Generated 2026-04-19T20:40:52.726252+00:00 from `cargo xtask native-whir-m31`._